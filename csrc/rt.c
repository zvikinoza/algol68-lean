/* The C runtime of a compiled program: Algol 68 values in C memory.

   A program compiled by a68lean keeps every value here — its frames, its operand stack,
   its names, rows, structures, unions and closures — and calls the Lean services
   (`A68/Runtime.lean`) only for what is computed on copies: transput, formatting, the
   arithmetic of `LONG` modes, the standard prelude.  Values cross in the `A68.Blob`
   encoding; names, closures and format texts cross as addresses that the Lean side
   reaches back through (`a68c_load` and its relatives at the end of this file).

   The semantics of every entry point are those of the evaluator (`A68/Interp.lean`), whose
   names are quoted where a rule is reproduced.  The representation is described in
   docs/GC-DESIGN.md.  Its invariants:

   * A value is a 16-byte slot `a68_val`; whether its payload is a pointer is decided by the
     tag alone.
   * A row value is a descriptor (`a68_rowd`) over a store; descriptors of *values* are
     never modified and may share a store; the descriptor a variable's cell holds is the
     only one that is mutated, and a store shared with a value is copied before the
     variable writes into it (copy on write, counted in `rc` of the store).
   * A name of a sub-row is a descriptor whose base is the variable's descriptor (a view);
     it follows the variable through copy-on-write because its coordinates are in the
     store's index space, which a copy preserves.
   * Structure and union values on the operand stack are never aliased by a cell: every
     extraction from a container copies (`copy_value`).
   * The emitted C never holds a heap pointer in a C variable across a call; every live
     value is on the operand stack, in a frame reachable from the environment, or in the
     saved-environment stack.  Those are the collector's roots. */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

/* ---------------------------------------------------------------- values */

enum {
  T_UNDEF = 0, T_INT, T_REAL, T_BOOL, T_CHAR, T_BITS, T_VOID, T_NIL,
  T_REF, T_ROW, T_STRUCT, T_UNION, T_CPROC, T_FMT, T_BUILTIN, T_FILE,
  T_MP, T_BIGINT, T_BIGBITS, T_LREF
};

typedef struct a68_obj a68_obj;

typedef struct a68_val {
  uint32_t tag;
  uint32_t aux;    /* REF: offset; UNION: mode; CPROC: fn | nparams << 24; FMT: skeleton;
                      BUILTIN: string index; FILE: id; LREF: cell */
  union { int64_t i; double r; uint64_t u; a68_obj* p; } v;
} a68_val;

static inline int tag_is_ptr(uint32_t t) {
  return t == T_REF || t == T_ROW || t == T_STRUCT || t == T_UNION || t == T_CPROC
      || t == T_FMT || t == T_MP || t == T_BIGINT || t == T_BIGBITS;
}

/* ---------------------------------------------------------------- objects */

enum { K_SLOTS = 1, K_LEAF = 2, K_ROWD = 3, K_FRAME = 4 };
enum { EK_BYTES = 0xff };           /* a leaf of raw bytes: decimal digits, MP digits */

struct a68_obj {
  uint8_t  kind;
  uint8_t  mark;
  uint16_t ek;      /* leaf: element tag (T_INT … T_BITS) or EK_BYTES */
  uint32_t n;       /* slots: slot count; leaf: element count; rowd: dimensions; frame: cells */
  uint32_t rc;      /* store: descriptors sharing it (copy-on-write); others unused */
  uint32_t size;    /* bytes, header included */
  a68_obj* next;    /* every object, for the sweep */
};

typedef struct { a68_obj h; a68_val s[]; } a68_slots;
typedef struct { a68_obj h; uint8_t d[]; } a68_leaf;     /* elements, then a bitmap of defined ones */
typedef struct { int64_t l, u, stride; } a68_dim;
typedef struct { a68_obj h; a68_obj* base; int64_t off; a68_dim dim[]; } a68_rowd;
typedef struct a68_frame { a68_obj h; struct a68_frame* parent; uint32_t depth; uint32_t pad; a68_val c[]; } a68_frame;

#define VIEW_OFF 0xffffffffu        /* a REF whose target is the row a view describes */

static a68_obj* all_objects = NULL;
static uint64_t bytes_allocated = 0;      /* since the last collection */
static uint64_t bytes_live = 0;           /* after the last collection */
static int gc_wanted = 0;                 /* set by allocation, acted on at the next safe point */

/* The collector's modes (`A68LEAN_GC`): `off`, `stress` (collect at every safe point),
   `verify` (never reuse freed memory; check after every collection that nothing reachable
   was freed) and `stats` (report at exit).  `A68LEAN_HEAP` limits the live bytes. */
static int gc_off = 0, gc_stress = 0, gc_verify = 0, gc_stats = 0;
static uint64_t gc_limit = 0;
static uint64_t gc_min_between = 8u << 20;
static uint64_t gc_collections = 0, gc_freed_bytes = 0, gc_peak_live = 0;
static double gc_seconds = 0.0;
static void gc_collect(void);
#define GC_POLL() do { if (__builtin_expect(gc_wanted, 0)) gc_collect(); } while (0)

static void* xmalloc(size_t n) {
  void* p = calloc(1, n ? n : 1);
  if (!p) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  return p;
}

static a68_obj* obj_alloc(uint8_t kind, size_t size) {
  a68_obj* o = (a68_obj*) xmalloc(size);
  o->kind = kind;
  o->size = (uint32_t) size;
  o->next = all_objects;
  all_objects = o;
  bytes_allocated += size;
  if (!gc_off && (gc_stress || bytes_allocated > gc_min_between + 2 * bytes_live)) gc_wanted = 1;
  return o;
}

static size_t leaf_esize(uint16_t ek) {
  switch (ek) {
    case T_INT: case T_REAL: case T_BITS: return 8;
    case T_CHAR: case T_BOOL: return 1;
    default: return 1;
  }
}

static a68_leaf* leaf_alloc(uint16_t ek, uint32_t n) {
  size_t es = leaf_esize(ek);
  size_t bytes = (size_t) n * es + (ek == EK_BYTES ? 0 : (n + 7) / 8);
  a68_leaf* l = (a68_leaf*) obj_alloc(K_LEAF, sizeof(a68_leaf) + bytes);
  l->h.ek = ek;
  l->h.n = n;
  l->h.rc = 0;
  return l;
}

static a68_slots* slots_alloc(uint32_t n) {
  a68_slots* s = (a68_slots*) obj_alloc(K_SLOTS, sizeof(a68_slots) + (size_t) n * sizeof(a68_val));
  s->h.n = n;
  return s;
}

static a68_rowd* rowd_alloc(uint32_t ndims) {
  a68_rowd* r = (a68_rowd*) obj_alloc(K_ROWD, sizeof(a68_rowd) + (size_t) ndims * sizeof(a68_dim));
  r->h.n = ndims;
  return r;
}

/* ---------------------------------------------------------------- the Lean services */

extern uint32_t a68_line_no;
extern uint32_t a68_jump_flag;
void a68_set_state(lean_object* s);

lean_object* a68l_boot(lean_object* blob, uint32_t ll, uint8_t reg, lean_object* args, lean_object* w);
lean_object* a68l_finish(lean_object* w);
lean_object* a68l_stop(lean_object* w);
lean_object* a68l_die(lean_object* msg, lean_object* w);
lean_object* a68l_flush(lean_object* w);
lean_object* a68l_call(lean_object* name, lean_object* args, uint32_t nargs, lean_object* w);
lean_object* a68l_dyop(lean_object* op, uint32_t m1, uint32_t m2, lean_object* args, lean_object* w);
lean_object* a68l_monop(lean_object* op, uint32_t m, lean_object* arg, lean_object* w);
lean_object* a68l_widen(uint32_t src, uint32_t dst, lean_object* arg, lean_object* w);
lean_object* a68l_skip(uint32_t m, lean_object* w);
lean_object* a68l_conform(uint32_t m, uint32_t vm, lean_object* w);
lean_object* a68l_mode_is_union(uint32_t m, lean_object* w);
lean_object* a68l_lcell(uint32_t c, lean_object* w);
lean_object* a68l_lstore(uint32_t c, lean_object* b, lean_object* w);

/* supplied by the compiled program */
void a68_dispatch_proc(size_t fn);
void a68_dispatch_hole(size_t idx);

#define LW lean_io_mk_world()

static lean_object* io_ok(lean_object* r) {
  if (lean_io_result_is_error(r)) { lean_io_result_show_error(r); exit(1); }
  lean_object* v = lean_io_result_get_value(r);
  lean_inc(v);
  lean_dec(r);
  return v;
}
static void io_unit(lean_object* r) {
  if (lean_io_result_is_error(r)) { lean_io_result_show_error(r); exit(1); }
  lean_dec(r);
}
static uint32_t io_u32(lean_object* r) {
  if (lean_io_result_is_error(r)) { lean_io_result_show_error(r); exit(1); }
  uint32_t v = lean_unbox_uint32(lean_io_result_get_value(r));
  lean_dec(r);
  return v;
}
static uint8_t io_u8(lean_object* r) {
  if (lean_io_result_is_error(r)) { lean_io_result_show_error(r); exit(1); }
  uint8_t v = (uint8_t) lean_unbox(lean_io_result_get_value(r));
  lean_dec(r);
  return v;
}

__attribute__((noreturn)) static void die(const char* msg) {
  io_unit(a68l_die(lean_mk_string(msg), LW));
  exit(1);
}

__attribute__((noreturn)) static void dief(const char* fmt, int64_t a, int64_t b, int64_t c) {
  char buf[256];
  snprintf(buf, sizeof buf, fmt, (long long) a, (long long) b, (long long) c);
  die(buf);
}

/* Objects the Lean side keeps beyond a call — the name an `associate`d file writes, the
   routine an `on logical file end` calls — are pinned for the rest of the run. */
static a68_obj** pins = NULL;
static size_t npins = 0, pins_cap = 0;

static void pin(a68_obj* o) {
  if (!o) return;
  for (size_t i = 0; i < npins; i++) if (pins[i] == o) return;
  if (npins == pins_cap) {
    pins_cap = pins_cap ? pins_cap * 2 : 64;
    pins = (a68_obj**) realloc(pins, pins_cap * sizeof(a68_obj*));
    if (!pins) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  }
  pins[npins++] = o;
}

/* ---------------------------------------------------------------- tables */

static char** strtab = NULL;       /* the program's string table: literals, names */
static size_t* strlen_tab = NULL;
static size_t nstr = 0;

typedef struct { char kind[10]; int64_t len; } mode_info;
static mode_info* modetab = NULL;
static size_t nmode = 0;

static int hexval(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return 10 + c - 'a';
  return 0;
}

/* Every line of the blob defines one entry of every table (`A68.Serial`): the string and
   mode tables are read here, the rest stays with the Lean side. */
static void parse_tables(const char* blob) {
  size_t lines = 1;
  for (const char* p = blob; *p; p++) if (*p == '\n') lines++;
  strtab = (char**) xmalloc(lines * sizeof(char*));
  strlen_tab = (size_t*) xmalloc(lines * sizeof(size_t));
  modetab = (mode_info*) xmalloc(lines * sizeof(mode_info));
  const char* p = blob;
  size_t i = 0;
  while (1) {
    const char* e = strchr(p, '\n');
    size_t n = e ? (size_t) (e - p) : strlen(p);
    strtab[i] = (char*) xmalloc(1); strlen_tab[i] = 0;
    strcpy(modetab[i].kind, ""); modetab[i].len = 0;
    if (n >= 2 && p[0] == 's' && p[1] == ' ') {
      size_t hn = n - 2;
      char* s = (char*) xmalloc(hn / 2 + 1);
      for (size_t k = 0; k + 1 < hn; k += 2) s[k / 2] = (char) (hexval(p[2 + k]) * 16 + hexval(p[3 + k]));
      free(strtab[i]);
      strtab[i] = s; strlen_tab[i] = hn / 2;
    } else if (n >= 2 && p[0] == 'm' && p[1] == ' ') {
      char kind[10] = {0};
      long long len = 0;
      sscanf(p + 2, "%9s %lld", kind, &len);
      strcpy(modetab[i].kind, kind);
      modetab[i].len = len;
    }
    i++;
    if (!e) break;
    p = e + 1;
  }
  nstr = nmode = i;
}

static lean_object* lstr_of_table(uint32_t i) {
  return lean_mk_string_from_bytes(strtab[i], strlen_tab[i]);
}

/* ---------------------------------------------------------------- stacks */

static a68_val* stack = NULL;
static size_t sp = 0, stack_cap = 0;

static a68_frame* env = NULL;              /* the innermost frame */
static a68_frame** saved = NULL;           /* environments saved by env_set */
static size_t nsaved = 0, saved_cap = 0;

static inline void push(a68_val v) {
  if (sp == stack_cap) {
    stack_cap = stack_cap ? stack_cap * 2 : 1024;
    stack = (a68_val*) realloc(stack, stack_cap * sizeof(a68_val));
    if (!stack) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  }
  stack[sp++] = v;
}

static inline a68_val pop(void) {
  if (sp == 0) { fprintf(stderr, "uncaught exception: operand stack underflow\n"); exit(1); }
  return stack[--sp];
}

static inline a68_val* top(void) {
  if (sp == 0) { fprintf(stderr, "uncaught exception: operand stack underflow\n"); exit(1); }
  return &stack[sp - 1];
}

static a68_val mk_int(int64_t i) { a68_val v; v.tag = T_INT; v.aux = 0; v.v.i = i; return v; }
static a68_val mk_real(double r) { a68_val v; v.tag = T_REAL; v.aux = 0; v.v.r = r; return v; }
static a68_val mk_bool(int b) { a68_val v; v.tag = T_BOOL; v.aux = 0; v.v.u = b ? 1 : 0; return v; }
static a68_val mk_char(uint32_t c) { a68_val v; v.tag = T_CHAR; v.aux = 0; v.v.u = c; return v; }
static a68_val mk_bits(uint64_t b) { a68_val v; v.tag = T_BITS; v.aux = 0; v.v.u = b; return v; }
static a68_val mk_tag(uint32_t t) { a68_val v; v.tag = t; v.aux = 0; v.v.u = 0; return v; }
static a68_val mk_ptr(uint32_t t, a68_obj* p, uint32_t aux) { a68_val v; v.tag = t; v.aux = aux; v.v.p = p; return v; }

static a68_frame* frame_alloc(uint32_t n) {
  a68_frame* f = (a68_frame*) obj_alloc(K_FRAME, sizeof(a68_frame) + (size_t) n * sizeof(a68_val));
  f->h.n = n;
  f->parent = env;
  f->depth = env ? env->depth + 1 : 1;
  for (uint32_t i = 0; i < n; i++) f->c[i] = mk_tag(T_UNDEF);
  return f;
}

static a68_val* cell_of(uint32_t depth, uint32_t slot) {
  a68_frame* f = env;
  for (uint32_t k = 0; k < depth && f; k++) f = f->parent;
  if (!f || slot >= f->h.n) { fprintf(stderr, "a68lean: internal: frame depth %u slot %u out of range\n", depth, slot); exit(1); }
  return &f->c[slot];
}

/* ---------------------------------------------------------------- rows */

static inline a68_obj* rowd_store(const a68_rowd* r) {
  return r->base->kind == K_ROWD ? ((a68_rowd*) r->base)->base : r->base;
}
static inline a68_rowd* rowd_owner(a68_rowd* r) {
  return r->base->kind == K_ROWD ? (a68_rowd*) r->base : r;
}

static int64_t row_count(const a68_rowd* r) {
  int64_t n = 1;
  for (uint32_t k = 0; k < r->h.n; k++) {
    int64_t d = r->dim[k].u - r->dim[k].l + 1;
    if (d <= 0) return 0;
    n *= d;
  }
  return n;
}

/* the store index of the element at flat position `flat` in row-major order of the view */
static int64_t row_store_index(const a68_rowd* r, int64_t flat) {
  int64_t idx = r->off;
  for (uint32_t k = r->h.n; k > 0; k--) {
    int64_t ext = r->dim[k - 1].u - r->dim[k - 1].l + 1;
    int64_t i = flat % ext;
    flat /= ext;
    idx += i * r->dim[k - 1].stride;
  }
  return idx;
}

static a68_val store_get(a68_obj* st, int64_t idx) {
  if (st->kind == K_SLOTS) return ((a68_slots*) st)->s[idx];
  a68_leaf* l = (a68_leaf*) st;
  size_t es = leaf_esize(l->h.ek);
  const uint8_t* bits = l->d + (size_t) l->h.n * es;
  if (!(bits[idx >> 3] & (1u << (idx & 7)))) return mk_tag(T_UNDEF);
  const uint8_t* e = l->d + (size_t) idx * es;
  switch (l->h.ek) {
    case T_INT: { int64_t x; memcpy(&x, e, 8); return mk_int(x); }
    case T_REAL: { double x; memcpy(&x, e, 8); return mk_real(x); }
    case T_BITS: { uint64_t x; memcpy(&x, e, 8); return mk_bits(x); }
    case T_CHAR: return mk_char(*e);
    case T_BOOL: return mk_bool(*e);
    default: return mk_tag(T_UNDEF);
  }
}

/* whether a leaf of kind `ek` can hold `v` */
static int leaf_accepts(uint16_t ek, const a68_val* v) {
  if (v->tag == T_UNDEF) return 1;
  if (v->tag != ek) return 0;
  if (ek == T_CHAR) return v->v.u < 256;
  return 1;
}

static void store_set(a68_obj* st, int64_t idx, a68_val v) {
  if (st->kind == K_SLOTS) { ((a68_slots*) st)->s[idx] = v; return; }
  a68_leaf* l = (a68_leaf*) st;
  size_t es = leaf_esize(l->h.ek);
  uint8_t* bits = l->d + (size_t) l->h.n * es;
  uint8_t* e = l->d + (size_t) idx * es;
  if (v.tag == T_UNDEF) { bits[idx >> 3] &= (uint8_t) ~(1u << (idx & 7)); return; }
  bits[idx >> 3] |= (uint8_t) (1u << (idx & 7));
  switch (l->h.ek) {
    case T_INT: memcpy(e, &v.v.i, 8); break;
    case T_REAL: memcpy(e, &v.v.r, 8); break;
    case T_BITS: memcpy(e, &v.v.u, 8); break;
    case T_CHAR: case T_BOOL: *e = (uint8_t) v.v.u; break;
    default: break;
  }
}

/* a store of `n` elements able to hold `sample`, and everything a leaf of its kind holds */
static a68_obj* store_alloc_for(uint32_t n, const a68_val* sample) {
  if (sample && (sample->tag == T_INT || sample->tag == T_REAL || sample->tag == T_BITS
                 || sample->tag == T_BOOL || (sample->tag == T_CHAR && sample->v.u < 256)))
    return (a68_obj*) leaf_alloc((uint16_t) sample->tag, n);
  return (a68_obj*) slots_alloc(n);
}

static a68_obj* store_alloc_slots(uint32_t n) { return (a68_obj*) slots_alloc(n); }

/* a copy of a store, same layout (copy on write) */
static a68_obj* store_copy(a68_obj* st) {
  if (st->kind == K_SLOTS) {
    a68_slots* c = slots_alloc(st->n);
    memcpy(c->s, ((a68_slots*) st)->s, (size_t) st->n * sizeof(a68_val));
    return (a68_obj*) c;
  }
  a68_leaf* l = (a68_leaf*) st;
  a68_leaf* c = leaf_alloc(l->h.ek, l->h.n);
  size_t es = leaf_esize(l->h.ek);
  memcpy(c->d, l->d, (size_t) l->h.n * es + (l->h.ek == EK_BYTES ? 0 : (l->h.n + 7) / 8));
  return (a68_obj*) c;
}

/* before writing through a variable's descriptor: give it a store of its own */
static void own_store(a68_rowd* owner) {
  a68_obj* st = owner->base;
  if (st->rc > 1) {
    a68_obj* c = store_copy(st);
    st->rc--;
    c->rc = 1;
    owner->base = c;
  }
}

/* a fresh descriptor over the same store and coordinates (a value from a name, or a copy) */
static a68_rowd* rowd_share(const a68_rowd* r) {
  a68_rowd* n = rowd_alloc(r->h.n);
  a68_obj* st = rowd_store(r);
  n->base = st;
  st->rc++;
  n->off = r->off;
  memcpy(n->dim, r->dim, (size_t) r->h.n * sizeof(a68_dim));
  return n;
}

/* a fresh row with canonical layout holding copies of the elements of `r` */
static a68_val copy_value(a68_val v);
static a68_rowd* row_canonical_copy(const a68_rowd* r) {
  int64_t n = row_count(r);
  a68_obj* st = rowd_store(r);
  a68_rowd* c = rowd_alloc(r->h.n);
  int64_t stride = 1;
  for (uint32_t k = r->h.n; k > 0; k--) {
    c->dim[k - 1].l = r->dim[k - 1].l;
    c->dim[k - 1].u = r->dim[k - 1].u;
    c->dim[k - 1].stride = stride;
    int64_t ext = r->dim[k - 1].u - r->dim[k - 1].l + 1;
    stride *= ext > 0 ? ext : 0;
  }
  c->off = 0;
  a68_obj* ns;
  if (st->kind == K_LEAF) {
    ns = (a68_obj*) leaf_alloc(st->ek, (uint32_t) n);
    for (int64_t i = 0; i < n; i++) store_set(ns, i, store_get(st, row_store_index(r, i)));
  } else {
    ns = store_alloc_slots((uint32_t) n);
    for (int64_t i = 0; i < n; i++) store_set(ns, i, copy_value(store_get(st, row_store_index(r, i))));
  }
  ns->rc = 1;
  c->base = ns;
  return c;
}

static a68_val copy_value(a68_val v) {
  switch (v.tag) {
    case T_ROW: return mk_ptr(T_ROW, (a68_obj*) rowd_share((a68_rowd*) v.v.p), 0);
    case T_STRUCT: {
      a68_slots* s = (a68_slots*) v.v.p;
      a68_slots* c = slots_alloc(s->h.n);
      for (uint32_t i = 0; i < s->h.n; i++) c->s[i] = copy_value(s->s[i]);
      return mk_ptr(T_STRUCT, (a68_obj*) c, 0);
    }
    case T_UNION: {
      a68_slots* s = (a68_slots*) v.v.p;
      a68_slots* c = slots_alloc(1);
      c->s[0] = copy_value(s->s[0]);
      return mk_ptr(T_UNION, (a68_obj*) c, v.aux);
    }
    default: return v;
  }
}

/* ---------------------------------------------------------------- names */

/* The value a name refers to, as stored (not copied). */
static a68_val* ref_slot(a68_val r) {
  a68_obj* b = r.v.p;
  if (b->kind == K_SLOTS) return &((a68_slots*) b)->s[r.aux / sizeof(a68_val)];
  if (b->kind == K_FRAME) return &((a68_frame*) b)->c[r.aux / sizeof(a68_val)];
  return NULL;
}

static a68_val ref_load(a68_val r) {
  a68_obj* b = r.v.p;
  if (b->kind == K_ROWD) {
    a68_rowd* d = (a68_rowd*) b;
    if (r.aux == VIEW_OFF) return mk_ptr(T_ROW, (a68_obj*) rowd_share(d), 0);
    return copy_value(store_get(rowd_store(d), (int64_t) r.aux));
  }
  a68_val* s = ref_slot(r);
  return copy_value(*s);
}

static a68_val deref(a68_val r) {
  switch (r.tag) {
    case T_REF: return ref_load(r);
    case T_FILE: return r;
    case T_NIL: die("attempt to dereference NIL");
    case T_UNDEF: die("attempt to use an uninitialised REF value");
    case T_LREF: return r;   /* resolved by the caller through the Lean side */
    default: die("internal: dereferencing a non-REF");
  }
}

/* The descriptor a row name designates: the variable's own, or a view. */
static a68_rowd* ref_rowd(a68_val r) {
  a68_obj* b = r.v.p;
  if (b->kind == K_ROWD) {
    if (r.aux == VIEW_OFF) return (a68_rowd*) b;
    a68_val e = store_get(rowd_store((a68_rowd*) b), (int64_t) r.aux);
    if (e.tag == T_ROW) return (a68_rowd*) e.v.p;   /* an element that is itself a row */
    return NULL;
  }
  a68_val* s = ref_slot(r);
  if (s->tag == T_ROW) return (a68_rowd*) s->v.p;
  return NULL;
}

/* Put a value into a slot of a cell, structure or row store: rows get a descriptor the
   slot owns, so that later assignments through the slot never touch a value's. */
static void slot_put(a68_val* slot, a68_val v) {
  if (v.tag == T_ROW) v = mk_ptr(T_ROW, (a68_obj*) rowd_share((a68_rowd*) v.v.p), 0);
  *slot = v;
}

static void bounds_mismatch(void) { die("bounds of source and destination do not match"); }

/* Copy the elements of `src` into the row `dst` designates, which has the same number of
   elements (checked by the caller); a view writes through its owner's store. */
static void row_copy_into(a68_rowd* dst, const a68_rowd* src) {
  a68_rowd* owner = rowd_owner(dst);
  own_store(owner);
  a68_obj* ds = rowd_store(dst);
  a68_obj* ss = rowd_store(src);
  int64_t n = row_count(dst);
  if (ds->kind == K_LEAF && ss->kind == K_LEAF && ds->ek == ss->ek) {
    for (int64_t i = 0; i < n; i++)
      store_set(ds, row_store_index(dst, i), store_get(ss, row_store_index(src, i)));
    return;
  }
  for (int64_t i = 0; i < n; i++) {
    a68_val e = store_get(ss, row_store_index(src, i));
    if (ds->kind == K_LEAF && !leaf_accepts(ds->ek, &e)) {
      /* the destination leaf cannot hold this element: widen the store to slots */
      a68_slots* ns = slots_alloc(ds->n);
      for (int64_t k = 0; k < (int64_t) ds->n; k++) ns->s[k] = store_get(ds, k);
      ns->h.rc = 1;
      owner->base = (a68_obj*) ns;
      ds = (a68_obj*) ns;
    }
    store_set(ds, row_store_index(dst, i), ds->kind == K_LEAF ? e : copy_value(e));
  }
}

/* Replace the row a variable's descriptor holds by a canonical copy of `src` (a flexible
   assignment); the descriptor object stays, so names into the variable stay valid. */
static void row_replace(a68_rowd* dst, const a68_rowd* src) {
  a68_rowd* c = row_canonical_copy(src);
  if (dst->base->kind != K_ROWD && dst->base->rc > 0) dst->base->rc--;
  if (dst->h.n == c->h.n) {
    dst->base = c->base;
    dst->off = c->off;
    memcpy(dst->dim, c->dim, (size_t) c->h.n * sizeof(a68_dim));
  } else {
    /* a different number of dimensions cannot happen for a well-typed program */
    die("internal: row assignment changes the rank");
  }
}

static int same_bounds(const a68_rowd* a, const a68_rowd* b) {
  if (a->h.n != b->h.n) return 0;
  for (uint32_t k = 0; k < a->h.n; k++)
    if (a->dim[k].l != b->dim[k].l || a->dim[k].u != b->dim[k].u) return 0;
  return 1;
}

/* Assign `v` into the slot `s`, keeping the objects the slot owns (`Interp.assignTo`,
   `Interp.updatePath`): a row is copied element by element when the bounds agree, a
   structure field by field, and anything else replaces the slot's value. */
static void assign_slot(a68_val* s, a68_val v, int flex, int checked) {
  if (v.tag == T_ROW) {
    a68_rowd* src = (a68_rowd*) v.v.p;
    if (s->tag == T_ROW) {
      a68_rowd* old = (a68_rowd*) s->v.p;
      int empty_old = row_count(old) == 0;
      if (checked && !flex && !same_bounds(old, src) && !empty_old) bounds_mismatch();
      if (!flex && same_bounds(old, src) && !checked) { row_copy_into(old, src); return; }
      if (!flex && same_bounds(old, src)) { row_copy_into(old, src); return; }
      row_replace(old, src);
      return;
    }
    slot_put(s, v);
    return;
  }
  if (v.tag == T_STRUCT && s->tag == T_STRUCT) {
    a68_slots* d = (a68_slots*) s->v.p;
    a68_slots* c = (a68_slots*) v.v.p;
    if (d->h.n == c->h.n) {
      for (uint32_t i = 0; i < d->h.n; i++) assign_slot(&d->s[i], c->s[i], 1, 0);
      return;
    }
  }
  slot_put(s, copy_value(v));
}

/* `Interp.assignTo`: the checks, then the write. */
static void assign_ref(a68_val d, a68_val v, int flex) {
  if (d.tag == T_NIL) die("attempt to assign to NIL");
  if (d.tag == T_LREF) {
    /* a name the Lean side made: hand the value over */
    extern lean_object* encode_blob(a68_val v);
    io_unit(a68l_lstore(d.aux, encode_blob(v), LW));
    return;
  }
  if (d.tag != T_REF) die("internal: assignment to a non-REF");
  if (v.tag == T_UNDEF) die("attempt to use an uninitialised value");
  a68_obj* b = d.v.p;
  if (b->kind == K_ROWD) {
    a68_rowd* r = (a68_rowd*) b;
    if (d.aux == VIEW_OFF) {
      /* assignment to a sub-row: the sizes have to agree */
      if (v.tag != T_ROW) die("internal: sub-row assignment of non-row");
      a68_rowd* src = (a68_rowd*) v.v.p;
      if (row_count(r) != row_count(src)) bounds_mismatch();
      row_copy_into(r, src);
      return;
    }
    a68_obj* st = rowd_store(r);
    if (st->kind == K_LEAF) {
      if (!leaf_accepts(st->ek, &v)) {
        /* the element's leaf store cannot hold this value: widen to slots */
        a68_rowd* owner = rowd_owner(r);
        own_store(owner);
        st = rowd_store(r);
        a68_slots* ns = slots_alloc(st->n);
        for (int64_t k = 0; k < (int64_t) st->n; k++) ns->s[k] = store_get(st, k);
        ns->h.rc = 1;
        owner->base = (a68_obj*) ns;
        st = (a68_obj*) ns;
        store_set(st, (int64_t) d.aux, copy_value(v));
        return;
      }
      own_store(rowd_owner(r));
      store_set(rowd_store(r), (int64_t) d.aux, v);
      return;
    }
    own_store(rowd_owner(r));
    st = rowd_store(r);
    assign_slot(&((a68_slots*) st)->s[d.aux], v, flex, 1);
    return;
  }
  assign_slot(ref_slot(d), v, flex, 1);
}

/* `Interp.writeRef`: write without the assignment's checks. */
static void store_ref(a68_val d, a68_val v) {
  if (d.tag == T_LREF) {
    extern lean_object* encode_blob(a68_val v);
    io_unit(a68l_lstore(d.aux, encode_blob(v), LW));
    return;
  }
  if (d.tag != T_REF) die("internal: assignment to a non-REF");
  a68_obj* b = d.v.p;
  if (b->kind == K_ROWD) {
    a68_rowd* r = (a68_rowd*) b;
    if (d.aux == VIEW_OFF) {
      if (v.tag != T_ROW) die("internal: sub-row assignment of non-row");
      a68_rowd* src = (a68_rowd*) v.v.p;
      if (row_count(r) != row_count(src)) bounds_mismatch();
      row_copy_into(r, src);
      return;
    }
    own_store(rowd_owner(r));
    a68_obj* st = rowd_store(r);
    if (st->kind == K_LEAF && !leaf_accepts(st->ek, &v)) {
      a68_rowd* owner = rowd_owner(r);
      a68_slots* ns = slots_alloc(st->n);
      for (int64_t k = 0; k < (int64_t) st->n; k++) ns->s[k] = store_get(st, k);
      ns->h.rc = 1;
      owner->base = (a68_obj*) ns;
      st = (a68_obj*) ns;
    }
    if (st->kind == K_LEAF) store_set(st, (int64_t) d.aux, v);
    else assign_slot(&((a68_slots*) st)->s[d.aux], v, 1, 0);
    return;
  }
  assign_slot(ref_slot(d), v, 1, 0);
}

/* The name of field `f` of the structure a name refers to. */
static a68_val ref_field(a68_val r, uint32_t f) {
  if (r.tag == T_NIL) die("attempt to select from NIL");
  if (r.tag != T_REF) die("internal: select via non-REF");
  a68_obj* b = r.v.p;
  a68_val target;
  if (b->kind == K_ROWD) {
    if (r.aux == VIEW_OFF) die("internal: unsupported multiple selection through a name");
    target = store_get(rowd_store((a68_rowd*) b), (int64_t) r.aux);
  } else target = *ref_slot(r);
  if (target.tag != T_STRUCT) die("internal: field selection on non-struct");
  a68_slots* s = (a68_slots*) target.v.p;
  if (f >= s->h.n) die("internal: field index out of range");
  return mk_ptr(T_REF, (a68_obj*) s, f * (uint32_t) sizeof(a68_val));
}

/* ---------------------------------------------------------------- slicing */

/* `Interp.sliceValue`.  `ixs[k]` describes indexer `k`: an index, or a trim with optional
   bounds and `AT`. */
typedef struct { int is_trim, has_lo, has_hi, has_at; int64_t i, lo, hi, at; } indexer;

static void slice_into(a68_rowd* r, int is_name, const indexer* ixs, uint32_t nidx, a68_val* out) {
  if (nidx != r->h.n) die("internal: wrong number of subscripts");
  int ntrim = 0;
  for (uint32_t k = 0; k < nidx; k++) if (ixs[k].is_trim) ntrim++;
  int64_t off = r->off;
  a68_rowd* nr = NULL;
  if (ntrim) nr = rowd_alloc((uint32_t) ntrim);
  int j = 0;
  for (uint32_t k = 0; k < nidx; k++) {
    int64_t l = r->dim[k].l, u = r->dim[k].u, st = r->dim[k].stride;
    if (!ixs[k].is_trim) {
      int64_t i = ixs[k].i;
      if (i < l || i > u) dief("index %lld out of bounds [%lld:%lld]", i, l, u);
      off += (i - l) * st;
    } else {
      int64_t lo = ixs[k].has_lo ? ixs[k].lo : l;
      int64_t hi = ixs[k].has_hi ? ixs[k].hi : u;
      if (lo < l || hi > u) {
        if (!(hi < lo)) dief("trim [%lld:%lld] out of bounds [%lld:%lld]", lo, hi, l /* :u below */);
      }
      int64_t nl = ixs[k].has_at ? ixs[k].at : 1;
      nr->dim[j].l = nl;
      nr->dim[j].u = nl + (hi - lo);
      nr->dim[j].stride = st;
      off += (lo - l) * st;
      j++;
    }
  }
  if (!ntrim) {
    if (is_name) { *out = mk_ptr(T_REF, (a68_obj*) r, (uint32_t) off); return; }
    *out = copy_value(store_get(rowd_store(r), off));
    return;
  }
  nr->off = off;
  if (is_name) {
    nr->base = (a68_obj*) rowd_owner(r);
    *out = mk_ptr(T_REF, (a68_obj*) nr, VIEW_OFF);
  } else {
    a68_obj* st = rowd_store(r);
    nr->base = st;
    st->rc++;
    *out = mk_ptr(T_ROW, (a68_obj*) nr, 0);
  }
}

/* the trim error above needs both bounds; `dief` takes three numbers, so report properly */
static void trim_error(int64_t lo, int64_t hi, int64_t l, int64_t u) {
  char buf[200];
  snprintf(buf, sizeof buf, "trim [%lld:%lld] out of bounds [%lld:%lld]", (long long) lo, (long long) hi, (long long) l, (long long) u);
  die(buf);
}

/* ---------------------------------------------------------------- the collector */
/*
   Mark–sweep, non-moving (docs/GC-DESIGN.md §4).  Marking is a worklist over objects: a
   SLOTS or FRAME object contributes each slot whose tag says pointer (and a frame its
   parent), a ROWD its base, a LEAF nothing.  The roots are the operand stack, the frame
   chain, the saved environments and the pins.  Sweeping frees every unmarked object, after
   dropping its share of a store that stays alive.  The C functions here transcribe
   `A68.Verified.GC`: `gc_mark` is `markAll`, `gc_sweep` is `sweep`. */

static a68_obj** worklist = NULL;
static size_t nwork = 0, work_cap = 0;

static inline void gc_push_obj(a68_obj* o) {
  if (!o || o->mark) return;
  o->mark = 1;
  if (nwork == work_cap) {
    work_cap = work_cap ? work_cap * 2 : 4096;
    worklist = (a68_obj**) realloc(worklist, work_cap * sizeof(a68_obj*));
    if (!worklist) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  }
  worklist[nwork++] = o;
}

static inline void gc_push_val(const a68_val* v) {
  if (tag_is_ptr(v->tag)) gc_push_obj(v->v.p);
}

static void gc_mark(void) {
  nwork = 0;
  for (size_t i = 0; i < sp; i++) gc_push_val(&stack[i]);
  gc_push_obj((a68_obj*) env);
  for (size_t i = 0; i < nsaved; i++) gc_push_obj((a68_obj*) saved[i]);
  for (size_t i = 0; i < npins; i++) gc_push_obj(pins[i]);
  while (nwork) {
    a68_obj* o = worklist[--nwork];
    switch (o->kind) {
      case K_SLOTS: { a68_slots* s = (a68_slots*) o; for (uint32_t i = 0; i < o->n; i++) gc_push_val(&s->s[i]); break; }
      case K_FRAME: { a68_frame* f = (a68_frame*) o; gc_push_obj((a68_obj*) f->parent); for (uint32_t i = 0; i < o->n; i++) gc_push_val(&f->c[i]); break; }
      case K_ROWD: gc_push_obj(((a68_rowd*) o)->base); break;
      default: break;
    }
  }
}

enum { K_FREED = 0xee };

static void gc_sweep(void) {
  /* a dead descriptor gives back its share of a store that survives */
  for (a68_obj* o = all_objects; o; o = o->next)
    if (!o->mark && o->kind == K_ROWD) {
      a68_obj* b = ((a68_rowd*) o)->base;
      if (b && b->mark && b->kind != K_ROWD && b->rc > 0) b->rc--;
    }
  a68_obj** link = &all_objects;
  uint64_t live = 0;
  while (*link) {
    a68_obj* o = *link;
    if (o->mark) { o->mark = 0; live += o->size; link = &o->next; continue; }
    *link = o->next;
    gc_freed_bytes += o->size;
    if (gc_verify) { o->kind = K_FREED; o->next = NULL; }   /* kept, poisoned, never reused */
    else free(o);
  }
  bytes_live = live;
}

/* In verify mode: nothing reachable may be poisoned. */
static void gc_verify_reachable(void) {
  gc_mark();
  for (a68_obj* o = all_objects; o; o = o->next) if (o->mark) {
    o->mark = 0;
    if (o->kind == K_FREED) { fprintf(stderr, "a68lean: gc verify: a freed object is reachable\n"); abort(); }
    switch (o->kind) {
      case K_SLOTS: { a68_slots* s = (a68_slots*) o; for (uint32_t i = 0; i < o->n; i++) if (tag_is_ptr(s->s[i].tag) && s->s[i].v.p->kind == K_FREED) { fprintf(stderr, "a68lean: gc verify: a slot points at a freed object\n"); abort(); } break; }
      case K_FRAME: { a68_frame* f = (a68_frame*) o; for (uint32_t i = 0; i < o->n; i++) if (tag_is_ptr(f->c[i].tag) && f->c[i].v.p->kind == K_FREED) { fprintf(stderr, "a68lean: gc verify: a cell points at a freed object\n"); abort(); } break; }
      case K_ROWD: if (((a68_rowd*) o)->base->kind == K_FREED) { fprintf(stderr, "a68lean: gc verify: a row points at a freed store\n"); abort(); } break;
      default: break;
    }
  }
  for (size_t i = 0; i < sp; i++) if (tag_is_ptr(stack[i].tag) && stack[i].v.p->kind == K_FREED) { fprintf(stderr, "a68lean: gc verify: the operand stack holds a freed object\n"); abort(); }
}

#include <time.h>

static void gc_collect(void) {
  gc_wanted = 0;
  if (gc_off) return;
  struct timespec t0, t1;
  clock_gettime(CLOCK_MONOTONIC, &t0);
  gc_mark();
  gc_sweep();
  if (gc_verify) gc_verify_reachable();
  clock_gettime(CLOCK_MONOTONIC, &t1);
  gc_seconds += (double) (t1.tv_sec - t0.tv_sec) + (double) (t1.tv_nsec - t0.tv_nsec) / 1e9;
  gc_collections++;
  bytes_allocated = 0;
  if (bytes_live > gc_peak_live) gc_peak_live = bytes_live;
  if (gc_limit && bytes_live > gc_limit) die("not enough memory");
}

static void gc_report(void) {
  if (!gc_stats) return;
  fprintf(stderr, "a68lean gc: %llu collections, %.1f MB freed, %.1f MB peak live, %.3f s\n",
          (unsigned long long) gc_collections, (double) gc_freed_bytes / 1048576.0,
          (double) gc_peak_live / 1048576.0, gc_seconds);
}

static void gc_init(void) {
  const char* m = getenv("A68LEAN_GC");
  if (m) {
    if (strstr(m, "off")) gc_off = 1;
    if (strstr(m, "stress")) gc_stress = 1;
    if (strstr(m, "verify")) gc_verify = 1;
    if (strstr(m, "stats")) gc_stats = 1;
  }
  const char* h = getenv("A68LEAN_HEAP");
  if (h) gc_limit = strtoull(h, NULL, 10);
  atexit(gc_report);
}

/* a68g's collector procedures: `sweep heap`, `collections`, `garbage`, `garbage seconds` */
lean_object* a68c_gc(uint32_t what, lean_object* w) {
  (void) w;
  switch (what) {
    case 0: gc_collect(); return lean_io_result_mk_ok(lean_box_float(0.0));
    case 1: return lean_io_result_mk_ok(lean_box_float((double) gc_collections));
    case 2: return lean_io_result_mk_ok(lean_box_float((double) gc_freed_bytes));
    case 3: return lean_io_result_mk_ok(lean_box_float(gc_seconds));
    default: return lean_io_result_mk_ok(lean_box_float(0.0));
  }
}

/* ---------------------------------------------------------------- the blob codec */

typedef struct { uint8_t* p; size_t n, cap; } buf;

static void buf_put(buf* b, const void* d, size_t n) {
  if (b->n + n > b->cap) {
    b->cap = (b->n + n) * 2 + 64;
    b->p = (uint8_t*) realloc(b->p, b->cap);
    if (!b->p) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  }
  memcpy(b->p + b->n, d, n);
  b->n += n;
}
static void put8(buf* b, uint8_t x) { buf_put(b, &x, 1); }
static void put32(buf* b, uint32_t x) { buf_put(b, &x, 4); }
static void put64(buf* b, uint64_t x) { buf_put(b, &x, 8); }
static void putstrn(buf* b, const uint8_t* s, uint32_t n) { put32(b, n); buf_put(b, s, n); }

enum { B_UNDEF = 0, B_INT, B_BIGINT, B_REAL, B_BOOL, B_CHAR, B_BITS, B_BIGBITS, B_VOID, B_NIL, B_REF,
       B_ROW, B_STRUCT, B_UNION, B_CPROC, B_CFMT, B_BUILTIN, B_FILE, B_MP, B_LREF };

static void encode_val(buf* b, a68_val v) {
  switch (v.tag) {
    case T_UNDEF: put8(b, B_UNDEF); break;
    case T_INT: put8(b, B_INT); put64(b, (uint64_t) v.v.i); break;
    case T_REAL: put8(b, B_REAL); put64(b, v.v.u); break;
    case T_BOOL: put8(b, B_BOOL); put8(b, (uint8_t) v.v.u); break;
    case T_CHAR: put8(b, B_CHAR); put32(b, (uint32_t) v.v.u); break;
    case T_BITS: put8(b, B_BITS); put64(b, v.v.u); break;
    case T_VOID: put8(b, B_VOID); break;
    case T_NIL: put8(b, B_NIL); break;
    case T_REF: put8(b, B_REF); put64(b, (uint64_t) (uintptr_t) v.v.p); put32(b, v.aux); break;
    case T_LREF: put8(b, B_LREF); put32(b, v.aux); break;
    case T_BUILTIN: put8(b, B_BUILTIN); putstrn(b, (const uint8_t*) strtab[v.aux], (uint32_t) strlen_tab[v.aux]); break;
    case T_FILE: put8(b, B_FILE); put32(b, v.aux); break;
    case T_CPROC: put8(b, B_CPROC); put32(b, v.aux & 0xffffff); put32(b, v.aux >> 24); put64(b, (uint64_t) (uintptr_t) v.v.p); break;
    case T_FMT: put8(b, B_CFMT); put64(b, (uint64_t) (uintptr_t) v.v.p); put32(b, v.aux); break;
    case T_BIGINT: case T_BIGBITS: case T_MP: {
      a68_leaf* l = (a68_leaf*) v.v.p;
      put8(b, v.tag == T_BIGINT ? B_BIGINT : v.tag == T_BIGBITS ? B_BIGBITS : B_MP);
      if (v.tag == T_MP) buf_put(b, l->d, l->h.n);   /* stored exactly as it crossed */
      else putstrn(b, l->d, l->h.n);
      break;
    }
    case T_UNION: {
      a68_slots* s = (a68_slots*) v.v.p;
      put8(b, B_UNION); put32(b, v.aux); encode_val(b, s->s[0]);
      break;
    }
    case T_STRUCT: {
      a68_slots* s = (a68_slots*) v.v.p;
      put8(b, B_STRUCT); put32(b, s->h.n);
      for (uint32_t i = 0; i < s->h.n; i++) encode_val(b, s->s[i]);
      break;
    }
    case T_ROW: {
      a68_rowd* r = (a68_rowd*) v.v.p;
      put8(b, B_ROW); put32(b, r->h.n);
      for (uint32_t k = 0; k < r->h.n; k++) { put64(b, (uint64_t) r->dim[k].l); put64(b, (uint64_t) r->dim[k].u); }
      int64_t n = row_count(r);
      put32(b, (uint32_t) n);
      a68_obj* st = rowd_store(r);
      for (int64_t i = 0; i < n; i++) encode_val(b, store_get(st, row_store_index(r, i)));
      break;
    }
    default: put8(b, B_UNDEF); break;
  }
}

lean_object* encode_blob(a68_val v) {
  buf b = {0};
  encode_val(&b, v);
  lean_object* r = lean_alloc_sarray(1, b.n, b.n);
  memcpy(lean_sarray_cptr(r), b.p, b.n);
  free(b.p);
  return r;
}

typedef struct { const uint8_t* p; size_t n, i; } rd;

static uint8_t get8(rd* r) { if (r->i + 1 > r->n) die("internal: blob truncated"); return r->p[r->i++]; }
static uint32_t get32(rd* r) { uint32_t x; if (r->i + 4 > r->n) die("internal: blob truncated"); memcpy(&x, r->p + r->i, 4); r->i += 4; return x; }
static uint64_t get64(rd* r) { uint64_t x; if (r->i + 8 > r->n) die("internal: blob truncated"); memcpy(&x, r->p + r->i, 8); r->i += 8; return x; }

static a68_val decode_val(rd* r) {
  uint8_t t = get8(r);
  switch (t) {
    case B_UNDEF: return mk_tag(T_UNDEF);
    case B_INT: return mk_int((int64_t) get64(r));
    case B_REAL: { a68_val v = mk_tag(T_REAL); v.v.u = get64(r); return v; }
    case B_BOOL: return mk_bool(get8(r));
    case B_CHAR: return mk_char(get32(r));
    case B_BITS: return mk_bits(get64(r));
    case B_VOID: return mk_tag(T_VOID);
    case B_NIL: return mk_tag(T_NIL);
    case B_REF: { uint64_t a = get64(r); uint32_t o = get32(r); return mk_ptr(T_REF, (a68_obj*) (uintptr_t) a, o); }
    case B_LREF: { a68_val v = mk_tag(T_LREF); v.aux = get32(r); return v; }
    case B_BUILTIN: {
      uint32_t n = get32(r);
      if (r->i + n > r->n) die("internal: blob truncated");
      /* find the name in the string table; add it when the Lean side made one up */
      for (size_t k = 0; k < nstr; k++)
        if (strlen_tab[k] == n && memcmp(strtab[k], r->p + r->i, n) == 0) { r->i += n; a68_val v = mk_tag(T_BUILTIN); v.aux = (uint32_t) k; return v; }
      strtab = (char**) realloc(strtab, (nstr + 1) * sizeof(char*));
      strlen_tab = (size_t*) realloc(strlen_tab, (nstr + 1) * sizeof(size_t));
      strtab[nstr] = (char*) xmalloc(n + 1); memcpy(strtab[nstr], r->p + r->i, n); strlen_tab[nstr] = n;
      r->i += n;
      a68_val v = mk_tag(T_BUILTIN); v.aux = (uint32_t) nstr; nstr++;
      return v;
    }
    case B_FILE: { a68_val v = mk_tag(T_FILE); v.aux = get32(r); return v; }
    case B_CPROC: { uint32_t fn = get32(r); uint32_t np = get32(r); uint64_t fr = get64(r); return mk_ptr(T_CPROC, (a68_obj*) (uintptr_t) fr, fn | (np << 24)); }
    case B_CFMT: { uint64_t fr = get64(r); uint32_t sk = get32(r); return mk_ptr(T_FMT, (a68_obj*) (uintptr_t) fr, sk); }
    case B_BIGINT: case B_BIGBITS: {
      uint32_t n = get32(r);
      if (r->i + n > r->n) die("internal: blob truncated");
      a68_leaf* l = leaf_alloc(EK_BYTES, n);
      memcpy(l->d, r->p + r->i, n);
      r->i += n;
      return mk_ptr(t == B_BIGINT ? T_BIGINT : T_BIGBITS, (a68_obj*) l, 0);
    }
    case B_MP: {
      /* st (8), ex (8), n (4), n digits (8 each): kept verbatim */
      if (r->i + 20 > r->n) die("internal: blob truncated");
      uint32_t n; memcpy(&n, r->p + r->i + 16, 4);
      size_t bytes = 20 + (size_t) n * 8;
      if (r->i + bytes > r->n) die("internal: blob truncated");
      a68_leaf* l = leaf_alloc(EK_BYTES, (uint32_t) bytes);
      memcpy(l->d, r->p + r->i, bytes);
      r->i += bytes;
      return mk_ptr(T_MP, (a68_obj*) l, 0);
    }
    case B_UNION: {
      uint32_t m = get32(r);
      a68_slots* s = slots_alloc(1);
      s->s[0] = decode_val(r);
      return mk_ptr(T_UNION, (a68_obj*) s, m);
    }
    case B_STRUCT: {
      uint32_t n = get32(r);
      a68_slots* s = slots_alloc(n);
      for (uint32_t i = 0; i < n; i++) s->s[i] = decode_val(r);
      return mk_ptr(T_STRUCT, (a68_obj*) s, 0);
    }
    case B_ROW: {
      uint32_t nd = get32(r);
      a68_rowd* d = rowd_alloc(nd);
      for (uint32_t k = 0; k < nd; k++) { d->dim[k].l = (int64_t) get64(r); d->dim[k].u = (int64_t) get64(r); }
      int64_t stride = 1;
      for (uint32_t k = nd; k > 0; k--) {
        d->dim[k - 1].stride = stride;
        int64_t ext = d->dim[k - 1].u - d->dim[k - 1].l + 1;
        stride *= ext > 0 ? ext : 0;
      }
      d->off = 0;
      uint32_t n = get32(r);
      a68_val* tmp = (a68_val*) xmalloc((n ? n : 1) * sizeof(a68_val));
      int leaf_ok = n > 0;
      for (uint32_t i = 0; i < n; i++) {
        tmp[i] = decode_val(r);
        if (i > 0 && tmp[i].tag != tmp[0].tag) leaf_ok = 0;
        if (tmp[i].tag == T_CHAR && tmp[i].v.u >= 256) leaf_ok = 0;
      }
      a68_obj* st = leaf_ok ? store_alloc_for(n, &tmp[0]) : store_alloc_slots(n);
      if (st->kind == K_SLOTS) for (uint32_t i = 0; i < n; i++) ((a68_slots*) st)->s[i] = tmp[i];
      else for (uint32_t i = 0; i < n; i++) store_set(st, i, tmp[i]);
      free(tmp);
      st->rc = 1;
      d->base = st;
      return mk_ptr(T_ROW, (a68_obj*) d, 0);
    }
    default: die("internal: bad blob tag");
  }
}

static a68_val decode_blob(lean_object* b) {
  rd r = { lean_sarray_cptr(b), lean_sarray_size(b), 0 };
  a68_val v = decode_val(&r);
  lean_dec(b);
  return v;
}

/* ---------------------------------------------------------------- the Lean side's view of C names */

static lean_object* bytes12(a68_val r) {
  lean_object* b = lean_alloc_sarray(1, 12, 12);
  uint64_t a = (uint64_t) (uintptr_t) r.v.p;
  memcpy(lean_sarray_cptr(b), &a, 8);
  memcpy(lean_sarray_cptr(b) + 8, &r.aux, 4);
  return b;
}

lean_object* a68c_load(uint64_t a, uint32_t o, lean_object* w) {
  (void) w;
  a68_val r = mk_ptr(T_REF, (a68_obj*) (uintptr_t) a, o);
  return lean_io_result_mk_ok(encode_blob(ref_load(r)));
}

lean_object* a68c_store(uint64_t a, uint32_t o, lean_object* b, lean_object* w) {
  (void) w;
  lean_inc(b);
  store_ref(mk_ptr(T_REF, (a68_obj*) (uintptr_t) a, o), decode_blob(b));
  return lean_io_result_mk_ok(lean_box(0));
}

lean_object* a68c_assign(uint64_t a, uint32_t o, lean_object* b, uint8_t flex, lean_object* w) {
  (void) w;
  lean_inc(b);
  assign_ref(mk_ptr(T_REF, (a68_obj*) (uintptr_t) a, o), decode_blob(b), flex);
  return lean_io_result_mk_ok(lean_box(0));
}

lean_object* a68c_field(uint64_t a, uint32_t o, uint32_t i, lean_object* w) {
  (void) w;
  return lean_io_result_mk_ok(bytes12(ref_field(mk_ptr(T_REF, (a68_obj*) (uintptr_t) a, o), i)));
}

/* The name of element `i`, in row-major order of the view, of the row a name refers to. */
lean_object* a68c_elem(uint64_t a, uint32_t o, uint32_t i, lean_object* w) {
  (void) w;
  a68_val r = mk_ptr(T_REF, (a68_obj*) (uintptr_t) a, o);
  a68_rowd* d = ref_rowd(r);
  if (!d) die("internal: element of a non-row");
  int64_t idx = row_store_index(d, (int64_t) i);
  return lean_io_result_mk_ok(bytes12(mk_ptr(T_REF, (a68_obj*) d, (uint32_t) idx)));
}

static void env_set(a68_frame* f) {
  if (nsaved == saved_cap) {
    saved_cap = saved_cap ? saved_cap * 2 : 64;
    saved = (a68_frame**) realloc(saved, saved_cap * sizeof(a68_frame*));
    if (!saved) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  }
  saved[nsaved++] = env;
  env = f;
}

static void env_restore(void) {
  if (nsaved == 0) { fprintf(stderr, "uncaught exception: environment stack underflow\n"); exit(1); }
  env = saved[--nsaved];
}

lean_object* a68c_call(uint32_t fn, uint32_t np, uint64_t fr, lean_object* args, uint32_t nargs, lean_object* w) {
  (void) w;
  lean_inc(args);
  rd r = { lean_sarray_cptr(args), lean_sarray_size(args), 0 };
  for (uint32_t i = 0; i < nargs; i++) push(decode_val(&r));
  lean_dec(args);
  a68_val f = mk_ptr(T_CPROC, (a68_obj*) (uintptr_t) fr, fn | (np << 24));
  /* the callee's prologue pops its arguments; when it left by a jump it pushed nothing */
  env_set((a68_frame*) f.v.p);
  a68_dispatch_proc(fn);
  env_restore();
  a68_val res = a68_jump_flag ? mk_tag(T_UNDEF) : pop();
  if (a68_jump_flag) { /* discard whatever the arguments left */ }
  return lean_io_result_mk_ok(encode_blob(res));
}

lean_object* a68c_hole(uint32_t fn, uint32_t idx, uint64_t fr, lean_object* w) {
  (void) w; (void) fn;
  env_set((a68_frame*) (uintptr_t) fr);
  a68_dispatch_hole(idx);
  env_restore();
  a68_val res = a68_jump_flag ? mk_tag(T_UNDEF) : pop();
  return lean_io_result_mk_ok(encode_blob(res));
}

/* ---------------------------------------------------------------- start-up and shutdown */

void a68rt_boot(const char* blob, uint32_t ll, uint8_t regression, int argc, char** argv, const char* src) {
  gc_init();
  parse_tables(blob);
  lean_object* args = lean_mk_empty_array();
  args = lean_array_push(args, lean_mk_string("a68g"));
  args = lean_array_push(args, lean_mk_string(src));
  for (int i = 1; i < argc; i++) args = lean_array_push(args, lean_mk_string(argv[i]));
  lean_object* st = io_ok(a68l_boot(lean_mk_string(blob), ll, regression, args, LW));
  a68_set_state(st);
}

uint32_t a68rt_finish(int w) { (void) w; return io_u32(a68l_finish(LW)); }
void a68rt_stop(int w) { (void) w; io_unit(a68l_stop(LW)); exit(0); }
void a68rt_line(uint32_t l, int w) { (void) w; a68_line_no = l; }

/* ---------------------------------------------------------------- jumps */

uint32_t a68rt_jump_pending(int w) { (void) w; return a68_jump_flag; }
void a68rt_jump_clear(int w) { (void) w; a68_jump_flag = 0; }
void a68rt_raise_jump(uint32_t l, int w) { (void) w; a68_jump_flag = l + 1; }

/* ---------------------------------------------------------------- environments */

void a68rt_enter(uint32_t n, int w) {
  GC_POLL(); (void) w; env = frame_alloc(n); }

void a68rt_enter_args(uint32_t n, uint32_t nargs, int w) {
  GC_POLL();
  (void) w;
  a68_frame* f = frame_alloc(n);
  for (uint32_t i = nargs; i > 0; i--) {
    a68_val v = pop();
    if (i - 1 < n) slot_put(&f->c[i - 1], v);
  }
  env = f;
}

uint32_t a68rt_heap_mark(int w) { (void) w; return 0; }
void a68rt_heap_release(uint32_t m, int w) { (void) m; (void) w; }
void a68rt_leave(int w) { (void) w; if (env) env = env->parent; }
uint32_t a68rt_env_depth(int w) { (void) w; return env ? env->depth : 0; }
void a68rt_env_truncate(uint32_t d, int w) { (void) w; while (env && env->depth > d) env = env->parent; }

/* ---------------------------------------------------------------- operand stack */

uint32_t a68rt_stack_depth(int w) { (void) w; return (uint32_t) sp; }
void a68rt_stack_truncate(uint32_t d, int w) { (void) w; if (d < sp) sp = d; }

void a68rt_push_int(int64_t v, int w) { (void) w; push(mk_int(v)); }
void a68rt_push_real(double v, int w) { (void) w; push(mk_real(v)); }
void a68rt_push_bool(uint8_t v, int w) { (void) w; push(mk_bool(v != 0)); }
void a68rt_push_char(uint32_t v, int w) { (void) w; push(mk_char(v)); }
void a68rt_push_bits(uint64_t v, int w) { (void) w; push(mk_bits(v)); }
void a68rt_push_undef(int w) { (void) w; push(mk_tag(T_UNDEF)); }
void a68rt_push_nil(int w) { (void) w; push(mk_tag(T_NIL)); }
void a68rt_push_void(int w) { (void) w; push(mk_tag(T_VOID)); }
void a68rt_push_builtin(uint32_t i, int w) { (void) w; a68_val v = mk_tag(T_BUILTIN); v.aux = i; push(v); }
void a68rt_push_file(uint32_t i, int w) { (void) w; a68_val v = mk_tag(T_FILE); v.aux = i; push(v); }

static a68_val big_of_string(uint32_t tag, const char* s, size_t n) {
  a68_leaf* l = leaf_alloc(EK_BYTES, (uint32_t) n);
  memcpy(l->d, s, n);
  return mk_ptr(tag, (a68_obj*) l, 0);
}

void a68rt_push_bigint(uint32_t i, int w) {
  GC_POLL(); (void) w; push(big_of_string(T_BIGINT, strtab[i], strlen_tab[i])); }
void a68rt_push_bigbits(uint32_t i, int w) {
  GC_POLL(); (void) w; push(big_of_string(T_BIGBITS, strtab[i], strlen_tab[i])); }

static a68_val string_row(const uint8_t* p, int64_t n, int64_t lwb) {
  a68_rowd* d = rowd_alloc(1);
  a68_leaf* l = leaf_alloc(T_CHAR, (uint32_t) n);
  memcpy(l->d, p, (size_t) n);
  memset(l->d + n, 0xff, ((size_t) n + 7) / 8);
  l->h.rc = 1;
  d->base = (a68_obj*) l;
  d->off = 0;
  d->dim[0].l = lwb; d->dim[0].u = lwb + n - 1; d->dim[0].stride = 1;
  return mk_ptr(T_ROW, (a68_obj*) d, 0);
}

void a68rt_push_str(uint32_t i, int w) {
  GC_POLL(); (void) w; push(string_row((const uint8_t*) strtab[i], (int64_t) strlen_tab[i], 1)); }

void a68rt_push_bytes(const uint8_t* p, int64_t n, int64_t lwb, int w) {
  GC_POLL(); (void) w; push(string_row(p, n, lwb)); }

/* The STRING on top of the operand stack as bytes the caller owns; the lower bound in `*lwb`. */
int64_t a68rt_pop_bytes(uint8_t** out, int64_t* lwb, int w) {
  (void) w;
  a68_val v = pop();
  if (v.tag == T_CHAR) {
    *out = (uint8_t*) xmalloc(1); (*out)[0] = (uint8_t) v.v.u; *lwb = 1; return 1;
  }
  if (v.tag == T_UNDEF) die("attempt to use an uninitialised value");
  if (v.tag != T_ROW) die("internal: STRING expected");
  a68_rowd* d = (a68_rowd*) v.v.p;
  if (d->h.n != 1) die("internal: STRING expected");
  int64_t n = row_count(d);
  uint8_t* b = (uint8_t*) xmalloc((size_t) n + 1);
  a68_obj* st = rowd_store(d);
  for (int64_t i = 0; i < n; i++) {
    a68_val e = store_get(st, row_store_index(d, i));
    if (e.tag == T_UNDEF) die("attempt to use an uninitialised CHAR value");
    if (e.tag != T_CHAR) die("internal: CHAR expected");
    b[i] = (uint8_t) e.v.u;
  }
  *out = b;
  *lwb = d->dim[0].l;
  return n;
}

/* `SKIP` of a mode: the Lean side knows the default (`Interp.defaultOf`). */
void a68rt_push_skip(uint32_t m, int w) {
  GC_POLL(); (void) w; push(decode_blob(io_ok(a68l_skip(m, LW)))); }

void a68rt_pop(int w) { (void) w; (void) pop(); }
void a68rt_dup(int w) { (void) w; a68_val v = *top(); push(v); }
void a68rt_nip(int w) {
  (void) w;
  if (sp < 2) { fprintf(stderr, "uncaught exception: nip on a short stack\n"); exit(1); }
  stack[sp - 2] = stack[sp - 1];
  sp--;
}

void a68rt_push_cell(uint32_t d, uint32_t s, int w) {
  GC_POLL();
  (void) w;
  a68_val* c = cell_of(d, s);
  if (c->tag == T_UNDEF) die("attempt to use an uninitialised value");
  push(copy_value(*c));
}

void a68rt_push_ref(uint32_t d, uint32_t s, int w) {
  (void) w;
  a68_frame* f = env;
  for (uint32_t k = 0; k < d && f; k++) f = f->parent;
  if (!f) die("internal: frame depth out of range");
  push(mk_ptr(T_REF, (a68_obj*) f, s * (uint32_t) sizeof(a68_val)));
}

void a68rt_store(uint32_t d, uint32_t s, int w) { (void) w; a68_val v = pop(); slot_put(cell_of(d, s), v); }
void a68rt_bind_cell(uint32_t d, uint32_t s, int w) { (void) w; a68_val v = pop(); slot_put(cell_of(d, s), v); }
void a68rt_set_int(uint32_t d, uint32_t s, int64_t v, int w) { (void) w; *cell_of(d, s) = mk_int(v); }

/* ---------------------------------------------------------------- native scalar access */

static const char* undef_msg(uint32_t t) {
  switch (t) {
    case T_INT: return "attempt to use an uninitialised INT value";
    case T_REAL: return "attempt to use an uninitialised REAL value";
    case T_BOOL: return "attempt to use an uninitialised BOOL value";
    case T_CHAR: return "attempt to use an uninitialised CHAR value";
    case T_BITS: return "attempt to use an uninitialised BITS value";
    default: return "attempt to use an uninitialised value";
  }
}

static int64_t as_int(a68_val v) {
  if (v.tag == T_INT) return v.v.i;
  if (v.tag == T_UNDEF) die(undef_msg(T_INT));
  fprintf(stderr, "uncaught exception: INT expected\n"); exit(1);
}
static double as_real(a68_val v) {
  if (v.tag == T_REAL) return v.v.r;
  if (v.tag == T_INT) return (double) v.v.i;
  if (v.tag == T_UNDEF) die(undef_msg(T_REAL));
  fprintf(stderr, "uncaught exception: REAL expected\n"); exit(1);
}
static uint8_t as_bool(a68_val v) {
  if (v.tag == T_BOOL) return (uint8_t) v.v.u;
  if (v.tag == T_UNDEF) die(undef_msg(T_BOOL));
  fprintf(stderr, "uncaught exception: BOOL expected\n"); exit(1);
}
static uint32_t as_char(a68_val v) {
  if (v.tag == T_CHAR) return (uint32_t) v.v.u;
  if (v.tag == T_UNDEF) die(undef_msg(T_CHAR));
  fprintf(stderr, "uncaught exception: CHAR expected\n"); exit(1);
}
static uint64_t as_bits(a68_val v) {
  if (v.tag == T_BITS) return v.v.u;
  if (v.tag == T_UNDEF) die(undef_msg(T_BITS));
  fprintf(stderr, "uncaught exception: BITS expected\n"); exit(1);
}

int64_t a68rt_cell_int(uint32_t d, uint32_t s, int w) { (void) w; return as_int(*cell_of(d, s)); }
double a68rt_cell_real(uint32_t d, uint32_t s, int w) { (void) w; return as_real(*cell_of(d, s)); }
uint8_t a68rt_cell_bool(uint32_t d, uint32_t s, int w) { (void) w; return as_bool(*cell_of(d, s)); }
uint32_t a68rt_cell_char(uint32_t d, uint32_t s, int w) { (void) w; return as_char(*cell_of(d, s)); }
uint64_t a68rt_cell_bits(uint32_t d, uint32_t s, int w) { (void) w; return as_bits(*cell_of(d, s)); }
void a68rt_set_cell_int(uint32_t d, uint32_t s, int64_t v, int w) { (void) w; *cell_of(d, s) = mk_int(v); }
void a68rt_set_cell_real(uint32_t d, uint32_t s, double v, int w) { (void) w; *cell_of(d, s) = mk_real(v); }
void a68rt_set_cell_bool(uint32_t d, uint32_t s, uint8_t v, int w) { (void) w; *cell_of(d, s) = mk_bool(v != 0); }
void a68rt_set_cell_char(uint32_t d, uint32_t s, uint32_t v, int w) { (void) w; *cell_of(d, s) = mk_char(v); }
void a68rt_set_cell_bits(uint32_t d, uint32_t s, uint64_t v, int w) { (void) w; *cell_of(d, s) = mk_bits(v); }

int64_t a68rt_pop_int(int w) { (void) w; return as_int(pop()); }
double a68rt_pop_real(int w) { (void) w; return as_real(pop()); }
uint8_t a68rt_pop_bool(int w) { (void) w; return as_bool(pop()); }
uint32_t a68rt_pop_char(int w) { (void) w; return as_char(pop()); }
uint64_t a68rt_pop_bits(int w) { (void) w; return as_bits(pop()); }

/* ---------------------------------------------------------------- row elements by subscript */

/* The row a cell holds, or the one the name in the cell refers to (`Interp.sliceGeneral`). */
static a68_rowd* cell_rowd(a68_val* c) {
  if (c->tag == T_ROW) return (a68_rowd*) c->v.p;
  if (c->tag == T_REF) { a68_rowd* r = ref_rowd(*c); if (r) return r; }
  if (c->tag == T_UNDEF) die("attempt to use an uninitialised value");
  if (c->tag == T_NIL) die("attempt to dereference NIL");
  die("internal: row expected");
}

/* the store index of `a[i]` or `a[i, j]`, with the evaluator's checks and messages */
static int64_t elem_index(a68_rowd* r, uint32_t rank, int64_t i, int64_t j) {
  if (r->h.n != rank) die("internal: wrong number of subscripts");
  if (i < r->dim[0].l || i > r->dim[0].u) dief("index %lld out of bounds [%lld:%lld]", i, r->dim[0].l, r->dim[0].u);
  int64_t idx = r->off + (i - r->dim[0].l) * r->dim[0].stride;
  if (rank == 2) {
    if (j < r->dim[1].l || j > r->dim[1].u) dief("index %lld out of bounds [%lld:%lld]", j, r->dim[1].l, r->dim[1].u);
    idx += (j - r->dim[1].l) * r->dim[1].stride;
  }
  return idx;
}

static a68_val row_elem(uint32_t d, uint32_t s, uint32_t rank, int64_t i, int64_t j) {
  a68_rowd* r = cell_rowd(cell_of(d, s));
  return store_get(rowd_store(r), elem_index(r, rank, i, j));
}

static void row_set_elem(uint32_t d, uint32_t s, uint32_t rank, int64_t i, int64_t j, a68_val v) {
  a68_rowd* r = cell_rowd(cell_of(d, s));
  int64_t idx = elem_index(r, rank, i, j);
  a68_val e = mk_ptr(T_REF, (a68_obj*) r, (uint32_t) idx);
  store_ref(e, v);
}

int64_t a68rt_row_int(uint32_t d, uint32_t s, uint32_t rank, int64_t i, int64_t j, int w) { (void) w; return as_int(row_elem(d, s, rank, i, j)); }
double a68rt_row_real(uint32_t d, uint32_t s, uint32_t rank, int64_t i, int64_t j, int w) { (void) w; return as_real(row_elem(d, s, rank, i, j)); }
uint8_t a68rt_row_bool(uint32_t d, uint32_t s, uint32_t rank, int64_t i, int64_t j, int w) { (void) w; return as_bool(row_elem(d, s, rank, i, j)); }
uint32_t a68rt_row_char(uint32_t d, uint32_t s, uint32_t rank, int64_t i, int64_t j, int w) { (void) w; return as_char(row_elem(d, s, rank, i, j)); }
uint64_t a68rt_row_bits(uint32_t d, uint32_t s, uint32_t rank, int64_t i, int64_t j, int w) { (void) w; return as_bits(row_elem(d, s, rank, i, j)); }
void a68rt_set_row_int(uint32_t d, uint32_t s, uint32_t rank, int64_t i, int64_t j, int64_t v, int w) { (void) w; row_set_elem(d, s, rank, i, j, mk_int(v)); }
void a68rt_set_row_real(uint32_t d, uint32_t s, uint32_t rank, int64_t i, int64_t j, double v, int w) { (void) w; row_set_elem(d, s, rank, i, j, mk_real(v)); }
void a68rt_set_row_bool(uint32_t d, uint32_t s, uint32_t rank, int64_t i, int64_t j, uint8_t v, int w) { (void) w; row_set_elem(d, s, rank, i, j, mk_bool(v != 0)); }
void a68rt_set_row_char(uint32_t d, uint32_t s, uint32_t rank, int64_t i, int64_t j, uint32_t v, int w) { (void) w; row_set_elem(d, s, rank, i, j, mk_char(v)); }
void a68rt_set_row_bits(uint32_t d, uint32_t s, uint32_t rank, int64_t i, int64_t j, uint64_t v, int w) { (void) w; row_set_elem(d, s, rank, i, j, mk_bits(v)); }

/* ---------------------------------------------------------------- structure fields */

/* `spec`: bits 0-1 the rank of a subscript (0 = none), bit 2 whether the cell holds a name
   of the structure rather than the structure, bits 8-11 how many fields follow; `fields`
   packs the field indices one byte each, innermost first (`Runtime.selRead`). */
static a68_val sel_read(uint32_t d, uint32_t s, uint32_t spec, int64_t i, int64_t j, uint32_t fields) {
  a68_val v = *cell_of(d, s);
  if (spec & 4) {
    if (v.tag == T_UNDEF) die("attempt to use an uninitialised value");
    if (v.tag == T_NIL) die("attempt to select from NIL");
    v = deref(v);
  }
  uint32_t rank = spec & 3;
  if (rank) {
    if (v.tag != T_ROW) die("internal: row expected");
    a68_rowd* r = (a68_rowd*) v.v.p;
    v = store_get(rowd_store(r), elem_index(r, rank, i, j));
  }
  uint32_t nf = (spec >> 8) & 15;
  for (uint32_t k = 0; k < nf; k++) {
    uint32_t f = (fields >> (8 * k)) & 255;
    if (v.tag != T_STRUCT) die("internal: field selection on non-struct");
    a68_slots* st = (a68_slots*) v.v.p;
    if (f >= st->h.n) die("internal: field index out of range");
    v = st->s[f];
  }
  return v;
}

static a68_val sel_ref(uint32_t d, uint32_t s, uint32_t spec, int64_t i, int64_t j, uint32_t fields) {
  a68_val r;
  if (spec & 4) {
    a68_val v = *cell_of(d, s);
    if (v.tag == T_UNDEF) die("attempt to use an uninitialised value");
    if (v.tag == T_NIL) die("attempt to select from NIL");
    r = v;
  } else {
    a68_frame* f = env;
    for (uint32_t k = 0; k < d && f; k++) f = f->parent;
    r = mk_ptr(T_REF, (a68_obj*) f, s * (uint32_t) sizeof(a68_val));
  }
  uint32_t rank = spec & 3;
  if (rank) {
    a68_rowd* rw = ref_rowd(r);
    if (!rw) die("internal: row expected");
    r = mk_ptr(T_REF, (a68_obj*) rw, (uint32_t) elem_index(rw, rank, i, j));
  }
  uint32_t nf = (spec >> 8) & 15;
  for (uint32_t k = 0; k < nf; k++) r = ref_field(r, (fields >> (8 * k)) & 255);
  return r;
}

void a68rt_sel_push(uint32_t d, uint32_t s, uint32_t spec, int64_t i, int64_t j, uint32_t f, int w) {
  GC_POLL();
  (void) w;
  a68_val v = sel_read(d, s, spec, i, j, f);
  if (v.tag == T_UNDEF) die("attempt to use an uninitialised value");
  push(copy_value(v));
}

uint8_t a68rt_cell_isnil(uint32_t d, uint32_t s, int w) {
  (void) w;
  a68_val* c = cell_of(d, s);
  if (c->tag == T_NIL) return 1;
  if (c->tag == T_UNDEF) die("attempt to use an uninitialised value");
  return 0;
}

void a68rt_sel_store(uint32_t dd, uint32_t ds, uint32_t d, uint32_t s, uint32_t spec, int64_t i, int64_t j, uint32_t f, int w) {
  GC_POLL();
  (void) w;
  a68_val v = sel_read(d, s, spec, i, j, f);
  if (v.tag == T_UNDEF) die("attempt to use an uninitialised value");
  slot_put(cell_of(dd, ds), copy_value(v));
}

int64_t a68rt_sel_int(uint32_t d, uint32_t s, uint32_t sp_, int64_t i, int64_t j, uint32_t f, int w) { (void) w; return as_int(sel_read(d, s, sp_, i, j, f)); }
double a68rt_sel_real(uint32_t d, uint32_t s, uint32_t sp_, int64_t i, int64_t j, uint32_t f, int w) { (void) w; return as_real(sel_read(d, s, sp_, i, j, f)); }
uint8_t a68rt_sel_bool(uint32_t d, uint32_t s, uint32_t sp_, int64_t i, int64_t j, uint32_t f, int w) { (void) w; return as_bool(sel_read(d, s, sp_, i, j, f)); }
uint32_t a68rt_sel_char(uint32_t d, uint32_t s, uint32_t sp_, int64_t i, int64_t j, uint32_t f, int w) { (void) w; return as_char(sel_read(d, s, sp_, i, j, f)); }
uint64_t a68rt_sel_bits(uint32_t d, uint32_t s, uint32_t sp_, int64_t i, int64_t j, uint32_t f, int w) { (void) w; return as_bits(sel_read(d, s, sp_, i, j, f)); }
void a68rt_set_sel_int(uint32_t d, uint32_t s, uint32_t sp_, int64_t i, int64_t j, uint32_t f, int64_t v, int w) { (void) w; store_ref(sel_ref(d, s, sp_, i, j, f), mk_int(v)); }
void a68rt_set_sel_real(uint32_t d, uint32_t s, uint32_t sp_, int64_t i, int64_t j, uint32_t f, double v, int w) { (void) w; store_ref(sel_ref(d, s, sp_, i, j, f), mk_real(v)); }
void a68rt_set_sel_bool(uint32_t d, uint32_t s, uint32_t sp_, int64_t i, int64_t j, uint32_t f, uint8_t v, int w) { (void) w; store_ref(sel_ref(d, s, sp_, i, j, f), mk_bool(v != 0)); }
void a68rt_set_sel_char(uint32_t d, uint32_t s, uint32_t sp_, int64_t i, int64_t j, uint32_t f, uint32_t v, int w) { (void) w; store_ref(sel_ref(d, s, sp_, i, j, f), mk_char(v)); }
void a68rt_set_sel_bits(uint32_t d, uint32_t s, uint32_t sp_, int64_t i, int64_t j, uint32_t f, uint64_t v, int w) { (void) w; store_ref(sel_ref(d, s, sp_, i, j, f), mk_bits(v)); }

/* ---------------------------------------------------------------- appending to a row variable */

/* `s +:= t` on a cell holding a one-dimensional row starting at 1 (`Interp.appendInPlace`):
   the elements are appended in place; anything else goes through the operator. */
static int append_in_place(a68_val* c, const a68_val* elems, int64_t n) {
  if (c->tag != T_ROW) return 0;
  a68_rowd* r = (a68_rowd*) c->v.p;
  if (r->h.n != 1 || r->dim[0].l != 1 || r->base->kind == K_ROWD) return 0;
  a68_obj* st = r->base;
  int64_t cur = row_count(r);
  if (r->off != 0 || r->dim[0].stride != 1 || (int64_t) st->n < cur) return 0;
  own_store(r);
  st = r->base;
  int64_t need = cur + n;
  if (need > (int64_t) st->n) {
    /* grow: a new store with room to spare */
    int64_t cap = need < 16 ? 16 : need * 2;
    a68_obj* ns;
    if (st->kind == K_LEAF) {
      ns = (a68_obj*) leaf_alloc(st->ek, (uint32_t) cap);
      for (int64_t i = 0; i < cur; i++) store_set(ns, i, store_get(st, i));
    } else {
      ns = store_alloc_slots((uint32_t) cap);
      memcpy(((a68_slots*) ns)->s, ((a68_slots*) st)->s, (size_t) cur * sizeof(a68_val));
    }
    st->rc--;
    ns->rc = 1;
    r->base = ns;
    st = ns;
  }
  for (int64_t i = 0; i < n; i++) {
    if (st->kind == K_LEAF && !leaf_accepts(st->ek, &elems[i])) {
      a68_slots* ns = slots_alloc(st->n);
      for (int64_t k = 0; k < cur + i; k++) ns->s[k] = store_get(st, k);
      st->rc--;
      ns->h.rc = 1;
      r->base = (a68_obj*) ns;
      st = (a68_obj*) ns;
    }
    store_set(st, cur + i, st->kind == K_LEAF ? elems[i] : copy_value(elems[i]));
  }
  r->dim[0].u = need;
  return 1;
}

void a68rt_append_char(uint32_t d, uint32_t s, uint32_t ch, int w) {
  GC_POLL();
  (void) w;
  a68_val* c = cell_of(d, s);
  a68_val e = mk_char(ch);
  if (!append_in_place(c, &e, 1)) {
    /* fall back to `+:=` on `REF STRING` and `STRING`, which reports the error */
    a68_val name = mk_ptr(T_REF, (a68_obj*) NULL, 0);
    (void) name;
    die("internal: append to a value that is not a string variable");
  }
}

void a68rt_append(uint32_t d, uint32_t s, int w) {
  GC_POLL();
  (void) w;
  a68_val v = pop();
  a68_val* c = cell_of(d, s);
  if (v.tag != T_ROW) die("internal: row expected in append");
  a68_rowd* src = (a68_rowd*) v.v.p;
  int64_t n = row_count(src);
  a68_val* tmp = (a68_val*) xmalloc((size_t) (n ? n : 1) * sizeof(a68_val));
  a68_obj* st = rowd_store(src);
  for (int64_t i = 0; i < n; i++) tmp[i] = store_get(st, row_store_index(src, i));
  int ok = append_in_place(c, tmp, n);
  free(tmp);
  if (!ok) die("internal: append to a value that is not a string variable");
}

/* ---------------------------------------------------------------- errors reported by native code */

void a68rt_undef_error(uint32_t kind, int w) {
  (void) w;
  switch (kind) {
    case 0: die("attempt to use an uninitialised INT value");
    case 1: die("attempt to use an uninitialised REAL value");
    case 2: die("attempt to use an uninitialised BOOL value");
    case 3: die("attempt to use an uninitialised CHAR value");
    default: die("attempt to use an uninitialised BITS value");
  }
}

uint32_t a68rt_cell_cproc(uint32_t d, uint32_t s, int w) {
  (void) w;
  a68_val* c = cell_of(d, s);
  if (c->tag == T_CPROC) return (c->aux & 0xffffff) + 1;
  return 0;
}

void a68rt_index_error(int64_t i, int64_t l, int64_t u, int w) { (void) w; dief("index %lld out of bounds [%lld:%lld]", i, l, u); }

void a68rt_arith_error(uint32_t kind, int w) {
  (void) w;
  switch (kind) {
    case 0: die("INT value overflow, result too large");
    case 1: die("INT division by zero");
    case 2: die("infinite REAL value");
    case 3: die("REAL value is not a number");
    case 4: die("INT value out of bounds");
    case 5: die("REAL division by zero");
    case 6: die("REPR argument out of range");
    case 7: die("REAL math error");
    default: die("invalid INT exponent");
  }
}

/* ---------------------------------------------------------------- operations */

void a68rt_deref(int w) {
  GC_POLL();
  (void) w;
  a68_val r = pop();
  a68_val v;
  if (r.tag == T_LREF) v = decode_blob(io_ok(a68l_lcell(r.aux, LW)));
  else v = deref(r);
  if (v.tag == T_UNDEF) die("attempt to use an uninitialised value");
  push(v);
}

static void call_value(a68_val f, uint32_t nargs) {
  switch (f.tag) {
    case T_CPROC: {
      /* the arguments are on top of the stack, above `f`'s former place */
      env_set((a68_frame*) f.v.p);
      size_t before = sp - nargs;
      a68_dispatch_proc(f.aux & 0xffffff);
      env_restore();
      if (a68_jump_flag) { sp = before; push(mk_tag(T_UNDEF)); }
      return;
    }
    case T_BUILTIN: {
      const char* name = strtab[f.aux];
      if (strcmp(name, "associate") == 0 || strcmp(name, "onlogicalfileend") == 0 || strcmp(name, "onfileend") == 0
          || strcmp(name, "onphysicalfileend") == 0 || strcmp(name, "onvalueerror") == 0 || strcmp(name, "onlineend") == 0)
        for (size_t i = sp - nargs; i < sp; i++) if (tag_is_ptr(stack[i].tag)) pin(stack[i].v.p);
      buf b = {0};
      for (size_t i = sp - nargs; i < sp; i++) encode_val(&b, stack[i]);
      lean_object* args = lean_alloc_sarray(1, b.n, b.n);
      memcpy(lean_sarray_cptr(args), b.p, b.n);
      free(b.p);
      /* the arguments stay on the stack, rooted, until the call returns: the Lean side may
         call back into compiled code, which may collect */
      lean_object* r = io_ok(a68l_call(lstr_of_table(f.aux), args, nargs, LW));
      a68_val res = decode_blob(r);
      sp -= nargs;
      push(res);
      return;
    }
    case T_NIL: die("attempt to call NIL");
    case T_UNDEF: die("attempt to call an uninitialised procedure");
    default: die("internal: call of a non-procedure");
  }
}

void a68rt_deproc(int w) {
  GC_POLL(); (void) w; a68_val f = pop(); call_value(f, 0); }

void a68rt_call(uint32_t nargs, int w) {
  GC_POLL();
  (void) w;
  if (sp < nargs + 1) { fprintf(stderr, "uncaught exception: operand stack underflow\n"); exit(1); }
  a68_val f = stack[sp - nargs - 1];
  memmove(&stack[sp - nargs - 1], &stack[sp - nargs], nargs * sizeof(a68_val));
  sp--;
  call_value(f, nargs);
}

void a68rt_widen(uint32_t src, uint32_t dst, int w) {
  GC_POLL();
  (void) w;
  a68_val v = pop();
  const mode_info* s = &modetab[src];
  const mode_info* d = &modetab[dst];
  if (v.tag == T_INT && strcmp(s->kind, "int") == 0 && s->len <= 0 && strcmp(d->kind, "real") == 0 && d->len <= 0) {
    push(mk_real((double) v.v.i));
    return;
  }
  if (strcmp(s->kind, d->kind) == 0 && s->len == d->len) { push(v); return; }
  push(v);   /* rooted while the Lean side widens */
  a68_val res = decode_blob(io_ok(a68l_widen(src, dst, encode_blob(v), LW)));
  (void) pop();
  push(res);
}

void a68rt_row_of(int w) {
  GC_POLL();
  (void) w;
  a68_val v = pop();
  if (v.tag == T_REF || v.tag == T_LREF) { push(v); return; }
  a68_rowd* d = rowd_alloc(1);
  a68_obj* st = store_alloc_for(1, &v);
  store_set(st, 0, v);
  st->rc = 1;
  d->base = st;
  d->off = 0;
  d->dim[0].l = 1; d->dim[0].u = 1; d->dim[0].stride = 1;
  push(mk_ptr(T_ROW, (a68_obj*) d, 0));
}

void a68rt_unite(uint32_t m, int w) {
  GC_POLL();
  (void) w;
  a68_val v = pop();
  a68_slots* s = slots_alloc(1);
  s->s[0] = v;
  push(mk_ptr(T_UNION, (a68_obj*) s, m));
}

void a68rt_voiding(int w) { (void) w; (void) pop(); push(mk_tag(T_VOID)); }

void a68rt_assign(uint8_t flex, int w) {
  GC_POLL();
  (void) w;
  a68_val v = pop();
  a68_val d = pop();
  assign_ref(d, v, flex != 0);
  push(d);
}

void a68rt_ident_rel(uint8_t isnt, int w) {
  (void) w;
  a68_val b = pop();
  a68_val a = pop();
  int same;
  if (a.tag == T_REF && b.tag == T_REF) same = a.v.p == b.v.p && a.aux == b.aux;
  else if (a.tag == T_LREF && b.tag == T_LREF) same = a.aux == b.aux;
  else if (a.tag == T_NIL && b.tag == T_NIL) same = 1;
  else same = 0;
  push(mk_bool(isnt ? !same : same));
}


/* ---------------------------------------------------------------- native operators */
/*
   The operators of the primitive modes, strings and row bounds, transcribed from
   `Interp.dyadic` and `Interp.monadic` with their checks and messages; anything else —
   LONG modes, COMPL, BYTES, rows compared as values, named modes — goes to the Lean side
   unchanged.  A mode is known by the kind and length its table line gives. */

#define A68_MAXINT 2147483647LL

static int mode_is(uint32_t m, const char* kind, int64_t len) {
  return m < nmode && strcmp(modetab[m].kind, kind) == 0 && modetab[m].len == len;
}
static int mode_kind(uint32_t m, const char* kind) { return m < nmode && strcmp(modetab[m].kind, kind) == 0; }

static int64_t int_range(int64_t r) {
  if (r > A68_MAXINT || r < -A68_MAXINT) die("INT value overflow, result too large");
  return r;
}

static double real_check(double x) {
  if (x != x) die("REAL value is not a number");
  if (isinf(x)) die("infinite REAL value");
  return x;
}

/* `Interp.powIntInt` */
static int64_t pow_int(int64_t m, int64_t n) {
  if (n < 0) die("invalid INT exponent");
  if (m == 0 && n == 0) return 1;
  if (m == 0 || m == 1) return m;
  if (m == -1) return (n % 2 == 0) ? 1 : -1;
  uint64_t nn = (uint64_t) n, bit = 1;
  int64_t mm = m, p = 1;
  for (;;) {
    if (nn & bit) p = int_range(p * mm);
    bit <<= 1;
    if (bit <= nn) mm = int_range(mm * mm);
    if (!(bit <= nn)) break;
  }
  return p;
}

/* `Interp.powRealIntPos` / `powRealInt` */
static double pow_real_int(double x, int64_t n) {
  uint64_t nn = n < 0 ? (uint64_t) (-(n + 1)) + 1 : (uint64_t) n;
  double p;
  if (x == 0.0 && nn == 0) p = 1.0;
  else if (x == 0.0 || x == 1.0) p = x;
  else if (x == -1.0) p = (nn % 2 == 0) ? 1.0 : -1.0;
  else {
    uint64_t bit = 1; double mm = x; p = 1.0;
    for (;;) {
      if (nn & bit) p = p * mm;
      bit <<= 1;
      if (bit <= nn) mm = mm * mm;
      if (!(bit <= nn)) break;
    }
    if (isinf(p) || p != p) die("infinite REAL value");
  }
  return n < 0 ? 1.0 / p : p;
}

static a68_val mk_compl(double re, double im) {
  a68_slots* c = slots_alloc(2);
  c->s[0] = mk_real(re);
  c->s[1] = mk_real(im);
  return mk_ptr(T_STRUCT, (a68_obj*) c, 0);
}

static int is_string_row(a68_val v) {
  return v.tag == T_ROW && ((a68_rowd*) v.v.p)->h.n == 1;
}

/* the characters of a string value, checked as `Interp.checkChars` checks them */
static uint8_t* string_bytes(a68_val v, int64_t* n) {
  a68_rowd* d = (a68_rowd*) v.v.p;
  *n = row_count(d);
  uint8_t* b = (uint8_t*) xmalloc((size_t) *n + 1);
  a68_obj* st = rowd_store(d);
  for (int64_t i = 0; i < *n; i++) {
    a68_val e = store_get(st, row_store_index(d, i));
    if (e.tag == T_UNDEF) { free(b); die("attempt to use an uninitialised CHAR value"); }
    if (e.tag != T_CHAR) { free(b); die("internal: [] CHAR expected"); }
    b[i] = (uint8_t) e.v.u;
  }
  return b;
}

static int cmp_op(const char* op, int c) {
  if (strcmp(op, "=") == 0) return c == 0;
  if (strcmp(op, "/=") == 0) return c != 0;
  if (strcmp(op, "<") == 0) return c < 0;
  if (strcmp(op, "<=") == 0) return c <= 0;
  if (strcmp(op, ">") == 0) return c > 0;
  return c >= 0;
}
static int is_cmp(const char* op) {
  return strcmp(op, "=") == 0 || strcmp(op, "/=") == 0 || strcmp(op, "<") == 0
      || strcmp(op, "<=") == 0 || strcmp(op, ">") == 0 || strcmp(op, ">=") == 0;
}

/* Try the operator natively; 1 when done (the result is in `*out`), 0 for the Lean side. */
static int native_dyop(const char* op, uint32_t m1, uint32_t m2, a68_val a, a68_val b, a68_val* out) {
  if (a.tag == T_UNDEF || b.tag == T_UNDEF) return 0;   /* the Lean side reports it in the mode's words */
  if (mode_is(m1, "int", 0) && mode_is(m2, "int", 0) && a.tag == T_INT && b.tag == T_INT) {
    int64_t x = a.v.i, y = b.v.i;
    if (strcmp(op, "+") == 0) { *out = mk_int(int_range(x + y)); return 1; }
    if (strcmp(op, "-") == 0) { *out = mk_int(int_range(x - y)); return 1; }
    if (strcmp(op, "*") == 0) { *out = mk_int(int_range(x * y)); return 1; }
    if (strcmp(op, "%") == 0) { if (y == 0) die("INT division by zero"); *out = mk_int(x / y); return 1; }
    if (strcmp(op, "%*") == 0) { if (y == 0) die("INT division by zero"); int64_t m = y < 0 ? -y : y; int64_t r = x % m; *out = mk_int(r < 0 ? r + m : r); return 1; }
    if (strcmp(op, "**") == 0) { *out = mk_int(pow_int(x, y)); return 1; }
    if (is_cmp(op)) { *out = mk_bool(cmp_op(op, x < y ? -1 : x > y ? 1 : 0)); return 1; }
    return 0;
  }
  if (mode_is(m1, "real", 0) && mode_is(m2, "real", 0) && (a.tag == T_REAL || a.tag == T_INT) && (b.tag == T_REAL || b.tag == T_INT)) {
    double x = as_real(a), y = as_real(b);
    if (strcmp(op, "+") == 0) { *out = mk_real(real_check(x + y)); return 1; }
    if (strcmp(op, "-") == 0) { *out = mk_real(real_check(x - y)); return 1; }
    if (strcmp(op, "*") == 0) { *out = mk_real(real_check(x * y)); return 1; }
    if (strcmp(op, "/") == 0) { if (y == 0.0) die("REAL value is not a number"); *out = mk_real(x / y); return 1; }
    if (strcmp(op, "I") == 0) { *out = mk_compl(x, y); return 1; }
    if (strcmp(op, "**") == 0) {
      if (y == 0.0) { *out = mk_real(1.0); return 1; }
      if (x < 0.0) die("REAL math error");
      if (x == 0.0) { if (y < 0.0) die("REAL math error"); *out = mk_real(0.0); return 1; }
      *out = mk_real(exp(y * log(x)));
      return 1;
    }
    if (is_cmp(op)) { *out = mk_bool(cmp_op(op, x < y ? -1 : x > y ? 1 : 0)); return 1; }
    return 0;
  }
  if (mode_is(m1, "real", 0) && mode_is(m2, "int", 0) && (a.tag == T_REAL || a.tag == T_INT) && b.tag == T_INT) {
    double x = as_real(a);
    if (strcmp(op, "**") == 0) { *out = mk_real(pow_real_int(x, b.v.i)); return 1; }
    if (strcmp(op, "I") == 0) { *out = mk_compl(x, (double) b.v.i); return 1; }
    return 0;
  }
  if (mode_kind(m1, "bool") && mode_kind(m2, "bool") && a.tag == T_BOOL && b.tag == T_BOOL) {
    int x = a.v.u != 0, y = b.v.u != 0;
    if (strcmp(op, "AND") == 0) { *out = mk_bool(x && y); return 1; }
    if (strcmp(op, "OR") == 0) { *out = mk_bool(x || y); return 1; }
    if (strcmp(op, "XOR") == 0 || strcmp(op, "/=") == 0) { *out = mk_bool(x != y); return 1; }
    if (strcmp(op, "=") == 0) { *out = mk_bool(x == y); return 1; }
    return 0;
  }
  if (mode_kind(m1, "char") && mode_kind(m2, "char") && a.tag == T_CHAR && b.tag == T_CHAR) {
    if (is_cmp(op)) { *out = mk_bool(cmp_op(op, a.v.u < b.v.u ? -1 : a.v.u > b.v.u ? 1 : 0)); return 1; }
    return 0;
  }
  if (mode_kind(m1, "row") && mode_kind(m2, "row") && is_string_row(a) && is_string_row(b)
      && rowd_store((a68_rowd*) a.v.p)->kind == K_LEAF && rowd_store((a68_rowd*) a.v.p)->ek == T_CHAR
      && rowd_store((a68_rowd*) b.v.p)->kind == K_LEAF && rowd_store((a68_rowd*) b.v.p)->ek == T_CHAR) {
    /* two strings whose stores are leaves of characters: a mode of `row` of `char` is what
       the elaborator gives both operands of the string operators */
    int64_t na, nb;
    if (strcmp(op, "+") == 0) {
      uint8_t* pa = string_bytes(a, &na);
      uint8_t* pb = string_bytes(b, &nb);
      uint8_t* c = (uint8_t*) xmalloc((size_t) (na + nb) + 1);
      memcpy(c, pa, (size_t) na); memcpy(c + na, pb, (size_t) nb);
      *out = string_row(c, na + nb, 1);
      free(pa); free(pb); free(c);
      return 1;
    }
    if (is_cmp(op)) {
      uint8_t* pa = string_bytes(a, &na);
      uint8_t* pb = string_bytes(b, &nb);
      int64_t m = na < nb ? na : nb;
      int c = 0;
      for (int64_t i = 0; i < m && c == 0; i++) c = pa[i] < pb[i] ? -1 : pa[i] > pb[i] ? 1 : 0;
      if (c == 0) c = na < nb ? -1 : na > nb ? 1 : 0;
      free(pa); free(pb);
      *out = mk_bool(cmp_op(op, c));
      return 1;
    }
    return 0;
  }
  if (mode_is(m1, "int", 0) && mode_kind(m2, "row") && a.tag == T_INT && b.tag == T_ROW) {
    a68_rowd* d = (a68_rowd*) b.v.p;
    int64_t k = a.v.i;
    if (strcmp(op, "LWB") == 0 || strcmp(op, "UPB") == 0) {
      if (k < 1 || k > (int64_t) d->h.n) die("LWB/UPB dimension out of range");
      *out = mk_int(strcmp(op, "LWB") == 0 ? d->dim[k - 1].l : d->dim[k - 1].u);
      return 1;
    }
    return 0;
  }
  if (mode_is(m1, "bits", 0) && mode_is(m2, "bits", 0) && a.tag == T_BITS && b.tag == T_BITS) {
    uint64_t x = a.v.u, y = b.v.u, mask = 0xffffffffu;
    if (strcmp(op, "AND") == 0) { *out = mk_bits(x & y); return 1; }
    if (strcmp(op, "OR") == 0) { *out = mk_bits((x | y) & mask); return 1; }
    if (strcmp(op, "XOR") == 0) { *out = mk_bits((x ^ y) & mask); return 1; }
    if (strcmp(op, "=") == 0) { *out = mk_bool(x == y); return 1; }
    if (strcmp(op, "/=") == 0) { *out = mk_bool(x != y); return 1; }
    if (strcmp(op, "<=") == 0) { *out = mk_bool((x & y) == x); return 1; }
    if (strcmp(op, ">=") == 0) { *out = mk_bool((x & y) == y); return 1; }
    return 0;
  }
  if (mode_is(m1, "bits", 0) && mode_is(m2, "int", 0) && a.tag == T_BITS && b.tag == T_INT) {
    uint64_t x = a.v.u, mask = 0xffffffffu;
    int64_t k = b.v.i;
    int64_t ak = k < 0 ? -k : k;
    if (strcmp(op, "SHL") == 0 || strcmp(op, "SHR") == 0 || strcmp(op, "DOWN") == 0) {
      if (ak > 32) die("shift count out of range");
      int64_t sh = strcmp(op, "SHL") == 0 ? k : -k;
      uint64_t r = sh >= 0 ? ((sh >= 64 ? 0 : (x << sh)) & mask) : (-sh >= 64 ? 0 : (x >> (-sh)));
      *out = mk_bits(r);
      return 1;
    }
    return 0;
  }
  if (mode_is(m1, "int", 0) && mode_is(m2, "bits", 0) && a.tag == T_INT && b.tag == T_BITS) {
    if (strcmp(op, "ELEM") == 0) {
      int64_t k = a.v.i;
      if (k < 1 || k > 32) die("ELEM index out of range");
      *out = mk_bool(((b.v.u >> (32 - k)) & 1) == 1);
      return 1;
    }
    return 0;
  }
  return 0;
}

/* `x +:= e` and its relatives on a name of a primitive mode, and `s +:= t` on a string
   variable: the value, the operation, the write, and the name as the result. */
static int native_assign_op(const char* op, uint32_t m1, uint32_t m2, a68_val a, a68_val b, a68_val* out) {
  (void) m2;
  if (a.tag != T_REF || !mode_kind(m1, "ref")) return 0;
  /* the mode line of a REF names the mode referred to by its index */
  uint32_t target = (uint32_t) modetab[m1].len;
  int t_int = mode_is(target, "int", 0), t_real = mode_is(target, "real", 0), t_row = mode_kind(target, "row");
  if (!t_int && !t_real && !t_row) return 0;
  if (t_row && strcmp(op, "+:=") == 0 && b.tag == T_ROW && is_string_row(b)) {
    /* appending to a string variable: in place when the cell holds a plain row */
    a68_val* slot = a.v.p->kind == K_ROWD ? NULL : ref_slot(a);
    if (slot && slot->tag == T_ROW) {
      a68_rowd* src = (a68_rowd*) b.v.p;
      int64_t n = row_count(src);
      a68_val* tmp = (a68_val*) xmalloc((size_t) (n ? n : 1) * sizeof(a68_val));
      a68_obj* st = rowd_store(src);
      for (int64_t i = 0; i < n; i++) tmp[i] = store_get(st, row_store_index(src, i));
      int ok = append_in_place(slot, tmp, n);
      free(tmp);
      if (ok) { *out = a; return 1; }
    }
    return 0;
  }
  if (t_row) return 0;
  a68_val cur = ref_load(a);
  if (cur.tag == T_UNDEF) return 0;
  a68_val r;
  if (t_int && cur.tag == T_INT && b.tag == T_INT) {
    int64_t x = cur.v.i, y = b.v.i;
    if (strcmp(op, "+:=") == 0) r = mk_int(int_range(x + y));
    else if (strcmp(op, "-:=") == 0) r = mk_int(int_range(x - y));
    else if (strcmp(op, "*:=") == 0) r = mk_int(int_range(x * y));
    else if (strcmp(op, "%:=") == 0) { if (y == 0) die("INT division by zero"); r = mk_int(x / y); }
    else if (strcmp(op, "%*:=") == 0) { if (y == 0) die("INT division by zero"); int64_t m = y < 0 ? -y : y; int64_t q = x % m; r = mk_int(q < 0 ? q + m : q); }
    else return 0;
  } else if (t_real && cur.tag == T_REAL && (b.tag == T_REAL || b.tag == T_INT)) {
    double x = cur.v.r, y = as_real(b);
    if (strcmp(op, "+:=") == 0) r = mk_real(real_check(x + y));
    else if (strcmp(op, "-:=") == 0) r = mk_real(real_check(x - y));
    else if (strcmp(op, "*:=") == 0) r = mk_real(real_check(x * y));
    else if (strcmp(op, "/:=") == 0) { if (y == 0.0) die("REAL value is not a number"); r = mk_real(x / y); }
    else return 0;
  } else return 0;
  store_ref(a, r);
  *out = a;
  return 1;
}

static int native_monop(const char* op, uint32_t m, a68_val v, a68_val* out) {
  if (v.tag == T_UNDEF) return 0;
  if (mode_is(m, "int", 0) && v.tag == T_INT) {
    int64_t x = v.v.i;
    if (strcmp(op, "-") == 0) { *out = mk_int(int_range(-x)); return 1; }
    if (strcmp(op, "+") == 0) { *out = v; return 1; }
    if (strcmp(op, "ABS") == 0) { *out = mk_int(x < 0 ? -x : x); return 1; }
    if (strcmp(op, "SIGN") == 0) { *out = mk_int(x > 0 ? 1 : x < 0 ? -1 : 0); return 1; }
    if (strcmp(op, "ODD") == 0) { *out = mk_bool(x % 2 != 0); return 1; }
    if (strcmp(op, "REPR") == 0) { if (x < 0 || x > 255) die("REPR argument out of range"); *out = mk_char((uint32_t) x); return 1; }
    if (strcmp(op, "BIN") == 0) {
      if (x < 0) die("BIN argument is negative");
      if (x > 0xffffffffLL) die("BIN argument out of range");
      *out = mk_bits((uint64_t) x); return 1;
    }
    return 0;
  }
  if (mode_is(m, "real", 0) && (v.tag == T_REAL || v.tag == T_INT)) {
    double x = as_real(v);
    if (strcmp(op, "-") == 0) { *out = mk_real(-x); return 1; }
    if (strcmp(op, "+") == 0) { *out = mk_real(x); return 1; }
    if (strcmp(op, "ABS") == 0) { *out = mk_real(fabs(x)); return 1; }
    if (strcmp(op, "SIGN") == 0) { *out = mk_int(x > 0 ? 1 : x < 0 ? -1 : 0); return 1; }
    if (strcmp(op, "ENTIER") == 0) {
      if (x < -(double) A68_MAXINT || x > (double) A68_MAXINT) die("INT value out of bounds");
      double f = floor(x);
      *out = mk_int(f < 0 ? -(int64_t) (uint64_t) (-f) : (int64_t) (uint64_t) f);
      return 1;
    }
    if (strcmp(op, "ROUND") == 0) {
      if (x < -(double) A68_MAXINT || x > (double) A68_MAXINT) die("INT value out of bounds");
      double ax = fabs(x);
      double r = floor(ax + 0.5);
      int64_t n = (int64_t) (uint64_t) r;
      *out = mk_int(x < 0 ? -n : n);
      return 1;
    }
    return 0;
  }
  if (mode_kind(m, "bool") && v.tag == T_BOOL) {
    if (strcmp(op, "NOT") == 0) { *out = mk_bool(!v.v.u); return 1; }
    if (strcmp(op, "ABS") == 0) { *out = mk_int(v.v.u ? 1 : 0); return 1; }
    return 0;
  }
  if (mode_kind(m, "char") && v.tag == T_CHAR) {
    if (strcmp(op, "ABS") == 0) { *out = mk_int((int64_t) v.v.u); return 1; }
    return 0;
  }
  if (mode_is(m, "bits", 0) && v.tag == T_BITS) {
    if (strcmp(op, "NOT") == 0) { *out = mk_bits(0xffffffffu ^ v.v.u); return 1; }
    if (strcmp(op, "ABS") == 0) { *out = mk_int(v.v.u >= 2147483648u ? (int64_t) v.v.u - 4294967296LL : (int64_t) v.v.u); return 1; }
    return 0;
  }
  if (mode_kind(m, "row") && v.tag == T_ROW) {
    a68_rowd* d = (a68_rowd*) v.v.p;
    if (strcmp(op, "LWB") == 0) { *out = mk_int(d->dim[0].l); return 1; }
    if (strcmp(op, "UPB") == 0) { *out = mk_int(d->dim[0].u); return 1; }
    if (strcmp(op, "ELEMS") == 0) { *out = mk_int(row_count(d)); return 1; }
    return 0;
  }
  return 0;
}

/* the operands stay on the stack while the Lean side computes */
void a68rt_dyop(uint32_t op, uint32_t m1, uint32_t m2, int w) {
  GC_POLL();
  (void) w;
  if (sp < 2) { fprintf(stderr, "uncaught exception: operand stack underflow\n"); exit(1); }
  {
    a68_val res;
    const char* name = strtab[op];
    if (native_dyop(name, m1, m2, stack[sp - 2], stack[sp - 1], &res)
        || native_assign_op(name, m1, m2, stack[sp - 2], stack[sp - 1], &res)) {
      sp -= 2;
      push(res);
      return;
    }
  }
  buf b = {0};
  encode_val(&b, stack[sp - 2]);
  encode_val(&b, stack[sp - 1]);
  lean_object* args = lean_alloc_sarray(1, b.n, b.n);
  memcpy(lean_sarray_cptr(args), b.p, b.n);
  free(b.p);
  a68_val res = decode_blob(io_ok(a68l_dyop(lstr_of_table(op), m1, m2, args, LW)));
  sp -= 2;
  push(res);
}

void a68rt_monop(uint32_t op, uint32_t m, int w) {
  GC_POLL();
  (void) w;
  {
    a68_val res;
    if (native_monop(strtab[op], m, *top(), &res)) { (void) pop(); push(res); return; }
  }
  a68_val res = decode_blob(io_ok(a68l_monop(lstr_of_table(op), m, encode_blob(*top()), LW)));
  (void) pop();
  push(res);
}

void a68rt_select(uint32_t idx, uint8_t via_ref, int w) {
  GC_POLL();
  (void) w;
  a68_val v = pop();
  if (via_ref) { push(ref_field(v, idx)); return; }
  if (v.tag == T_STRUCT) {
    a68_slots* s = (a68_slots*) v.v.p;
    if (idx >= s->h.n) die("internal: field index out of range");
    push(copy_value(s->s[idx]));
    return;
  }
  if (v.tag == T_ROW) {
    /* multiple selection: the field of every element */
    a68_rowd* r = (a68_rowd*) v.v.p;
    int64_t n = row_count(r);
    a68_rowd* d = rowd_alloc(r->h.n);
    memcpy(d->dim, r->dim, (size_t) r->h.n * sizeof(a68_dim));
    int64_t stride = 1;
    for (uint32_t k = r->h.n; k > 0; k--) { d->dim[k - 1].stride = stride; int64_t ext = d->dim[k - 1].u - d->dim[k - 1].l + 1; stride *= ext > 0 ? ext : 0; }
    d->off = 0;
    a68_slots* st = slots_alloc((uint32_t) n);
    a68_obj* src = rowd_store(r);
    for (int64_t i = 0; i < n; i++) {
      a68_val e = store_get(src, row_store_index(r, i));
      if (e.tag != T_STRUCT) die("internal: field selection on non-struct element");
      st->s[i] = copy_value(((a68_slots*) e.v.p)->s[idx]);
    }
    st->h.rc = 1;
    d->base = (a68_obj*) st;
    push(mk_ptr(T_ROW, (a68_obj*) d, 0));
    return;
  }
  die("internal: select from non-struct");
}

/* The indexer values were pushed in order; `kinds` holds four bits per indexer: bit 0 = a
   trim, bit 1 = a lower bound was given, bit 2 = an upper bound, bit 3 = an `AT`. */
void a68rt_slice(uint32_t nidx, uint64_t kinds, uint8_t via_ref, int w) {
  GC_POLL();
  (void) w;
  indexer ixs[64];
  if (nidx > 64) die("internal: too many subscripts");
  uint32_t nvals = 0;
  for (uint32_t i = 0; i < nidx; i++) {
    uint32_t k = (uint32_t) ((kinds >> (4 * i)) & 15);
    if (!(k & 1)) nvals++;
    else { if (k & 2) nvals++; if (k & 4) nvals++; if (k & 8) nvals++; }
  }
  if (sp < nvals + 1) { fprintf(stderr, "uncaught exception: operand stack underflow\n"); exit(1); }
  const a68_val* vals = &stack[sp - nvals];
  uint32_t vi = 0;
  for (uint32_t i = 0; i < nidx; i++) {
    uint32_t k = (uint32_t) ((kinds >> (4 * i)) & 15);
    memset(&ixs[i], 0, sizeof ixs[i]);
    if (!(k & 1)) { ixs[i].i = as_int(vals[vi++]); }
    else {
      ixs[i].is_trim = 1;
      if (k & 2) { ixs[i].has_lo = 1; ixs[i].lo = as_int(vals[vi++]); }
      if (k & 4) { ixs[i].has_hi = 1; ixs[i].hi = as_int(vals[vi++]); }
      if (k & 8) { ixs[i].has_at = 1; ixs[i].at = as_int(vals[vi++]); }
    }
  }
  sp -= nvals;
  a68_val base = pop();
  a68_val out;
  if (via_ref) {
    if (base.tag == T_NIL) die("attempt to dereference NIL");
    if (base.tag == T_UNDEF) die("attempt to use an uninitialised REF value");
    if (base.tag != T_REF) die("internal: slice via non-REF");
    a68_rowd* r = ref_rowd(base);
    if (!r) {
      a68_val t = *ref_slot(base);
      if (t.tag == T_UNDEF) die("attempt to use an uninitialised value");
      die("internal: row expected");
    }
    /* check the trims against the bounds first, in the evaluator's order */
    for (uint32_t k = 0; k < nidx; k++) {
      if (ixs[k].is_trim) {
        int64_t l = r->dim[k].l, u = r->dim[k].u;
        int64_t lo = ixs[k].has_lo ? ixs[k].lo : l, hi = ixs[k].has_hi ? ixs[k].hi : u;
        if ((lo < l || hi > u) && !(hi < lo)) {
          /* the index checks of earlier dimensions come first */
          for (uint32_t q = 0; q < k; q++) if (!ixs[q].is_trim && (ixs[q].i < r->dim[q].l || ixs[q].i > r->dim[q].u)) dief("index %lld out of bounds [%lld:%lld]", ixs[q].i, r->dim[q].l, r->dim[q].u);
          trim_error(lo, hi, l, u);
        }
      }
    }
    slice_into(r, 1, ixs, nidx, &out);
  } else {
    if (base.tag == T_UNDEF) die("attempt to use an uninitialised value");
    if (base.tag != T_ROW) die("internal: slice of non-row");
    a68_rowd* r = (a68_rowd*) base.v.p;
    for (uint32_t k = 0; k < nidx; k++) {
      if (ixs[k].is_trim) {
        int64_t l = r->dim[k].l, u = r->dim[k].u;
        int64_t lo = ixs[k].has_lo ? ixs[k].lo : l, hi = ixs[k].has_hi ? ixs[k].hi : u;
        if ((lo < l || hi > u) && !(hi < lo)) {
          for (uint32_t q = 0; q < k; q++) if (!ixs[q].is_trim && (ixs[q].i < r->dim[q].l || ixs[q].i > r->dim[q].u)) dief("index %lld out of bounds [%lld:%lld]", ixs[q].i, r->dim[q].l, r->dim[q].u);
          trim_error(lo, hi, l, u);
        }
      }
    }
    slice_into(r, 0, ixs, nidx, &out);
  }
  push(out);
}

void a68rt_new_row(uint32_t ndims, uint8_t flex, int w) {
  GC_POLL();
  (void) w; (void) flex;
  if (sp < 2 * ndims + 1) { fprintf(stderr, "uncaught exception: operand stack underflow\n"); exit(1); }
  a68_rowd* d = rowd_alloc(ndims);
  const a68_val* bounds = &stack[sp - 2 * ndims];
  for (uint32_t k = 0; k < ndims; k++) {
    if (bounds[2 * k].tag != T_INT || bounds[2 * k + 1].tag != T_INT) die("internal: row bounds must be INT");
    d->dim[k].l = bounds[2 * k].v.i;
    d->dim[k].u = bounds[2 * k + 1].v.i;
  }
  sp -= 2 * ndims;
  a68_val init = pop();
  int64_t stride = 1;
  for (uint32_t k = ndims; k > 0; k--) { d->dim[k - 1].stride = stride; int64_t ext = d->dim[k - 1].u - d->dim[k - 1].l + 1; stride *= ext > 0 ? ext : 0; }
  d->off = 0;
  int64_t n = row_count(d);
  a68_obj* st = store_alloc_for((uint32_t) n, &init);
  if (st->kind == K_LEAF) { for (int64_t i = 0; i < n; i++) store_set(st, i, init); }
  else for (int64_t i = 0; i < n; i++) ((a68_slots*) st)->s[i] = copy_value(init);
  st->rc = 1;
  d->base = st;
  push(mk_ptr(T_ROW, (a68_obj*) d, 0));
}

void a68rt_gen(int w) {
  GC_POLL();
  (void) w;
  a68_val v = pop();
  a68_slots* c = slots_alloc(1);
  slot_put(&c->s[0], v);
  push(mk_ptr(T_REF, (a68_obj*) c, 0));
}

void a68rt_collateral(uint32_t n, uint8_t is_struct, uint32_t dims, int w) {
  GC_POLL();
  (void) w;
  if (sp < n) { fprintf(stderr, "uncaught exception: operand stack underflow\n"); exit(1); }
  const a68_val* vs = &stack[sp - n];
  if (is_struct) {
    a68_slots* s = slots_alloc(n);
    for (uint32_t i = 0; i < n; i++) s->s[i] = vs[i];
    sp -= n;
    push(mk_ptr(T_STRUCT, (a68_obj*) s, 0));
    return;
  }
  if (dims <= 1) {
    a68_rowd* d = rowd_alloc(1);
    d->dim[0].l = 1; d->dim[0].u = n; d->dim[0].stride = 1; d->off = 0;
    int leaf_ok = n > 0;
    for (uint32_t i = 0; i < n && leaf_ok; i++)
      if (vs[i].tag != vs[0].tag || (vs[i].tag == T_CHAR && vs[i].v.u >= 256)) leaf_ok = 0;
    a68_obj* st = leaf_ok ? store_alloc_for(n, &vs[0]) : store_alloc_slots(n);
    for (uint32_t i = 0; i < n; i++) store_set(st, i, vs[i]);
    st->rc = 1;
    d->base = st;
    sp -= n;
    push(mk_ptr(T_ROW, (a68_obj*) d, 0));
    return;
  }
  /* rows of (dims-1)-dimensional rows with equal bounds */
  if (n == 0) {
    a68_rowd* d = rowd_alloc(dims);
    for (uint32_t k = 0; k < dims; k++) { d->dim[k].l = 1; d->dim[k].u = 0; d->dim[k].stride = 1; }
    d->off = 0;
    a68_obj* st = store_alloc_slots(0);
    st->rc = 1;
    d->base = st;
    push(mk_ptr(T_ROW, (a68_obj*) d, 0));
    return;
  }
  if (vs[0].tag != T_ROW) die("internal: row display");
  a68_rowd* first = (a68_rowd*) vs[0].v.p;
  for (uint32_t i = 0; i < n; i++) {
    if (vs[i].tag != T_ROW) die("internal: row display");
    if (!same_bounds(first, (a68_rowd*) vs[i].v.p)) die("bounds of row display elements differ");
  }
  uint32_t nd = first->h.n + 1;
  a68_rowd* d = rowd_alloc(nd);
  d->dim[0].l = 1; d->dim[0].u = n;
  for (uint32_t k = 0; k < first->h.n; k++) { d->dim[k + 1].l = first->dim[k].l; d->dim[k + 1].u = first->dim[k].u; }
  int64_t stride = 1;
  for (uint32_t k = nd; k > 0; k--) { d->dim[k - 1].stride = stride; int64_t ext = d->dim[k - 1].u - d->dim[k - 1].l + 1; stride *= ext > 0 ? ext : 0; }
  d->off = 0;
  int64_t per = row_count(first);
  int64_t total = per * n;
  a68_obj* st0 = rowd_store(first);
  int leaf_ok = st0->kind == K_LEAF;
  for (uint32_t i = 0; i < n && leaf_ok; i++) { a68_obj* s = rowd_store((a68_rowd*) vs[i].v.p); if (s->kind != K_LEAF || s->ek != st0->ek) leaf_ok = 0; }
  a68_obj* st = leaf_ok ? (a68_obj*) leaf_alloc(st0->ek, (uint32_t) total) : store_alloc_slots((uint32_t) total);
  for (uint32_t i = 0; i < n; i++) {
    a68_rowd* r = (a68_rowd*) vs[i].v.p;
    a68_obj* s = rowd_store(r);
    for (int64_t j = 0; j < per; j++) store_set(st, (int64_t) i * per + j, store_get(s, row_store_index(r, j)));
  }
  st->rc = 1;
  d->base = st;
  sp -= n;
  push(mk_ptr(T_ROW, (a68_obj*) d, 0));
}

void a68rt_push_proc(uint32_t fn, uint32_t np, int w) { (void) w; push(mk_ptr(T_CPROC, (a68_obj*) env, fn | (np << 24))); }
void a68rt_push_format(uint32_t skel, int w) { (void) w; push(mk_ptr(T_FMT, (a68_obj*) env, skel)); }

uint32_t a68rt_case_index(uint32_t n, int w) {
  (void) w;
  a68_val v = pop();
  if (v.tag == T_UNDEF) die("attempt to use an uninitialised INT value");
  if (v.tag != T_INT) { fprintf(stderr, "uncaught exception: INT expected in CASE\n"); exit(1); }
  return (v.v.i >= 1 && v.v.i <= (int64_t) n) ? (uint32_t) v.v.i : 0;
}

/* the mode inside a united value, looking through unions united into unions
   (`Interp.unionContent`) */
static a68_val union_content(a68_val v, uint32_t* vm) {
  *vm = 0xffffffffu;
  while (v.tag == T_UNION) {
    *vm = v.aux;
    a68_val inner = ((a68_slots*) v.v.p)->s[0];
    if (inner.tag != T_UNION) return inner;
    v = inner;
  }
  return v;
}

/* conformity answers are cached per (mode, value mode) pair */
typedef struct { uint32_t m, vm; uint8_t ok; } conform_entry;
static conform_entry* conform_cache = NULL;
static size_t nconform = 0, conform_cap = 0;

static int conforms(uint32_t m, uint32_t vm) {
  for (size_t i = 0; i < nconform; i++)
    if (conform_cache[i].m == m && conform_cache[i].vm == vm) return conform_cache[i].ok;
  uint8_t ok = io_u8(a68l_conform(m, vm, LW));
  if (nconform == conform_cap) {
    conform_cap = conform_cap ? conform_cap * 2 : 64;
    conform_cache = (conform_entry*) realloc(conform_cache, conform_cap * sizeof(conform_entry));
    if (!conform_cache) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  }
  conform_cache[nconform].m = m; conform_cache[nconform].vm = vm; conform_cache[nconform].ok = ok;
  nconform++;
  return ok;
}

uint8_t a68rt_conform(uint32_t m, uint8_t bind, int w) {
  GC_POLL();
  (void) w;
  a68_val v = *top();
  uint32_t vm;
  a68_val inner = union_content(v, &vm);
  int ok = conforms(m, vm);
  if (ok && bind) {
    if (io_u8(a68l_mode_is_union(m, LW))) push(copy_value(v));
    else push(copy_value(inner));
  }
  return ok ? 1 : 0;
}
