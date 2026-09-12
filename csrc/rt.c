/* The C runtime of a compiled program: Algol 68 values in C memory.

   A program compiled by a68lean keeps every value here — its frames, its operand stack,
   its names, rows, structures, unions and closures.  The rest of the runtime is plain C
   too: transput and the prelude (io.c, prelude.c), the general operators and coercions
   (ops.c), number formatting (fmt.c), multi-precision arithmetic (mp*.c) and the
   operating-system services (os.c); a compiled program links these and the C library.

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
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#include "a68rt.h"
#include "tables.h"
#include "io.h"
#include "stackmap.h"

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

void*  xmalloc(size_t n) {
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

a68_leaf*  leaf_alloc(uint16_t ek, uint32_t n) {
  size_t es = leaf_esize(ek);
  size_t bytes = (size_t) n * es + (ek == EK_BYTES ? 0 : (n + 7) / 8);
  a68_leaf* l = (a68_leaf*) obj_alloc(K_LEAF, sizeof(a68_leaf) + bytes);
  l->h.ek = ek;
  l->h.n = n;
  l->h.rc = 0;
  return l;
}

a68_slots*  slots_alloc(uint32_t n) {
  a68_slots* s = (a68_slots*) obj_alloc(K_SLOTS, sizeof(a68_slots) + (size_t) n * sizeof(a68_val));
  s->h.n = n;
  return s;
}

a68_rowd*  rowd_alloc(uint32_t ndims) {
  a68_rowd* r = (a68_rowd*) obj_alloc(K_ROWD, sizeof(a68_rowd) + (size_t) ndims * sizeof(a68_dim));
  r->h.n = ndims;
  return r;
}

/* ---------------------------------------------------------------- the other modules */

uint32_t a68_line_no = 0;      /* the source line the program last reached (`a68rt_line`) */
uint32_t a68_jump_flag = 0;    /* the label a jump is heading for, plus one; zero when none */

/* supplied by the compiled program */
void a68_dispatch_proc(size_t fn);
void a68_dispatch_hole(size_t idx);

/* ops.c */
a68_val ops_dyadic(const char* op, uint32_t m1, uint32_t m2, a68_val a, a68_val b);
a68_val ops_monadic(const char* op, uint32_t m, a68_val v);
a68_val ops_widen(uint32_t src, uint32_t dst, a68_val v);
a68_val ops_default(uint32_t m);
int ops_conform(uint32_t m, uint32_t vm);
int ops_mode_is_union(uint32_t m);

__attribute__((noreturn)) void die(const char* msg) { io_die(msg); }

__attribute__((noreturn)) void dief(const char* fmt, int64_t a, int64_t b, int64_t c) {
  char buf[256];
  snprintf(buf, sizeof buf, fmt, (long long) a, (long long) b, (long long) c);
  die(buf);
}

/* ---------------------------------------------------------------- tables */

char** strtab = NULL;       /* the program's string table: literals, names (tables.c) */
size_t* strlen_tab = NULL;
size_t nstr = 0;

/* ---------------------------------------------------------------- stacks */

a68_val* stack = NULL;
size_t sp = 0;
static size_t stack_cap = 0;

static a68_frame* env = NULL;              /* the innermost frame */
static a68_frame** saved = NULL;           /* environments saved by env_set */
static size_t nsaved = 0, saved_cap = 0;

static int trace_env2 = -1;
void  push(a68_val v) {
  if (trace_env2 < 0) trace_env2 = getenv("A68LEAN_TRACE") != NULL;
  if (trace_env2 > 0) fprintf(stderr, "push tag=%u sp=%zu line=%u\n", v.tag, sp + 1, a68_line_no);
  if (sp == stack_cap) {
    stack_cap = stack_cap ? stack_cap * 2 : 1024;
    stack = (a68_val*) realloc(stack, stack_cap * sizeof(a68_val));
    if (!stack) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  }
  stack[sp++] = v;
}

a68_val  pop(void) {
  if (trace_env2 > 0) fprintf(stderr, "pop tag=%u sp=%zu line=%u\n", sp ? stack[sp - 1].tag : 99, sp - 1, a68_line_no);
  if (sp == 0) { fprintf(stderr, "uncaught exception: operand stack underflow\n"); exit(1); }
  return stack[--sp];
}

a68_val*  top(void) {
  if (sp == 0) { fprintf(stderr, "uncaught exception: operand stack underflow\n"); exit(1); }
  return &stack[sp - 1];
}

a68_val  mk_int(int64_t i) { a68_val v; v.tag = T_INT; v.aux = 0; v.v.i = i; return v; }
a68_val  mk_real(double r) { a68_val v; v.tag = T_REAL; v.aux = 0; v.v.r = r; return v; }
a68_val  mk_bool(int b) { a68_val v; v.tag = T_BOOL; v.aux = 0; v.v.u = b ? 1 : 0; return v; }
a68_val  mk_char(uint32_t c) { a68_val v; v.tag = T_CHAR; v.aux = 0; v.v.u = c; return v; }
a68_val  mk_bits(uint64_t b) { a68_val v; v.tag = T_BITS; v.aux = 0; v.v.u = b; return v; }
a68_val  mk_tag(uint32_t t) { a68_val v; v.tag = t; v.aux = 0; v.v.u = 0; return v; }
a68_val  mk_ptr(uint32_t t, a68_obj* p, uint32_t aux) { a68_val v; v.tag = t; v.aux = aux; v.v.p = p; return v; }

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

a68_obj*  rowd_store(const a68_rowd* r) {
  return r->base->kind == K_ROWD ? ((a68_rowd*) r->base)->base : r->base;
}
static inline a68_rowd* rowd_owner(a68_rowd* r) {
  return r->base->kind == K_ROWD ? (a68_rowd*) r->base : r;
}

int64_t  row_count(const a68_rowd* r) {
  int64_t n = 1;
  for (uint32_t k = 0; k < r->h.n; k++) {
    int64_t d = r->dim[k].u - r->dim[k].l + 1;
    if (d <= 0) return 0;
    n *= d;
  }
  return n;
}

/* the store index of the element at flat position `flat` in row-major order of the view */
int64_t  row_store_index(const a68_rowd* r, int64_t flat) {
  int64_t idx = r->off;
  for (uint32_t k = r->h.n; k > 0; k--) {
    int64_t ext = r->dim[k - 1].u - r->dim[k - 1].l + 1;
    int64_t i = flat % ext;
    flat /= ext;
    idx += i * r->dim[k - 1].stride;
  }
  return idx;
}

a68_val  store_get(a68_obj* st, int64_t idx) {
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

static a68_val unborrow(a68_val v);
void  store_set(a68_obj* st, int64_t idx, a68_val v) {
  if (st->kind == K_SLOTS) { ((a68_slots*) st)->s[idx] = unborrow(v); return; }
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
a68_obj*  store_alloc_for(uint32_t n, const a68_val* sample) {
  if (sample && (sample->tag == T_INT || sample->tag == T_REAL || sample->tag == T_BITS
                 || sample->tag == T_BOOL || (sample->tag == T_CHAR && sample->v.u < 256)))
    return (a68_obj*) leaf_alloc((uint16_t) sample->tag, n);
  return (a68_obj*) slots_alloc(n);
}

a68_obj*  store_alloc_slots(uint32_t n) { return (a68_obj*) slots_alloc(n); }

/* The element at a store index of the row a descriptor describes, through its field
   selection when it has one. */
a68_val  rowd_get(const a68_rowd* r, int64_t idx) {
  a68_val e = store_get(rowd_store(r), idx);
  if (r->field) {
    if (e.tag != T_STRUCT) die("internal: field selection on non-struct element");
    a68_slots* st = (a68_slots*) e.v.p;
    if (r->field - 1 >= st->h.n) die("internal: field index out of range");
    return st->s[r->field - 1];
  }
  return e;
}

/* The slot to write for that element, or NULL when the store is a leaf. */
static a68_val* rowd_slot(a68_rowd* r, int64_t idx) {
  a68_obj* st = rowd_store(r);
  if (st->kind != K_SLOTS) return NULL;
  a68_val* e = &((a68_slots*) st)->s[idx];
  if (r->field) {
    if (e->tag != T_STRUCT) die("internal: field selection on non-struct element");
    a68_slots* fs = (a68_slots*) e->v.p;
    if (r->field - 1 >= fs->h.n) die("internal: field index out of range");
    return &fs->s[r->field - 1];
  }
  return e;
}

static void assign_slot(a68_val* s, a68_val v, int flex, int checked);
void  rowd_put(a68_rowd* r, int64_t idx, a68_val v) {
  a68_val* sl = rowd_slot(r, idx);
  if (sl) assign_slot(sl, v, 1, 0);
  else store_set(rowd_store(r), idx, v);
}

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
/* A store's share count is exact for shares kept in cells and containers; values on the
   operand stack only borrow (see `rowd_borrow`), so a variable is copied at a write only
   when another kept value really shares its store. */
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
  n->field = r->field;
  memcpy(n->dim, r->dim, (size_t) r->h.n * sizeof(a68_dim));
  return n;
}

/* A value taken from a variable for the operand stack borrows the store: the descriptor
   is fresh, but the store's share count is not raised, so the variable is not copied at
   its next write on account of a value that only looked (`UPB d`, `d` passed on).  A
   borrow that is kept — stored in a cell, a structure, a union or a row — becomes a
   share first (`unborrow`); the sweep gives nothing back for a borrow. */
static a68_rowd* rowd_borrow(const a68_rowd* r) {
  a68_rowd* n = rowd_alloc(r->h.n);
  n->base = rowd_store(r);
  n->pad2 = 1;
  n->off = r->off;
  n->field = r->field;
  memcpy(n->dim, r->dim, (size_t) r->h.n * sizeof(a68_dim));
  return n;
}

static a68_val unborrow(a68_val v) {
  if (v.tag == T_ROW) {
    a68_rowd* d = (a68_rowd*) v.v.p;
    if (d->pad2) { d->pad2 = 0; d->base->rc++; }
  }
  return v;
}

/* a fresh row with canonical layout holding copies of the elements of `r` */
a68_val  copy_value(a68_val v);
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
    for (int64_t i = 0; i < n; i++) store_set(ns, i, rowd_get(r, row_store_index(r, i)));
  } else {
    ns = store_alloc_slots((uint32_t) n);
    for (int64_t i = 0; i < n; i++) store_set(ns, i, copy_value(rowd_get(r, row_store_index(r, i))));
  }
  ns->rc = 1;
  c->base = ns;
  return c;
}

a68_val  copy_value(a68_val v) {
  switch (v.tag) {
    case T_ROW: return mk_ptr(T_ROW, (a68_obj*) rowd_borrow((a68_rowd*) v.v.p), 0);
    case T_STRUCT: {
      a68_slots* s = (a68_slots*) v.v.p;
      a68_slots* c = slots_alloc(s->h.n);
      for (uint32_t i = 0; i < s->h.n; i++) c->s[i] = unborrow(copy_value(s->s[i]));
      return mk_ptr(T_STRUCT, (a68_obj*) c, 0);
    }
    case T_UNION: {
      a68_slots* s = (a68_slots*) v.v.p;
      a68_slots* c = slots_alloc(1);
      c->s[0] = unborrow(copy_value(s->s[0]));
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

a68_val  ref_load(a68_val r) {
  a68_obj* b = r.v.p;
  if (b->kind == K_ROWD) {
    a68_rowd* d = (a68_rowd*) b;
    if (r.aux == VIEW_OFF) return mk_ptr(T_ROW, (a68_obj*) rowd_share(d), 0);
    return copy_value(rowd_get(d, (int64_t) r.aux));
  }
  a68_val* s = ref_slot(r);
  return copy_value(*s);
}

a68_val  deref(a68_val r) {
  switch (r.tag) {
    case T_REF: return ref_load(r);
    case T_FILE: return r;
    case T_NIL: die("attempt to dereference NIL");
    case T_UNDEF: die("attempt to use an uninitialised REF value");
    default: die("internal: dereferencing a non-REF");
  }
}

/* The descriptor a row name designates: the variable's own, or a view. */
a68_rowd*  ref_rowd(a68_val r) {
  a68_obj* b = r.v.p;
  if (b->kind == K_ROWD) {
    if (r.aux == VIEW_OFF) return (a68_rowd*) b;
    a68_val e = rowd_get((a68_rowd*) b, (int64_t) r.aux);
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
      rowd_put(dst, row_store_index(dst, i), rowd_get(src, row_store_index(src, i)));
    return;
  }
  for (int64_t i = 0; i < n; i++) {
    a68_val e = rowd_get(src, row_store_index(src, i));
    if (ds->kind == K_LEAF && !leaf_accepts(ds->ek, &e)) {
      /* the destination leaf cannot hold this element: widen the store to slots */
      a68_slots* ns = slots_alloc(ds->n);
      for (int64_t k = 0; k < (int64_t) ds->n; k++) ns->s[k] = store_get(ds, k);
      ns->h.rc = 1;
      owner->base = (a68_obj*) ns;
      ds = (a68_obj*) ns;
    }
    rowd_put(dst, row_store_index(dst, i), ds->kind == K_LEAF ? e : copy_value(e));
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
void  assign_ref(a68_val d, a68_val v, int flex) {
  if (d.tag == T_NIL) die("attempt to assign to NIL");
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
    assign_slot(rowd_slot(r, (int64_t) d.aux), v, flex, 1);
    return;
  }
  assign_slot(ref_slot(d), v, flex, 1);
}

/* `Interp.writeRef`: write without the assignment's checks. */
void  store_ref(a68_val d, a68_val v) {
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
    else assign_slot(rowd_slot(r, (int64_t) d.aux), v, 1, 0);
    return;
  }
  assign_slot(ref_slot(d), v, 1, 0);
}

/* The name of field `f` of the structure a name refers to. */
a68_val  ref_field(a68_val r, uint32_t f) {
  if (r.tag == T_NIL) die("attempt to select from NIL");
  if (r.tag != T_REF) die("internal: select via non-REF");
  a68_obj* b = r.v.p;
  a68_val target;
  if (b->kind == K_ROWD && r.aux == VIEW_OFF) target = mk_ptr(T_ROW, b, 0);
  else if (b->kind == K_ROWD) target = rowd_get((a68_rowd*) b, (int64_t) r.aux);
  else target = *ref_slot(r);
  if (target.tag == T_ROW) {
    /* `f OF a` where `a` names a row of structures: a name of the row of that field of
       every element, which reads and writes through the elements (`Interp.readPath`,
       `Interp.updatePath` with `.field` on a row) */
    a68_rowd* rw = ref_rowd(r);
    if (!rw) die("internal: field selection on non-struct");
    if (rw->field) die("internal: nested multiple selection");
    a68_rowd* v = rowd_alloc(rw->h.n);
    v->base = (a68_obj*) rowd_owner(rw);
    v->off = rw->off;
    v->field = f + 1;
    memcpy(v->dim, rw->dim, (size_t) rw->h.n * sizeof(a68_dim));
    return mk_ptr(T_REF, (a68_obj*) v, VIEW_OFF);
  }
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
    *out = copy_value(rowd_get(r, off));
    return;
  }
  nr->off = off;
  nr->field = r->field;   /* a trim of a multiple selection still selects the field */
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
   chain, the saved environments, the pins, and — in a program of the LLVM back end — the
   heap pointers its native frames hold at their statepoints, found through the LLVM stack
   maps (stackmap.c).  Sweeping frees every unmarked object, after
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

/* a root the LLVM stack maps report: always an object base (docs/GC-DESIGN.md §3.4) */
static void gc_mark_root(void* obj) { gc_push_obj((a68_obj*) obj); }

static void gc_mark(void) {
  nwork = 0;
  for (size_t i = 0; i < sp; i++) gc_push_val(&stack[i]);
  gc_push_obj((a68_obj*) env);
  for (size_t i = 0; i < nsaved; i++) gc_push_obj((a68_obj*) saved[i]);
  io_gc_roots(gc_push_val);
  stackmap_roots(gc_mark_root);   /* returns at once when the binary has no stack maps */
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

/* In verify mode a freed object is poisoned rather than freed, so that a dangling
   reference is caught by the next check; it is kept for `QUARANTINE` collections (a
   reference to it that survives that long would have been seen), then released, so that
   an allocation-heavy program can run under verify mode. */
#define QUARANTINE 4
static a68_obj* quarantine[QUARANTINE];

static void quarantine_release(size_t slot) {
  a68_obj* o = quarantine[slot];
  while (o) { a68_obj* n = o->next; free(o); o = n; }
  quarantine[slot] = NULL;
}

static void gc_sweep(void) {
  /* a dead descriptor gives back its share of a store that survives */
  for (a68_obj* o = all_objects; o; o = o->next)
    if (!o->mark && o->kind == K_ROWD) {
      a68_obj* b = ((a68_rowd*) o)->base;
      if (b && b->mark && b->kind != K_ROWD && b->rc > 0 && !((a68_rowd*) o)->pad2) b->rc--;
    }
  a68_obj** link = &all_objects;
  uint64_t live = 0;
  while (*link) {
    a68_obj* o = *link;
    if (o->mark) { o->mark = 0; live += o->size; link = &o->next; continue; }
    *link = o->next;
    gc_freed_bytes += o->size;
    if (gc_verify) {   /* kept, poisoned, released after QUARANTINE collections */
      size_t slot = (size_t) (gc_collections % QUARANTINE);
      o->kind = K_FREED; o->next = quarantine[slot]; quarantine[slot] = o;
    } else free(o);
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
  if (gc_verify) quarantine_release((size_t) ((gc_collections + 1) % QUARANTINE));
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
double a68_gc_query(uint32_t what) {
  switch (what) {
    case 0: gc_collect(); return 0.0;
    case 1: return (double) gc_collections;
    case 2: return (double) gc_freed_bytes;
    case 3: return gc_seconds;
    default: return 0.0;
  }
}

/* The name of element `i`, in row-major order of the view, of the row a name refers to
   (`Interp.refElem`). */
a68_val ref_elem(a68_val r, uint32_t i) {
  a68_rowd* d = ref_rowd(r);
  if (!d) die("internal: element of a non-row");
  int64_t idx = row_store_index(d, (int64_t) i);
  return mk_ptr(T_REF, (a68_obj*) d, (uint32_t) idx);
}

void  env_set(a68_frame* f) {
  if (nsaved == saved_cap) {
    saved_cap = saved_cap ? saved_cap * 2 : 64;
    saved = (a68_frame**) realloc(saved, saved_cap * sizeof(a68_frame*));
    if (!saved) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  }
  saved[nsaved++] = env;
  env = f;
}

size_t env_saved_depth(void) { return nsaved; }
void env_saved_truncate(size_t n) { if (n < nsaved) { env = saved[n]; nsaved = n; } }

void  env_restore(void) {
  if (nsaved == 0) { fprintf(stderr, "uncaught exception: environment stack underflow\n"); exit(1); }
  env = saved[--nsaved];
}

/* ---------------------------------------------------------------- start-up and shutdown */

void a68rt_boot(const char* blob, uint32_t ll, uint8_t regression, int argc, char** argv, const char* src) {
  gc_init();
  stackmap_init();   /* a no-op for the C back end, whose binaries carry no stack maps */
  tables_parse(blob, &strtab, &strlen_tab, &nstr);
  io_init(argc, argv, src, regression != 0, (int) ll);
  a68_jump_flag = 0;
}

uint32_t a68rt_finish(int w) { (void) w; return io_finish(); }
void a68rt_stop(int w) { (void) w; io_stop(); }
void a68rt_line(uint32_t l, int w) { (void) w; a68_line_no = l; }

/* ---------------------------------------------------------------- jumps */

uint32_t a68rt_jump_pending(int w) { (void) w; return a68_jump_flag; }
void a68rt_jump_clear(int w) { (void) w; a68_jump_flag = 0; }
void a68rt_raise_jump(uint32_t l, int w) { (void) w; a68_jump_flag = l + 1; }

/* ---------------------------------------------------------------- environments */

static int trace_env = -1;
/* `enter` and `enter_args` return the new frame's cells, and `frame_cells` those of the
   frame `depth` levels out, so that compiled code can address cells directly: a frame
   is never moved, and one on the environment chain is never collected. */
void* a68rt_enter(uint32_t n, int w) {
  GC_POLL(); (void) w; env = frame_alloc(n);
  if (trace_env < 0) trace_env = getenv("A68LEAN_TRACE") != NULL;
  if (trace_env) fprintf(stderr, "enter(%u) depth=%u line=%u\n", n, env ? env->depth : 0, a68_line_no);
  return env->c; }

void* a68rt_enter_args(uint32_t n, uint32_t nargs, int w) {
  GC_POLL();
  (void) w;
  a68_frame* f = frame_alloc(n);
  for (uint32_t i = nargs; i > 0; i--) {
    a68_val v = pop();
    if (i - 1 < n) slot_put(&f->c[i - 1], v);
  }
  env = f;
  return f->c;
}

void* a68rt_frame_cells(uint32_t depth, int w) {
  (void) w;
  a68_frame* f = env;
  for (uint32_t k = 0; k < depth && f; k++) f = f->parent;
  if (!f) { fprintf(stderr, "a68lean: internal: frame depth %u out of range\n", depth); exit(1); }
  return f->c;
}

uint32_t a68rt_heap_mark(int w) { (void) w; return 0; }
void a68rt_heap_release(uint32_t m, int w) { (void) m; (void) w; }
void a68rt_leave(int w) { (void) w; if (env) env = env->parent;
  if (trace_env > 0) fprintf(stderr, "leave depth=%u line=%u\n", env ? env->depth : 0, a68_line_no); }
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

a68_val  string_row(const uint8_t* p, int64_t n, int64_t lwb) {
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

  for (int64_t i = 0; i < n; i++) {
    a68_val e = rowd_get(d, row_store_index(d, i));
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
  GC_POLL(); (void) w; push(ops_default(m)); }

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
void a68rt_set_int(uint32_t d, uint32_t s, int64_t v, int w) {
  if (trace_env > 0) fprintf(stderr, "set_int(%u,%u,%lld) env depth=%u\n", d, s, (long long) v, env ? env->depth : 0); (void) w; *cell_of(d, s) = mk_int(v); }

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

int64_t  as_int(a68_val v) {
  if (v.tag == T_INT) return v.v.i;
  if (v.tag == T_UNDEF) die(undef_msg(T_INT));
  dief("internal: INT expected, got tag %lld", (int64_t) v.tag, 0, 0);
}
double  as_real(a68_val v) {
  if (v.tag == T_REAL) return v.v.r;
  if (v.tag == T_INT) return (double) v.v.i;
  if (v.tag == T_UNDEF) die(undef_msg(T_REAL));
  dief("internal: REAL expected, got tag %lld", (int64_t) v.tag, 0, 0);
}
uint8_t  as_bool(a68_val v) {
  if (v.tag == T_BOOL) return (uint8_t) v.v.u;
  if (v.tag == T_UNDEF) die(undef_msg(T_BOOL));
  die("internal: BOOL expected");
}
uint32_t  as_char(a68_val v) {
  if (v.tag == T_CHAR) return (uint32_t) v.v.u;
  if (v.tag == T_UNDEF) die(undef_msg(T_CHAR));
  die("internal: CHAR expected");
}
uint64_t  as_bits(a68_val v) {
  if (v.tag == T_BITS) return v.v.u;
  if (v.tag == T_UNDEF) die(undef_msg(T_BITS));
  die("internal: BITS expected");
}

int64_t a68rt_cell_int(uint32_t d, uint32_t s, int w) { (void) w;
  if (trace_env > 0) fprintf(stderr, "cell_int(%u,%u) tag=%u env depth=%u line=%u\n", d, s, cell_of(d, s)->tag, env ? env->depth : 0, a68_line_no);
  return as_int(*cell_of(d, s)); }
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
  return rowd_get(r, elem_index(r, rank, i, j));
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
/* `f OF r` on a row value: the row of that field of every element (`Interp.readPath`). */
static a68_val row_field_select(a68_val v, uint32_t idx) {
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
    a68_val e = rowd_get(r, row_store_index(r, i));
    if (e.tag != T_STRUCT) die("internal: field selection on non-struct element");
    st->s[i] = unborrow(copy_value(((a68_slots*) e.v.p)->s[idx]));
  }
  st->h.rc = 1;
  d->base = (a68_obj*) st;
  return mk_ptr(T_ROW, (a68_obj*) d, 0);
}

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
    v = rowd_get(r, elem_index(r, rank, i, j));
  }
  uint32_t nf = (spec >> 8) & 15;
  for (uint32_t k = 0; k < nf; k++) {
    uint32_t f = (fields >> (8 * k)) & 255;
    if (v.tag == T_ROW) { v = row_field_select(v, f); continue; }
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

  for (int64_t i = 0; i < n; i++) tmp[i] = rowd_get(src, row_store_index(src, i));
  int ok = append_in_place(c, tmp, n);
  free(tmp);
  if (!ok) die("internal: append to a value that is not a string variable");
}

/* append elements in place through a name of a string variable (`Interp.appendInPlace`
   as `fileOut` uses it); 0 when the name is not a plain cell */
int ref_append_values(a68_val r, const a68_val* vs, int64_t n) {
  if (r.tag != T_REF) return 0;
  a68_obj* b = r.v.p;
  if (b->kind != K_SLOTS && b->kind != K_FRAME) return 0;
  return append_in_place(ref_slot(r), vs, n);
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
  a68_val v = deref(r);
  if (v.tag == T_UNDEF) die("attempt to use an uninitialised value");
  push(v);
}

void  call_value(a68_val f, uint32_t nargs) {
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
      /* the arguments stay on the stack, rooted, until the call returns: the prelude may
         call back into compiled code, which may collect */
      size_t base = sp - nargs;
      a68_val res;
      call_builtin(f.aux, nargs, &res);
      sp = base;
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
  const a68_mode* s = mode_at(src);
  const a68_mode* d = mode_at(dst);
  if (v.tag == T_INT && s->k == M_INT && s->len <= 0 && d->k == M_REAL && d->len <= 0) {
    push(mk_real((double) v.v.i));
    return;
  }
  if (s->k == d->k && s->len == d->len && s->k != M_NAMED) { push(v); return; }
  push(ops_widen(src, dst, v));
}

void a68rt_row_of(int w) {
  GC_POLL();
  (void) w;
  a68_val v = pop();
  if (v.tag == T_REF) { push(v); return; }
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
  s->s[0] = unborrow(v);
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

static int mode_is(uint32_t m, a68_mkind k, int64_t len) { return mode_at(m)->k == k && mode_at(m)->len == len; }
static int mode_kind(uint32_t m, a68_mkind k) { return mode_at(m)->k == k; }

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

int  is_string_row(a68_val v) {
  return v.tag == T_ROW && ((a68_rowd*) v.v.p)->h.n == 1;
}

/* the characters of a string value, checked as `Interp.checkChars` checks them */
uint8_t*  string_bytes(a68_val v, int64_t* n) {
  a68_rowd* d = (a68_rowd*) v.v.p;
  *n = row_count(d);
  uint8_t* b = (uint8_t*) xmalloc((size_t) *n + 1);

  for (int64_t i = 0; i < *n; i++) {
    a68_val e = rowd_get(d, row_store_index(d, i));
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

/* The common cases of the primitive modes, answered here; 1 when done (the result is in
   `*out`), 0 for the general path in ops.c. */
static int native_dyop(const char* op, uint32_t m1, uint32_t m2, a68_val a, a68_val b, a68_val* out) {
  if (a.tag == T_UNDEF || b.tag == T_UNDEF) return 0;   /* the general path reports it in the mode's words */
  if (mode_is(m1, M_INT, 0) && mode_is(m2, M_INT, 0) && a.tag == T_INT && b.tag == T_INT) {
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
  if (mode_is(m1, M_REAL, 0) && mode_is(m2, M_REAL, 0) && (a.tag == T_REAL || a.tag == T_INT) && (b.tag == T_REAL || b.tag == T_INT)) {
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
  if (mode_is(m1, M_REAL, 0) && mode_is(m2, M_INT, 0) && (a.tag == T_REAL || a.tag == T_INT) && b.tag == T_INT) {
    double x = as_real(a);
    if (strcmp(op, "**") == 0) { *out = mk_real(pow_real_int(x, b.v.i)); return 1; }
    if (strcmp(op, "I") == 0) { *out = mk_compl(x, (double) b.v.i); return 1; }
    return 0;
  }
  if (mode_kind(m1, M_BOOL) && mode_kind(m2, M_BOOL) && a.tag == T_BOOL && b.tag == T_BOOL) {
    int x = a.v.u != 0, y = b.v.u != 0;
    if (strcmp(op, "AND") == 0) { *out = mk_bool(x && y); return 1; }
    if (strcmp(op, "OR") == 0) { *out = mk_bool(x || y); return 1; }
    if (strcmp(op, "XOR") == 0 || strcmp(op, "/=") == 0) { *out = mk_bool(x != y); return 1; }
    if (strcmp(op, "=") == 0) { *out = mk_bool(x == y); return 1; }
    return 0;
  }
  if (mode_kind(m1, M_CHAR) && mode_kind(m2, M_CHAR) && a.tag == T_CHAR && b.tag == T_CHAR) {
    if (is_cmp(op)) { *out = mk_bool(cmp_op(op, a.v.u < b.v.u ? -1 : a.v.u > b.v.u ? 1 : 0)); return 1; }
    return 0;
  }
  if (mode_kind(m1, M_ROW) && mode_kind(m2, M_ROW) && is_string_row(a) && is_string_row(b)
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
  if (mode_is(m1, M_INT, 0) && mode_kind(m2, M_ROW) && a.tag == T_INT && b.tag == T_ROW) {
    a68_rowd* d = (a68_rowd*) b.v.p;
    int64_t k = a.v.i;
    if (strcmp(op, "LWB") == 0 || strcmp(op, "UPB") == 0) {
      if (k < 1 || k > (int64_t) d->h.n) die("LWB/UPB dimension out of range");
      *out = mk_int(strcmp(op, "LWB") == 0 ? d->dim[k - 1].l : d->dim[k - 1].u);
      return 1;
    }
    return 0;
  }
  if (mode_is(m1, M_BITS, 0) && mode_is(m2, M_BITS, 0) && a.tag == T_BITS && b.tag == T_BITS) {
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
  if (mode_is(m1, M_BITS, 0) && mode_is(m2, M_INT, 0) && a.tag == T_BITS && b.tag == T_INT) {
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
  if (mode_is(m1, M_INT, 0) && mode_is(m2, M_BITS, 0) && a.tag == T_INT && b.tag == T_BITS) {
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
  if (a.tag != T_REF || !mode_kind(m1, M_REF)) return 0;
  /* the mode line of a REF names the mode referred to by its index */
  uint32_t target = mode_at(m1)->sub;
  int t_int = mode_is(target, M_INT, 0), t_real = mode_is(target, M_REAL, 0), t_row = mode_kind(target, M_ROW);
  if (!t_int && !t_real && !t_row) return 0;
  if (t_row && strcmp(op, "+:=") == 0 && b.tag == T_ROW && is_string_row(b)) {
    /* appending to a string variable: in place when the cell holds a plain row */
    a68_val* slot = a.v.p->kind == K_ROWD ? NULL : ref_slot(a);
    if (slot && slot->tag == T_ROW) {
      a68_rowd* src = (a68_rowd*) b.v.p;
      int64_t n = row_count(src);
      a68_val* tmp = (a68_val*) xmalloc((size_t) (n ? n : 1) * sizeof(a68_val));
      a68_obj* st = rowd_store(src);
      for (int64_t i = 0; i < n; i++) tmp[i] = rowd_get(src, row_store_index(src, i));
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
  if (mode_is(m, M_INT, 0) && v.tag == T_INT) {
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
  if (mode_is(m, M_REAL, 0) && (v.tag == T_REAL || v.tag == T_INT)) {
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
  if (mode_kind(m, M_BOOL) && v.tag == T_BOOL) {
    if (strcmp(op, "NOT") == 0) { *out = mk_bool(!v.v.u); return 1; }
    if (strcmp(op, "ABS") == 0) { *out = mk_int(v.v.u ? 1 : 0); return 1; }
    return 0;
  }
  if (mode_kind(m, M_CHAR) && v.tag == T_CHAR) {
    if (strcmp(op, "ABS") == 0) { *out = mk_int((int64_t) v.v.u); return 1; }
    return 0;
  }
  if (mode_is(m, M_BITS, 0) && v.tag == T_BITS) {
    if (strcmp(op, "NOT") == 0) { *out = mk_bits(0xffffffffu ^ v.v.u); return 1; }
    if (strcmp(op, "ABS") == 0) { *out = mk_int(v.v.u >= 2147483648u ? (int64_t) v.v.u - 4294967296LL : (int64_t) v.v.u); return 1; }
    return 0;
  }
  if (mode_kind(m, M_ROW) && v.tag == T_ROW) {
    a68_rowd* d = (a68_rowd*) v.v.p;
    if (strcmp(op, "LWB") == 0) { *out = mk_int(d->dim[0].l); return 1; }
    if (strcmp(op, "UPB") == 0) { *out = mk_int(d->dim[0].u); return 1; }
    if (strcmp(op, "ELEMS") == 0) { *out = mk_int(row_count(d)); return 1; }
    return 0;
  }
  return 0;
}

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
  /* the operands stay on the stack while the general path computes */
  a68_val res = ops_dyadic(strtab[op], m1, m2, stack[sp - 2], stack[sp - 1]);
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
  a68_val res = ops_monadic(strtab[op], m, *top());
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
  if (v.tag == T_ROW) { push(row_field_select(v, idx)); return; }
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

/* `ek`: the leaf kind the elements will have when the initial value is undefined, so
   that a row of a primitive mode starts as a leaf with every element undefined rather
   than as slots of T_UNDEF: the same values, in the layout compiled code reads inline. */
void a68rt_new_row_of(uint32_t ndims, uint8_t flex, uint32_t ek, int w) {
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
  a68_obj* st = (init.tag == T_UNDEF && ek != 0) ? (a68_obj*) leaf_alloc((uint16_t) ek, (uint32_t) n)
                                                 : store_alloc_for((uint32_t) n, &init);
  if (init.tag == T_UNDEF && ek != 0) { /* a fresh leaf: every defined bit clear */ }
  else if (st->kind == K_LEAF) { for (int64_t i = 0; i < n; i++) store_set(st, i, init); }
  else for (int64_t i = 0; i < n; i++) ((a68_slots*) st)->s[i] = unborrow(copy_value(init));
  st->rc = 1;
  d->base = st;
  push(mk_ptr(T_ROW, (a68_obj*) d, 0));
}

void a68rt_new_row(uint32_t ndims, uint8_t flex, int w) { a68rt_new_row_of(ndims, flex, 0, w); }

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
    for (uint32_t i = 0; i < n; i++) s->s[i] = unborrow(vs[i]);
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
    for (int64_t j = 0; j < per; j++) store_set(st, (int64_t) i * per + j, rowd_get(r, row_store_index(r, j)));
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
  uint8_t ok = (uint8_t) ops_conform(m, vm);
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
    if (ops_mode_is_union(m)) push(copy_value(v));
    else push(copy_value(inner));
  }
  return ok ? 1 : 0;
}
