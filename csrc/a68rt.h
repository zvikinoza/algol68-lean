/* The C runtime of compiled programs: the representation of values, the collector's
   objects, and the entry points the modules of the runtime share.  The design is
   docs/GC-DESIGN.md; the semantics of everything here are those of the evaluator
   (A68/Interp.lean), whose definitions are named where a rule is reproduced. */
#ifndef A68RT_H
#define A68RT_H
#include <stdint.h>
#include <stddef.h>

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
typedef struct { a68_obj h; uint8_t d[]; } a68_leaf;     /* elements, then one defined byte per element */
typedef struct { int64_t l, u, stride; } a68_dim;
/* `field`: one plus the field a multiple selection through a name picks in every element,
   0 for a plain row (`Interp.readPath` with `.field` on a row) */
typedef struct { a68_obj h; a68_obj* base; int64_t off; uint32_t field; uint32_t pad2; a68_dim dim[]; } a68_rowd;
typedef struct a68_frame { a68_obj h; struct a68_frame* parent; uint32_t depth; uint32_t pad; a68_val c[]; } a68_frame;

#define VIEW_OFF 0xffffffffu        /* a REF whose target is the row a view describes */

/* ---------------------------------------------------------------- the shared API (rt.c) */

__attribute__((noreturn)) void die(const char* msg);
__attribute__((noreturn)) void dief(const char* fmt, int64_t a, int64_t b, int64_t c);
void* xmalloc(size_t n);

a68_val mk_int(int64_t i);
a68_val mk_real(double r);
a68_val mk_bool(int b);
a68_val mk_char(uint32_t c);
a68_val mk_bits(uint64_t b);
a68_val mk_tag(uint32_t t);
a68_val mk_ptr(uint32_t t, a68_obj* p, uint32_t aux);

void push(a68_val v);
a68_val pop(void);
a68_val* top(void);
extern a68_val* stack;
extern size_t sp;

a68_slots* slots_alloc(uint32_t n);
a68_leaf* leaf_alloc(uint16_t ek, uint32_t n);
a68_rowd* rowd_alloc(uint32_t ndims);
a68_obj* store_alloc_for(uint32_t n, const a68_val* sample);
a68_obj* store_alloc_slots(uint32_t n);
a68_obj* rowd_store(const a68_rowd* r);
int64_t row_count(const a68_rowd* r);
int64_t row_store_index(const a68_rowd* r, int64_t flat);
a68_val rowd_get(const a68_rowd* r, int64_t idx);
void rowd_put(a68_rowd* r, int64_t idx, a68_val v);
void store_set(a68_obj* st, int64_t idx, a68_val v);
a68_val store_get(a68_obj* st, int64_t idx);
a68_val copy_value(a68_val v);
a68_val string_row(const uint8_t* p, int64_t n, int64_t lwb);
uint8_t* string_bytes(a68_val v, int64_t* n);   /* `Interp.strOf` / `checkChars`: caller frees */
int is_string_row(a68_val v);

a68_val ref_load(a68_val r);           /* `Interp.readRef` on a C name */
void store_ref(a68_val d, a68_val v);  /* `Interp.writeRef` */
void assign_ref(a68_val d, a68_val v, int flex);   /* `Interp.assignTo` */
a68_val ref_field(a68_val r, uint32_t f);
a68_val ref_elem(a68_val r, uint32_t i);           /* `Interp.refElem`: element i in the view's order */
a68_rowd* ref_rowd(a68_val r);
a68_val deref(a68_val r);

int64_t as_int(a68_val v);
double as_real(a68_val v);
uint8_t as_bool(a68_val v);
uint32_t as_char(a68_val v);
uint64_t as_bits(a68_val v);

/* apply a procedure value to the `nargs` values on top of the stack; the result replaces them */
void call_value(a68_val f, uint32_t nargs);

extern char** strtab;
extern size_t* strlen_tab;
extern size_t nstr;
extern uint32_t a68_jump_flag;
extern uint32_t a68_line_no;

/* the frame chain, for evaluating the holes of a format text in its own environment */
void env_set(a68_frame* f);
void env_restore(void);
void a68_dispatch_hole(size_t idx);

#endif
