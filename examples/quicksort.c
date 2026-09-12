
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>


/* The C runtime (csrc/rt.c and its companions), plain C: a compiled program links it and
   the C library only.  Every entry point takes a trailing dummy argument `W`, a leftover of
   the Lean-backed runtime this one replaced, kept so that the generator's call sites read
   the same. */
#define W 0
void a68rt_boot(const char* blob, uint32_t ll, uint8_t reg, int argc, char** argv, const char* src);
uint32_t a68rt_finish(int w);
void a68rt_line(uint32_t l, int w);
void a68rt_stop(int w);
uint32_t a68rt_jump_pending(int w);
void a68rt_jump_clear(int w);
void a68rt_raise_jump(uint32_t l, int w);
void a68rt_enter(uint32_t n, int w);
void a68rt_enter_args(uint32_t n, uint32_t k, int w);
uint32_t a68rt_heap_mark(int w);
void a68rt_heap_release(uint32_t m, int w);
void a68rt_leave(int w);
uint32_t a68rt_env_depth(int w);
void a68rt_env_truncate(uint32_t d, int w);
uint32_t a68rt_stack_depth(int w);
void a68rt_stack_truncate(uint32_t d, int w);
void a68rt_push_int(int64_t v, int w);
void a68rt_push_bigint(uint32_t i, int w);
void a68rt_push_bigbits(uint32_t i, int w);
void a68rt_push_real(double v, int w);
void a68rt_push_bool(uint8_t v, int w);
void a68rt_push_char(uint32_t v, int w);
void a68rt_push_bits(uint64_t v, int w);
void a68rt_push_str(uint32_t i, int w);
void a68rt_push_undef(int w);
void a68rt_push_nil(int w);
void a68rt_push_void(int w);
void a68rt_push_builtin(uint32_t i, int w);
void a68rt_push_file(uint32_t i, int w);
void a68rt_push_skip(uint32_t m, int w);
void a68rt_push_cell(uint32_t d, uint32_t s, int w);
void a68rt_push_ref(uint32_t d, uint32_t s, int w);
void a68rt_push_proc(uint32_t fn, uint32_t np, int w);
void a68rt_push_format(uint32_t k, int w);
void a68rt_store(uint32_t d, uint32_t s, int w);
void a68rt_bind_cell(uint32_t d, uint32_t s, int w);
void a68rt_set_int(uint32_t d, uint32_t s, int64_t v, int w);
void a68rt_pop(int w);
void a68rt_nip(int w);
void a68rt_dup(int w);
int64_t a68rt_pop_int(int w);
uint8_t a68rt_pop_bool(int w);
double a68rt_pop_real(int w);
uint32_t a68rt_pop_char(int w);
uint64_t a68rt_pop_bits(int w);
void a68rt_deref(int w);
void a68rt_deproc(int w);
void a68rt_widen(uint32_t a, uint32_t b, int w);
void a68rt_row_of(int w);
void a68rt_unite(uint32_t m, int w);
void a68rt_voiding(int w);
void a68rt_assign(uint8_t flex, int w);
void a68rt_ident_rel(uint8_t isnt, int w);
void a68rt_dyop(uint32_t op, uint32_t m1, uint32_t m2, int w);
void a68rt_monop(uint32_t op, uint32_t m, int w);
void a68rt_call(uint32_t n, int w);
void a68rt_select(uint32_t i, uint8_t viaRef, int w);
void a68rt_slice(uint32_t n, uint64_t kinds, uint8_t viaRef, int w);
void a68rt_new_row(uint32_t n, uint8_t flex, int w);
void a68rt_gen(int w);
void a68rt_collateral(uint32_t n, uint8_t st, uint32_t dims, int w);
uint32_t a68rt_case_index(uint32_t n, int w);
uint8_t a68rt_conform(uint32_t m, uint8_t bind, int w);
int64_t a68rt_cell_int(uint32_t d, uint32_t s, int w);
double a68rt_cell_real(uint32_t d, uint32_t s, int w);
uint8_t a68rt_cell_bool(uint32_t d, uint32_t s, int w);
uint32_t a68rt_cell_char(uint32_t d, uint32_t s, int w);
uint64_t a68rt_cell_bits(uint32_t d, uint32_t s, int w);
void a68rt_set_cell_int(uint32_t d, uint32_t s, int64_t v, int w);
void a68rt_set_cell_real(uint32_t d, uint32_t s, double v, int w);
void a68rt_set_cell_bool(uint32_t d, uint32_t s, uint8_t v, int w);
void a68rt_set_cell_char(uint32_t d, uint32_t s, uint32_t v, int w);
void a68rt_set_cell_bits(uint32_t d, uint32_t s, uint64_t v, int w);
void a68rt_arith_error(uint32_t k, int w);
void a68rt_undef_error(uint32_t k, int w);
int64_t a68rt_row_int(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, int w);
double a68rt_row_real(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, int w);
uint8_t a68rt_row_bool(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, int w);
uint32_t a68rt_row_char(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, int w);
uint64_t a68rt_row_bits(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, int w);
void a68rt_set_row_int(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, int64_t v, int w);
void a68rt_set_row_real(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, double v, int w);
void a68rt_set_row_bool(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, uint8_t v, int w);
void a68rt_set_row_char(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, uint32_t v, int w);
void a68rt_set_row_bits(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, uint64_t v, int w);
void a68rt_sel_push(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, int w);
int64_t a68rt_sel_int(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, int w);
double a68rt_sel_real(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, int w);
uint8_t a68rt_sel_bool(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, int w);
uint32_t a68rt_sel_char(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, int w);
uint64_t a68rt_sel_bits(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, int w);
void a68rt_set_sel_int(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, int64_t v, int w);
void a68rt_set_sel_real(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, double v, int w);
void a68rt_set_sel_bool(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, uint8_t v, int w);
void a68rt_set_sel_char(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, uint32_t v, int w);
void a68rt_set_sel_bits(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, uint64_t v, int w);
uint8_t a68rt_cell_isnil(uint32_t d, uint32_t s, int w);
void a68rt_sel_store(uint32_t dd, uint32_t ds, uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, int w);
void a68rt_append_char(uint32_t d, uint32_t s, uint32_t ch, int w);
void a68rt_append(uint32_t d, uint32_t s, int w);
void a68rt_index_error(int64_t i, int64_t l, int64_t u, int w);
uint32_t a68rt_cell_cproc(uint32_t d, uint32_t s, int w);
void a68rt_push_bytes(const uint8_t* p, int64_t n, int64_t l, int w);
int64_t a68rt_pop_bytes(uint8_t** out, int64_t* l, int w);
/* the results of the runtime are plain C values now; these wrappers are identities */
#define a68_v(x)   ((void) (x))
#define a68_u32(x) (x)
#define a68_i64(x) (x)
#define a68_u8(x)  (x)
#define a68_f64(x) (x)
#define a68_u64(x) (x)


extern uint32_t a68_line_no;
#define a68_line(n) (a68_line_no = (n))
extern uint32_t a68_jump_flag;
#define a68_jump()        a68_jump_flag
#define a68_jump_clear()  (a68_jump_flag = 0)
#define a68_env_depth()   a68_u32(a68rt_env_depth(W))
#define a68_stack_depth() a68_u32(a68rt_stack_depth(W))
#define a68_bool()        (a68_u8(a68rt_pop_bool(W)) != 0)
#define a68_int()         a68_i64(a68rt_pop_int(W))
#define a68_case(n)       a68_u32(a68rt_case_index(n, W))
#define a68_conform(m,b)  (a68_u8(a68rt_conform(m, b, W)) != 0)

/* ---- native scalar arithmetic ----------------------------------------------
   Values of primitive mode are computed in C types here, so an expression like
   s + i * 3 allocates nothing and never touches the operand stack.  Each helper
   reproduces exactly the check its interpreted counterpart performs, and reports
   a failure through a68rt_arith_error, which prints and exits like any other
   runtime error. */


#define a68_cell_i(d,s)   a68_i64(a68rt_cell_int(d, s, W))
#define a68_cell_r(d,s)   a68_f64(a68rt_cell_real(d, s, W))
#define a68_cell_b(d,s)   a68_u8(a68rt_cell_bool(d, s, W))
#define a68_cell_c(d,s)   a68_u32(a68rt_cell_char(d, s, W))
#define a68_cell_u(d,s)   a68_u64(a68rt_cell_bits(d, s, W))
#define a68_set_i(d,s,v)  a68_v(a68rt_set_cell_int(d, s, v, W))
#define a68_set_r(d,s,v)  a68_v(a68rt_set_cell_real(d, s, v, W))
#define a68_set_b(d,s,v)  a68_v(a68rt_set_cell_bool(d, s, v, W))
#define a68_set_c(d,s,v)  a68_v(a68rt_set_cell_char(d, s, v, W))
#define a68_set_u(d,s,v)  a68_v(a68rt_set_cell_bits(d, s, v, W))


#define a68_row_i(d,s,r,i,j)  a68_i64(a68rt_row_int(d, s, r, i, j, W))
#define a68_row_r(d,s,r,i,j)  a68_f64(a68rt_row_real(d, s, r, i, j, W))
#define a68_row_b(d,s,r,i,j)  a68_u8(a68rt_row_bool(d, s, r, i, j, W))
#define a68_row_c(d,s,r,i,j)  a68_u32(a68rt_row_char(d, s, r, i, j, W))
#define a68_row_u(d,s,r,i,j)  a68_u64(a68rt_row_bits(d, s, r, i, j, W))
#define a68_set_row_i(d,s,r,i,j,v)  a68_v(a68rt_set_row_int(d, s, r, i, j, v, W))
#define a68_set_row_r(d,s,r,i,j,v)  a68_v(a68rt_set_row_real(d, s, r, i, j, v, W))
#define a68_set_row_b(d,s,r,i,j,v)  a68_v(a68rt_set_row_bool(d, s, r, i, j, v, W))
#define a68_set_row_c(d,s,r,i,j,v)  a68_v(a68rt_set_row_char(d, s, r, i, j, v, W))
#define a68_set_row_u(d,s,r,i,j,v)  a68_v(a68rt_set_row_bits(d, s, r, i, j, v, W))

/* One field of a structure a cell holds, or that is an element of a row a cell holds, or
   that a cell points at.  `spec` and `fields` describe the chain of selectors; see the
   runtime.  Anything that does not fit the shape falls back to the general machinery. */
#define a68_isnil(d,s)  a68_u8(a68rt_cell_isnil(d, s, W))

#define a68_sel_i(d,s,sp,i,j,f)  a68_i64(a68rt_sel_int(d, s, sp, i, j, f, W))
#define a68_sel_r(d,s,sp,i,j,f)  a68_f64(a68rt_sel_real(d, s, sp, i, j, f, W))
#define a68_sel_b(d,s,sp,i,j,f)  a68_u8(a68rt_sel_bool(d, s, sp, i, j, f, W))
#define a68_sel_c(d,s,sp,i,j,f)  a68_u32(a68rt_sel_char(d, s, sp, i, j, f, W))
#define a68_sel_u(d,s,sp,i,j,f)  a68_u64(a68rt_sel_bits(d, s, sp, i, j, f, W))
#define a68_set_sel_i(d,s,sp,i,j,f,v)  a68_v(a68rt_set_sel_int(d, s, sp, i, j, f, v, W))
#define a68_set_sel_r(d,s,sp,i,j,f,v)  a68_v(a68rt_set_sel_real(d, s, sp, i, j, f, v, W))
#define a68_set_sel_b(d,s,sp,i,j,f,v)  a68_v(a68rt_set_sel_bool(d, s, sp, i, j, f, v, W))
#define a68_set_sel_c(d,s,sp,i,j,f,v)  a68_v(a68rt_set_sel_char(d, s, sp, i, j, f, v, W))
#define a68_set_sel_u(d,s,sp,i,j,f,v)  a68_v(a68rt_set_sel_bits(d, s, sp, i, j, f, v, W))

/* `s +:= c` and `s +:= t` where `s` is a row a cell holds: appended in place. */
#define a68_appendc(d,s,ch)  a68_v(a68rt_append_char(d, s, ch, W))

#define a68_pop_i()  a68_i64(a68rt_pop_int(W))
#define a68_pop_r()  a68_f64(a68rt_pop_real(W))
#define a68_pop_b()  a68_u8(a68rt_pop_bool(W))
#define a68_pop_c()  a68_u32(a68rt_pop_char(W))
#define a68_pop_u()  a68_u64(a68rt_pop_bits(W))

/* A promoted variable read before it was assigned: report exactly what the evaluator
   would have reported for an uninitialised cell of that mode. */
static int64_t  a68_und_i(void) { a68_v(a68rt_undef_error(0, W)); return 0; }
static double   a68_und_r(void) { a68_v(a68rt_undef_error(1, W)); return 0.0; }
static uint8_t  a68_und_b(void) { a68_v(a68rt_undef_error(2, W)); return 0; }
static uint32_t a68_und_c(void) { a68_v(a68rt_undef_error(3, W)); return 0; }
static uint64_t a68_und_u(void) { a68_v(a68rt_undef_error(4, W)); return 0; }
/* Rows promoted to C arrays: bounds checks that report what the evaluator's subscripting
   reports, and element reads that apply its undefined test. */
static void a68_index_error(int64_t i, int64_t l, int64_t u) { a68_v(a68rt_index_error(i, l, u, W)); exit(1); }
static inline size_t a68_ao(int64_t l, int64_t u, int64_t i) {
  if (__builtin_expect(i < l || i > u, 0)) a68_index_error(i, l, u);
  return (size_t)(i - l);
}
static inline size_t a68_ao2(int64_t l0, int64_t u0, int64_t l1, int64_t u1, int64_t i, int64_t j) {
  if (__builtin_expect(i < l0 || i > u0, 0)) a68_index_error(i, l0, u0);
  if (__builtin_expect(j < l1 || j > u1, 0)) a68_index_error(j, l1, u1);
  return (size_t)((i - l0) * (u1 - l1 + 1) + (j - l1));
}
/* the value of an element of a row of unions; its tag says which member holds it */
typedef union { int64_t i; double r; uint64_t u; } a68_uv;
static void* a68_row_alloc(size_t n, size_t sz) {
  void* p = calloc(n ? n : 1, sz);
  if (!p) exit(1);
  return p;
}
#define A68_AR(S, T, UND) static inline T a68_ar_##S(T* p, uint8_t* d, int64_t l, int64_t u, int64_t i) { size_t o = a68_ao(l, u, i); return d[o] ? p[o] : UND(); } static inline T a68_ar2_##S(T* p, uint8_t* d, int64_t l0, int64_t u0, int64_t l1, int64_t u1, int64_t i, int64_t j) { size_t o = a68_ao2(l0, u0, l1, u1, i, j); return d[o] ? p[o] : UND(); }
A68_AR(i, int64_t, a68_und_i)
A68_AR(r, double, a68_und_r)
A68_AR(b, uint8_t, a68_und_b)
A68_AR(c, uint32_t, a68_und_c)
A68_AR(u, uint64_t, a68_und_u)
/* A STRING kept in a C buffer: its bytes, how many, the capacity, and its lower bound. */
typedef struct { uint8_t* p; int64_t n, cap, l; } a68_str;
static void a68_str_reserve(a68_str* s, int64_t n) {
  if (n <= s->cap) return;
  int64_t c = s->cap ? s->cap : 16;
  while (c < n) c *= 2;
  s->p = (uint8_t*) realloc(s->p, (size_t) c);
  if (!s->p) exit(1);
  s->cap = c;
}
static void a68_str_setn(a68_str* s, const char* b, int64_t n, int64_t l) {
  a68_str_reserve(s, n);
  if (n) memcpy(s->p, b, (size_t) n);
  s->n = n; s->l = l;
}
static inline void a68_str_addc(a68_str* s, uint32_t c) {
  if (s->n == s->cap) a68_str_reserve(s, s->n + 1);
  s->p[s->n++] = (uint8_t) c; s->l = 1;
}
static void a68_str_addn(a68_str* s, const char* b, int64_t n) {
  a68_str_reserve(s, s->n + n);
  if (n) memcpy(s->p + s->n, b, (size_t) n);
  s->n += n; s->l = 1;
}
static void a68_str_adds(a68_str* s, const a68_str* o) {
  int64_t n = o->n;
  a68_str_reserve(s, s->n + n);
  if (n) memmove(s->p + s->n, o->p, (size_t) n);
  s->n += n; s->l = 1;
}
static inline uint32_t a68_str_at(const a68_str* s, int64_t i) {
  if (__builtin_expect(i < s->l || i > s->l + s->n - 1, 0)) a68_index_error(i, s->l, s->l + s->n - 1);
  return s->p[i - s->l];
}
static int a68_str_cmp(const uint8_t* a, int64_t na, const uint8_t* b, int64_t nb) {
  int64_t m = na < nb ? na : nb;
  int r = m ? memcmp(a, b, (size_t) m) : 0;
  if (r) return r < 0 ? -1 : 1;
  return na < nb ? -1 : (na > nb ? 1 : 0);
}
static void a68_str_push(const a68_str* s) {
  a68rt_push_bytes(s->p, s->n, s->l, W);
}
static void a68_str_pop(a68_str* s) {
  uint8_t* q = NULL; int64_t l = 1;
  int64_t n = a68rt_pop_bytes(&q, &l, W);
  a68_str_setn(s, (const char*) q, n, l);
  free(q);
}
static void a68_str_popadd(a68_str* s) {
  uint8_t* q = NULL; int64_t l = 1;
  int64_t n = a68rt_pop_bytes(&q, &l, W);
  a68_str_addn(s, (const char*) q, n);
  free(q);
}
#define A68_INT_MAX 2147483647LL

static int64_t a68_die_i(uint32_t k) { a68_v(a68rt_arith_error(k, W)); return 0; }
static double  a68_die_r(uint32_t k) { a68_v(a68rt_arith_error(k, W)); return 0.0; }

/* INT is the range [-2147483647, 2147483647]; operands are always inside it, so the
   int64 intermediate of a sum or product cannot itself overflow. */
static inline int64_t a68_rng(int64_t v) {
  if (v > A68_INT_MAX || v < -A68_INT_MAX) return a68_die_i(0);
  return v;
}
static inline int64_t a68_add_i(int64_t a, int64_t b) { return a68_rng(a + b); }
static inline int64_t a68_sub_i(int64_t a, int64_t b) { return a68_rng(a - b); }
static inline int64_t a68_mul_i(int64_t a, int64_t b) { return a68_rng(a * b); }
static inline int64_t a68_neg_i(int64_t a)            { return a68_rng(-a); }
static inline int64_t a68_abs_i(int64_t a)            { return a68_rng(a < 0 ? -a : a); }
static inline int64_t a68_sign_i(int64_t a) { return a > 0 ? 1 : (a < 0 ? -1 : 0); }
static inline int64_t a68_sign_r(double a)  { return a > 0 ? 1 : (a < 0 ? -1 : 0); }

/* OVER truncates toward zero, which is C division. */
static inline int64_t a68_over_i(int64_t a, int64_t b) {
  if (b == 0) return a68_die_i(1);
  return a / b;
}
/* MOD is Euclidean against the absolute value of the right operand, so it is never
   negative; C remainder takes the sign of the left operand and has to be corrected. */
static inline int64_t a68_mod_i(int64_t a, int64_t b) {
  if (b == 0) return a68_die_i(1);
  int64_t m = b < 0 ? -b : b;
  int64_t r = a % m;
  return r < 0 ? r + m : r;
}
static inline double a68_chk_r(double x) {
  if (x != x) return a68_die_r(3);
  if (x > 1.7976931348623157e308 || x < -1.7976931348623157e308) return a68_die_r(2);
  return x;
}
/* REAL division checks the divisor, not the quotient, as a68g does: an infinite or NaN
   result is reported only by a later operation that checks.  `/:=` behaves the same. */
static inline double a68_div_r(double a, double b) {
  if (b == 0.0) return a68_die_r(3);
  return a / b;
}
static inline double a68_diveq_r(double a, double b) {
  if (b == 0.0) return a68_die_r(3);
  return a / b;
}
/* Exponentiation and the REAL standard functions, following the evaluator: INT ** INT and
   REAL ** INT by square-and-multiply with its checks, REAL ** REAL as exp (y ln x), and each
   function with its domain check and, except exp and exp2, a check of its result. */
static inline int64_t a68_pow_i(int64_t m, int64_t n) {
  if (n < 0) return a68_die_i(8);
  if (m == 0 && n == 0) return 1;
  if (m == 0 || m == 1) return m;
  if (m == -1) return (n % 2 == 0) ? 1 : -1;
  uint64_t nn = (uint64_t) n, bit = 1; int64_t mm = m, p = 1;
  for (;;) {
    if (nn & bit) p = a68_mul_i(p, mm);
    bit <<= 1;
    if (bit <= nn) mm = a68_mul_i(mm, mm);
    if (!(bit <= nn)) break;
  }
  return p;
}
static inline double a68_pow_ri(double x, int64_t n) {
  uint64_t nn = n < 0 ? (uint64_t)(-(n + 1)) + 1 : (uint64_t) n;
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
    if (p != p || p > 1.7976931348623157e308 || p < -1.7976931348623157e308) return a68_die_r(2);
  }
  return n < 0 ? 1.0 / p : p;
}
static inline double a68_pow_rr(double x, double y) {
  if (y == 0.0) return 1.0;
  if (x < 0.0) return a68_die_r(7);
  if (x == 0.0) { if (y < 0.0) return a68_die_r(7); return 0.0; }
  return exp(y * log(x));
}
static inline double a68_m_acos(double x) { if (x < -1.0 || x > 1.0) return a68_die_r(3); return a68_chk_r(acos(x)); }
static inline double a68_m_arccos(double x) { if (x < -1.0 || x > 1.0) return a68_die_r(3); return a68_chk_r(acos(x)); }
static inline double a68_m_arccosh(double x) { return a68_chk_r(acosh(x)); }
static inline double a68_m_arcsin(double x) { if (x < -1.0 || x > 1.0) return a68_die_r(3); return a68_chk_r(asin(x)); }
static inline double a68_m_arcsinh(double x) { return a68_chk_r(asinh(x)); }
static inline double a68_m_arctan(double x) { return a68_chk_r(atan(x)); }
static inline double a68_m_arctanh(double x) { return a68_chk_r(atanh(x)); }
static inline double a68_m_asin(double x) { if (x < -1.0 || x > 1.0) return a68_die_r(3); return a68_chk_r(asin(x)); }
static inline double a68_m_atan(double x) { return a68_chk_r(atan(x)); }
static inline double a68_m_cbrt(double x) { return a68_chk_r(cbrt(x)); }
static inline double a68_m_cos(double x) { return a68_chk_r(cos(x)); }
static inline double a68_m_cosh(double x) { return a68_chk_r(cosh(x)); }
static inline double a68_m_curt(double x) { return a68_chk_r(cbrt(x)); }
static inline double a68_m_exp(double x) { return exp(x); }
static inline double a68_m_exp2(double x) { return exp2(x); }
static inline double a68_m_ln(double x) { if (x < 0.0) return a68_die_r(3); return a68_chk_r(log(x)); }
static inline double a68_m_log(double x) { if (x < 0.0) return a68_die_r(3); return a68_chk_r(log10(x)); }
static inline double a68_m_log10(double x) { if (x < 0.0) return a68_die_r(3); return a68_chk_r(log10(x)); }
static inline double a68_m_log2(double x) { return a68_chk_r(log2(x)); }
static inline double a68_m_sin(double x) { return a68_chk_r(sin(x)); }
static inline double a68_m_sinh(double x) { return a68_chk_r(sinh(x)); }
static inline double a68_m_sqrt(double x) { if (x < 0.0) return a68_die_r(3); return a68_chk_r(sqrt(x)); }
static inline double a68_m_tan(double x) { return a68_chk_r(tan(x)); }
static inline double a68_m_tanh(double x) { return a68_chk_r(tanh(x)); }
static inline int64_t a68_entier(double x) {
  if (x < -2147483647.0 || x > 2147483647.0) return a68_die_i(4);
  return (int64_t) __builtin_floor(x);
}
static inline int64_t a68_round(double x) {
  if (x < -2147483647.0 || x > 2147483647.0) return a68_die_i(4);
  double ax = x < 0 ? -x : x;
  int64_t n = (int64_t) __builtin_floor(ax + 0.5);
  return x < 0 ? -n : n;
}
static inline double a68_fabs(double x) { return x < 0 ? -x : x; }
static inline uint32_t a68_repr(int64_t x) {
  if (x < 0 || x > 255) { a68_v(a68rt_arith_error(6, W)); return 0; }
  return (uint32_t) x;
}

static const char* A68_BLOB =
  "m void\n"
  "s 3c\n"
  "m int 0\n"
  "s 3d\n"
  "m char\n"
  "m row 1 1 4\n"
  "s 414e44\n"
  "m bool\n"
  "s 4f52\n"
  "s \n"
  "s 616461\n"
  "s 627269616e\n"
  "s 6361726f6c\n"
  "s 64616e\n"
  "s 657665\n"
  "s 6672616e6b\n"
  "s 6772616365\n"
  "s 6865696469\n"
  "s 555042\n"
  "s 504552534f4e\n"
  "m named 19\n"
  "m row 1 0 20\n"
  "s 7072696e7466\n"
  "f dig 1\n"
  "f rep 2 0 23\n"
  "f sign 0\n"
  "f dig 0\n"
  "s 2e20\n"
  "f lit 27\n"
  "f gen 0\n"
  "f sep\n"
  "s 2061676520\n"
  "f lit 31\n"
  "k 10 24 25 26 28 29 30 32 24 25 26\n"
  "m format\n"
  "s 7072696e74\n"
  "s 6e65776c696e65\n"
  "m file\n"
  "m ref 37\n"
  "m proc 0 1 38\n"
  "s 6d65616e206167653a20\n"
  "f lit 40\n"
  "f point\n"
  "f nl\n"
  "k 9 41 24 25 26 42 26 26 30 43\n"
  "m real 0\n"
  "s 2f\n"
  "s 6e616d65\n"
  "s 616765\n"
  "m struct 2 47 5 48 2\n"
  "n 19 49\n"
;

static void a68_fn0(void);
static void a68_fn1(void);
static void a68_fn2(void);
static void* const a68_nf_of_fn[] = { NULL, NULL, NULL, NULL };

static void a68_fn0(void) {
  a68_v(a68rt_enter_args(0, 0, W));
  {
    int64_t p0_3 = 0;
    a68_v(a68rt_enter(4, W));
    a68_line(5);
    a68_v(a68rt_push_proc(1, 4, W));
    a68_v(a68rt_store(0, 1, W));
    a68_line(17);
    a68_v(a68rt_push_proc(2, 2, W));
    a68_v(a68rt_store(0, 2, W));
    a68_v(a68rt_push_str(9, W));
    a68_v(a68rt_push_undef(W));
    a68_v(a68rt_collateral(2, 1, 0, W));
    a68_v(a68rt_push_int(1LL, W));
    a68_v(a68rt_push_int(8LL, W));
    a68_v(a68rt_new_row(1, 0, W));
    a68_v(a68rt_store(0, 0, W));
    a68_line(3);
    a68_v(a68rt_push_ref(0, 0, W));
    a68_v(a68rt_push_str(10, W));
    a68_v(a68rt_push_int(36LL, W));
    a68_v(a68rt_collateral(2, 1, 0, W));
    a68_v(a68rt_push_str(11, W));
    a68_v(a68rt_push_int(29LL, W));
    a68_v(a68rt_collateral(2, 1, 0, W));
    a68_v(a68rt_push_str(12, W));
    a68_v(a68rt_push_int(52LL, W));
    a68_v(a68rt_collateral(2, 1, 0, W));
    a68_v(a68rt_push_str(13, W));
    a68_v(a68rt_push_int(41LL, W));
    a68_v(a68rt_collateral(2, 1, 0, W));
    a68_v(a68rt_push_str(14, W));
    a68_v(a68rt_push_int(29LL, W));
    a68_v(a68rt_collateral(2, 1, 0, W));
    a68_v(a68rt_push_str(15, W));
    a68_v(a68rt_push_int(63LL, W));
    a68_v(a68rt_collateral(2, 1, 0, W));
    a68_v(a68rt_push_str(16, W));
    a68_v(a68rt_push_int(45LL, W));
    a68_v(a68rt_collateral(2, 1, 0, W));
    a68_v(a68rt_push_str(17, W));
    a68_v(a68rt_push_int(33LL, W));
    a68_v(a68rt_collateral(2, 1, 0, W));
    a68_v(a68rt_collateral(8, 0, 1, W));
    a68_v(a68rt_assign(0, W));
    a68_v(a68rt_pop(W));
    a68_line(18);
    a68_v(a68rt_push_cell(0, 1, W));
    a68_v(a68rt_push_ref(0, 0, W));
    a68_v(a68rt_push_int(1LL, W));
    a68_v(a68rt_push_cell(0, 0, W));
    a68_v(a68rt_monop(18, 21, W));
    a68_v(a68rt_push_cell(0, 2, W));
    a68_v(a68rt_call(4, W));
    if (a68_jump()) return;
    a68_v(a68rt_pop(W));
    a68_line(20);
    p0_3 = 0LL;
    a68_line(21);
    int64_t from6 = 1LL;
    int64_t by6 = 1LL;
    a68_v(a68rt_push_cell(0, 0, W));
    a68_v(a68rt_monop(18, 21, W));
    int64_t to6 = a68_int(); int has6 = 1;
    for (int64_t i6 = from6; ; i6 += by6) {
      if (has6 && ((by6 > 0 && i6 > to6) || (by6 < 0 && i6 < to6))) break;
      a68_v(a68rt_enter(1, W));
      a68_v(a68rt_set_int(0, 0, i6, W));
      a68_line(22);
      a68_v(a68rt_push_builtin(22, W));
      a68_v(a68rt_push_format(33, W));
      a68_v(a68rt_unite(34, W));
      a68_v(a68rt_push_cell(0, 0, W));
      a68_v(a68rt_unite(2, W));
      a68_v(a68rt_sel_push(1, 0, 257u, a68_cell_i(0, 0), 0, 0u, W));
      a68_v(a68rt_unite(5, W));
      a68_v(a68rt_sel_push(1, 0, 257u, a68_cell_i(0, 0), 0, 1u, W));
      a68_v(a68rt_unite(2, W));
      a68_v(a68rt_collateral(4, 0, 1, W));
      a68_v(a68rt_call(1, W));
      if (a68_jump()) return;
      a68_v(a68rt_pop(W));
      a68_line(23);
      p0_3 = a68_add_i(p0_3, a68_sel_i(1, 0, 257u, a68_cell_i(0, 0), 0, 1u));
      a68_line(24);
      a68_v(a68rt_push_builtin(35, W));
      a68_v(a68rt_push_builtin(36, W));
      a68_v(a68rt_unite(39, W));
      a68_v(a68rt_row_of(W));
      a68_v(a68rt_call(1, W));
      if (a68_jump()) return;
      a68_v(a68rt_pop(W));
      a68_v(a68rt_leave(W));
    }
    a68_line(26);
    a68_v(a68rt_push_builtin(22, W));
    a68_v(a68rt_push_format(44, W));
    a68_v(a68rt_unite(34, W));
    a68_v(a68rt_push_real(((double)(p0_3)), W));
    a68_v(a68rt_push_cell(0, 0, W));
    a68_v(a68rt_monop(18, 21, W));
    a68_v(a68rt_widen(2, 45, W));
    a68_v(a68rt_dyop(46, 45, 45, W));
    a68_v(a68rt_unite(45, W));
    a68_v(a68rt_collateral(2, 0, 1, W));
    a68_v(a68rt_call(1, W));
    if (a68_jump()) return;
    B0: a68_v(a68rt_leave(W));
  }
  a68_v(a68rt_leave(W));
}

static void a68_fn1(void) {
  a68_v(a68rt_enter_args(4, 4, W));
  void* a68_pc3 = (void*) 1;
  if ((uint8_t)((a68_cell_i(0, 1)) < (a68_cell_i(0, 2)))) {
    {
      int64_t p1_1 = 0;
      int64_t p1_2 = 0;
      a68_v(a68rt_enter(3, W));
      a68_line(7);
      a68_v(a68rt_push_cell(1, 0, W));
      a68_v(a68rt_push_int(a68_over_i(a68_add_i(a68_cell_i(1, 1), a68_cell_i(1, 2)), 2LL), W));
      a68_v(a68rt_slice(1, 0ULL, 1, W));
      a68_v(a68rt_deref(W));
      a68_v(a68rt_store(0, 0, W));
      a68_line(8);
      p1_1 = a68_cell_i(1, 1);
      a68_line(8);
      p1_2 = a68_cell_i(1, 2);
      a68_line(9);
      int64_t from2 = 1LL;
      int64_t by2 = 1LL;
      int64_t to2 = 0; int has2 = 0;
      for (int64_t i2 = from2; ; i2 += by2) {
        if (has2 && ((by2 > 0 && i2 > to2) || (by2 < 0 && i2 < to2))) break;
        uint8_t cnd2 = 0;
        if ((uint8_t)((p1_1) <= (p1_2))) {
          a68_line(10);
          int64_t from3 = 1LL;
          int64_t by3 = 1LL;
          int64_t to3 = 0; int has3 = 0;
          for (int64_t i3 = from3; ; i3 += by3) {
            if (has3 && ((by3 > 0 && i3 > to3) || (by3 < 0 && i3 < to3))) break;
            uint8_t cnd3 = 0;
            a68_line(10);
            a68_v(a68rt_push_cell(1, 3, W));
            a68_v(a68rt_push_cell(1, 0, W));
            a68_v(a68rt_push_int(p1_1, W));
            a68_v(a68rt_slice(1, 0ULL, 1, W));
            a68_v(a68rt_deref(W));
            a68_v(a68rt_push_cell(0, 0, W));
            a68_v(a68rt_call(2, W));
            if (a68_jump()) return;
            if (a68_bool()) {
              a68_line(10);
              p1_1 = a68_add_i(p1_1, 1LL);
              cnd3 = 1;
            } else {
              cnd3 = 0;
            }
            if (!cnd3) { break; }
          }
          a68_line(11);
          int64_t from4 = 1LL;
          int64_t by4 = 1LL;
          int64_t to4 = 0; int has4 = 0;
          for (int64_t i4 = from4; ; i4 += by4) {
            if (has4 && ((by4 > 0 && i4 > to4) || (by4 < 0 && i4 < to4))) break;
            uint8_t cnd4 = 0;
            a68_line(11);
            a68_v(a68rt_push_cell(1, 3, W));
            a68_v(a68rt_push_cell(0, 0, W));
            a68_v(a68rt_push_cell(1, 0, W));
            a68_v(a68rt_push_int(p1_2, W));
            a68_v(a68rt_slice(1, 0ULL, 1, W));
            a68_v(a68rt_deref(W));
            a68_v(a68rt_call(2, W));
            if (a68_jump()) return;
            if (a68_bool()) {
              a68_line(11);
              p1_2 = a68_sub_i(p1_2, 1LL);
              cnd4 = 1;
            } else {
              cnd4 = 0;
            }
            if (!cnd4) { break; }
          }
          a68_line(12);
          if ((uint8_t)((p1_1) <= (p1_2))) {
            {
              a68_v(a68rt_enter(1, W));
              a68_line(12);
              a68_v(a68rt_push_cell(2, 0, W));
              a68_v(a68rt_push_int(p1_1, W));
              a68_v(a68rt_slice(1, 0ULL, 1, W));
              a68_v(a68rt_deref(W));
              a68_v(a68rt_store(0, 0, W));
              a68_line(12);
              a68_v(a68rt_push_cell(2, 0, W));
              a68_v(a68rt_push_int(p1_1, W));
              a68_v(a68rt_slice(1, 0ULL, 1, W));
              a68_v(a68rt_push_cell(2, 0, W));
              a68_v(a68rt_push_int(p1_2, W));
              a68_v(a68rt_slice(1, 0ULL, 1, W));
              a68_v(a68rt_deref(W));
              a68_v(a68rt_assign(0, W));
              a68_v(a68rt_pop(W));
              a68_line(12);
              a68_v(a68rt_push_cell(2, 0, W));
              a68_v(a68rt_push_int(p1_2, W));
              a68_v(a68rt_slice(1, 0ULL, 1, W));
              a68_v(a68rt_push_cell(0, 0, W));
              a68_v(a68rt_assign(0, W));
              a68_v(a68rt_pop(W));
              a68_line(12);
              p1_1 = a68_add_i(p1_1, 1LL);
              a68_line(12);
              p1_2 = a68_sub_i(p1_2, 1LL);
              B5: a68_v(a68rt_leave(W));
            }
          } else {
          }
          cnd2 = 1;
        } else {
          cnd2 = 0;
        }
        if (!cnd2) { break; }
      }
      a68_line(14);
      a68_v(a68rt_push_cell(2, 1, W));
      a68_v(a68rt_push_cell(1, 0, W));
      a68_v(a68rt_push_cell(1, 1, W));
      a68_v(a68rt_push_int(p1_2, W));
      a68_v(a68rt_push_cell(1, 3, W));
      a68_v(a68rt_call(4, W));
      if (a68_jump()) return;
      a68_v(a68rt_pop(W));
      a68_line(14);
      a68_v(a68rt_push_cell(2, 1, W));
      a68_v(a68rt_push_cell(1, 0, W));
      a68_v(a68rt_push_int(p1_1, W));
      a68_v(a68rt_push_cell(1, 2, W));
      a68_v(a68rt_push_cell(1, 3, W));
      a68_v(a68rt_call(4, W));
      if (a68_jump()) return;
      B1: a68_v(a68rt_leave(W));
    }
  } else {
    a68_v(a68rt_push_skip(0, W));
  }
  a68_v(a68rt_leave(W));
}

static void a68_fn2(void) {
  uint32_t a68_hm = a68_u32(a68rt_heap_mark(W));
  a68_v(a68rt_enter_args(2, 2, W));
  a68_v(a68rt_push_cell(0, 0, W));
  a68_v(a68rt_select(1, 0, W));
  a68_v(a68rt_push_cell(0, 1, W));
  a68_v(a68rt_select(1, 0, W));
  a68_v(a68rt_dyop(1, 2, 2, W));
  a68_line(17);
  a68_v(a68rt_push_cell(0, 0, W));
  a68_v(a68rt_select(1, 0, W));
  a68_v(a68rt_push_cell(0, 1, W));
  a68_v(a68rt_select(1, 0, W));
  a68_v(a68rt_dyop(3, 2, 2, W));
  a68_v(a68rt_push_cell(0, 0, W));
  a68_v(a68rt_select(0, 0, W));
  a68_v(a68rt_push_cell(0, 1, W));
  a68_v(a68rt_select(0, 0, W));
  a68_v(a68rt_dyop(1, 5, 5, W));
  a68_v(a68rt_dyop(6, 7, 7, W));
  a68_v(a68rt_dyop(8, 7, 7, W));
  a68_v(a68rt_leave(W));
  a68_v(a68rt_heap_release(a68_hm, W));
}

void a68_dispatch_proc(size_t fn) {
  switch (fn) {
    case 0: a68_fn0(); break;
    case 1: a68_fn1(); break;
    case 2: a68_fn2(); break;
    default: break;
  }
}

void a68_dispatch_hole(size_t idx) {
  switch (idx) {
    default: break;
  }
}

int main(int argc, char** argv) {
  a68rt_boot(A68_BLOB, 12, 0, argc, argv, "quicksort.a68");
  a68_fn0();
  uint32_t rc = a68rt_finish(W);
  return (int) rc;
}
