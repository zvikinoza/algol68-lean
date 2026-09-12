/* The operators of the standard prelude and the coercions, in full: `Interp.dyadic`,
   `Interp.monadic`, `Interp.widenValue`, `Interp.defaultOf` and the conformity test of
   `Runtime.conform`.  rt.c answers the common cases of the primitive modes itself and
   comes here for everything else, so this is the reference path; each arm transcribes
   the arm of the same shape in A68/Interp.lean. */
#include "io.h"
#include "tables.h"
#include "fmt.h"
#include "bigint.h"
#include "os.h"
#include "mp.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define A68_MAXINT 2147483647LL

static int eq(const char* a, const char* b) { return strcmp(a, b) == 0; }

static const a68_mode* rm(uint32_t m) { return mode_at(mode_resolve(m)); }

__attribute__((noreturn)) static void die_m(const char* pre, uint32_t m, const char* post) {
  char* ms = mode_string(m);
  size_t n = strlen(pre) + strlen(ms) + strlen(post) + 1;
  char* b = (char*) xmalloc(n);
  snprintf(b, n, "%s%s%s", pre, ms, post);
  free(ms);
  die(b);
}

__attribute__((noreturn)) static void die_m2(const char* pre, const char* op, uint32_t m1, uint32_t m2) {
  char* s1 = mode_string(m1); char* s2 = mode_string(m2);
  size_t n = strlen(pre) + strlen(op) + strlen(s1) + strlen(s2) + 16;
  char* b = (char*) xmalloc(n);
  snprintf(b, n, "%s%s on %s and %s", pre, op, s1, s2);
  free(s1); free(s2);
  die(b);
}

/* ---------------------------------------------------------------- integers of any length */

static a68_big* big_of(a68_val v) {
  switch (v.tag) {
    case T_INT: return big_from_i64(v.v.i);
    case T_BIGINT: case T_BIGBITS: { a68_leaf* l = (a68_leaf*) v.v.p; return big_from_dec((const char*) l->d, l->h.n); }
    case T_BITS: {
      char t[32]; snprintf(t, sizeof t, "%llu", (unsigned long long) v.v.u);
      return big_from_dec(t, strlen(t));
    }
    case T_UNDEF: die("attempt to use an uninitialised INT value");
    default: die("internal: INT expected");
  }
}

static a68_val val_of_big(const a68_big* b) {
  if (big_fits_i64(b)) return mk_int(big_to_i64(b));
  char* s = big_to_dec(b);
  size_t n = strlen(s);
  a68_leaf* l = leaf_alloc(EK_BYTES, (uint32_t) n);
  memcpy(l->d, s, n);
  free(s);
  return mk_ptr(T_BIGINT, (a68_obj*) l, 0);
}

/* Numfmt.maxIntOf, fresh */
static a68_big* max_int_of(int64_t longness) {
  if (longness <= 0) return big_from_i64(A68_MAXINT);
  a68_big* p = big_pow10(longness == 1 ? 49 : a68_ll_digits * 7);
  a68_big* one = big_from_i64(1);
  a68_big* r = big_sub(p, one);
  big_free(p); big_free(one);
  return r;
}

static int over_limit(const a68_big* r, int64_t longness) {
  a68_big* lim = max_int_of(longness);
  a68_big* ar = big_abs(r);
  int over = big_cmp(ar, lim) > 0;
  big_free(lim); big_free(ar);
  return over;
}

/* `Interp.checkIntRange` on a plain INT */
static int64_t int_range(int64_t r, int64_t longness) {
  if (longness <= 0) { if (r > A68_MAXINT || r < -A68_MAXINT) die("INT value overflow, result too large"); return r; }
  a68_big* b = big_from_i64(r);
  int over = over_limit(b, longness);
  big_free(b);
  if (over) die_m("", mode_simple(M_INT, longness), " value overflow, result too large");
  return r;
}

static int64_t expect_int(a68_val v) { return as_int(v); }

/* `Interp.longIntDyadic`: exact integer operations, range-checked (see the Lean for why) */
static a68_val long_int_dyadic(const char* op, int64_t n, a68_val a, a68_val b) {
  a68_big* x = big_of(a); a68_big* y = big_of(b);
  a68_val res;
  if (eq(op, "+") || eq(op, "-") || eq(op, "*")) {
    a68_big* r = eq(op, "+") ? big_add(x, y) : eq(op, "-") ? big_sub(x, y) : big_mul(x, y);
    if (over_limit(r, n)) { big_free(r); big_free(x); big_free(y); die_m("", mode_simple(M_INT, n), " value out of bounds"); }
    res = val_of_big(r);
    big_free(r);
  } else if (eq(op, "%")) {
    if (big_is_zero(y)) { big_free(x); big_free(y); die_m("", mode_simple(M_INT, n), " division by zero"); }
    a68_big* rem; a68_big* q = big_divmod(x, y, &rem);
    res = val_of_big(q);
    big_free(q); big_free(rem);
  } else if (eq(op, "%*")) {
    if (big_is_zero(y)) { big_free(x); big_free(y); die_m("", mode_simple(M_INT, n), " value is not a number"); }
    /* `Int.emod x |y|`: the non-negative remainder */
    a68_big* ay = big_abs(y);
    a68_big* rem; a68_big* q = big_divmod(x, ay, &rem);
    if (big_sign(rem) < 0) { a68_big* t = big_add(rem, ay); big_free(rem); rem = t; }
    res = val_of_big(rem);
    big_free(q); big_free(rem); big_free(ay);
  } else if (eq(op, "=") || eq(op, "/=") || eq(op, "<") || eq(op, "<=") || eq(op, ">") || eq(op, ">=")) {
    int c = big_cmp(x, y);
    int r = eq(op, "=") ? c == 0 : eq(op, "/=") ? c != 0 : eq(op, "<") ? c < 0 : eq(op, "<=") ? c <= 0 : eq(op, ">") ? c > 0 : c >= 0;
    res = mk_bool(r);
  } else {
    big_free(x); big_free(y);
    char buf[128]; char* ms = mode_string(mode_simple(M_INT, n));
    snprintf(buf, sizeof buf, "internal: %s operator %s", ms, op); free(ms);
    die(buf);
  }
  big_free(x); big_free(y);
  return res;
}

/* `Interp.longIntPow` */
static a68_val long_int_pow(int64_t n, a68_val a, int64_t k) {
  a68_big* x = big_of(a);
  a68_big* lim = max_int_of(n);
  if (k < 0) {
    a68_big* one = big_from_i64(1); a68_big* mone = big_from_i64(-1);
    int is1 = big_cmp(x, one) == 0, ism1 = big_cmp(x, mone) == 0;
    big_free(one); big_free(mone); big_free(x); big_free(lim);
    if (is1) return mk_int(1);
    if (ism1) return mk_int(k % 2 == 0 ? 1 : -1);
    die_m("", mode_simple(M_INT, n), " value out of bounds");
  }
  a68_big* ax = big_abs(x);
  a68_big* r = big_from_i64(1);
  a68_big* one = big_from_i64(1);
  for (int64_t i = 0; i < k; i++) {
    a68_big* t = big_mul(r, ax); big_free(r); r = t;
    if (big_cmp(r, lim) > 0) { big_free(r); big_free(ax); big_free(x); big_free(lim); big_free(one); die_m("", mode_simple(M_INT, n), " value out of bounds"); }
    if (big_cmp(ax, one) <= 0) break;
  }
  if (big_sign(x) < 0 && k % 2 == 1) { a68_big* t = big_neg(r); big_free(r); r = t; }
  a68_val res = val_of_big(r);
  big_free(r); big_free(ax); big_free(x); big_free(lim); big_free(one);
  return res;
}

/* ---------------------------------------------------------------- bits of any width */

/* a68g's LONG BITS are up to 279 bits wide at the default precision: 10 limbs suffice */
#define WB 12
typedef struct { uint32_t l[WB]; } wbits;

static int bits_width_of(int64_t longness) { return a68_fmt_bits_width(longness, a68_ll_digits); }

static wbits wb_of_big(const a68_big* b) {
  wbits w; memset(&w, 0, sizeof w);
  a68_big* z = big_abs(b);
  a68_big* base = big_from_i64(4294967296LL);
  for (int i = 0; i < WB && !big_is_zero(z); i++) {
    a68_big* rem; a68_big* q = big_divmod(z, base, &rem);
    w.l[i] = (uint32_t) big_to_i64(rem);
    big_free(rem); big_free(z); z = q;
  }
  big_free(z); big_free(base);
  return w;
}

static wbits wb_of_val(a68_val v) {
  if (v.tag == T_BITS) { wbits w; memset(&w, 0, sizeof w); w.l[0] = (uint32_t) v.v.u; w.l[1] = (uint32_t) (v.v.u >> 32); return w; }
  if (v.tag == T_UNDEF) die("attempt to use an uninitialised BITS value");
  if (v.tag != T_BIGBITS) die("internal: BITS expected");
  a68_big* b = big_of(v);
  wbits w = wb_of_big(b);
  big_free(b);
  return w;
}

static a68_big* big_of_wb(const wbits* w) {
  a68_big* r = big_from_i64(0);
  a68_big* base = big_from_i64(4294967296LL);
  for (int i = WB - 1; i >= 0; i--) {
    a68_big* t = big_mul(r, base);
    a68_big* d = big_from_i64((int64_t) w->l[i]);
    a68_big* u = big_add(t, d);
    big_free(r); big_free(t); big_free(d);
    r = u;
  }
  big_free(base);
  return r;
}

static a68_val val_of_wb(const wbits* w) {
  int high = 0;
  for (int i = 2; i < WB; i++) if (w->l[i]) high = 1;
  if (!high) return mk_bits((uint64_t) w->l[0] | ((uint64_t) w->l[1] << 32));
  a68_big* b = big_of_wb(w);
  char* s = big_to_dec(b);
  size_t n = strlen(s);
  a68_leaf* l = leaf_alloc(EK_BYTES, (uint32_t) n);
  memcpy(l->d, s, n);
  free(s); big_free(b);
  return mk_ptr(T_BIGBITS, (a68_obj*) l, 0);
}

static wbits wb_mask(int width) {
  wbits w; memset(&w, 0, sizeof w);
  for (int i = 0; i < width && i / 32 < WB; i++) w.l[i / 32] |= 1u << (i % 32);
  return w;
}

static int wb_bit(const wbits* w, int i) { return i / 32 < WB ? (w->l[i / 32] >> (i % 32)) & 1 : 0; }
static wbits wb_and(wbits a, wbits b) { for (int i = 0; i < WB; i++) a.l[i] &= b.l[i]; return a; }
static wbits wb_or(wbits a, wbits b) { for (int i = 0; i < WB; i++) a.l[i] |= b.l[i]; return a; }
static wbits wb_xor(wbits a, wbits b) { for (int i = 0; i < WB; i++) a.l[i] ^= b.l[i]; return a; }
static int wb_eq(wbits a, wbits b) { return memcmp(&a, &b, sizeof a) == 0; }
static wbits wb_shl(wbits a, int s) {
  wbits r; memset(&r, 0, sizeof r);
  for (int i = 0; i < WB * 32; i++) if (wb_bit(&a, i) && i + s < WB * 32 && i + s >= 0) r.l[(i + s) / 32] |= 1u << ((i + s) % 32);
  return r;
}
/* `v > mask`, the range test of BIN */
static int wb_exceeds(wbits v, int width) {
  for (int i = width; i < WB * 32; i++) if (wb_bit(&v, i)) return 1;
  return 0;
}

/* ---------------------------------------------------------------- reals and complex numbers */

static double real_check(double x) {
  if (x != x) die("REAL value is not a number");
  if (isinf(x)) die("infinite REAL value");
  return x;
}

static a68_val mk_compl(double re, double im) {
  a68_slots* c = slots_alloc(2);
  c->s[0] = mk_real(re);
  c->s[1] = mk_real(im);
  return mk_ptr(T_STRUCT, (a68_obj*) c, 0);
}

/* a68g's CHECK_COMPLEX: the real part is tested, then the imaginary part */
static a68_val check_compl(double re, double im) {
  double parts[2] = { re, im };
  for (int k = 0; k < 2; k++) {
    if (parts[k] != parts[k]) die("COMPL value is not a number");
    if (isinf(parts[k])) die("infinite COMPL value");
  }
  return mk_compl(re, im);
}

static a68_val compl_bin(uint8_t which, double ar, double ai, double br, double bi) {
  return check_compl(a68_compl_op(which, 0, ar, ai, br, bi), a68_compl_op(which, 1, ar, ai, br, bi));
}

static int compl_reals(a68_val v, double* re, double* im) {
  if (v.tag != T_STRUCT) return 0;
  a68_slots* s = (a68_slots*) v.v.p;
  if (s->h.n != 2 || s->s[0].tag != T_REAL || s->s[1].tag != T_REAL) return 0;
  *re = s->s[0].v.r; *im = s->s[1].v.r;
  return 1;
}

static int compl_mps(a68_val v, a68_val* re, a68_val* im) {
  if (v.tag != T_STRUCT) return 0;
  a68_slots* s = (a68_slots*) v.v.p;
  if (s->h.n != 2 || s->s[0].tag != T_MP || s->s[1].tag != T_MP) return 0;
  *re = s->s[0]; *im = s->s[1];
  return 1;
}

static a68_val struct2(a68_val a, a68_val b) {
  a68_slots* s = slots_alloc(2);
  s->s[0] = a; s->s[1] = b;
  return mk_ptr(T_STRUCT, (a68_obj*) s, 0);
}

/* `Interp.powIntInt` */
static int64_t pow_int(int64_t m, int64_t n, int64_t longness) {
  if (n < 0) die("invalid INT exponent");
  if (m == 0 && n == 0) return 1;
  if (m == 0 || m == 1) return m;
  if (m == -1) return (n % 2 == 0) ? 1 : -1;
  uint64_t nn = (uint64_t) n, bit = 1;
  int64_t mm = m, p = 1;
  for (;;) {
    if (nn & bit) p = int_range(p * mm, longness);
    bit <<= 1;
    if (bit <= nn) mm = int_range(mm * mm, longness);
    if (!(bit <= nn)) break;
  }
  return p;
}

/* `Interp.powRealInt` */
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

/* ---------------------------------------------------------------- rows */

static a68_rowd* row_of(a68_val v) {
  if (v.tag == T_UNDEF) die("attempt to use an uninitialised row");
  if (v.tag != T_ROW) die("internal: row expected");
  return (a68_rowd*) v.v.p;
}

/* every element of a row of CHAR, checked exactly as `strOf` checks it */
static void check_chars(a68_rowd* d) {
  int64_t n = row_count(d);
  for (int64_t i = 0; i < n; i++) {
    a68_val e = rowd_get(d, row_store_index(d, i));
    if (e.tag == T_UNDEF) die("attempt to use an uninitialised CHAR value");
    if (e.tag != T_CHAR) die("internal: [] CHAR expected");
  }
}

/* `Interp.compareChars` */
static int compare_chars(a68_val a, a68_val b) {
  a68_rowd* x = row_of(a); a68_rowd* y = row_of(b);
  check_chars(x); check_chars(y);
  int64_t nx = row_count(x), ny = row_count(y);
  int64_t n = nx < ny ? nx : ny;
  for (int64_t i = 0; i < n; i++) {
    uint32_t cx = (uint32_t) rowd_get(x, row_store_index(x, i)).v.u, cy = (uint32_t) rowd_get(y, row_store_index(y, i)).v.u;
    if (cx < cy) return -1;
    if (cx > cy) return 1;
  }
  return nx < ny ? -1 : nx > ny ? 1 : 0;
}

static int cmp_result(const char* op, int c, const char* what) {
  if (eq(op, "=")) return c == 0;
  if (eq(op, "/=")) return c != 0;
  if (eq(op, "<")) return c < 0;
  if (eq(op, "<=")) return c <= 0;
  if (eq(op, ">")) return c > 0;
  if (eq(op, ">=")) return c >= 0;
  char buf[96]; snprintf(buf, sizeof buf, "internal: %s operator %s", what, op); die(buf);
}

/* the elements of a row, in order, into a fresh array */
static a68_val* row_elems(a68_rowd* d, int64_t* n) {
  *n = row_count(d);
  a68_val* es = (a68_val*) xmalloc((size_t) (*n ? *n : 1) * sizeof(a68_val));
  for (int64_t i = 0; i < *n; i++) es[i] = rowd_get(d, row_store_index(d, i));
  return es;
}

static a68_val row_of_elems(const a68_val* es, int64_t n) { return row_of_values(es, n); }

/* xs ++ ys as a row from 1 */
static a68_val row_concat(a68_val a, a68_val b) {
  int64_t nx, ny;
  a68_val* xs = row_elems(row_of(a), &nx);
  a68_val* ys = row_elems(row_of(b), &ny);
  a68_val* zs = (a68_val*) xmalloc((size_t) (nx + ny ? nx + ny : 1) * sizeof(a68_val));
  memcpy(zs, xs, (size_t) nx * sizeof(a68_val));
  memcpy(zs + nx, ys, (size_t) ny * sizeof(a68_val));
  a68_val r = row_of_elems(zs, nx + ny);
  free(xs); free(ys); free(zs);
  return r;
}

/* xs repeated k times */
static a68_val row_repeat(a68_val a, int64_t k) {
  int64_t nx;
  a68_val* xs = row_elems(row_of(a), &nx);
  int64_t n = k > 0 ? k : 0;
  a68_val* zs = (a68_val*) xmalloc((size_t) (nx * n ? nx * n : 1) * sizeof(a68_val));
  for (int64_t i = 0; i < n; i++) memcpy(zs + i * nx, xs, (size_t) nx * sizeof(a68_val));
  a68_val r = row_of_elems(zs, nx * n);
  free(xs); free(zs);
  return r;
}

/* `Interp.valuesEqual` */
static int values_equal(a68_val a, a68_val b) {
  if (a.tag == T_INT && b.tag == T_INT) return a.v.i == b.v.i;
  if (a.tag == T_REAL && b.tag == T_REAL) return a.v.r == b.v.r;
  if (a.tag == T_MP && b.tag == T_MP) {
    a68_leaf* x = (a68_leaf*) a.v.p; a68_leaf* y = (a68_leaf*) b.v.p;
    return x->h.n == y->h.n && memcmp(x->d, y->d, x->h.n) == 0;
  }
  if ((a.tag == T_BIGINT && b.tag == T_BIGINT) || (a.tag == T_BIGBITS && b.tag == T_BIGBITS)) {
    a68_leaf* x = (a68_leaf*) a.v.p; a68_leaf* y = (a68_leaf*) b.v.p;
    return x->h.n == y->h.n && memcmp(x->d, y->d, x->h.n) == 0;
  }
  if (a.tag == T_INT && b.tag == T_REAL) return (double) a.v.i == b.v.r;
  if (a.tag == T_REAL && b.tag == T_INT) return a.v.r == (double) b.v.i;
  if (a.tag == T_BOOL && b.tag == T_BOOL) return a.v.u == b.v.u;
  if (a.tag == T_CHAR && b.tag == T_CHAR) return a.v.u == b.v.u;
  if (a.tag == T_BITS && b.tag == T_BITS) return a.v.u == b.v.u;
  if (a.tag == T_ROW && b.tag == T_ROW) {
    a68_rowd* x = (a68_rowd*) a.v.p; a68_rowd* y = (a68_rowd*) b.v.p;
    int64_t n = row_count(x);
    if (n != row_count(y)) return 0;
    for (int64_t i = 0; i < n; i++)
      if (!values_equal(rowd_get(x, row_store_index(x, i)), rowd_get(y, row_store_index(y, i)))) return 0;
    return 1;
  }
  if (a.tag == T_STRUCT && b.tag == T_STRUCT) {
    a68_slots* x = (a68_slots*) a.v.p; a68_slots* y = (a68_slots*) b.v.p;
    if (x->h.n != y->h.n) return 0;
    for (uint32_t i = 0; i < x->h.n; i++) if (!values_equal(x->s[i], y->s[i])) return 0;
    return 1;
  }
  if (a.tag == T_UNION && b.tag == T_UNION) return values_equal(((a68_slots*) a.v.p)->s[0], ((a68_slots*) b.v.p)->s[0]);
  return 0;
}

/* ---------------------------------------------------------------- multi-precision helpers */

static a68_val mp_pow_int_val(a68_val x, int64_t k, int64_t longness) {
  int digs = mp_digits_of(longness);
  a68_mp xv = mp_view(x);
  a68_mp z = mp_nil(digs);
  mp_move(&z, &xv, xv.digs < digs ? xv.digs : digs);
  char err[MP_ERR_LEN];
  if (mp_pow_int(&z, &z, k, digs, err)) die(err);
  a68_val r = mp_leaf(&z);
  mp_free(&z);
  return r;
}

/* `MP.toInt32 (intToMP x longDigits) longDigits`: SHORTEN of a LONG INT */
static int64_t shorten_long_int(a68_val v) {
  char err[MP_ERR_LEN];
  a68_big* b = big_of(v);
  char* s = big_to_dec(b);
  a68_mp z;
  if (mp_of_dec_string(s, strlen(s), MP_LONG_DIGITS, &z, err)) { free(s); big_free(b); die(err); }
  free(s); big_free(b);
  int32_t r;
  if (mp_to_int32(&z, MP_LONG_DIGITS, &r, err)) { mp_free(&z); die(err); }
  mp_free(&z);
  return r;
}

/* ---------------------------------------------------------------- dyadic operators */

static a68_val assigning(const char* op, uint32_t m1, a68_val a, a68_val b);

a68_val ops_dyadic(const char* op, uint32_t m1, uint32_t m2, a68_val a, a68_val b) {
  const a68_mode* p1 = rm(m1);
  const a68_mode* p2 = rm(m2);
  if (p1->k == M_REF) return assigning(op, m1, a, b);
  if (mode_is_string(mode_resolve(m1)) && p2->k == M_REF) {
    /* "+=:"  value PLUSTO ref */
    a68_val cur = ref_load_checked(b);
    a68_val res = row_concat(a, cur);
    store_ref(b, res);
    return b;
  }
  int64_t n1 = p1->len;
  switch (p1->k) {
    case M_INT:
      if (p2->k == M_INT) {
        if (n1 >= 1) {
          if (eq(op, "**")) return long_int_pow(n1, a, expect_int(b));
          return long_int_dyadic(op, n1, a, b);
        }
        int64_t x = expect_int(a), y = expect_int(b);
        if (eq(op, "+")) return mk_int(int_range(x + y, n1));
        if (eq(op, "-")) return mk_int(int_range(x - y, n1));
        if (eq(op, "*")) return mk_int(int_range(x * y, n1));
        if (eq(op, "%")) { if (y == 0) die("INT division by zero"); return mk_int(x / y); }
        if (eq(op, "%*")) { if (y == 0) die("INT division by zero"); int64_t m = y < 0 ? -y : y; int64_t r = x % m; return mk_int(r < 0 ? r + m : r); }
        if (eq(op, "**")) return mk_int(pow_int(x, y, n1));
        return mk_bool(cmp_result(op, x < y ? -1 : x > y ? 1 : 0, "INT"));
      }
      if (mode_is_string(mode_resolve(m2))) {
        int64_t k = expect_int(a);
        a68_rowd* d = row_of(b);
        /* `k UPB s` on a STRING is a bounds enquiry, not the replication `k * s` */
        if (eq(op, "LWB") || eq(op, "UPB")) {
          if (k < 1 || k > (int64_t) d->h.n) die("LWB/UPB dimension out of range");
          return mk_int(eq(op, "LWB") ? d->dim[k - 1].l : d->dim[k - 1].u);
        }
        return row_repeat(b, k);
      }
      if (p2->k == M_BITS) {
        int64_t k = expect_int(a);
        wbits x = wb_of_val(b);
        int w = bits_width_of(p2->len);
        if (eq(op, "ELEM")) {
          if (k < 1 || k > w) die("ELEM index out of range");
          return mk_bool(wb_bit(&x, w - (int) k));
        }
        char buf[64]; snprintf(buf, sizeof buf, "internal: INT/BITS operator %s", op); die(buf);
      }
      if (p2->k == M_BYTES) {
        int64_t k = expect_int(a);
        a68_rowd* d = row_of(b);
        int64_t n = row_count(d);
        if (k < 1 || k > n) dief("index %lld out of bounds [1:%lld]", k, n, 0);
        return rowd_get(d, row_store_index(d, k - 1));
      }
      if (p2->k == M_ROW) {
        int64_t k = expect_int(a);
        a68_rowd* d = row_of(b);
        if (k < 1 || k > (int64_t) d->h.n) die("LWB/UPB dimension out of range");
        if (eq(op, "LWB")) return mk_int(d->dim[k - 1].l);
        if (eq(op, "UPB")) return mk_int(d->dim[k - 1].u);
        char buf[64]; snprintf(buf, sizeof buf, "internal: INT/row operator %s", op); die(buf);
      }
      break;
    case M_REAL:
      if (p2->k == M_REAL) {
        if (n1 >= 1) {
          if (eq(op, "I")) return struct2(a, b);
          if (a.tag != T_MP) { if (a.tag == T_UNDEF) die("attempt to use an uninitialised LONG REAL value"); die("internal: LONG REAL expected"); }
          if (b.tag != T_MP) { if (b.tag == T_UNDEF) die("attempt to use an uninitialised LONG REAL value"); die("internal: LONG REAL expected"); }
          return mp_dyadic(op, n1, a, b);
        }
        double x = as_real(a), y = as_real(b);
        if (eq(op, "+")) return mk_real(real_check(x + y));
        if (eq(op, "-")) return mk_real(real_check(x - y));
        if (eq(op, "*")) return mk_real(real_check(x * y));
        /* a68g checks the divisor but not the quotient */
        if (eq(op, "/")) { if (y == 0.0) die("REAL value is not a number"); return mk_real(x / y); }
        if (eq(op, "I")) return mk_compl(x, y);
        if (eq(op, "**")) {
          if (y == 0.0) return mk_real(1.0);
          if (x < 0.0) die("REAL math error");
          if (x == 0.0) { if (y < 0.0) die("REAL math error"); return mk_real(0.0); }
          return mk_real(exp(y * log(x)));   /* a68g: exp overflow is not checked here */
        }
        return mk_bool(cmp_result(op, x < y ? -1 : x > y ? 1 : 0, "REAL"));
      }
      if (p2->k == M_INT) {
        if (n1 >= 1) {
          if (a.tag != T_MP) { if (a.tag == T_UNDEF) die("attempt to use an uninitialised LONG REAL value"); die("internal: LONG REAL expected"); }
          int64_t k = expect_int(b);
          if (eq(op, "**")) return mp_pow_int_val(a, k, n1);
          char buf[96]; char* ms = mode_string(mode_simple(M_REAL, n1));
          snprintf(buf, sizeof buf, "internal: %s/INT operator %s", ms, op); free(ms); die(buf);
        }
        double x = as_real(a);
        int64_t y = expect_int(b);
        if (eq(op, "**")) return mk_real(pow_real_int(x, y));
        if (eq(op, "I")) return mk_compl(x, (double) y);
        char buf[64]; snprintf(buf, sizeof buf, "internal: REAL/INT operator %s (%lld)", op, (long long) n1); die(buf);
      }
      break;
    case M_COMPL:
      if (p2->k == M_INT) {
        if (n1 >= 1) return mp_compl_pow(n1, a, expect_int(b));
        double re, im;
        if (!compl_reals(a, &re, &im)) die("internal: COMPL expected");
        int64_t y = expect_int(b);
        /* a68g's square-and-multiply; a negative exponent then divides 1 by the power */
        uint64_t nn = y < 0 ? (uint64_t) (-(y + 1)) + 1 : (uint64_t) y;
        a68_val z = check_compl(a68_compl_pow(0, re, im, nn), a68_compl_pow(1, re, im, nn));
        if (y < 0) { double zr, zi; compl_reals(z, &zr, &zi); return compl_bin(1, 1.0, 0.0, zr, zi); }
        return z;
      }
      if (p2->k == M_COMPL) {
        if (n1 >= 1) return mp_compl_dyadic(op, n1, a, b);
        double ar, ai, br, bi;
        if (!compl_reals(a, &ar, &ai) || !compl_reals(b, &br, &bi)) die("internal: COMPL expected");
        if (eq(op, "+")) return check_compl(ar + br, ai + bi);
        if (eq(op, "-")) return check_compl(ar - br, ai - bi);
        if (eq(op, "*")) return compl_bin(0, ar, ai, br, bi);
        if (eq(op, "/")) return compl_bin(1, ar, ai, br, bi);
        if (eq(op, "=")) return mk_bool(ar == br && ai == bi);
        if (eq(op, "/=")) return mk_bool(!(ar == br && ai == bi));
        char buf[64]; snprintf(buf, sizeof buf, "internal: COMPL operator %s", op); die(buf);
      }
      break;
    case M_BOOL:
      if (p2->k == M_BOOL) {
        int x = as_bool(a) != 0, y = as_bool(b) != 0;
        if (eq(op, "AND")) return mk_bool(x && y);
        if (eq(op, "OR")) return mk_bool(x || y);
        if (eq(op, "XOR")) return mk_bool(x != y);
        if (eq(op, "=")) return mk_bool(x == y);
        if (eq(op, "/=")) return mk_bool(x != y);
        char buf[64]; snprintf(buf, sizeof buf, "internal: BOOL operator %s", op); die(buf);
      }
      break;
    case M_CHAR:
      if (p2->k == M_CHAR) {
        uint32_t x = as_char(a), y = as_char(b);
        return mk_bool(cmp_result(op, x < y ? -1 : x > y ? 1 : 0, "CHAR"));
      }
      break;
    case M_ROW:
      if (mode_is_string(mode_resolve(m1)) && mode_is_string(mode_resolve(m2))) {
        if (eq(op, "+")) { row_of(a); row_of(b); return row_concat(a, b); }
        int c = compare_chars(a, b);
        return mk_bool(cmp_result(op, c, "STRING"));
      }
      if (mode_is_string(mode_resolve(m1)) && p2->k == M_INT) {
        int64_t k = expect_int(b);
        return row_repeat(a, k);
      }
      if (p2->k == M_ROW) {
        if (eq(op, "=") || eq(op, "/=")) {
          int e = values_equal(a, b);
          return mk_bool(eq(op, "=") ? e : !e);
        }
        char buf[64]; snprintf(buf, sizeof buf, "internal: row operator %s", op); die(buf);
      }
      break;
    case M_BITS:
      if (p2->k == M_BITS) {
        wbits x = wb_of_val(a), y = wb_of_val(b);
        wbits mask = wb_mask(bits_width_of(n1));
        if (eq(op, "AND")) { wbits r = wb_and(x, y); return val_of_wb(&r); }
        if (eq(op, "OR")) { wbits r = wb_and(wb_or(x, y), mask); return val_of_wb(&r); }
        if (eq(op, "XOR")) { wbits r = wb_and(wb_xor(x, y), mask); return val_of_wb(&r); }
        if (eq(op, "=")) return mk_bool(wb_eq(x, y));
        if (eq(op, "/=")) return mk_bool(!wb_eq(x, y));
        if (eq(op, "<=")) return mk_bool(wb_eq(wb_and(x, y), x));
        if (eq(op, ">=")) return mk_bool(wb_eq(wb_and(x, y), y));
        char buf[64]; snprintf(buf, sizeof buf, "internal: BITS operator %s", op); die(buf);
      }
      if (p2->k == M_INT) {
        wbits x = wb_of_val(a);
        int64_t k = expect_int(b);
        int w = bits_width_of(n1);
        wbits mask = wb_mask(w);
        int64_t ak = k < 0 ? -k : k;
        if (eq(op, "SHL") || eq(op, "SHR") || eq(op, "DOWN")) {
          if (ak > w) die("shift count out of range");
          int64_t s = eq(op, "SHL") ? k : -k;
          wbits r = s >= 0 ? wb_and(wb_shl(x, (int) s), mask) : wb_shl(x, (int) s);
          return val_of_wb(&r);
        }
        char buf[64]; snprintf(buf, sizeof buf, "internal: BITS/INT operator %s", op); die(buf);
      }
      break;
    case M_BYTES:
      if (p2->k == M_BYTES) {
        int c = compare_chars(a, b);
        return mk_bool(cmp_result(op, c, "BYTES"));
      }
      break;
    default: break;
  }
  die_m2("internal: operator ", op, m1, m2);
}

/* the assigning operators: `a` is a name (`Interp.dyadic`, the `.ref m, _` arm) */
static a68_val assigning(const char* op, uint32_t m1, a68_val a, a68_val b) {
  const a68_mode* p1 = rm(m1);
  uint32_t mr = mode_resolve(p1->sub);
  const a68_mode* p = mode_at(mr);
  a68_val cur = ref_load_checked(a);
  /* LONG modes: the operator of the same name, then the assignment (`genie_f_and_becomes`) */
  const char* base = eq(op, "+:=") ? "+" : eq(op, "-:=") ? "-" : eq(op, "*:=") ? "*" : eq(op, "/:=") ? "/" : eq(op, "%:=") ? "%" : eq(op, "%*:=") ? "%*" : op;
  int64_t n = p->len;
  if (p->k == M_INT && n >= 1) { store_ref(a, long_int_dyadic(base, n, cur, b)); return a; }
  if (p->k == M_REAL && n >= 1) {
    if (cur.tag != T_MP) { if (cur.tag == T_UNDEF) die("attempt to use an uninitialised LONG REAL value"); die("internal: LONG REAL expected"); }
    if (b.tag != T_MP) { if (b.tag == T_UNDEF) die("attempt to use an uninitialised LONG REAL value"); die("internal: LONG REAL expected"); }
    store_ref(a, mp_dyadic(base, n, cur, b)); return a;
  }
  if (p->k == M_COMPL && n >= 1) { store_ref(a, mp_compl_dyadic(base, n, cur, b)); return a; }
  a68_val res;
  switch (p->k) {
    case M_INT: {
      int64_t x = expect_int(cur), y = expect_int(b);
      if (eq(op, "+:=")) res = mk_int(int_range(x + y, n));
      else if (eq(op, "-:=")) res = mk_int(int_range(x - y, n));
      else if (eq(op, "*:=")) res = mk_int(int_range(x * y, n));
      else if (eq(op, "%:=")) { if (y == 0) die("INT division by zero"); res = mk_int(x / y); }
      else if (eq(op, "%*:=")) { if (y == 0) die("INT division by zero"); int64_t m = y < 0 ? -y : y; int64_t r = x % m; res = mk_int(r < 0 ? r + m : r); }
      else if (eq(op, "/:=")) die("operator /:= not defined for INT");
      else { char buf[64]; snprintf(buf, sizeof buf, "internal: assigning operator %s on INT", op); die(buf); }
      break;
    }
    case M_REAL: {
      double x = as_real(cur), y = as_real(b);
      if (eq(op, "+:=")) res = mk_real(real_check(x + y));
      else if (eq(op, "-:=")) res = mk_real(real_check(x - y));
      else if (eq(op, "*:=")) res = mk_real(real_check(x * y));
      else if (eq(op, "/:=")) { if (y == 0.0) die("REAL value is not a number"); res = mk_real(x / y); }   /* the quotient is not checked */
      else { char buf[64]; snprintf(buf, sizeof buf, "internal: assigning operator %s on REAL", op); die(buf); }
      break;
    }
    case M_COMPL: {
      double ar, ai, br, bi;
      if (!compl_reals(cur, &ar, &ai) || !compl_reals(b, &br, &bi)) die("internal: COMPL expected");
      if (eq(op, "+:=")) res = mk_compl(ar + br, ai + bi);
      else if (eq(op, "-:=")) res = mk_compl(ar - br, ai - bi);
      else if (eq(op, "*:=")) res = compl_bin(0, ar, ai, br, bi);
      else if (eq(op, "/:=")) res = compl_bin(1, ar, ai, br, bi);
      else { char buf[64]; snprintf(buf, sizeof buf, "internal: assigning operator %s on COMPL", op); die(buf); }
      break;
    }
    case M_BITS: {
      wbits x = wb_of_val(cur), y = wb_of_val(b);
      wbits mask = wb_mask(bits_width_of(n));
      if (eq(op, "&:=")) { wbits r = wb_and(x, y); res = val_of_wb(&r); }
      else if (eq(op, "|:=")) { wbits r = wb_and(wb_or(x, y), mask); res = val_of_wb(&r); }
      else { char buf[64]; snprintf(buf, sizeof buf, "internal: assigning operator %s on BITS", op); die(buf); }
      break;
    }
    case M_ROW: {
      if (p->dims != 1) { char buf[64]; snprintf(buf, sizeof buf, "internal: assigning operator %s", op); die(buf); }
      if (eq(op, "+:=")) res = row_concat(cur, b);
      else if (eq(op, "*:=")) res = row_repeat(cur, expect_int(b));
      else { char buf[64]; snprintf(buf, sizeof buf, "internal: assigning operator %s on STRING", op); die(buf); }
      break;
    }
    default: { char buf[64]; snprintf(buf, sizeof buf, "internal: assigning operator %s", op); die(buf); }
  }
  store_ref(a, res);
  return a;
}

/* ---------------------------------------------------------------- monadic operators */

a68_val ops_monadic(const char* op, uint32_t m, a68_val v) {
  uint32_t mri = mode_resolve(m);
  const a68_mode* p = mode_at(mri);
  int64_t n = p->len;
  if (p->k == M_REAL) {
    if (eq(op, "DENOT")) {
      /* a [LONG] LONG REAL denotation, converted as `genie_denotation` converts it */
      int64_t tn; uint8_t* text = str_of(v, &tn);
      int ok;
      a68_val z = mp_of_string(text, (size_t) tn, n, &ok);
      free(text);
      if (!ok) die_m("error in ", mode_simple(M_REAL, n), " denotation");
      return z;
    }
    if (n >= 1 && (eq(op, "-") || eq(op, "+") || eq(op, "ABS") || eq(op, "SIGN") || eq(op, "ENTIER") || eq(op, "ROUND") || eq(op, "SHORTEN"))) {
      if (v.tag != T_MP) { if (v.tag == T_UNDEF) die("attempt to use an uninitialised LONG REAL value"); die("internal: LONG REAL expected"); }
      return mp_monadic(op, n, v);
    }
  }
  if (p->k == M_COMPL && n >= 1 && (eq(op, "-") || eq(op, "+") || eq(op, "RE") || eq(op, "IM") || eq(op, "CONJ") || eq(op, "ABS") || eq(op, "ARG") || eq(op, "SHORTEN")))
    return mp_compl_monadic(op, n, v);
  switch (p->k) {
    case M_INT:
      if (eq(op, "-")) {
        if (v.tag == T_BIGINT) { a68_big* b = big_of(v); a68_big* r = big_neg(b); a68_val res = val_of_big(r); big_free(b); big_free(r); return res; }
        return mk_int(int_range(-expect_int(v), n));
      }
      if (eq(op, "+")) { if (v.tag == T_UNDEF) expect_int(v); return v; }
      if (eq(op, "ABS")) {
        if (v.tag == T_BIGINT) { a68_big* b = big_of(v); a68_big* r = big_abs(b); a68_val res = val_of_big(r); big_free(b); big_free(r); return res; }
        int64_t x = expect_int(v); return mk_int(x < 0 ? -x : x);
      }
      if (eq(op, "SIGN")) {
        if (v.tag == T_BIGINT) { a68_big* b = big_of(v); int s = big_sign(b); big_free(b); return mk_int(s); }
        int64_t x = expect_int(v); return mk_int(x > 0 ? 1 : x < 0 ? -1 : 0);
      }
      if (eq(op, "ODD")) {
        if (v.tag == T_BIGINT) { a68_leaf* l = (a68_leaf*) v.v.p; return mk_bool((l->d[l->h.n - 1] - '0') % 2 != 0); }
        return mk_bool(expect_int(v) % 2 != 0);
      }
      if (eq(op, "REPR")) { int64_t x = expect_int(v); if (x < 0 || x > 255) die("REPR argument out of range"); return mk_char((uint32_t) x); }
      if (eq(op, "BIN")) {
        a68_big* b = big_of(v);
        if (big_sign(b) < 0) { big_free(b); die("BIN argument is negative"); }
        wbits w = wb_of_big(b);
        big_free(b);
        if (wb_exceeds(w, bits_width_of(n))) die("BIN argument out of range");
        return val_of_wb(&w);
      }
      if (eq(op, "SHORTEN")) {
        if (n == 1) return mk_int(shorten_long_int(v));   /* `mp_to_int`: its 32-bit weights wrap past two digits */
        a68_big* b = big_of(v);
        if (over_limit(b, n - 1)) { big_free(b); die_m("", mode_simple(M_INT, n - 1), " value overflow, result too large"); }
        a68_val r = val_of_big(b); big_free(b); return r;
      }
      break;
    case M_REAL:
      if (eq(op, "-")) return mk_real(-as_real(v));
      if (eq(op, "+")) { as_real(v); return v; }
      if (eq(op, "ABS")) return mk_real(fabs(as_real(v)));
      if (eq(op, "SIGN")) { double x = as_real(v); return mk_int(x > 0 ? 1 : x < 0 ? -1 : 0); }
      if (eq(op, "ENTIER") || eq(op, "ROUND")) {
        double x = as_real(v);
        double lim = (double) A68_MAXINT;   /* plain REAL only: LONG went to mp_monadic */
        if (x < -lim || x > lim) die("INT value out of bounds");
        if (eq(op, "ENTIER")) { double f = floor(x); return mk_int(f < 0 ? -(int64_t) (uint64_t) (-f) : (int64_t) (uint64_t) f); }
        double r = floor(fabs(x) + 0.5);
        int64_t k = (int64_t) (uint64_t) r;
        return mk_int(x < 0 ? -k : k);
      }
      if (eq(op, "SHORTEN")) { as_real(v); return v; }
      break;
    case M_COMPL: {
      double re, im;
      if (eq(op, "+") || eq(op, "SHORTEN")) return v;
      if (!compl_reals(v, &re, &im)) die("internal");
      if (eq(op, "-")) return mk_compl(-re, -im);
      if (eq(op, "ABS")) return mk_real(a68_compl_abs(re, im));
      if (eq(op, "RE")) return mk_real(re);
      if (eq(op, "IM")) return mk_real(im);
      if (eq(op, "CONJ")) return mk_compl(re, -im);
      if (eq(op, "ARG")) { if (re == 0.0 && im == 0.0) die("invalid COMPL argument"); return mk_real(atan2(im, re)); }
      break;
    }
    case M_CHAR: if (eq(op, "ABS")) return mk_int((int64_t) as_char(v)); break;
    case M_BOOL:
      if (eq(op, "ABS")) return mk_int(as_bool(v) ? 1 : 0);
      if (eq(op, "NOT")) return mk_bool(!as_bool(v));
      break;
    case M_BITS:
      if (eq(op, "ABS")) {
        /* a68g reads the 32 bits of a BITS as a C int: ABS NOT BIN 3 is -4 */
        if (v.tag == T_BITS) return mk_int(n <= 0 && v.v.u >= 2147483648u ? (int64_t) v.v.u - 4294967296LL : (int64_t) v.v.u);
        a68_big* b = big_of(v); a68_val r = val_of_big(b); big_free(b); return r;
      }
      if (eq(op, "NOT")) { wbits x = wb_of_val(v); wbits r = wb_xor(wb_mask(bits_width_of(n)), x); return val_of_wb(&r); }
      if (eq(op, "SHORTEN")) { wbits x = wb_of_val(v); wbits r = wb_and(x, wb_mask(bits_width_of(n - 1))); return val_of_wb(&r); }
      break;
    case M_ROW: {
      a68_rowd* d = row_of(v);
      if (eq(op, "LWB")) return mk_int(d->dim[0].l);
      if (eq(op, "UPB")) return mk_int(d->dim[0].u);
      if (eq(op, "ELEMS")) return mk_int(row_count(d));
      break;
    }
    default: break;
  }
  char* ms = mode_string(m);
  size_t bn = strlen(op) + strlen(ms) + 40;
  char* buf = (char*) xmalloc(bn);
  snprintf(buf, bn, "internal: monadic operator %s on %s", op, ms);
  free(ms);
  die(buf);
}

/* ---------------------------------------------------------------- widening */

static a68_val row_of_bools(a68_val v, int64_t longness) {
  int w = bits_width_of(longness);
  wbits x = wb_of_val(v);
  a68_val* es = (a68_val*) xmalloc((size_t) w * sizeof(a68_val));
  for (int i = 0; i < w; i++) es[i] = mk_bool(wb_bit(&x, w - 1 - i));
  a68_val r = row_of_values(es, w);
  free(es);
  return r;
}

/* `Interp.widenValue` */
a68_val ops_widen(uint32_t src, uint32_t dst, a68_val v) {
  const a68_mode* s = rm(src);
  const a68_mode* d = rm(dst);
  int64_t a = s->len, b = d->len;
  if (v.tag == T_UNDEF) die("attempt to use an uninitialised value");
  if (s->k == M_INT && d->k == M_INT) return v;
  if (s->k == M_INT && d->k == M_REAL && (v.tag == T_INT || v.tag == T_BIGINT)) {
    if (b >= 1) { a68_big* k = big_of(v); a68_val z = mp_of_int(k, b); big_free(k); return z; }
    return mk_real((double) v.v.i);
  }
  if (s->k == M_REAL && d->k == M_REAL) {
    if (v.tag == T_REAL) return a <= 0 && b >= 1 ? mp_of_real(v.v.r, b) : v;
    if (v.tag == T_MP) return a == 1 && b >= 2 ? mp_widen(v, 1, 2) : v;
    return v;
  }
  if (s->k == M_INT && d->k == M_COMPL && (v.tag == T_INT || v.tag == T_BIGINT)) {
    if (b >= 1) {
      a68_big* k = big_of(v); a68_val re = mp_of_int(k, b); big_free(k);
      a68_big* zero = big_from_i64(0); a68_val im = mp_of_int(zero, b); big_free(zero);
      return struct2(re, im);
    }
    return mk_compl((double) v.v.i, 0.0);
  }
  if (s->k == M_REAL && d->k == M_COMPL && v.tag == T_REAL) {
    if (b >= 1) { a68_big* zero = big_from_i64(0); a68_val im = mp_of_int(zero, b); big_free(zero); return struct2(mp_of_real(v.v.r, b), im); }
    return mk_compl(v.v.r, 0.0);
  }
  if (s->k == M_REAL && d->k == M_COMPL && v.tag == T_MP) {
    a68_val x = a == 1 && b >= 2 ? mp_widen(v, 1, 2) : v;
    a68_big* zero = big_from_i64(0); a68_val im = mp_of_int(zero, b); big_free(zero);
    return struct2(x, im);
  }
  if (s->k == M_COMPL && d->k == M_COMPL) {
    double re, im; a68_val mre, mim;
    if (compl_reals(v, &re, &im)) return b >= 1 ? struct2(mp_of_real(re, b), mp_of_real(im, b)) : v;
    if (compl_mps(v, &mre, &mim)) return a == 1 && b >= 2 ? struct2(mp_widen(mre, 1, 2), mp_widen(mim, 1, 2)) : v;
    return v;
  }
  if (s->k == M_BITS && a == 0 && d->k == M_BITS && v.tag == T_BITS) {
    if (b <= 0) return v;
    /* a68g widens a BITS to LONG BITS with `genie_lengthen_int_to_mp`, reading the 32 bits
       as an INT.  A value with its top bit set comes out as that INT plus 2^32, kept to as
       many radix-10^7 digits as the INT's magnitude has: `LENG NOT BIN 0` is 4967295. */
    uint64_t bits = v.v.u;
    if (bits < 2147483648u) return v;
    int64_t k = (int64_t) bits - 4294967296LL;
    int64_t ak = k < 0 ? -k : k;
    int64_t modulus = ak < 10000000 ? 10000000 : 100000000000000LL;
    return mk_bits(bits % (uint64_t) modulus);
  }
  if (s->k == M_BITS && d->k == M_BITS) return v;
  /* a BYTES value is its row of characters, NUL padded to `bytes width` */
  if (s->k == M_BYTES && mode_is_string(mode_resolve(dst))) return v;
  if (s->k == M_BYTES && d->k == M_BYTES && v.tag == T_ROW) {
    int64_t w = b >= 1 ? 256 : 32;
    int64_t n; a68_val* es = row_elems(row_of(v), &n);
    a68_val* zs = (a68_val*) xmalloc((size_t) (w > n ? w : n) * sizeof(a68_val));
    memcpy(zs, es, (size_t) n * sizeof(a68_val));
    for (int64_t i = n; i < w; i++) zs[i] = mk_char(0);
    a68_val r = row_of_values(zs, w > n ? w : n);
    free(es); free(zs);
    return r;
  }
  if (s->k == M_BITS && d->k == M_ROW && mode_at(d->sub)->k == M_BOOL && (v.tag == T_BITS || v.tag == T_BIGBITS)) return row_of_bools(v, a);
  char* s1 = mode_string(src); char* s2 = mode_string(dst);
  size_t bn = strlen(s1) + strlen(s2) + 40;
  char* buf = (char*) xmalloc(bn);
  snprintf(buf, bn, "internal: cannot widen %s to %s", s1, s2);
  free(s1); free(s2);
  die(buf);
}

/* ---------------------------------------------------------------- SKIP and conformity */

/* `Interp.defaultOf`: the value a `SKIP` of a mode denotes */
a68_val ops_default(uint32_t m) {
  const a68_mode* p = rm(m);
  switch (p->k) {
    case M_VOID: return mk_tag(T_VOID);
    case M_ROW: {
      a68_rowd* d = rowd_alloc(p->dims);
      a68_obj* st = store_alloc_slots(0);
      st->rc = 1;
      d->base = st;
      d->off = 0;
      for (uint32_t k = 0; k < p->dims; k++) { d->dim[k].l = 1; d->dim[k].u = 0; d->dim[k].stride = 1; }
      return mk_ptr(T_ROW, (a68_obj*) d, 0);
    }
    case M_UNION: {
      a68_slots* s = slots_alloc(1);
      s->s[0] = mk_tag(T_UNDEF);
      return mk_ptr(T_UNION, (a68_obj*) s, mode_empty_union());
    }
    default: return mk_tag(T_UNDEF);
  }
}

/* `Runtime.conform`: does a value whose united mode is `vm` (0xffffffff for a value that
   is not a union) conform to mode `m`? */
int ops_conform(uint32_t m, uint32_t vm) {
  uint32_t vmm = vm == 0xffffffffu ? mode_simple(M_VOID, 0) : vm;
  const a68_mode* p = rm(m);
  if (p->k == M_UNION) {
    for (uint32_t i = 0; i < p->n; i++) if (mode_eqv(p->modes[i], vmm)) return 1;
    return 0;
  }
  return mode_eqv(m, vmm);
}

int ops_mode_is_union(uint32_t m) { return rm(m)->k == M_UNION; }
