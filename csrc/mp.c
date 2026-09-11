/* mp.c -- the multi-precision kernel: a transcription of A68/MP.lean.

   Digits are doubles holding integers.  Where the Lean computes with exact integers the
   double arithmetic here is exact too (every scratch value is below 2^53, see MP.lean);
   where the Lean emulates a rounded double operation (`fma`, `truncDiv`, `dblOfInt`) the
   corresponding double operation is used.  Contraction of `a * b + c` into a fused
   multiply-add is switched off so that only the explicit `fma()` calls fuse. */
#include "mp.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#pragma STDC FP_CONTRACT OFF

#define R      10000000.0            /* `MP.R` as a double */
#define RI     10000000LL            /* … and as an integer */
#define HALF_R 5000000.0

/* ------------------------------------------------------------------ helpers */

static void seterr(char* err, const char* msg) {
  if (err) { strncpy(err, msg, MP_ERR_LEN - 1); err[MP_ERR_LEN - 1] = 0; }
}
#define FAIL(err, msg) (seterr((err), (msg)), 1)
#define TRY(e) do { int rc__ = (e); if (rc__) return rc__; } while (0)

static double* xcalloc_d(size_t n) {
  double* p = (double*) calloc(n, sizeof(double));
  if (!p) { fputs("a68: out of memory\n", stderr); abort(); }
  return p;
}

/* Numbers are created at the precision they are used with; the Lean's `grow` never has
   anything to do in the paths transcribed here, so growing is an internal error. */
static void ensure(const a68_mp* z, int n) {
  if (z->digs < n) {
    fprintf(stderr, "a68: internal: multiprecision number of %d digits used with %d\n", z->digs, n);
    abort();
  }
}

/* A temporary of `n` digits on the caller's stack (`nil n`). */
#define MP_TEMP(name, n) double name##_buf[(n) + 1]; a68_mp name = mp_temp(name##_buf, (n))

static a68_mp mp_temp(double* buf, int n) {
  a68_mp z;
  memset(buf, 0, ((size_t) n + 1) * sizeof(double));
  z.st = MP_INIT; z.ex = 0; z.digs = n; z.d = buf;
  return z;
}

/* Negation that never produces -0.0 (the Lean negates integers). */
static inline double neg0(double v) { return v == 0.0 ? 0.0 : -v; }

/* `MP.dig` of `x.setDig 1 |x1|`: the digits of |x|. */
static inline double adig(const a68_mp* z, int k) {
  double v = mp_dig(z, k);
  return k == 1 ? fabs(v) : v;
}

int mp_width_to_digits(int n) { return MP_GUARDS + (n + MP_LOG_RADIX - 1) / MP_LOG_RADIX; }

/* --------------------------------------------------------- construction */

a68_mp mp_nil(int digs) {
  a68_mp z;
  z.st = MP_INIT; z.ex = 0; z.digs = digs; z.d = xcalloc_d((size_t) digs + 1);
  return z;
}

a68_mp mp_lit(int digs, double u, int64_t e) {
  a68_mp z = mp_nil(digs);
  z.d[1] = u; z.ex = e;
  return z;
}

a68_mp mp_one(int digs) { return mp_lit(digs, 1.0, 0); }

a68_mp mp_copy(const a68_mp* x) {
  a68_mp z = mp_nil(x->digs);
  z.st = x->st; z.ex = x->ex;
  memcpy(z.d + 1, x->d + 1, (size_t) x->digs * sizeof(double));
  return z;
}

/* `lenMp u digs gdigs` into a number of `gdigs` digits. */
static void len_into(a68_mp* z, const a68_mp* u, int digs, int gdigs) {
  int m = digs < gdigs ? digs : gdigs, k;
  uint32_t st = u->st; int64_t ex = u->ex;
  ensure(z, gdigs);
  for (k = 1; k <= m; k++) z->d[k] = mp_dig(u, k);
  for (k = m + 1; k <= gdigs; k++) z->d[k] = 0.0;
  z->st = st; z->ex = ex;
}

a68_mp mp_len(const a68_mp* u, int digs, int gdigs) {
  a68_mp z = mp_nil(gdigs);
  len_into(&z, u, digs, gdigs);
  return z;
}

void mp_free(a68_mp* z) { free(z->d); z->d = NULL; z->digs = 0; }

double mp_dig(const a68_mp* z, int k) { return (k >= 1 && k <= z->digs) ? z->d[k] : 0.0; }

void mp_set_dig(a68_mp* z, int k, double v) {
  if (k > z->digs) {
    double* d = xcalloc_d((size_t) k + 1);
    memcpy(d, z->d, ((size_t) z->digs + 1) * sizeof(double));
    free(z->d); z->d = d; z->digs = k;
  }
  z->d[k] = v;
}

/* `setMp (z, x, expo, digs)`. */
void mp_set(a68_mp* z, double x, int64_t e, int digs) {
  ensure(z, digs);
  memset(z->d + 1, 0, (size_t) digs * sizeof(double));
  z->d[1] = x; z->st = MP_INIT; z->ex = e;
}

void mp_set_zero(a68_mp* z, int digs) { mp_set(z, 0.0, 0, digs); }
void mp_set_one(a68_mp* z, int digs) { mp_set(z, 1.0, 0, digs); }

/* `moveMp (z, x, n)`: status, exponent and `n` digits. */
void mp_move(a68_mp* z, const a68_mp* x, int n) {
  uint32_t st = x->st; int64_t ex = x->ex; int k;
  ensure(z, n);
  if (z != x) for (k = 1; k <= n; k++) z->d[k] = mp_dig(x, k);
  z->st = st; z->ex = ex;
}

void mp_set_nan(a68_mp* z)  { z->st = MP_NAN | MP_INIT; }
void mp_set_pinf(a68_mp* z) { z->st = MP_PINF | MP_INIT; }
void mp_set_minf(a68_mp* z) { z->st = MP_MINF | MP_INIT; }
void mp_negate1(a68_mp* z)  { z->d[1] = neg0(z->d[1]); }

int mp_is_nan(const a68_mp* z)    { return (z->st & MP_NAN) != 0; }
int mp_is_pinf(const a68_mp* z)   { return (z->st & MP_PINF) != 0; }
int mp_is_minf(const a68_mp* z)   { return (z->st & MP_MINF) != 0; }
int mp_is_inf(const a68_mp* z)    { return mp_is_pinf(z) || mp_is_minf(z); }
int mp_is_finite(const a68_mp* z) { return mp_is_nan(z) ? 0 : !mp_is_inf(z); }
int mp_is_zero(const a68_mp* z)   { return mp_dig(z, 1) == 0.0; }
int mp_is_plus(const a68_mp* z)   { return mp_dig(z, 1) > 0.0; }
int mp_is_minus(const a68_mp* z)  { return mp_dig(z, 1) < 0.0; }

/* `checkExp`. */
int mp_check_exp(const a68_mp* z, char* err) {
  int64_t e = z->ex < 0 ? -z->ex : z->ex;
  if (e > MP_MAX_EXPO || (e == MP_MAX_EXPO && fabs(mp_dig(z, 1)) > 1.0))
    return FAIL(err, "multiprecision value out of bounds");
  return 0;
}

/* `catchNaN`. */
int mp_catch_nan(const a68_mp* x, char* err) {
  if (mp_is_nan(x)) return FAIL(err, "LONG LONG REAL value is not a number");
  return 0;
}

/* ------------------------------------------------- normalisation and rounding */

/* `carryAt`: one carry of `norm_mp` at position `j >= 2`.  The carries are computed on
   the integer value of the digit, as the Lean does. */
static void carry_at(double* a, int j) {
  double zv = a[j], lo = a[j - 1];
  if (zv >= R) {
    int64_t c = (int64_t) zv / RI;
    a[j] = zv - (double) c * R;
    a[j - 1] = lo + (double) c;
  } else if (zv < 0.0) {
    int64_t c = 1 + ((int64_t) -zv - 1) / RI;
    a[j] = zv + (double) c * R;
    a[j - 1] = lo - (double) c;
  }
}

/* `normDigits w k digs`: carries at `digs, digs - 1, …, k` (never below position 1). */
static void norm_digits(double* w, int k, int digs) {
  int j;
  for (j = digs; j >= k && j >= 1; j--) carry_at(w, j);
}

/* `roundInternal (z, w, wex, digs)`: `w` has at least `digs + 3` entries. */
static void round_internal(a68_mp* z, double* w, int64_t wex, int digs) {
  int last = (w[1] == 0.0) ? 2 + digs : 1 + digs, k;
  /* GAUSSIAN_ROUNDING as written in mp.c */
  if (w[last] > HALF_R) {
    w[last - 1] += 1.0;
  } else if (w[last] == HALF_R) {
    if (fmod(w[last - 1], 2.0) == 0.0) w[last - 1] += 1.0;
    w[last - 1] += 1.0;
  }
  if (w[last - 1] >= R) norm_digits(w, 2, last);
  ensure(z, digs);
  if (w[1] == 0.0) {
    for (k = 1; k <= digs; k++) z->d[k] = w[k + 1];
    z->ex = wex - 1;
  } else {
    for (k = 1; k <= digs; k++) z->d[k] = w[k];
    z->ex = wex;
  }
  if (z->d[1] == 0.0) z->ex = 0;
}

/* ----------------------------------------------- shortening and lengthening */

/* `lengthenRaw`. */
static void lengthen_raw(a68_mp* z, const a68_mp* x, int digs_z, int digs_x) {
  uint32_t st = x->st; int64_t ex = x->ex; int k;
  ensure(z, digs_z);
  if (z != x) for (k = 1; k <= digs_x; k++) z->d[k] = mp_dig(x, k);
  for (k = digs_x + 1; k <= digs_z; k++) z->d[k] = 0.0;
  z->st = st; z->ex = ex;
}

/* `shortenMp (z, digs, x, digs_x)`. */
int mp_shorten(a68_mp* z, int digs, const a68_mp* x, int digs_x, char* err) {
  int neg, k; uint32_t st; int64_t ex;
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_minf(z); return 0; }
  if (digs > digs_x) { lengthen_raw(z, x, digs, digs_x); return 0; }
  if (digs == digs_x) { mp_move(z, x, digs); return 0; }
  neg = mp_is_minus(x); st = x->st; ex = x->ex;
  {
    double w[digs + 3];
    memset(w, 0, sizeof w);
    for (k = 1; k <= digs + 1; k++) {
      double v = mp_dig(x, k);
      w[k + 1] = (k == 1 && neg) ? -v : v;
    }
    round_internal(z, w, ex + 1, digs);
  }
  if (neg) mp_negate1(z);
  z->st = st;
  return 0;
}

/* `lengthenMp`. */
int mp_lengthen(a68_mp* z, int digs_z, const a68_mp* x, int digs_x, char* err) {
  if (digs_z < digs_x) return mp_shorten(z, digs_z, x, digs_x, err);
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_minf(z); return 0; }
  if (digs_z == digs_x) { mp_move(z, x, digs_z); return 0; }
  lengthen_raw(z, x, digs_z, digs_x);
  return 0;
}

/* --------------------------------------------------- addition and subtraction */

/* `digitOr0` on the digits of |a|. */
static inline double digit_or0(const a68_mp* a, int digs, int64_t j) {
  if (j <= 0 || j > digs) return 0.0;
  return adig(a, (int) j);
}

/* `alignedSum`: the aligned digit sums of |x| and s·|y| into `w[0 .. digs + 2]`. */
static int64_t aligned_sum(double* w, const a68_mp* x, const a68_mp* y, int digs, double s) {
  int64_t xex = x->ex, yex = y->ex;
  int64_t shl_x = yex > xex ? yex - xex : 0, shl_y = xex > yex ? xex - yex : 0;
  int i;
  w[0] = 0.0; w[1] = 0.0;
  for (i = 2; i <= digs + 2; i++)
    w[i] = digit_or0(x, digs, (int64_t) i - 1 - shl_x) + s * digit_or0(y, digs, (int64_t) i - 1 - shl_y);
  return 1 + (xex > yex ? xex : yex);
}

/* `addMp z xa ya digs` for the finite, non-negative copies `xa`, `ya` of `x`, `y`. */
static int add_abs(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err) {
  z->st |= MP_INIT;
  if (mp_is_zero(x)) { mp_move(z, y, digs); z->d[1] = fabs(z->d[1]); return 0; }
  if (mp_is_zero(y)) { mp_move(z, x, digs); z->d[1] = fabs(z->d[1]); return 0; }
  {
    double w[digs + 3];
    int64_t wex = aligned_sum(w, x, y, digs, 1.0);
    norm_digits(w, 2, digs + 2);
    round_internal(z, w, wex, digs);
  }
  return mp_check_exp(z, err);
}

/* `subMp z xa ya digs` for the finite, non-negative copies `xa`, `ya` of `x`, `y`. */
static int sub_abs(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err) {
  int digs_h = digs + 2, negative = 0, f, j;
  z->st |= MP_INIT;
  if (mp_is_zero(x)) { mp_move(z, y, digs); z->d[1] = neg0(fabs(z->d[1])); return 0; }
  if (mp_is_zero(y)) { mp_move(z, x, digs); z->d[1] = fabs(z->d[1]); return 0; }
  {
    double w[digs + 3];
    int64_t wex = aligned_sum(w, x, y, digs, -1.0);
    if (w[2] <= 0.0) {
      f = 0;
      for (j = 2; j <= digs_h; j++) if (w[j] != 0.0) { f = j; break; }
      if (f != 0) {
        negative = w[f] < 0.0;
        if (negative) for (j = f; j <= digs_h; j++) w[j] = neg0(w[j]);
      }
    }
    norm_digits(w, 2, digs_h);
    f = 0;
    for (j = 1; j <= digs_h; j++) if (w[j] != 0.0) { f = j; break; }
    if (f > 1) {
      int j2 = f - 1;
      for (j = 1; j <= digs_h - j2; j++) { w[j] = w[j + j2]; w[j + j2] = 0.0; }
      wex -= j2;
    }
    round_internal(z, w, wex, digs);
  }
  if (negative) mp_negate1(z);
  return mp_check_exp(z, err);
}

/* `addMp (z, x, y, digs)`. */
int mp_add(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err) {
  double x1, y1;
  TRY(mp_catch_nan(x, err)); TRY(mp_catch_nan(y, err));
  if (mp_is_pinf(x) && mp_is_minf(y)) { mp_set_nan(z); return 0; }
  if (mp_is_pinf(y) && mp_is_minf(x)) { mp_set_nan(z); return 0; }
  if (mp_is_pinf(x) || mp_is_pinf(y)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x) || mp_is_minf(y)) { mp_set_minf(z); return 0; }
  z->st |= MP_INIT;
  if (mp_is_zero(x)) { mp_move(z, y, digs); return 0; }
  if (mp_is_zero(y)) { mp_move(z, x, digs); return 0; }
  x1 = mp_dig(x, 1); y1 = mp_dig(y, 1);
  if (x1 >= 0.0 && y1 < 0.0) return sub_abs(z, x, y, digs, err);
  if (x1 < 0.0 && y1 >= 0.0) return sub_abs(z, y, x, digs, err);
  if (x1 < 0.0 && y1 < 0.0) { TRY(add_abs(z, x, y, digs, err)); mp_negate1(z); return 0; }
  return add_abs(z, x, y, digs, err);
}

/* `subMp (z, x, y, digs)`. */
int mp_sub(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err) {
  double x1, y1;
  TRY(mp_catch_nan(x, err)); TRY(mp_catch_nan(y, err));
  if (mp_is_pinf(x) && mp_is_minf(y)) { mp_set_nan(z); return 0; }
  if (mp_is_pinf(y) && mp_is_minf(x)) { mp_set_nan(z); return 0; }
  if (mp_is_pinf(x) || mp_is_pinf(y)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x) || mp_is_minf(y)) { mp_set_minf(z); return 0; }
  z->st |= MP_INIT;
  if (mp_is_zero(x)) { mp_move(z, y, digs); mp_negate1(z); return 0; }
  if (mp_is_zero(y)) { mp_move(z, x, digs); return 0; }
  x1 = mp_dig(x, 1); y1 = mp_dig(y, 1);
  if (x1 >= 0.0 && y1 < 0.0) return add_abs(z, x, y, digs, err);
  if (x1 < 0.0 && y1 >= 0.0) { TRY(add_abs(z, y, x, digs, err)); mp_negate1(z); return 0; }
  if (x1 < 0.0 && y1 < 0.0) return sub_abs(z, y, x, digs, err);
  return sub_abs(z, x, y, digs, err);
}

/* ------------------------------------------------------------ multiplication */

/* `mulInf (u, v, w)` when `v` is infinite. */
static void mul_inf(a68_mp* u, const a68_mp* v, const a68_mp* w) {
  int plus = mp_is_pinf(v);
  if (mp_is_pinf(w)) { if (plus) mp_set_pinf(u); else mp_set_minf(u); }
  else if (mp_is_minf(w)) { if (plus) mp_set_minf(u); else mp_set_pinf(u); }
  else if (mp_is_zero(w)) mp_set_nan(u);
  else if (mp_is_plus(w)) { if (plus) mp_set_pinf(u); else mp_set_minf(u); }
  else { if (plus) mp_set_minf(u); else mp_set_pinf(u); }
}

/* `mulMp (z, x, y, digs)`: grammar-school multiplication with intermittent normalisation. */
int mp_mul(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err) {
  const int oflow = 44;      /* floor (MAX_REPR_INT / (2 R^2)) - 1 */
  int digs_h = 2 + digs, i, jj;
  double x1, y1, z1; int64_t wex;
  TRY(mp_catch_nan(x, err)); TRY(mp_catch_nan(y, err));
  if (mp_is_inf(x)) { mul_inf(z, x, y); return 0; }
  if (mp_is_inf(y)) { mul_inf(z, y, x); return 0; }
  if (mp_is_zero(x) || mp_is_zero(y)) { mp_set_zero(z, digs); return 0; }
  x1 = mp_dig(x, 1); y1 = mp_dig(y, 1); wex = x->ex + y->ex + 1;
  z->st |= MP_INIT;
  {
    double w[digs_h + 1];
    memset(w, 0, sizeof w);
    for (i = digs; i >= 1; i--) {
      double yi = adig(y, i);
      if (yi != 0.0) {
        int k = digs_h - i;
        int j = k > digs ? digs : k;
        if ((digs - i + 1) % oflow == 0) norm_digits(w, 2, digs_h);
        for (jj = j; jj >= 1; jj--) w[i + jj] = w[i + jj] + yi * adig(x, jj);
      }
    }
    norm_digits(w, 2, digs_h);
    round_internal(z, w, wex, digs);
  }
  z1 = z->d[1];
  z->d[1] = (x1 * y1 >= 0.0) ? z1 : neg0(z1);
  return mp_check_exp(z, err);
}

/* `scaleDigits (z, x, y, wex, digs)`: |x| scaled by the digit `y`. */
static void scale_digits(a68_mp* z, const a68_mp* x, double y, int64_t wex, int digs) {
  int digs_h = 2 + digs, j;
  double w[digs_h + 1];
  memset(w, 0, sizeof w);
  for (j = digs; j >= 1; j--) w[j + 1] = w[j + 1] + y * adig(x, j);
  norm_digits(w, 2, digs_h);
  round_internal(z, w, wex, digs);
}

/* `halfMp z xa digs` and `tenthMp` on a finite |x|. */
static int half_abs(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int64_t ex = x->ex;
  z->st |= MP_INIT;
  scale_digits(z, x, HALF_R, ex, digs);
  return mp_check_exp(z, err);
}

static int tenth_abs(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int64_t ex = x->ex;
  z->st |= MP_INIT;
  scale_digits(z, x, R / 10.0, ex, digs);
  return mp_check_exp(z, err);
}

/* `halfMp (z, x, digs)`. */
int mp_half(a68_mp* z, const a68_mp* x, int digs, char* err) {
  double x1, z1;
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_minf(z); return 0; }
  x1 = mp_dig(x, 1);
  z->st |= MP_INIT;
  scale_digits(z, x, HALF_R, x->ex, digs);
  z1 = z->d[1];
  z->d[1] = x1 >= 0.0 ? z1 : neg0(z1);
  return mp_check_exp(z, err);
}

/* `tenthMp (z, x, digs)`. */
int mp_tenth(a68_mp* z, const a68_mp* x, int digs, char* err) {
  double x1, z1;
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_minf(z); return 0; }
  x1 = mp_dig(x, 1);
  z->st |= MP_INIT;
  scale_digits(z, x, R / 10.0, x->ex, digs);
  z1 = z->d[1];
  z->d[1] = x1 >= 0.0 ? z1 : neg0(z1);
  return mp_check_exp(z, err);
}

/* `mulMpDigit (z, x, y, digs)`. */
int mp_mul_digit(a68_mp* z, const a68_mp* x, int64_t y, int digs, char* err) {
  double x1, z1; int64_t ya, ex;
  TRY(mp_catch_nan(x, err));
  if (mp_is_inf(x) && y == 0) { mp_set_nan(z); return 0; }
  if (mp_is_inf(x)) {
    if (mp_is_pinf(x)) { if (y > 0) mp_set_pinf(z); else mp_set_minf(z); }
    else { if (y < 0) mp_set_pinf(z); else mp_set_minf(z); }
    return 0;
  }
  x1 = mp_dig(x, 1); ex = x->ex;
  z->st |= MP_INIT;
  ya = y < 0 ? -y : y;
  if (ya == 2) TRY(add_abs(z, x, x, digs, err));
  else scale_digits(z, x, (double) ya, ex + 1, digs);
  z1 = z->d[1];
  z->d[1] = (x1 * (double) y >= 0.0) ? z1 : neg0(z1);
  return mp_check_exp(z, err);
}

/* ------------------------------------------------------------------ division */

/* `divDigitLoop`: |x| / ya for ya not in {2, 10}. */
static void div_digit_loop(a68_mp* z, const a68_mp* x, int64_t ya, int digs, int oflow) {
  int wdigs = 4 + digs, k;
  int64_t ex = x->ex;
  double w[wdigs + 1];
  /* div_mp_digit computes its denominator with two plain multiplications */
  double den = ((double) ya * R) * R;
  memset(w, 0, sizeof w);
  for (k = 1; k <= digs; k++) w[k + 1] = adig(x, k);
  for (k = 1; k <= digs + 2; k++) {
    int first = k + 2;
    double t2 = (wdigs >= first + 2) ? w[k + 3] : 0.0;
    /* `qDigit`: a68g's fused estimate `(int) (nom / den)` */
    double nom = fma(fma(fma(w[k], R, w[k + 1]), R, w[k + 2]), R, t2);
    double q = trunc(nom / den);
    double wk = w[k];
    w[k + 1] = w[k + 1] + (wk * R - q * (double) ya);
    w[k] = q;
    if (k % oflow == 0 || k == digs + 2) norm_digits(w, first, wdigs);
  }
  norm_digits(w, 2, digs);
  round_internal(z, w, ex, digs);
}

/* `divLoop`: |x| / |y| after D. M. Smith, with a68g's estimates. */
static void div_loop(a68_mp* z, const a68_mp* x, const a68_mp* y, int nzdigs, int digs, int oflow,
                     int64_t wex) {
  int wdigs = 4 + digs, k, j;
  double w[wdigs + 1];
  double y1 = adig(y, 1), y2 = mp_dig(y, 2), y3 = mp_dig(y, 3);
  double den = fma(fma(y1, R, y2), R, y3);
  memset(w, 0, sizeof w);
  for (k = 1; k <= digs; k++) w[k + 1] = adig(x, k);
  for (k = 1; k <= digs + 2; k++) {
    int first = k + 2, len = digs + 1 + k;
    double t2 = (wdigs >= first + 2) ? w[k + 3] : 0.0;
    double tm1 = w[k], t0 = w[k + 1], t1 = w[k + 2];
    /* `nomZero` and `qDigit` on the fused numerator */
    double nom = fma(fma(fma(tm1, R, t0), R, t1), R, t2);
    double q = 0.0, wk;
    if (nom != 0.0) {
      int lim = len < wdigs ? len : wdigs;
      q = trunc(nom / den);
      if (nzdigs + first <= lim + 1) lim = first + nzdigs - 1;
      for (j = first; j <= lim; j++) {
        int idx = k + 1 + (j - first);
        w[idx] = w[idx] - q * adig(y, 1 + (j - first));
      }
    }
    wk = w[k];
    w[k + 1] = fma(wk, R, w[k + 1]);
    w[k] = q;
    if (k % oflow == 0 || k == digs + 2) norm_digits(w, first, wdigs);
  }
  norm_digits(w, 2, digs);
  round_internal(z, w, wex, digs);
}

/* `divMpDigit z xa ya digs` for |x| and ya > 0: the non-negative quotient. */
static int div_digit_abs(a68_mp* z, const a68_mp* x, int64_t ya, int digs, char* err) {
  const int oflow = 29;
  z->st |= MP_INIT;
  if (ya == 2) return half_abs(z, x, digs, err);
  if (ya == 10) return tenth_abs(z, x, digs, err);
  div_digit_loop(z, x, ya, digs, oflow);
  return mp_check_exp(z, err);
}

/* `divMpDigit (z, x, y, digs)`. */
int mp_div_digit(a68_mp* z, const a68_mp* x, int64_t y, int digs, char* err) {
  double x1, z1;
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_minf(z); return 0; }
  if (y == 0) { mp_set_nan(z); return 0; }
  x1 = mp_dig(x, 1);
  TRY(div_digit_abs(z, x, y < 0 ? -y : y, digs, err));
  z1 = z->d[1];
  z->d[1] = (x1 * (double) y >= 0.0) ? z1 : neg0(z1);
  return mp_check_exp(z, err);
}

/* `divMp (z, x, y, digs)`. */
int mp_div(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err) {
  const int oflow = 29;
  double x1, y1, z1; int nzdigs;
  TRY(mp_catch_nan(x, err)); TRY(mp_catch_nan(y, err));
  if (mp_is_inf(x)) { mp_set_nan(z); return 0; }
  if (mp_is_inf(y)) { mp_set_zero(z, digs); return 0; }
  if (mp_is_zero(y)) {
    if (mp_is_zero(x)) mp_set_nan(z);
    else if (mp_is_plus(x)) mp_set_pinf(z);
    else mp_set_minf(z);
    return 0;
  }
  x1 = mp_dig(x, 1); y1 = mp_dig(y, 1);
  z->st |= MP_INIT;
  nzdigs = digs;
  while (adig(y, nzdigs) == 0.0 && nzdigs > 1) nzdigs--;
  if (nzdigs == 1 && y->ex == 0) {
    TRY(div_digit_abs(z, x, (int64_t) adig(y, 1), digs, err));
  } else {
    int64_t wex = x->ex - y->ex;
    div_loop(z, x, y, nzdigs, digs, oflow, wex);
  }
  z1 = z->d[1];
  z->d[1] = (x1 * y1 >= 0.0) ? z1 : neg0(z1);
  return mp_check_exp(z, err);
}

/* `recMp (z, x, digs)`. */
int mp_rec(a68_mp* z, const a68_mp* x, int digs, char* err) {
  if (mp_is_zero(x)) { mp_set_nan(z); return 0; }
  {
    MP_TEMP(one, digs);
    one.d[1] = 1.0;
    return mp_div(z, &one, x, digs, err);
  }
}

/* ---------------------------------------------------- truncation and rounding */

/* `truncMp (z, x, digs)`. */
int mp_trunc(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int64_t ex, k;
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_minf(z); return 0; }
  ex = x->ex;
  if (ex < 0) { mp_set_zero(z, digs); return 0; }
  if (ex >= digs) return FAIL(err, "value out of bounds");
  mp_move(z, x, digs);
  for (k = ex + 2; k <= digs; k++) z->d[k] = 0.0;
  z->st |= MP_INIT;
  return 0;
}

/* `overMp (z, x, y, digs)`: truncated quotient. */
int mp_over(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err) {
  int dg = digs + MP_GUARDS;
  TRY(mp_catch_nan(x, err)); TRY(mp_catch_nan(y, err));
  if (mp_is_inf(x)) { mp_set_nan(z); return 0; }
  if (mp_is_inf(y)) { mp_set_zero(z, digs); return 0; }
  if (mp_is_zero(y)) {
    if (mp_is_zero(x)) mp_set_nan(z);
    else if (mp_is_plus(x)) mp_set_pinf(z);
    else mp_set_minf(z);
    return 0;
  }
  {
    MP_TEMP(zg, dg); MP_TEMP(xg, dg); MP_TEMP(yg, dg);
    len_into(&xg, x, digs, dg); len_into(&yg, y, digs, dg);
    TRY(mp_div(&zg, &xg, &yg, dg, err));
    TRY(mp_trunc(&zg, &zg, dg, err));
    TRY(mp_shorten(z, digs, &zg, dg, err));
  }
  z->st |= MP_INIT;
  return 0;
}

/* `overMpDigit (z, x, y, digs)`. */
int mp_over_digit(a68_mp* z, const a68_mp* x, int64_t y, int digs, char* err) {
  int dg = digs + MP_GUARDS;
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_minf(z); return 0; }
  if (y == 0) { mp_set_nan(z); return 0; }
  {
    MP_TEMP(zg, dg); MP_TEMP(xg, dg);
    len_into(&xg, x, digs, dg);
    TRY(mp_div_digit(&zg, &xg, y, dg, err));
    TRY(mp_trunc(&zg, &zg, dg, err));
    return mp_shorten(z, digs, &zg, dg, err);
  }
}

/* `modMp (z, x, y, digs)`: `x - y · trunc (x / y)`. */
int mp_mod(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err) {
  int dg = digs + MP_GUARDS;
  TRY(mp_catch_nan(x, err)); TRY(mp_catch_nan(y, err));
  if (mp_is_inf(x) || mp_is_inf(y)) { mp_set_nan(z); return 0; }
  if (mp_is_zero(y)) { mp_set_nan(z); return 0; }
  {
    MP_TEMP(xg, dg); MP_TEMP(yg, dg); MP_TEMP(zg, dg);
    len_into(&xg, x, digs, dg); len_into(&yg, y, digs, dg);
    TRY(mp_over(&zg, &xg, &yg, dg, err));
    TRY(mp_mul(&zg, &yg, &zg, dg, err));
    TRY(mp_sub(&zg, &xg, &zg, dg, err));
    return mp_shorten(z, digs, &zg, dg, err);
  }
}

/* `roundMp (z, x, digs)`: add or subtract one half, then truncate. */
int mp_round(a68_mp* z, const a68_mp* x, int digs, char* err) {
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_minf(z); return 0; }
  {
    MP_TEMP(y, digs);            /* SET_MP_HALF */
    y.d[1] = HALF_R; y.ex = -1;
    if (mp_dig(x, 1) >= 0.0) TRY(mp_add(z, x, &y, digs, err));
    else TRY(mp_sub(z, x, &y, digs, err));
  }
  TRY(mp_trunc(z, z, digs, err));
  z->st |= MP_INIT;
  return 0;
}

/* `entierMp (z, x, digs)`; the scratch copy is taken from `z`. */
int mp_entier(a68_mp* z, const a68_mp* x, int digs, char* err) {
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_minf(z); return 0; }
  if (mp_dig(x, 1) >= 0.0) return mp_trunc(z, x, digs, err);
  {
    MP_TEMP(y, digs);
    mp_move(&y, z, digs);
    TRY(mp_trunc(z, x, digs, err));
    TRY(mp_sub(&y, &y, z, digs, err));
    if (mp_dig(&y, 1) != 0.0) {
      MP_TEMP(one, digs);
      one.d[1] = 1.0;
      TRY(mp_sub(z, z, &one, digs, err));
    }
  }
  z->st |= MP_INIT;
  return 0;
}

/* `minusMp`, `absMp`. */
int mp_minus(a68_mp* x, char* err) {
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_minf(x); return 0; }
  if (mp_is_minf(x)) { mp_set_pinf(x); return 0; }
  mp_negate1(x); x->st |= MP_INIT;
  return 0;
}

int mp_abs(a68_mp* x, char* err) {
  TRY(mp_catch_nan(x, err));
  if (mp_is_inf(x)) { mp_set_pinf(x); return 0; }
  x->d[1] = fabs(x->d[1]); x->st |= MP_INIT;
  return 0;
}

/* `x ± 1`, `1 - x`. */
int mp_minus_one(a68_mp* z, const a68_mp* x, int digs, char* err) {
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_minf(z); return 0; }
  { MP_TEMP(one, digs); one.d[1] = 1.0; return mp_sub(z, x, &one, digs, err); }
}

int mp_plus_one(a68_mp* z, const a68_mp* x, int digs, char* err) {
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_minf(z); return 0; }
  { MP_TEMP(one, digs); one.d[1] = 1.0; return mp_add(z, x, &one, digs, err); }
}

int mp_one_minus(a68_mp* z, const a68_mp* x, int digs, char* err) {
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_minf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_pinf(z); return 0; }
  { MP_TEMP(one, digs); one.d[1] = 1.0; return mp_sub(z, &one, x, digs, err); }
}

/* `powMpInt (z, x, n, digs)`: square and multiply at two guard digits. */
int mp_pow_int(a68_mp* z, const a68_mp* x, int64_t n, int digs, char* err) {
  int dg = digs + MP_GUARDS;
  TRY(mp_catch_nan(x, err));
  if (mp_is_inf(x)) {
    if (n == 0) mp_set_nan(z);
    else if (n < 0) mp_set_zero(z, digs);
    else if (mp_is_pinf(x)) mp_set_pinf(z);
    else if (n % 2 == 0) mp_set_pinf(z);
    else mp_set_minf(z);
    return 0;
  }
  {
    MP_TEMP(xg, dg); MP_TEMP(zg, dg);
    int neg = n < 0;
    uint64_t nn = n < 0 ? (uint64_t) (-(n + 1)) + 1 : (uint64_t) n, bit = 1;
    len_into(&xg, x, digs, dg);
    zg.d[1] = 1.0;
    while (bit <= nn) {
      if (nn & bit) TRY(mp_mul(&zg, &zg, &xg, dg, err));
      TRY(mp_mul(&xg, &xg, &xg, dg, err));
      if (bit > UINT64_MAX / 2) break;
      bit <<= 1;
    }
    if (neg) TRY(mp_rec(&zg, &zg, dg, err));
    TRY(mp_shorten(z, digs, &zg, dg, err));
  }
  return mp_check_exp(z, err);
}

/* ---------------------------------------------------------------- comparison */

/* `eqMp`, `ltMp`, `gtMp` and their negations, as a68g computes them (by subtraction,
   which can itself overflow). */
int mp_eq(const a68_mp* x, const a68_mp* y, int digs, char* err) {
  if (mp_is_nan(x) || mp_is_nan(y)) return 0;
  if (mp_is_finite(x) && mp_is_finite(y)) {
    MP_TEMP(v, digs);
    if (mp_sub(&v, x, y, digs, err)) return -1;
    return mp_dig(&v, 1) == 0.0;
  }
  return (mp_is_pinf(x) && mp_is_pinf(y)) || (mp_is_minf(x) && mp_is_minf(y));
}

int mp_lt(const a68_mp* x, const a68_mp* y, int digs, char* err) {
  if (mp_is_nan(x) || mp_is_nan(y)) return 0;
  if (mp_is_finite(x) && mp_is_finite(y)) {
    MP_TEMP(v, digs);
    if (mp_sub(&v, x, y, digs, err)) return -1;
    return mp_is_minus(&v);
  }
  return (mp_is_minf(x) && mp_is_pinf(y)) || (mp_is_finite(x) && mp_is_pinf(y))
      || (mp_is_minf(x) && mp_is_finite(y));
}

int mp_gt(const a68_mp* x, const a68_mp* y, int digs, char* err) {
  if (mp_is_nan(x) || mp_is_nan(y)) return 0;
  if (mp_is_finite(x) && mp_is_finite(y)) {
    MP_TEMP(v, digs);
    if (mp_sub(&v, x, y, digs, err)) return -1;
    return mp_is_plus(&v);
  }
  return (mp_is_pinf(x) && mp_is_minf(y)) || (mp_is_pinf(x) && mp_is_finite(y))
      || (mp_is_finite(x) && mp_is_minf(y));
}

int mp_ne(const a68_mp* x, const a68_mp* y, int digs, char* err) {
  int r = mp_eq(x, y, digs, err); return r < 0 ? r : !r;
}
int mp_le(const a68_mp* x, const a68_mp* y, int digs, char* err) {
  int r = mp_gt(x, y, digs, err); return r < 0 ? r : !r;
}
int mp_ge(const a68_mp* x, const a68_mp* y, int digs, char* err) {
  int r = mp_lt(x, y, digs, err); return r < 0 ? r : !r;
}

/* --------------------------------------------------------------- conversions */

/* `alignMp (z, &expo, digs)`: shift the decimal digits of a mantissa built in radix 10 so
   that the exponent becomes a multiple of LOG_MP_RADIX; returns the new exponent. */
static int64_t align_mp(a68_mp* z, int64_t expo, int digs) {
  int64_t shift, e, s; int j;
  if (!mp_is_finite(z)) return expo;
  if (expo >= 0) { shift = MP_LOG_RADIX - expo % MP_LOG_RADIX - 1; e = expo / MP_LOG_RADIX; }
  else { shift = (-expo - 1) % MP_LOG_RADIX; e = (expo + 1) / MP_LOG_RADIX - 1; }
  ensure(z, digs);
  for (s = 0; s < shift; s++) {
    int64_t carry = 0;
    for (j = 1; j <= digs; j++) {
      int64_t v = (int64_t) z->d[j];
      int64_t k = v % 10;
      z->d[j] = (double) (v / 10 + carry * (RI / 10));
      carry = k;
    }
  }
  return e;
}

/* `intToMp (z, k, digs)`. */
int mp_int_to_mp(a68_mp* z, int64_t k, int digs, char* err) {
  uint64_t a = k < 0 ? (uint64_t) (-(k + 1)) + 1 : (uint64_t) k, m = a, kk;
  int n = 0, j;
  while (m / (uint64_t) RI != 0) { m /= (uint64_t) RI; n++; }
  if (n + 1 > z->digs) return FAIL(err, "value out of bounds");
  mp_set(z, 0.0, n, digs);
  kk = a;
  for (j = 1 + n; j >= 1; j--) { z->d[j] = (double) (kk % (uint64_t) RI); kk /= (uint64_t) RI; }
  if (k < 0) mp_negate1(z);
  return mp_check_exp(z, err);
}

a68_mp mp_of_i64(int64_t k, int digs) {
  a68_mp z = mp_nil(digs);
  char err[MP_ERR_LEN];
  if (mp_int_to_mp(&z, k, digs, err)) { fprintf(stderr, "a68: internal: %s\n", err); abort(); }
  return z;
}

/* The exact `intToMp` of a decimal integer: `|d1| d2 … dn` are its radix-10^7 digits. */
int mp_of_dec_string(const char* s, size_t n, int digs, a68_mp* out, char* err) {
  size_t i = 0, first, len;
  int neg = 0, nd, j;
  if (i < n && (s[i] == '+' || s[i] == '-')) { neg = s[i] == '-'; i++; }
  for (first = i; i < n; i++) if (s[i] < '0' || s[i] > '9') return FAIL(err, "invalid integer denotation");
  i = first;
  while (i < n && s[i] == '0') i++;
  len = n - i;
  nd = (int) ((len + MP_LOG_RADIX - 1) / MP_LOG_RADIX);
  if (nd > digs) return FAIL(err, "value out of bounds");
  *out = mp_nil(digs);
  if (nd == 0) return 0;
  {
    size_t head = len - (size_t) (nd - 1) * MP_LOG_RADIX, p = i, c;
    for (j = 1; j <= nd; j++) {
      size_t w = (j == 1) ? head : MP_LOG_RADIX;
      int64_t v = 0;
      for (c = 0; c < w; c++) v = v * 10 + (s[p + c] - '0');
      out->d[j] = (double) v;
      p += w;
    }
  }
  out->ex = nd - 1;
  if (neg) mp_negate1(out);
  return mp_check_exp(out, err);
}

/* `toIntTrunc`. */
int mp_to_i64_trunc(const a68_mp* z, int64_t* out) {
  uint64_t s = 0; int64_t j, e;
  if (z->ex < 0) { *out = 0; return 0; }
  e = z->ex;
  for (j = 1; j <= e + 1; j++) {
    uint64_t dj = (uint64_t) adig(z, (int) j);
    if (s > (UINT64_MAX - dj) / (uint64_t) RI) return 1;
    s = s * (uint64_t) RI + dj;
  }
  if (mp_dig(z, 1) < 0.0) {
    if (s > (uint64_t) INT64_MAX + 1) return 1;
    *out = s == (uint64_t) INT64_MAX + 1 ? INT64_MIN : -(int64_t) s;
  } else {
    if (s > (uint64_t) INT64_MAX) return 1;
    *out = (int64_t) s;
  }
  return 0;
}

/* `isIntOfDigits` (`check_mp_int`). */
int mp_is_int_of_digits(const a68_mp* z, int digs) { return z->ex >= 0 && z->ex < digs; }

/* `toInt32`: `mp_to_int` for 32-bit INT (weights wrap as C `int` does). */
static int64_t wrap32(int64_t v) {
  int64_t m = v % 4294967296LL;
  if (m < 0) m += 4294967296LL;
  return m >= 2147483648LL ? m - 4294967296LL : m;
}

int mp_to_int32(const a68_mp* z, int digs, int32_t* out, char* err) {
  const int64_t max_int = 2147483647;
  int64_t sum = 0, weight = 1, e, j;
  int neg;
  if (z->ex >= digs) return FAIL(err, "value out of bounds");
  neg = mp_dig(z, 1) < 0.0;
  e = z->ex < 0 ? 0 : z->ex;
  for (j = 1 + e; j >= 1; j--) {
    int64_t dj = (int64_t) adig(z, (int) j), term;
    if (weight == 0) return FAIL(err, "division by zero");
    if (dj > max_int / weight) return FAIL(err, "INT value out of bounds");
    term = wrap32(dj * weight);
    if (sum > max_int - term) return FAIL(err, "INT value out of bounds");
    sum += term;
    weight = wrap32(weight * RI);
  }
  *out = (int32_t) (neg ? -sum : sum);
  return 0;
}

/* `tenUpMp (z, n, digs)`. */
int mp_ten_up(a68_mp* z, int64_t n, int digs, char* err) {
  static const double y[7] = { 1, 10, 100, 1000, 10000, 100000, 1000000 };
  if (n >= 0) mp_set(z, y[n % MP_LOG_RADIX], n / MP_LOG_RADIX, digs);
  else mp_set(z, y[(MP_LOG_RADIX + n % MP_LOG_RADIX) % MP_LOG_RADIX], (n + 1) / MP_LOG_RADIX - 1, digs);
  return mp_check_exp(z, err);
}

/* `stringToMp (z, s, digs)`. */
int mp_string_to_mp(a68_mp* z, const char* s, size_t n, int digs, int* valid, char* err) {
  size_t i0 = 0, i = 0;
  int sign = 1, dig = 1, ok = 1;
  int64_t sum = 0, dot = -1, one = -1, pow = 0, W = RI / 10, expo = 0, e;
#define CHR(k) ((i0 + (k) < n) ? s[i0 + (k)] : '\0')
#define ISDIGIT(c) ((c) >= '0' && (c) <= '9')
  mp_set_zero(z, digs);
  while (i0 < n && (s[i0] == ' ' || s[i0] == '\t' || s[i0] == '\n')) i0++;
  if (i0 < n && s[i0] == '-') sign = -1;
  if (i0 < n && (s[i0] == '+' || s[i0] == '-')) i0++;
  while (i0 < n && s[i0] == '0') i0++;
  while (CHR(i) != '\0' && dig <= digs && (ISDIGIT(CHR(i)) || CHR(i) == '.')) {
    if (CHR(i) == '.') dot = (int64_t) i;
    else {
      int64_t value = CHR(i) - '0';
      if (one < 0 && value > 0) one = pow;
      sum += W * value;
      if (one >= 0) W /= 10;
      pow++;
      if (W < 1) {
        z->d[dig] = (double) sum;
        dig++;
        sum = 0;
        W = RI / 10;
      }
    }
    i++;
  }
  if (dig <= digs) { z->d[dig] = (double) sum; dig++; }
  if (CHR(i) == 'e' || CHR(i) == 'E') {
    /* strtol: optional blanks and sign, then digits; everything must be consumed */
    size_t p = i0 + i + 1, q, dstart;
    int neg = 0;
    int64_t v = 0;
    q = p;
    while (q < n && s[q] == ' ') q++;
    if (q < n && s[q] == '-') { neg = 1; q++; }
    else if (q < n && s[q] == '+') q++;
    dstart = q;
    while (q < n && ISDIGIT(s[q])) { v = v * 10 + (s[q] - '0'); q++; }
    expo = neg ? -v : v;
    if (q == dstart) ok = (p == n);
    else ok = (q == n);
  } else {
    ok = CHR(i) == '\0';
  }
  if (dot >= 0) {
    if (one > dot) expo -= (one - dot + 1);
    else expo += dot - 1;
  } else {
    expo += pow - 1;
  }
  e = align_mp(z, expo, digs);
  z->ex = (z->d[1] == 0.0) ? 0 : e;
  z->d[1] = z->d[1] * (double) sign;
  TRY(mp_check_exp(z, err));
  *valid = ok;
  return 0;
#undef CHR
#undef ISDIGIT
}

/* a68g's `ten_up`: 10^expo by binary powers in double precision, with its range check. */
int mp_ten_up_real(int64_t expo, double* out, char* err) {
  static const double table[9] = { 10.0, 100.0, 1.0e4, 1.0e8, 1.0e16, 1.0e32, 1.0e64, 1.0e128, 1.0e256 };
  int64_t e = expo < 0 ? -expo : expo;
  double r = 1.0; int i = 0;
  if (e > 511) return FAIL(err, "invalid REAL value");
  while (e != 0) {
    if (e % 2 == 1) r = r * table[i];
    e /= 2;
    i++;
  }
  *out = expo < 0 ? 1.0 / r : r;
  return 0;
}

/* `realToMp (z, x, digs)` of the generic build. */
int mp_real_to_mp(a68_mp* z, double x, int digs, char* err) {
  double a, t, sign_x; int64_t expo; int j, k;
  if (isnan(x)) { mp_set_nan(z); return 0; }
  if (isinf(x)) { if (x > 0) mp_set_pinf(z); else mp_set_minf(z); return 0; }
  mp_set_zero(z, digs);
  if (x == 0.0) return 0;
  if (fabs(x) < 1.0e7 && floor(fabs(x)) == fabs(x)) return mp_int_to_mp(z, (int64_t) x, digs, err);
  sign_x = x > 0 ? 1.0 : -1.0;
  a = fabs(x);
  expo = (int64_t) log10(a);
  TRY(mp_ten_up_real(expo, &t, err));
  a = a / t;
  expo -= 1;
  if (a >= 1.0) { a = a / 10.0; expo += 1; }
  j = 1; k = 0;
  while (k <= 15 && j <= digs) {
    double dg;
    t = a * 1.0e7;
    dg = floor(t);
    a = t - dg;
    z->d[j] = (double) (int64_t) dg;
    j++;
    k += MP_LOG_RADIX;
  }
  z->ex = align_mp(z, expo, digs);
  z->d[1] = z->d[1] * sign_x;
  return mp_check_exp(z, err);
}

/* `a68g_neumaier_sum_real`. */
static double neumaier_sum(const double* terms, int n) {
  int ascend, k;
  double sum = 0.0, lost = 0.0;
  if (n == 0) return 0.0;
  ascend = fabs(terms[0]) < fabs(terms[n - 1]);
  for (k = 0; k < n; k++) {
    double u = terms[ascend ? k : n - k - 1];
    double v = sum + u;
    if (fabs(sum) >= fabs(u)) lost = lost + ((sum - v) + u);
    else lost = lost + ((u - v) + sum);
    sum = v;
  }
  return sum + lost;
}

/* `mpToReal (p, z, digs)` of the generic build, checked as CHECK_REAL checks it. */
int mp_to_double(const a68_mp* z, int digs, double* out, char* err) {
  int lim = digs < 36 ? digs : 36, k;
  double weight = 1.0, sum, t;
  double terms[36];
  if (mp_is_nan(z)) { *out = 0.0 / 0.0; return 0; }
  if (mp_is_pinf(z)) { *out = 1.0 / 0.0; return 0; }
  if (mp_is_minf(z)) { *out = -1.0 / 0.0; return 0; }
  if (z->ex * MP_LOG_RADIX <= -307) { *out = 0.0; return 0; }
  for (k = 0; k < lim; k++) {
    terms[k] = adig(z, k + 1) * weight;
    weight = weight / 1.0e7;
  }
  TRY(mp_ten_up_real(z->ex * MP_LOG_RADIX, &t, err));
  sum = neumaier_sum(terms, lim) * t;
  if (isnan(sum)) return FAIL(err, "REAL value is not a number");
  if (isinf(sum)) return FAIL(err, "infinite REAL value");
  *out = mp_dig(z, 1) >= 0.0 ? sum : -sum;
  return 0;
}
