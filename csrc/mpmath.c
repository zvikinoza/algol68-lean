/* mpmath.c -- a68g's multi-precision elementary functions: a transcription of
   A68/MPMath.lean (`mp-math.c`, `mp-pi.c`, `mp-complex.c` of the level-2 build).

   Newton iterations seeded from `double` estimates (`sqrt`, `cbrt`, `log`, `atan` of the
   C library), Taylor series with a68g's stopping rule, argument reductions (halving for
   `exp`, thirds for `sin`), and a68g's caches: `mp_pi` keeps π and seven derived
   constants computed at the precision of the request that last needed more digits, and
   later requests for fewer digits truncate the cached value; `mp_ln_scale` (ln 10^7) and
   `mp_ln_10` are kept at full precision and rounded on each use.  The cache is the
   `Cache` state the Lean threads through `MM`; `mp_cache_reset` empties it. */
#include "mp.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#pragma STDC FP_CONTRACT OFF

#define R 10000000.0
#define TRY(e) do { int rc__ = (e); if (rc__) return rc__; } while (0)
#define MP_TEMP(name, n) double name##_buf[(n) + 1]; a68_mp name = mp_temp(name##_buf, (n))

static a68_mp mp_temp(double* buf, int n) {
  a68_mp z;
  memset(buf, 0, ((size_t) n + 1) * sizeof(double));
  z.st = MP_INIT; z.ex = 0; z.digs = n; z.d = buf;
  return z;
}

/* `lenMp u digs gdigs` into a temporary of `gdigs` digits. */
static void len_into(a68_mp* z, const a68_mp* u, int digs, int gdigs) {
  int m = digs < gdigs ? digs : gdigs, k;
  uint32_t st = u->st; int64_t ex = u->ex;
  for (k = 1; k <= m; k++) z->d[k] = mp_dig(u, k);
  for (k = m + 1; k <= gdigs; k++) z->d[k] = 0.0;
  z->st = st; z->ex = ex;
}

static inline int64_t iabs64(int64_t v) { return v < 0 ? -v : v; }

/* `DOUBLE_ACCURACY`: `A68G_REAL_DIG - 1`. */
#define DOUBLE_ACCURACY 14

/* ------------------------------------------------------------------ the cache */

static struct {
  int has_pi; int pi_size; a68_mp pic[8];      /* `(mp_pi_size, constants)`, by mp_pi_mod */
  int has_ls; int ls_size; a68_mp ls;          /* `(mp_ln_scale_size, value)` */
  int has_l10; int l10_size; a68_mp l10;       /* `(mp_ln_10_size, value)` */
} cache;

static void cache_drop_pi(void) {
  int k;
  if (cache.has_pi) for (k = 0; k < 8; k++) mp_free(&cache.pic[k]);
  cache.has_pi = 0;
}

void mp_cache_reset(void) {
  cache_drop_pi();
  if (cache.has_ls) mp_free(&cache.ls);
  if (cache.has_l10) mp_free(&cache.l10);
  memset(&cache, 0, sizeof cache);
}

/* ------------------------------------------------------------------ helpers */

/* `mustReduce`: |z| > 0.001, as a68g estimates it. */
int mp_must_reduce(const a68_mp* z, int digs, int* out, char* err) {
  int64_t expo; double est, t;
  if (mp_is_zero(z)) { *out = 0; return 0; }
  expo = z->ex * MP_LOG_RADIX;
  if (expo >= 0) { *out = 1; return 0; }
  if (expo < -2 * MP_LOG_RADIX) { *out = 0; return 0; }
  TRY(mp_ten_up_real(expo * MP_LOG_RADIX, &t, err));
  est = fabs(mp_dig(z, 1)) * t;
  if (digs > 1) {
    TRY(mp_ten_up_real(MP_LOG_RADIX, &t, err));
    est = est + (mp_dig(z, 2) * (double) expo) / t;
  }
  *out = est > 0.001;
  return 0;
}

/* `sameMp`. */
int mp_same(const a68_mp* x, const a68_mp* y, int digs) {
  int k;
  if (mp_is_nan(x) || mp_is_nan(y)) return 0;
  if (x->st != y->st || x->ex != y->ex) return 0;
  for (k = 1; k <= digs; k++) if (mp_dig(x, k) != mp_dig(y, k)) return 0;
  return 1;
}

/* ------------------------------------------------------------- roots */

/* `sqrtMp (z, x, digs)`. */
int mp_sqrt(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int gdigs = digs + MP_GUARDS, reciprocal;
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_nan(z); return 0; }
  if (mp_dig(x, 1) == 0.0) { mp_set_zero(z, digs); return 0; }
  if (mp_dig(x, 1) < 0.0) { mp_set_nan(z); return 0; }
  {
    MP_TEMP(zg, gdigs); MP_TEMP(xg, gdigs); MP_TEMP(tmp, gdigs);
    len_into(&xg, x, digs, gdigs);
    reciprocal = xg.ex < 0;
    if (reciprocal) TRY(mp_rec(&xg, &xg, gdigs, err));
    if (iabs64(xg.ex) >= 2) {
      int64_t expo = xg.ex;
      xg.ex = expo % 2;
      TRY(mp_sqrt(&zg, &xg, gdigs, err));
      zg.ex = zg.ex + expo / 2;
    } else {
      double xd; int decimals = DOUBLE_ACCURACY;
      TRY(mp_to_double(&xg, gdigs, &xd, err));
      TRY(mp_real_to_mp(&zg, sqrt(xd), gdigs, err));
      for (;;) {
        int hdigs;
        decimals *= 2;
        hdigs = 1 + decimals / MP_LOG_RADIX;
        if (hdigs > gdigs) hdigs = gdigs;
        TRY(mp_div(&tmp, &xg, &zg, hdigs, err));
        TRY(mp_add(&tmp, &zg, &tmp, hdigs, err));
        TRY(mp_half(&zg, &tmp, hdigs, err));
        if (!(decimals < 2 * gdigs * MP_LOG_RADIX)) break;
      }
    }
    if (reciprocal) TRY(mp_rec(&zg, &zg, digs, err));
    return mp_shorten(z, digs, &zg, gdigs, err);
  }
}

/* `curtMp (z, x, digs)`. */
int mp_curt(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int gdigs = digs + MP_GUARDS, reciprocal, change_sign;
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_nan(z); return 0; }
  if (mp_dig(x, 1) == 0.0) { mp_set_zero(z, digs); return 0; }
  change_sign = mp_dig(x, 1) < 0.0;
  {
    MP_TEMP(zg, gdigs); MP_TEMP(xg, gdigs); MP_TEMP(tmp, gdigs);
    len_into(&xg, x, digs, gdigs);
    if (change_sign) mp_negate1(&xg);
    reciprocal = xg.ex < 0;
    if (reciprocal) TRY(mp_rec(&xg, &xg, gdigs, err));
    if (iabs64(xg.ex) >= 3) {
      int64_t expo = xg.ex;
      xg.ex = expo % 3;
      TRY(mp_curt(&zg, &xg, gdigs, err));
      zg.ex = zg.ex + expo / 3;
    } else {
      double xd; int decimals = DOUBLE_ACCURACY;
      TRY(mp_to_double(&xg, gdigs, &xd, err));
      TRY(mp_real_to_mp(&zg, cbrt(xd), gdigs, err));
      for (;;) {
        int hdigs;
        decimals *= 2;
        hdigs = 1 + decimals / MP_LOG_RADIX;
        if (hdigs > gdigs) hdigs = gdigs;
        TRY(mp_mul(&tmp, &zg, &zg, hdigs, err));
        TRY(mp_div(&tmp, &xg, &tmp, hdigs, err));
        TRY(mp_add(&tmp, &zg, &tmp, hdigs, err));
        TRY(mp_add(&tmp, &zg, &tmp, hdigs, err));
        TRY(mp_div_digit(&zg, &tmp, 3, hdigs, err));
        if (!(decimals < gdigs * MP_LOG_RADIX)) break;
      }
    }
    if (reciprocal) TRY(mp_rec(&zg, &zg, digs, err));
    TRY(mp_shorten(z, digs, &zg, gdigs, err));
  }
  if (change_sign) mp_negate1(z);
  return 0;
}

/* ------------------------------------------------------------- exponential */

/* `expSeries`: the Taylor terms x^k / k! for k = 2 … 9 that `exp_mp` and `expm1_mp` add
   without a test, followed by the open-ended loop.  `sum` holds the initial sum. */
static int exp_series(a68_mp* sum, const a68_mp* xg, int gdigs, char* err) {
  static const int64_t facs[7] = { 6, 24, 120, 720, 5040, 40320, 362880 };
  int f, iter;
  int64_t n = 10;
  MP_TEMP(pwr, gdigs); MP_TEMP(tmp, gdigs); MP_TEMP(fac, gdigs);
  TRY(mp_add(sum, sum, xg, gdigs, err));
  TRY(mp_mul(&pwr, xg, xg, gdigs, err));
  TRY(mp_half(&tmp, &pwr, gdigs, err));
  TRY(mp_add(sum, sum, &tmp, gdigs, err));
  for (f = 0; f < 7; f++) {
    TRY(mp_mul(&pwr, &pwr, xg, gdigs, err));
    TRY(mp_div_digit(&tmp, &pwr, facs[f], gdigs, err));
    TRY(mp_add(sum, sum, &tmp, gdigs, err));
  }
  TRY(mp_mul(&pwr, &pwr, xg, gdigs, err));
  mp_set(&fac, 3628800.0, 0, gdigs);
  iter = mp_dig(&pwr, 1) != 0.0;
  while (iter) {
    TRY(mp_div(&tmp, &pwr, &fac, gdigs, err));
    if (tmp.ex <= sum->ex - gdigs) iter = 0;
    else {
      TRY(mp_add(sum, sum, &tmp, gdigs, err));
      TRY(mp_mul(&pwr, &pwr, xg, gdigs, err));
      n++;
      TRY(mp_mul_digit(&fac, &fac, n, gdigs, err));
    }
  }
  return 0;
}

/* `expMp (z, x, digs)`. */
int mp_exp(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int gdigs = digs + MP_GUARDS, m = 0, reduce, k;
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_zero(z, digs); return 0; }
  if (mp_dig(x, 1) == 0.0) { mp_set_one(z, digs); return 0; }
  {
    MP_TEMP(xg, gdigs); MP_TEMP(sum, gdigs);
    len_into(&xg, x, digs, gdigs);
    for (;;) {
      TRY(mp_must_reduce(&xg, gdigs, &reduce, err));
      if (!reduce) break;
      m++;
      TRY(mp_half(&xg, &xg, gdigs, err));
    }
    mp_set_one(&sum, gdigs);
    TRY(exp_series(&sum, &xg, gdigs, err));
    for (k = 0; k < m; k++) TRY(mp_mul(&sum, &sum, &sum, gdigs, err));
    return mp_shorten(z, digs, &sum, gdigs, err);
  }
}

/* `expm1Mp (z, x, digs)` (a68g returns 1 for a zero argument). */
int mp_expm1(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set(z, -1.0, 0, digs); return 0; }
  if (mp_dig(x, 1) == 0.0) { mp_set_one(z, digs); return 0; }
  {
    MP_TEMP(xg, gdigs); MP_TEMP(sum, gdigs);
    len_into(&xg, x, digs, gdigs);
    TRY(exp_series(&sum, &xg, gdigs, err));
    return mp_shorten(z, digs, &sum, gdigs, err);
  }
}

/* ------------------------------------------------------------- logarithm */

static int ln_const(double u, int64_t e, int gdigs, a68_mp* store, int* has, int* size, a68_mp* out, char* err);

/* `lnMp`, `mp_ln_scale`, `mp_ln_10`. */
int mp_ln(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int gdigs = digs + MP_GUARDS, neg, scale;
  int64_t expo = 0;
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_nan(z); return 0; }
  if (mp_dig(x, 1) == 0.0) { mp_set_minf(z); return 0; }
  if (mp_dig(x, 1) < 0.0) { mp_set_nan(z); return 0; }
  {
    MP_TEMP(xg, gdigs); MP_TEMP(zg, gdigs); MP_TEMP(tmp, gdigs);
    len_into(&xg, x, digs, gdigs);
    neg = xg.ex < 0;
    if (neg) TRY(mp_rec(&xg, &xg, digs, err));
    scale = iabs64(xg.ex) >= 2;
    if (scale) { expo = xg.ex; xg.ex = 0; }
    if (xg.ex == 0 && mp_dig(&xg, 1) == 1.0 && mp_dig(&xg, 2) == 0.0) {
      MP_TEMP(pwr, gdigs);
      int64_t n = 2; int iter;
      TRY(mp_minus_one(&xg, &xg, gdigs, err));
      TRY(mp_mul(&pwr, &xg, &xg, gdigs, err));
      mp_move(&zg, &xg, gdigs);
      iter = mp_dig(&pwr, 1) != 0.0;
      while (iter) {
        TRY(mp_div_digit(&tmp, &pwr, n, gdigs, err));
        if (tmp.ex <= zg.ex - gdigs) iter = 0;
        else {
          if (n % 2 == 0) mp_negate1(&tmp);
          TRY(mp_add(&zg, &zg, &tmp, gdigs, err));
          TRY(mp_mul(&pwr, &pwr, &xg, gdigs, err));
          n++;
        }
      }
    } else {
      double xd; int decimals = DOUBLE_ACCURACY;
      TRY(mp_to_double(&xg, gdigs, &xd, err));
      TRY(mp_real_to_mp(&zg, log(xd), gdigs, err));
      for (;;) {
        int hdigs;
        decimals *= 2;
        hdigs = 1 + decimals / MP_LOG_RADIX;
        if (hdigs > gdigs) hdigs = gdigs;
        TRY(mp_exp(&tmp, &zg, hdigs, err));
        TRY(mp_div(&tmp, &xg, &tmp, hdigs, err));
        TRY(mp_minus_one(&zg, &zg, hdigs, err));
        TRY(mp_add(&zg, &zg, &tmp, hdigs, err));
        if (!(decimals < gdigs * MP_LOG_RADIX)) break;
      }
    }
    if (scale) {
      MP_TEMP(ln_base, gdigs);
      TRY(mp_ln_scale(&ln_base, gdigs, err));
      TRY(mp_mul_digit(&ln_base, &ln_base, expo, gdigs, err));
      TRY(mp_add(&zg, &zg, &ln_base, gdigs, err));
    }
    if (neg) mp_negate1(&zg);
    return mp_shorten(z, digs, &zg, gdigs, err);
  }
}

/* `computeLnConst`: ln (u · R^e) at `gdigs` digits, stored in the cache. */
static int ln_const(double u, int64_t e, int gdigs, a68_mp* store, int* has, int* size, a68_mp* out, char* err) {
  a68_mp zg = mp_nil(gdigs);
  mp_set(&zg, u, e, gdigs);
  if (mp_ln(&zg, &zg, gdigs, err)) { mp_free(&zg); return 1; }
  if (*has) mp_free(store);
  *store = zg; *has = 1; *size = gdigs;
  mp_move(out, &zg, gdigs);
  return 0;
}

/* `mp_ln_scale (z, digs)`: ln R, kept at the longest precision computed so far. */
int mp_ln_scale(a68_mp* z, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  MP_TEMP(zg, gdigs);
  if (cache.has_ls && gdigs <= cache.ls_size) mp_move(&zg, &cache.ls, gdigs);
  else TRY(ln_const(1.0, 1, gdigs, &cache.ls, &cache.has_ls, &cache.ls_size, &zg, err));
  return mp_shorten(z, digs, &zg, gdigs, err);
}

/* `mp_ln_10 (z, digs)`. */
int mp_ln_10(a68_mp* z, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  MP_TEMP(zg, gdigs);
  if (cache.has_l10 && gdigs <= cache.l10_size) mp_move(&zg, &cache.l10, gdigs);
  else TRY(ln_const(10.0, 0, gdigs, &cache.l10, &cache.has_l10, &cache.l10_size, &zg, err));
  return mp_shorten(z, digs, &zg, gdigs, err);
}

/* `logMp (z, x, digs)`. */
int mp_log(a68_mp* z, const a68_mp* x, int digs, char* err) {
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) { mp_set_pinf(z); return 0; }
  if (mp_is_minf(x)) { mp_set_nan(z); return 0; }
  if (mp_dig(x, 1) == 0.0) { mp_set_minf(z); return 0; }
  if (mp_dig(x, 1) < 0.0) { mp_set_nan(z); return 0; }
  TRY(mp_ln(z, x, digs, err));
  if (mp_is_nan(z)) { mp_set_nan(z); return 0; }
  {
    MP_TEMP(l10, digs);
    TRY(mp_ln_10(&l10, digs, err));
    return mp_div(z, z, &l10, digs, err);
  }
}

/* ------------------------------------------------------------------- π */

/* `fetchPi`. */
static void fetch_pi(a68_mp* api, mp_pi_mod md, int digs) {
  if (cache.has_pi) mp_move(api, &cache.pic[md], digs);
  else mp_set_nan(api);
}

/* `piMp (api, mod, digs)`. */
int mp_pi(a68_mp* api, mp_pi_mod md, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  int need = !cache.has_pi || gdigs > cache.pi_size;
  if (need) {
    cache_drop_pi();
    {
      MP_TEMP(pi_g, gdigs); MP_TEMP(two, gdigs); MP_TEMP(xg, gdigs); MP_TEMP(yg, gdigs);
      MP_TEMP(ug, gdigs); MP_TEMP(vg, gdigs); MP_TEMP(api1, digs);
      a68_mp c[8]; int k;
      two.d[1] = 2.0; xg.d[1] = 2.0;
      TRY(mp_sqrt(&xg, &xg, gdigs, err));
      TRY(mp_add(&pi_g, &xg, &two, gdigs, err));
      TRY(mp_sqrt(&yg, &xg, gdigs, err));
      for (;;) {
        TRY(mp_sqrt(&ug, &xg, gdigs, err));
        TRY(mp_rec(&vg, &ug, gdigs, err));
        TRY(mp_add(&ug, &ug, &vg, gdigs, err));
        TRY(mp_half(&xg, &ug, gdigs, err));
        TRY(mp_plus_one(&ug, &xg, gdigs, err));
        TRY(mp_plus_one(&vg, &yg, gdigs, err));
        TRY(mp_div(&ug, &ug, &vg, gdigs, err));
        TRY(mp_mul(&vg, &pi_g, &ug, gdigs, err));
        if (mp_same(&vg, &pi_g, gdigs)) break;
        mp_move(&pi_g, &vg, gdigs);
        TRY(mp_sqrt(&ug, &xg, gdigs, err));
        TRY(mp_rec(&vg, &ug, gdigs, err));
        TRY(mp_mul(&ug, &yg, &ug, gdigs, err));
        TRY(mp_add(&ug, &ug, &vg, gdigs, err));
        TRY(mp_plus_one(&vg, &yg, gdigs, err));
        TRY(mp_div(&yg, &ug, &vg, gdigs, err));
      }
      /* `api'`: the caller's number shortened to `digs`, from which the constants derive */
      mp_move(&api1, api, digs);
      TRY(mp_shorten(&api1, digs, &pi_g, gdigs, err));
      for (k = 0; k < 8; k++) c[k] = mp_nil(digs);
      mp_move(&c[MP_PI], &api1, digs);
      TRY(mp_half(&c[MP_HALF_PI], &api1, digs, err));
      TRY(mp_sqrt(&c[MP_SQRT_PI], &api1, digs, err));
      TRY(mp_ln(&c[MP_LN_PI], &api1, digs, err));
      TRY(mp_mul_digit(&c[MP_TWO_PI], &api1, 2, digs, err));
      TRY(mp_sqrt(&c[MP_SQRT_TWO_PI], &c[MP_TWO_PI], digs, err));
      TRY(mp_div_digit(&c[MP_PI_OVER_180], &api1, 180, digs, err));
      TRY(mp_rec(&c[MP_180_OVER_PI], &c[MP_PI_OVER_180], digs, err));
      for (k = 0; k < 8; k++) cache.pic[k] = c[k];
      cache.has_pi = 1; cache.pi_size = gdigs;
      mp_move(api, &api1, digs);
    }
  }
  fetch_pi(api, md, digs);
  return 0;
}

/* --------------------------------------------------------- hyperbolic functions */

/* `hypMp (sh, ch, z, digs)`. */
static int hyp_mp(a68_mp* sh, a68_mp* ch, const a68_mp* z, int digs, char* err) {
  MP_TEMP(zg, digs); MP_TEMP(xg, digs); MP_TEMP(yg, digs);
  mp_move(&zg, z, digs);
  TRY(mp_exp(&xg, &zg, digs, err));
  TRY(mp_rec(&yg, &xg, digs, err));
  TRY(mp_add(ch, &xg, &yg, digs, err));
  if ((mp_dig(&xg, 1) == 1.0 && mp_dig(&xg, 2) == 0.0) || (mp_dig(&yg, 1) == 1.0 && mp_dig(&yg, 2) == 0.0)) {
    TRY(mp_expm1(&xg, &zg, digs, err));
    mp_negate1(&zg);
    TRY(mp_expm1(&yg, &zg, digs, err));
  }
  TRY(mp_sub(sh, &xg, &yg, digs, err));
  TRY(mp_half(sh, sh, digs, err));
  TRY(mp_half(ch, ch, digs, err));
  return 0;
}

int mp_sinh(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  MP_TEMP(s, gdigs); MP_TEMP(c, gdigs); MP_TEMP(xg, gdigs);
  TRY(mp_catch_nan(x, err));
  len_into(&xg, x, digs, gdigs);
  TRY(hyp_mp(&s, &c, &xg, gdigs, err));
  return mp_shorten(z, digs, &s, gdigs, err);
}

int mp_cosh(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  MP_TEMP(s, gdigs); MP_TEMP(c, gdigs); MP_TEMP(xg, gdigs);
  TRY(mp_catch_nan(x, err));
  len_into(&xg, x, digs, gdigs);
  TRY(hyp_mp(&s, &c, &xg, gdigs, err));
  return mp_shorten(z, digs, &c, gdigs, err);
}

int mp_tanh(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  MP_TEMP(s, gdigs); MP_TEMP(c, gdigs); MP_TEMP(xg, gdigs);
  TRY(mp_catch_nan(x, err));
  len_into(&xg, x, digs, gdigs);
  TRY(hyp_mp(&s, &c, &xg, gdigs, err));
  TRY(mp_div(&c, &s, &c, gdigs, err));
  return mp_shorten(z, digs, &c, gdigs, err);
}

int mp_asinh(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int gdigs;
  TRY(mp_catch_nan(x, err));
  if (mp_is_zero(x)) { mp_set_zero(z, digs); return 0; }
  gdigs = x->ex >= -1 ? digs + MP_GUARDS : 2 * (digs + MP_GUARDS);
  {
    MP_TEMP(xg, gdigs); MP_TEMP(zg, gdigs); MP_TEMP(yg, gdigs); MP_TEMP(one, gdigs);
    len_into(&xg, x, digs, gdigs);
    mp_set_one(&one, gdigs);
    TRY(mp_mul(&zg, &xg, &xg, gdigs, err));
    TRY(mp_add(&yg, &zg, &one, gdigs, err));
    TRY(mp_sqrt(&yg, &yg, gdigs, err));
    TRY(mp_add(&yg, &yg, &xg, gdigs, err));
    TRY(mp_ln(&zg, &yg, gdigs, err));
    if (mp_is_zero(&zg)) { mp_move(z, x, digs); return 0; }
    return mp_shorten(z, digs, &zg, gdigs, err);
  }
}

int mp_acosh(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int gdigs = (mp_dig(x, 1) == 1.0 && mp_dig(x, 2) == 0.0) ? 2 * (digs + MP_GUARDS) : digs + MP_GUARDS;
  MP_TEMP(xg, gdigs); MP_TEMP(zg, gdigs); MP_TEMP(yg, gdigs); MP_TEMP(one, gdigs);
  len_into(&xg, x, digs, gdigs);
  mp_set_one(&one, gdigs);
  TRY(mp_mul(&zg, &xg, &xg, gdigs, err));
  TRY(mp_sub(&yg, &zg, &one, gdigs, err));
  TRY(mp_sqrt(&yg, &yg, gdigs, err));
  TRY(mp_add(&yg, &yg, &xg, gdigs, err));
  TRY(mp_ln(&zg, &yg, gdigs, err));
  return mp_shorten(z, digs, &zg, gdigs, err);
}

int mp_atanh(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  MP_TEMP(xg, gdigs); MP_TEMP(yg, gdigs); MP_TEMP(zg, gdigs);
  TRY(mp_catch_nan(x, err));
  len_into(&xg, x, digs, gdigs);
  mp_set_one(&yg, gdigs);
  TRY(mp_add(&zg, &yg, &xg, gdigs, err));
  TRY(mp_sub(&yg, &yg, &xg, gdigs, err));
  TRY(mp_div(&yg, &zg, &yg, gdigs, err));
  TRY(mp_ln(&zg, &yg, gdigs, err));
  TRY(mp_half(&zg, &zg, gdigs, err));
  return mp_shorten(z, digs, &zg, gdigs, err);
}

/* ----------------------------------------------------------- circular functions */

/* `sinMp (z, x, digs)`. */
int mp_sin(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int gdigs = digs + MP_GUARDS, neg, flip, m = 0, reduce, k, even, iter;
  int64_t n = 9;
  if (!mp_is_finite(x)) { mp_set_nan(z); return 0; }
  {
    MP_TEMP(pi, gdigs); MP_TEMP(tpi, gdigs); MP_TEMP(hpi, gdigs); MP_TEMP(xg, gdigs);
    MP_TEMP(tmp, gdigs); MP_TEMP(sqr, gdigs); MP_TEMP(pwr, gdigs); MP_TEMP(zg, gdigs); MP_TEMP(fac, gdigs);
    TRY(mp_pi(&pi, MP_PI, gdigs, err));
    TRY(mp_pi(&tpi, MP_TWO_PI, gdigs, err));
    TRY(mp_pi(&hpi, MP_HALF_PI, gdigs, err));
    len_into(&xg, x, digs, gdigs);
    TRY(mp_mod(&xg, &xg, &tpi, gdigs, err));
    neg = mp_dig(&xg, 1) < 0.0;
    if (neg) mp_negate1(&xg);
    TRY(mp_sub(&tmp, &xg, &pi, gdigs, err));
    flip = mp_dig(&tmp, 1) > 0.0;
    if (flip) TRY(mp_sub(&xg, &xg, &pi, gdigs, err));
    TRY(mp_sub(&tmp, &xg, &hpi, gdigs, err));
    if (mp_dig(&tmp, 1) > 0.0) TRY(mp_sub(&xg, &pi, &xg, gdigs, err));
    for (;;) {
      TRY(mp_must_reduce(&xg, gdigs, &reduce, err));
      if (!reduce) break;
      m++;
      TRY(mp_div_digit(&xg, &xg, 3, gdigs, err));
    }
    TRY(mp_mul(&sqr, &xg, &xg, gdigs, err));
    TRY(mp_mul(&pwr, &sqr, &xg, gdigs, err));
    mp_move(&zg, &xg, gdigs);
    TRY(mp_div_digit(&tmp, &pwr, 6, gdigs, err));
    TRY(mp_sub(&zg, &zg, &tmp, gdigs, err));
    TRY(mp_mul(&pwr, &pwr, &sqr, gdigs, err));
    TRY(mp_div_digit(&tmp, &pwr, 120, gdigs, err));
    TRY(mp_add(&zg, &zg, &tmp, gdigs, err));
    TRY(mp_mul(&pwr, &pwr, &sqr, gdigs, err));
    TRY(mp_div_digit(&tmp, &pwr, 5040, gdigs, err));
    TRY(mp_sub(&zg, &zg, &tmp, gdigs, err));
    TRY(mp_mul(&pwr, &pwr, &sqr, gdigs, err));
    mp_set(&fac, 362880.0, 0, gdigs);
    even = 1;
    iter = mp_dig(&pwr, 1) != 0.0;
    while (iter) {
      TRY(mp_div(&tmp, &pwr, &fac, gdigs, err));
      if (tmp.ex <= zg.ex - gdigs) iter = 0;
      else {
        if (even) { TRY(mp_add(&zg, &zg, &tmp, gdigs, err)); even = 0; }
        else { TRY(mp_sub(&zg, &zg, &tmp, gdigs, err)); even = 1; }
        TRY(mp_mul(&pwr, &pwr, &sqr, gdigs, err));
        n++;
        TRY(mp_mul_digit(&fac, &fac, n, gdigs, err));
        n++;
        TRY(mp_mul_digit(&fac, &fac, n, gdigs, err));
      }
    }
    mp_set(&fac, 3.0, 0, gdigs);
    for (k = 0; k < m; k++) {
      TRY(mp_mul(&pwr, &zg, &zg, gdigs, err));
      TRY(mp_mul_digit(&pwr, &pwr, 4, gdigs, err));
      TRY(mp_sub(&pwr, &fac, &pwr, gdigs, err));
      TRY(mp_mul(&zg, &pwr, &zg, gdigs, err));
    }
    TRY(mp_shorten(z, digs, &zg, gdigs, err));
  }
  if (neg != flip) mp_negate1(z);
  return 0;
}

/* `atanMp (z, x, digs)`. */
int mp_atan(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int gdigs = digs + MP_GUARDS, neg, flip;
  TRY(mp_catch_nan(x, err));
  if (mp_is_pinf(x)) return mp_pi(z, MP_HALF_PI, digs, err);
  if (mp_is_minf(x)) { TRY(mp_pi(z, MP_HALF_PI, digs, err)); mp_negate1(z); return 0; }
  if (mp_dig(x, 1) == 0.0) { mp_set_zero(z, digs); return 0; }
  {
    MP_TEMP(xg, gdigs); MP_TEMP(zg, gdigs);
    len_into(&xg, x, digs, gdigs);
    neg = mp_dig(&xg, 1) < 0.0;
    if (neg) mp_negate1(&xg);
    flip = ((xg.ex > 0) || (xg.ex == 0 && mp_dig(&xg, 1) > 1.0)) && mp_dig(&xg, 1) != 0.0;
    if (flip) TRY(mp_rec(&xg, &xg, gdigs, err));
    if (xg.ex < -1 || (xg.ex == -1 && mp_dig(&xg, 1) < R / 100.0)) {
      MP_TEMP(sqr, gdigs); MP_TEMP(pwr, gdigs); MP_TEMP(tmp, gdigs);
      int64_t n = 3; int even = 0, iter;
      TRY(mp_mul(&sqr, &xg, &xg, gdigs, err));
      TRY(mp_mul(&pwr, &sqr, &xg, gdigs, err));
      mp_move(&zg, &xg, gdigs);
      iter = mp_dig(&pwr, 1) != 0.0;
      while (iter) {
        TRY(mp_div_digit(&tmp, &pwr, n, gdigs, err));
        if (tmp.ex <= zg.ex - gdigs) iter = 0;
        else {
          if (even) { TRY(mp_add(&zg, &zg, &tmp, gdigs, err)); even = 0; }
          else { TRY(mp_sub(&zg, &zg, &tmp, gdigs, err)); even = 1; }
          TRY(mp_mul(&pwr, &pwr, &sqr, gdigs, err));
          n += 2;
        }
      }
    } else {
      MP_TEMP(sns, gdigs); MP_TEMP(cns, gdigs); MP_TEMP(tmp, gdigs);
      double xd; int decimals = DOUBLE_ACCURACY;
      TRY(mp_to_double(&xg, gdigs, &xd, err));
      TRY(mp_real_to_mp(&zg, atan(xd), gdigs, err));
      for (;;) {
        int hdigs;
        decimals *= 2;
        hdigs = 1 + decimals / MP_LOG_RADIX;
        if (hdigs > gdigs) hdigs = gdigs;
        TRY(mp_sin(&sns, &zg, hdigs, err));
        TRY(mp_mul(&tmp, &sns, &sns, hdigs, err));
        TRY(mp_one_minus(&tmp, &tmp, hdigs, err));
        TRY(mp_sqrt(&cns, &tmp, hdigs, err));
        TRY(mp_mul(&tmp, &xg, &cns, hdigs, err));
        TRY(mp_sub(&tmp, &sns, &tmp, hdigs, err));
        TRY(mp_mul(&tmp, &tmp, &cns, hdigs, err));
        TRY(mp_sub(&zg, &zg, &tmp, hdigs, err));
        if (!(decimals < gdigs * MP_LOG_RADIX)) break;
      }
    }
    if (flip) {
      MP_TEMP(hpi, gdigs);
      TRY(mp_pi(&hpi, MP_HALF_PI, gdigs, err));
      TRY(mp_sub(&zg, &hpi, &zg, gdigs, err));
    }
    TRY(mp_shorten(z, digs, &zg, gdigs, err));
  }
  if (neg) mp_negate1(z);
  return 0;
}

/* `cosMp (z, x, digs)`: `sin (π/2 - (x mod 2π))`. */
int mp_cos(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  if (!mp_is_finite(x)) { mp_set_nan(z); return 0; }
  {
    MP_TEMP(hpi, gdigs); MP_TEMP(tpi, gdigs); MP_TEMP(xg, gdigs); MP_TEMP(y, digs);
    TRY(mp_pi(&hpi, MP_HALF_PI, gdigs, err));
    TRY(mp_pi(&tpi, MP_TWO_PI, gdigs, err));
    len_into(&xg, x, digs, gdigs);
    TRY(mp_mod(&xg, &xg, &tpi, gdigs, err));
    TRY(mp_sub(&xg, &hpi, &xg, gdigs, err));
    TRY(mp_shorten(&y, digs, &xg, gdigs, err));
    return mp_sin(z, &y, digs, err);
  }
}

/* `tanMp` and `cotMp`: `sin x / sqrt (1 - sin² x)` with the sign from `x mod π`,
   dividing the other way for the cotangent. */
static int tan_cot(a68_mp* z, const a68_mp* x, int digs, int cot, char* err) {
  int gdigs = digs + MP_GUARDS, neg;
  if (cot) TRY(mp_catch_nan(x, err));
  else if (!mp_is_finite(x)) { mp_set_nan(z); return 0; }
  {
    MP_TEMP(pi, gdigs); MP_TEMP(hpi, gdigs); MP_TEMP(xg, gdigs); MP_TEMP(yg, gdigs);
    MP_TEMP(x1, digs); MP_TEMP(sns, digs); MP_TEMP(cns, digs);
    TRY(mp_pi(&pi, MP_PI, gdigs, err));
    TRY(mp_pi(&hpi, MP_HALF_PI, gdigs, err));
    len_into(&xg, x, digs, gdigs);
    TRY(mp_mod(&xg, &xg, &pi, gdigs, err));
    if (mp_dig(&xg, 1) >= 0.0) {
      TRY(mp_sub(&yg, &xg, &hpi, gdigs, err));
      neg = mp_dig(&yg, 1) > 0.0;
    } else {
      TRY(mp_add(&yg, &xg, &hpi, gdigs, err));
      neg = mp_dig(&yg, 1) < 0.0;
    }
    /* `x'`: the argument with the reduced digits (the Lean rebinds `x`; `z` keeps its own) */
    mp_move(&x1, x, digs);
    TRY(mp_shorten(&x1, digs, &xg, gdigs, err));
    TRY(mp_sin(&sns, &x1, digs, err));
    TRY(mp_mul(&cns, &sns, &sns, digs, err));
    TRY(mp_one_minus(&cns, &cns, digs, err));
    TRY(mp_sqrt(&cns, &cns, digs, err));
    if (cot) TRY(mp_div(z, &cns, &sns, digs, err));
    else TRY(mp_div(z, &sns, &cns, digs, err));
  }
  if (mp_is_nan(z)) { mp_set_nan(z); return 0; }
  if (neg) mp_negate1(z);
  return 0;
}

int mp_tan(a68_mp* z, const a68_mp* x, int digs, char* err) { return tan_cot(z, x, digs, 0, err); }
int mp_cot(a68_mp* z, const a68_mp* x, int digs, char* err) { return tan_cot(z, x, digs, 1, err); }

/* `asinMp (z, x, digs)`. */
int mp_asin(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  if (!mp_is_finite(x)) { mp_set_nan(z); return 0; }
  {
    MP_TEMP(xg, gdigs); MP_TEMP(zg, gdigs); MP_TEMP(y, digs);
    len_into(&xg, x, digs, gdigs);
    TRY(mp_mul(&zg, &xg, &xg, gdigs, err));
    TRY(mp_one_minus(&zg, &zg, gdigs, err));
    TRY(mp_sqrt(&zg, &zg, digs, err));
    if (mp_is_nan(&zg)) { mp_set_nan(z); return 0; }
    if (mp_dig(&zg, 1) == 0.0) {
      TRY(mp_pi(z, MP_HALF_PI, digs, err));
      if (mp_dig(&xg, 1) < 0.0) mp_negate1(z);
      return 0;
    }
    TRY(mp_div(&xg, &xg, &zg, gdigs, err));
    if (mp_is_nan(&xg)) { mp_set_nan(z); return 0; }
    TRY(mp_shorten(&y, digs, &xg, gdigs, err));
    return mp_atan(z, &y, digs, err);
  }
}

/* `acosMp (z, x, digs)`. */
int mp_acos(a68_mp* z, const a68_mp* x, int digs, char* err) {
  int gdigs = digs + MP_GUARDS, neg;
  if (!mp_is_finite(x)) { mp_set_nan(z); return 0; }
  neg = mp_dig(x, 1) < 0.0;
  if (mp_dig(x, 1) == 0.0) return mp_pi(z, MP_HALF_PI, digs, err);
  {
    MP_TEMP(xg, gdigs); MP_TEMP(zg, gdigs); MP_TEMP(y, digs);
    len_into(&xg, x, digs, gdigs);
    TRY(mp_mul(&zg, &xg, &xg, gdigs, err));
    TRY(mp_one_minus(&zg, &zg, gdigs, err));
    TRY(mp_sqrt(&zg, &zg, digs, err));
    if (mp_is_nan(&zg)) { mp_set_nan(z); return 0; }
    TRY(mp_div(&xg, &zg, &xg, gdigs, err));
    if (mp_is_nan(&xg)) { mp_set_nan(z); return 0; }
    TRY(mp_shorten(&y, digs, &xg, gdigs, err));
    TRY(mp_atan(z, &y, digs, err));
    if (neg) {
      TRY(mp_pi(&y, MP_PI, digs, err));
      TRY(mp_add(z, z, &y, digs, err));
    }
  }
  return 0;
}

/* `atan2Mp (z, x, y, digs)`: `z` receives the angle of the point `(x, y)`. */
int mp_atan2(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err) {
  int flip;
  if (mp_dig(x, 1) == 0.0 && mp_dig(y, 1) == 0.0) { mp_set_nan(z); return 0; }
  flip = mp_dig(y, 1) < 0.0;
  {
    MP_TEMP(ya, y->digs); MP_TEMP(xa, x->digs);
    mp_move(&ya, y, y->digs); ya.d[1] = fabs(ya.d[1]);
    if (mp_is_zero(x)) {
      TRY(mp_pi(z, MP_HALF_PI, digs, err));
    } else {
      int flop = mp_dig(x, 1) <= 0.0;
      mp_move(&xa, x, x->digs); xa.d[1] = fabs(xa.d[1]);
      TRY(mp_div(z, &ya, &xa, digs, err));
      TRY(mp_atan(z, z, digs, err));
      if (flop) {
        MP_TEMP(t, digs);
        TRY(mp_pi(&t, MP_PI, digs, err));
        TRY(mp_sub(z, &t, z, digs, err));
      }
    }
  }
  if (flip) mp_negate1(z);
  return 0;
}

/* `powMp (z, x, y, digs)`: `exp (y · ln x)`. */
int mp_pow(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err) {
  TRY(mp_catch_nan(x, err)); TRY(mp_catch_nan(y, err));
  TRY(mp_ln(z, x, digs, err));
  if (mp_is_nan(z)) { strncpy(err, "invalid argument", MP_ERR_LEN); return 1; }
  TRY(mp_mul(z, y, z, digs, err));
  return mp_exp(z, z, digs, err);
}

/* `hypotMp (z, x, y, digs)`. */
int mp_hypot(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err) {
  MP_TEMP(u, digs); MP_TEMP(v, digs); MP_TEMP(t, digs);
  TRY(mp_catch_nan(x, err)); TRY(mp_catch_nan(y, err));
  mp_move(&u, x, digs); u.d[1] = fabs(u.d[1]);
  mp_move(&v, y, digs); v.d[1] = fabs(v.d[1]);
  if (mp_is_zero(&u)) { mp_move(z, &v, digs); return 0; }
  if (mp_is_zero(&v)) { mp_move(z, &u, digs); return 0; }
  mp_set_one(&t, digs);
  TRY(mp_sub(z, &u, &v, digs, err));
  if (mp_dig(z, 1) > 0.0) {
    TRY(mp_div(z, &v, &u, digs, err));
    TRY(mp_mul(z, z, z, digs, err));
    TRY(mp_add(z, &t, z, digs, err));
    TRY(mp_sqrt(z, z, digs, err));
    return mp_mul(z, &u, z, digs, err);
  } else {
    TRY(mp_div(z, &u, &v, digs, err));
    TRY(mp_mul(z, z, z, digs, err));
    TRY(mp_add(z, &t, z, digs, err));
    TRY(mp_sqrt(z, z, digs, err));
    return mp_mul(z, &v, z, digs, err);
  }
}

/* ---------------------------------------------- the degree and π-scaled variants */

/* `recOf f`. */
static int rec_of(mp_fn f, a68_mp* z, const a68_mp* x, int digs, char* err) {
  TRY(f(z, x, digs, err));
  return mp_rec(z, z, digs, err);
}

/* `viaPiOver180 f`. */
static int via_pi_over_180(mp_fn f, a68_mp* z, const a68_mp* x, int digs, char* err) {
  MP_TEMP(fct, digs); MP_TEMP(g, digs);
  TRY(mp_catch_nan(x, err));
  TRY(mp_pi(&fct, MP_PI_OVER_180, digs, err));
  TRY(mp_mul(&g, x, &fct, digs, err));
  return f(z, &g, digs, err);
}

/* `times180OverPi f`. */
static int times_180_over_pi(mp_fn f, a68_mp* z, const a68_mp* x, int digs, char* err) {
  MP_TEMP(fr, digs); MP_TEMP(g, digs);
  TRY(mp_catch_nan(x, err));
  TRY(f(&fr, x, digs, err));
  TRY(mp_pi(&g, MP_180_OVER_PI, digs, err));
  return mp_mul(z, &fr, &g, digs, err);
}

int mp_csc(a68_mp* z, const a68_mp* x, int digs, char* err) { return rec_of(mp_sin, z, x, digs, err); }
int mp_sec(a68_mp* z, const a68_mp* x, int digs, char* err) { return rec_of(mp_cos, z, x, digs, err); }

int mp_arccsc(a68_mp* z, const a68_mp* x, int digs, char* err) {
  TRY(mp_rec(z, x, digs, err));
  return mp_asin(z, z, digs, err);
}

int mp_arcsec(a68_mp* z, const a68_mp* x, int digs, char* err) {
  TRY(mp_rec(z, x, digs, err));
  return mp_acos(z, z, digs, err);
}

int mp_arccot(a68_mp* z, const a68_mp* x, int digs, char* err) {
  MP_TEMP(f, digs);
  TRY(mp_catch_nan(x, err));
  TRY(mp_rec(&f, x, digs, err));
  return mp_atan(z, &f, digs, err);
}

int mp_sindg(a68_mp* z, const a68_mp* x, int digs, char* err) { return via_pi_over_180(mp_sin, z, x, digs, err); }
int mp_cosdg(a68_mp* z, const a68_mp* x, int digs, char* err) { return via_pi_over_180(mp_cos, z, x, digs, err); }
int mp_tandg(a68_mp* z, const a68_mp* x, int digs, char* err) { return via_pi_over_180(mp_tan, z, x, digs, err); }
int mp_cotdg(a68_mp* z, const a68_mp* x, int digs, char* err) { return via_pi_over_180(mp_cot, z, x, digs, err); }
int mp_cscdg(a68_mp* z, const a68_mp* x, int digs, char* err) { return rec_of(mp_sindg, z, x, digs, err); }
/* a68g does not take the reciprocal for `secdg` */
int mp_secdg(a68_mp* z, const a68_mp* x, int digs, char* err) { return via_pi_over_180(mp_cos, z, x, digs, err); }
int mp_arcsindg(a68_mp* z, const a68_mp* x, int digs, char* err) { return times_180_over_pi(mp_asin, z, x, digs, err); }
int mp_arccosdg(a68_mp* z, const a68_mp* x, int digs, char* err) { return times_180_over_pi(mp_acos, z, x, digs, err); }
int mp_arctandg(a68_mp* z, const a68_mp* x, int digs, char* err) { return times_180_over_pi(mp_atan, z, x, digs, err); }
int mp_arccotdg(a68_mp* z, const a68_mp* x, int digs, char* err) { return times_180_over_pi(mp_arccot, z, x, digs, err); }

int mp_arccscdg(a68_mp* z, const a68_mp* x, int digs, char* err) {
  TRY(mp_rec(z, x, digs, err));
  return times_180_over_pi(mp_asin, z, z, digs, err);
}

int mp_arcsecdg(a68_mp* z, const a68_mp* x, int digs, char* err) {
  TRY(mp_rec(z, x, digs, err));
  return times_180_over_pi(mp_acos, z, z, digs, err);
}

int mp_cas(a68_mp* z, const a68_mp* x, int digs, char* err) {
  MP_TEMP(c, digs); MP_TEMP(s, digs);
  if (!mp_is_finite(x)) { mp_set_nan(z); return 0; }
  TRY(mp_cos(&c, x, digs, err));
  TRY(mp_sin(&s, x, digs, err));
  return mp_add(z, &c, &s, digs, err);
}

/* ------------------------------------------------------------- LONG COMPLEX */

/* `cmulMp (a, b, c, d, digs)`: `(a + bi)(c + di)` at two guard digits. */
int mp_cmul(a68_mp* a, a68_mp* b, const a68_mp* c, const a68_mp* d, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  MP_TEMP(la, gdigs); MP_TEMP(lb, gdigs); MP_TEMP(lc, gdigs); MP_TEMP(ld, gdigs);
  MP_TEMP(ac, gdigs); MP_TEMP(bd, gdigs); MP_TEMP(ad, gdigs); MP_TEMP(bc, gdigs);
  len_into(&la, a, digs, gdigs); len_into(&lb, b, digs, gdigs);
  len_into(&lc, c, digs, gdigs); len_into(&ld, d, digs, gdigs);
  TRY(mp_mul(&ac, &la, &lc, gdigs, err));
  TRY(mp_mul(&bd, &lb, &ld, gdigs, err));
  TRY(mp_mul(&ad, &la, &ld, gdigs, err));
  TRY(mp_mul(&bc, &lb, &lc, gdigs, err));
  TRY(mp_sub(&la, &ac, &bd, gdigs, err));
  TRY(mp_add(&lb, &ad, &bc, gdigs, err));
  TRY(mp_shorten(a, digs, &la, gdigs, err));
  return mp_shorten(b, digs, &lb, gdigs, err);
}

/* `cdivMp (a, b, c, d, digs)`: `(a + bi) / (c + di)`, dividing by the larger of |c|, |d|. */
int mp_cdiv(a68_mp* a, a68_mp* b, const a68_mp* c, const a68_mp* d, int digs, char* err) {
  MP_TEMP(q, digs); MP_TEMP(r, digs); MP_TEMP(c1, digs); MP_TEMP(d1, digs);
  if (mp_dig(c, 1) == 0.0 && mp_dig(d, 1) == 0.0) { mp_set_nan(a); mp_set_nan(b); return 0; }
  mp_move(&q, c, digs); mp_move(&r, d, digs);
  q.d[1] = fabs(q.d[1]); r.d[1] = fabs(r.d[1]);
  TRY(mp_sub(&q, &q, &r, digs, err));
  if (mp_dig(&q, 1) >= 0.0) {
    TRY(mp_div(&q, d, c, digs, err));
    if (mp_is_nan(&q)) { mp_set_nan(a); mp_set_nan(b); return 0; }
    TRY(mp_mul(&r, d, &q, digs, err));
    TRY(mp_add(&r, &r, c, digs, err));
    TRY(mp_mul(&c1, b, &q, digs, err));
    TRY(mp_add(&c1, &c1, a, digs, err));
    TRY(mp_div(&c1, &c1, &r, digs, err));
    TRY(mp_mul(&d1, a, &q, digs, err));
    TRY(mp_sub(&d1, b, &d1, digs, err));
    TRY(mp_div(&d1, &d1, &r, digs, err));
  } else {
    TRY(mp_div(&q, c, d, digs, err));
    if (mp_is_nan(&q)) { mp_set_nan(a); mp_set_nan(b); return 0; }
    TRY(mp_mul(&r, c, &q, digs, err));
    TRY(mp_add(&r, &r, d, digs, err));
    TRY(mp_mul(&c1, a, &q, digs, err));
    TRY(mp_add(&c1, &c1, b, digs, err));
    TRY(mp_div(&c1, &c1, &r, digs, err));
    TRY(mp_mul(&d1, b, &q, digs, err));
    TRY(mp_sub(&d1, &d1, a, digs, err));
    TRY(mp_div(&d1, &d1, &r, digs, err));
  }
  mp_move(a, &c1, digs);
  mp_move(b, &d1, digs);
  return 0;
}

/* `mpComplPow`: `LONG COMPLEX ** INT` (`genie_pow_mp_complex_int`). */
int mp_cpow_int(a68_mp* re, a68_mp* im, int64_t j, int digs, char* err) {
  MP_TEMP(re_z, digs); MP_TEMP(im_z, digs); MP_TEMP(re_y, digs); MP_TEMP(im_y, digs);
  MP_TEMP(rea, digs); MP_TEMP(acc, digs);
  uint64_t jj = j < 0 ? (uint64_t) (-(j + 1)) + 1 : (uint64_t) j, expo = 1;
  re_z.d[1] = 1.0;
  mp_move(&re_y, re, digs); mp_move(&im_y, im, digs);
  while (expo <= jj) {
    if (expo & jj) {
      TRY(mp_mul(&acc, &im_z, &im_y, digs, err));
      TRY(mp_mul(&rea, &re_z, &re_y, digs, err));
      TRY(mp_sub(&rea, &rea, &acc, digs, err));
      TRY(mp_mul(&acc, &im_z, &re_y, digs, err));
      TRY(mp_mul(&im_z, &re_z, &im_y, digs, err));
      TRY(mp_add(&im_z, &im_z, &acc, digs, err));
      mp_move(&re_z, &rea, digs);
    }
    TRY(mp_mul(&acc, &im_y, &im_y, digs, err));
    TRY(mp_mul(&rea, &re_y, &re_y, digs, err));
    TRY(mp_sub(&rea, &rea, &acc, digs, err));
    TRY(mp_mul(&acc, &im_y, &re_y, digs, err));
    TRY(mp_mul(&im_y, &re_y, &im_y, digs, err));
    TRY(mp_add(&im_y, &im_y, &acc, digs, err));
    mp_move(&re_y, &rea, digs);
    if (expo > UINT64_MAX / 2) break;
    expo <<= 1;
  }
  if (j < 0) {
    MP_TEMP(one, digs); MP_TEMP(zero, digs);
    one.d[1] = 1.0;
    TRY(mp_cdiv(&one, &zero, &re_z, &im_z, digs, err));
    mp_move(re, &one, digs); mp_move(im, &zero, digs);
    return 0;
  }
  mp_move(re, &re_z, digs); mp_move(im, &im_z, digs);
  return 0;
}

/* `csqrtMp (r, i, digs)`. */
int mp_csqrt(a68_mp* r, a68_mp* i, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  MP_TEMP(re, gdigs); MP_TEMP(im, gdigs);
  len_into(&re, r, digs, gdigs); len_into(&im, i, digs, gdigs);
  if (mp_is_zero(&re) && mp_is_zero(&im)) {
    mp_set_zero(&re, gdigs);
    mp_set_zero(&im, gdigs);
  } else {
    MP_TEMP(c1, gdigs); MP_TEMP(x, gdigs); MP_TEMP(y, gdigs); MP_TEMP(w, gdigs);
    MP_TEMP(u, gdigs); MP_TEMP(v, gdigs); MP_TEMP(t, gdigs);
    c1.d[1] = 1.0;
    mp_move(&x, &re, gdigs); x.d[1] = fabs(x.d[1]);
    mp_move(&y, &im, gdigs); y.d[1] = fabs(y.d[1]);
    TRY(mp_sub(&w, &x, &y, gdigs, err));
    if (mp_dig(&w, 1) >= 0.0) {
      TRY(mp_div(&t, &y, &x, gdigs, err));
      TRY(mp_mul(&v, &t, &t, gdigs, err));
      TRY(mp_add(&u, &c1, &v, gdigs, err));
      TRY(mp_sqrt(&v, &u, gdigs, err));
      TRY(mp_add(&u, &c1, &v, gdigs, err));
      TRY(mp_half(&v, &u, gdigs, err));
      TRY(mp_sqrt(&u, &v, gdigs, err));
      TRY(mp_sqrt(&v, &x, gdigs, err));
      TRY(mp_mul(&w, &u, &v, gdigs, err));
    } else {
      TRY(mp_div(&t, &x, &y, gdigs, err));
      TRY(mp_mul(&v, &t, &t, gdigs, err));
      TRY(mp_add(&u, &c1, &v, gdigs, err));
      TRY(mp_sqrt(&v, &u, gdigs, err));
      TRY(mp_add(&u, &t, &v, gdigs, err));
      TRY(mp_half(&v, &u, gdigs, err));
      TRY(mp_sqrt(&u, &v, gdigs, err));
      TRY(mp_sqrt(&v, &y, gdigs, err));
      TRY(mp_mul(&w, &u, &v, gdigs, err));
    }
    if (mp_dig(&re, 1) >= 0.0) {
      mp_move(&re, &w, gdigs);
      TRY(mp_add(&u, &w, &w, gdigs, err));
      TRY(mp_div(&im, &im, &u, gdigs, err));
    } else {
      if (mp_dig(&im, 1) < 0.0) mp_negate1(&w);
      TRY(mp_add(&v, &w, &w, gdigs, err));
      TRY(mp_div(&re, &im, &v, gdigs, err));
      mp_move(&im, &w, gdigs);
    }
  }
  TRY(mp_shorten(r, digs, &re, gdigs, err));
  return mp_shorten(i, digs, &im, gdigs, err);
}

/* `cexpMp (r, i, digs)`. */
int mp_cexp(a68_mp* r, a68_mp* i, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  MP_TEMP(re, gdigs); MP_TEMP(im, gdigs); MP_TEMP(u, gdigs);
  len_into(&re, r, digs, gdigs); len_into(&im, i, digs, gdigs);
  if (mp_is_zero(&im)) {
    TRY(mp_exp(&re, &re, gdigs, err));
  } else {
    TRY(mp_exp(&u, &re, gdigs, err));
    TRY(mp_cos(&re, &im, gdigs, err));
    TRY(mp_sin(&im, &im, gdigs, err));
    TRY(mp_mul(&re, &re, &u, gdigs, err));
    TRY(mp_mul(&im, &im, &u, gdigs, err));
  }
  TRY(mp_shorten(r, digs, &re, gdigs, err));
  return mp_shorten(i, digs, &im, gdigs, err);
}

/* `clnMp (r, i, digs)`. */
int mp_cln(a68_mp* r, a68_mp* i, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  MP_TEMP(re, gdigs); MP_TEMP(im, gdigs); MP_TEMP(s, gdigs); MP_TEMP(t, gdigs);
  MP_TEMP(re1, gdigs); MP_TEMP(im1, gdigs); MP_TEMP(re2, gdigs); MP_TEMP(im2, gdigs);
  len_into(&re, r, digs, gdigs); len_into(&im, i, digs, gdigs);
  mp_move(&re1, &re, gdigs); mp_move(&im1, &im, gdigs);
  TRY(mp_hypot(&s, &re1, &im1, gdigs, err));
  mp_move(&re2, &re, gdigs); mp_move(&im2, &im, gdigs);
  TRY(mp_atan2(&t, &re2, &im2, gdigs, err));
  TRY(mp_ln(&re, &s, gdigs, err));
  mp_move(&im, &t, gdigs);
  TRY(mp_shorten(r, digs, &re, gdigs, err));
  return mp_shorten(i, digs, &im, gdigs, err);
}

/* `csinCosMp`: `csin_mp`, and `ccos_mp` with `cosine`. */
static int csin_cos(int cosine, a68_mp* r, a68_mp* i, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  MP_TEMP(re, gdigs); MP_TEMP(im, gdigs);
  len_into(&re, r, digs, gdigs); len_into(&im, i, digs, gdigs);
  if (mp_is_zero(&im)) {
    if (cosine) TRY(mp_cos(&re, &re, gdigs, err));
    else TRY(mp_sin(&re, &re, gdigs, err));
    mp_set_zero(&im, gdigs);
  } else {
    MP_TEMP(s, gdigs); MP_TEMP(c, gdigs); MP_TEMP(sh, gdigs); MP_TEMP(ch, gdigs);
    TRY(mp_sin(&s, &re, gdigs, err));
    TRY(mp_cos(&c, &re, gdigs, err));
    TRY(hyp_mp(&sh, &ch, &im, gdigs, err));
    if (cosine) {
      TRY(mp_mul(&re, &c, &ch, gdigs, err));
      mp_negate1(&sh);
      TRY(mp_mul(&im, &s, &sh, gdigs, err));
    } else {
      TRY(mp_mul(&re, &s, &ch, gdigs, err));
      TRY(mp_mul(&im, &c, &sh, gdigs, err));
    }
  }
  TRY(mp_shorten(r, digs, &re, gdigs, err));
  return mp_shorten(i, digs, &im, gdigs, err);
}

int mp_csin(a68_mp* r, a68_mp* i, int digs, char* err) { return csin_cos(0, r, i, digs, err); }
int mp_ccos(a68_mp* r, a68_mp* i, int digs, char* err) { return csin_cos(1, r, i, digs, err); }

/* `ctanMp (r, i, digs)`: `csin / ccos` at the same precision. */
int mp_ctan(a68_mp* r, a68_mp* i, int digs, char* err) {
  MP_TEMP(su, digs); MP_TEMP(sv, digs); MP_TEMP(cu, digs); MP_TEMP(cv, digs);
  MP_TEMP(s, digs); MP_TEMP(t, digs);
  mp_move(&su, r, digs); mp_move(&sv, i, digs);
  TRY(csin_cos(0, &su, &sv, digs, err));
  mp_move(&cu, r, digs); mp_move(&cv, i, digs);
  TRY(csin_cos(1, &cu, &cv, digs, err));
  mp_move(&s, &su, digs); mp_move(&t, &sv, digs);
  TRY(mp_cdiv(&s, &t, &cu, &cv, digs, err));
  mp_move(r, &s, digs); mp_move(i, &t, digs);
  return 0;
}

/* `casinAcosMp`: `casin_mp`, and `cacos_mp` with `arccos`. */
static int casin_acos(int arccos, a68_mp* r, a68_mp* i, int digs, char* err) {
  int gdigs = digs + MP_GUARDS, negim, flip_im;
  MP_TEMP(re, gdigs); MP_TEMP(im, gdigs); MP_TEMP(c1, gdigs); MP_TEMP(a, gdigs); MP_TEMP(b, gdigs);
  MP_TEMP(u, gdigs); MP_TEMP(v, gdigs);
  len_into(&re, r, digs, gdigs); len_into(&im, i, digs, gdigs);
  negim = mp_dig(&im, 1) < 0.0;
  c1.d[1] = 1.0;
  TRY(mp_add(&a, &re, &c1, gdigs, err));
  TRY(mp_sub(&b, &re, &c1, gdigs, err));
  TRY(mp_hypot(&u, &a, &im, gdigs, err));
  TRY(mp_hypot(&v, &b, &im, gdigs, err));
  TRY(mp_add(&a, &u, &v, gdigs, err));
  TRY(mp_half(&a, &a, gdigs, err));
  TRY(mp_sub(&b, &u, &v, gdigs, err));
  TRY(mp_half(&b, &b, gdigs, err));
  TRY(mp_mul(&u, &a, &a, gdigs, err));
  TRY(mp_sub(&u, &u, &c1, gdigs, err));
  TRY(mp_sqrt(&u, &u, gdigs, err));
  TRY(mp_add(&u, &a, &u, gdigs, err));
  TRY(mp_ln(&im, &u, gdigs, err));
  if (arccos) TRY(mp_acos(&re, &b, gdigs, err));
  else TRY(mp_asin(&re, &b, gdigs, err));
  flip_im = arccos ? !negim : negim;
  if (flip_im) mp_negate1(&im);
  TRY(mp_shorten(r, digs, &re, gdigs, err));
  return mp_shorten(i, digs, &im, gdigs, err);
}

int mp_casin(a68_mp* r, a68_mp* i, int digs, char* err) { return casin_acos(0, r, i, digs, err); }
int mp_cacos(a68_mp* r, a68_mp* i, int digs, char* err) { return casin_acos(1, r, i, digs, err); }

/* `catanMp (r, i, digs)`. */
int mp_catan(a68_mp* r, a68_mp* i, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  MP_TEMP(re, gdigs); MP_TEMP(im, gdigs); MP_TEMP(u, gdigs); MP_TEMP(v, gdigs);
  len_into(&re, r, digs, gdigs); len_into(&im, i, digs, gdigs);
  if (mp_is_zero(&im)) {
    TRY(mp_atan(&u, &re, gdigs, err));
    mp_set_zero(&v, gdigs);
  } else {
    MP_TEMP(c1, gdigs); MP_TEMP(a, gdigs); MP_TEMP(b, gdigs);
    c1.d[1] = 1.0;
    TRY(mp_add(&a, &im, &c1, gdigs, err));
    TRY(mp_sub(&b, &im, &c1, gdigs, err));
    TRY(mp_hypot(&u, &re, &a, gdigs, err));
    TRY(mp_hypot(&v, &re, &b, gdigs, err));
    TRY(mp_div(&u, &u, &v, gdigs, err));
    TRY(mp_ln(&v, &u, gdigs, err));
    TRY(mp_half(&v, &v, gdigs, err));
    TRY(mp_mul(&a, &re, &re, gdigs, err));
    TRY(mp_mul(&b, &im, &im, gdigs, err));
    TRY(mp_add(&a, &a, &b, gdigs, err));
    TRY(mp_sub(&u, &c1, &a, gdigs, err));
    if (mp_is_zero(&u)) {
      TRY(mp_pi(&u, MP_HALF_PI, gdigs, err));
    } else {
      int neg = mp_dig(&u, 1) < 0.0;
      TRY(mp_add(&a, &re, &re, gdigs, err));
      TRY(mp_div(&a, &a, &u, gdigs, err));
      TRY(mp_atan(&u, &a, gdigs, err));
      if (neg) {
        TRY(mp_pi(&a, MP_PI, gdigs, err));
        if (mp_dig(&re, 1) < 0.0) TRY(mp_sub(&u, &u, &a, gdigs, err));
        else TRY(mp_add(&u, &u, &a, gdigs, err));
      }
      TRY(mp_half(&u, &u, gdigs, err));
    }
  }
  TRY(mp_shorten(r, digs, &u, gdigs, err));
  return mp_shorten(i, digs, &v, gdigs, err);
}

/* `chypMp`: `csinh_mp`, `ccosh_mp`, `ctanh_mp`, `casinh_mp`, `cacosh_mp`, `catanh_mp` —
   the circular functions of `± i z`, multiplied back, as `mp-complex.c` composes them
   (`ctanh_mp` overwrites its intermediate result before the last multiplication, so it
   always yields 1). */
enum { CH_SINH, CH_COSH, CH_TANH, CH_ASINH, CH_ACOSH, CH_ATANH };

static int chyp(int which, a68_mp* r, a68_mp* i, int digs, char* err) {
  int gdigs = digs + MP_GUARDS;
  MP_TEMP(re, gdigs); MP_TEMP(im, gdigs); MP_TEMP(zero, gdigs); MP_TEMP(one, gdigs); MP_TEMP(minus_one, gdigs);
  len_into(&re, r, digs, gdigs); len_into(&im, i, digs, gdigs);
  mp_set_one(&one, gdigs);
  mp_set(&minus_one, -1.0, 0, gdigs);
  switch (which) {
    case CH_SINH:
      TRY(mp_cmul(&re, &im, &zero, &one, gdigs, err));
      TRY(csin_cos(0, &re, &im, gdigs, err));
      TRY(mp_cmul(&re, &im, &zero, &minus_one, gdigs, err));
      break;
    case CH_COSH:
      TRY(mp_cmul(&re, &im, &zero, &one, gdigs, err));
      TRY(csin_cos(1, &re, &im, gdigs, err));
      break;
    case CH_TANH:
      TRY(mp_cmul(&re, &im, &zero, &one, gdigs, err));
      TRY(mp_ctan(&re, &im, gdigs, err));
      mp_set_zero(&re, gdigs);
      mp_set(&im, -1.0, 0, gdigs);
      TRY(mp_cmul(&re, &im, &zero, &one, gdigs, err));
      break;
    case CH_ASINH:
      TRY(mp_cmul(&re, &im, &zero, &minus_one, gdigs, err));
      TRY(casin_acos(0, &re, &im, gdigs, err));
      TRY(mp_cmul(&re, &im, &zero, &one, gdigs, err));
      break;
    case CH_ACOSH:
      TRY(casin_acos(1, &re, &im, gdigs, err));
      TRY(mp_cmul(&re, &im, &zero, &one, gdigs, err));
      break;
    default:
      TRY(mp_cmul(&re, &im, &zero, &minus_one, gdigs, err));
      TRY(mp_catan(&re, &im, gdigs, err));
      TRY(mp_cmul(&re, &im, &zero, &one, gdigs, err));
      break;
  }
  TRY(mp_shorten(r, digs, &re, gdigs, err));
  return mp_shorten(i, digs, &im, gdigs, err);
}

int mp_csinh(a68_mp* r, a68_mp* i, int digs, char* err)  { return chyp(CH_SINH, r, i, digs, err); }
int mp_ccosh(a68_mp* r, a68_mp* i, int digs, char* err)  { return chyp(CH_COSH, r, i, digs, err); }
int mp_ctanh(a68_mp* r, a68_mp* i, int digs, char* err)  { return chyp(CH_TANH, r, i, digs, err); }
int mp_casinh(a68_mp* r, a68_mp* i, int digs, char* err) { return chyp(CH_ASINH, r, i, digs, err); }
int mp_cacosh(a68_mp* r, a68_mp* i, int digs, char* err) { return chyp(CH_ACOSH, r, i, digs, err); }
int mp_catanh(a68_mp* r, a68_mp* i, int digs, char* err) { return chyp(CH_ATANH, r, i, digs, err); }
