/* Algol 68 Genie's multi-precision arithmetic, digit for digit, in C.

   This is a transcription of A68/MP.lean (the kernel), A68/MPMath.lean (the elementary
   functions, π and LONG COMPLEX) and A68/MPFmt.lean (formatting), which model a68g's
   `mp.c`, `mp-math.c`, `mp-pi.c`, `mp-complex.c` and `transput-formatting.c`.  Every
   function names the Lean definition it transcribes; the Lean is the specification, and
   a differential test against the evaluator (`csrc/mp_test.c`) checks the transcription.

   Representation (`A68.MP.MP`): a number is a status word `st`, an exponent `ex` and
   digits in radix R = 10^7, `d[1] … d[digs]` (`d[0]` is unused and zero), denoting
   Σ d[k] · R^(ex - k + 1); only `d[1]` carries the sign.  Digits are C doubles holding
   integers, as in a68g: every scratch value stays below 2^53 by design, so the double
   arithmetic on them is exact; the one place a68g relies on rounding — the quotient-digit
   estimates of the division routines, compiled to fused multiply-adds — uses `fma()`.

   As in the Lean model, the array may be longer than the precision an operation uses:
   an operation on `digs` digits writes exactly the status, the exponent and the first
   `digs` digits of its destination and leaves the rest alone (a68g relies on stale guard
   digits), and a digit read past `digs` is zero (`MP.dig` is `getD … 0`).

   Every operation writes its destination in place; the destination may alias an operand
   (every routine reads its operands completely before it writes).  Operations that can
   fail in a68g (a NaN operand under strict maths, an exponent out of range, a truncation
   out of bounds) return a non-zero code and copy a68g's message into the caller's `err`
   buffer of MP_ERR_LEN bytes; on success they return 0 and leave `err` alone. */
#ifndef A68_MP_H
#define A68_MP_H

#include <stddef.h>
#include <stdint.h>
#include "a68rt.h"
#include "bigint.h"
#include "fmt.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct { uint32_t st; int64_t ex; int digs; double* d; } a68_mp;

/* `MP_RADIX`, `LOG_MP_RADIX`, `A68G_MP_GUARDS`, `LONG_MP_DIGITS`, the default
   `LONG LONG` digits and `MAX_MP_EXPONENT` (A68/MP.lean). */
#define MP_RADIX        10000000
#define MP_LOG_RADIX    7
#define MP_GUARDS       2
#define MP_LONG_DIGITS  7
#define MP_LONG_LONG_DIGITS 12
#define MP_MAX_EXPO     142857

/* Status bits (`a68g-masks.h`). */
#define MP_INIT 0x10u
#define MP_PINF 0x20u
#define MP_MINF 0x40u
#define MP_NAN  0x80u

/* Size of the error buffer every fallible function takes. */
#define MP_ERR_LEN 80

/* `widthToDigits`: digits of a `LONG LONG` mode after `PR precision n PR`. */
int mp_width_to_digits(int n);

/* ---- construction and inspection (`nil`, `lit`, `setMp`, `moveMp`, `lenMp` …) ---- */

a68_mp mp_nil(int digs);                            /* `nil digs`: a fresh zero */
a68_mp mp_lit(int digs, double u, int64_t e);       /* `lit digs u e` */
a68_mp mp_one(int digs);                            /* `one digs` */
a68_mp mp_copy(const a68_mp* x);                    /* the same digits, fresh storage */
a68_mp mp_len(const a68_mp* u, int digs, int gdigs);/* `lenMp u digs gdigs` */
void   mp_free(a68_mp* z);

double mp_dig(const a68_mp* z, int k);              /* `MP.dig`: 0 past the digits held */
void   mp_set_dig(a68_mp* z, int k, double v);      /* `MP.setDig` (grows the array) */
void   mp_set(a68_mp* z, double x, int64_t e, int digs);   /* `setMp` */
void   mp_set_zero(a68_mp* z, int digs);            /* `setZero` */
void   mp_set_one(a68_mp* z, int digs);             /* `setOne` */
void   mp_move(a68_mp* z, const a68_mp* x, int n);  /* `moveMp` */
void   mp_set_nan(a68_mp* z);
void   mp_set_pinf(a68_mp* z);
void   mp_set_minf(a68_mp* z);
void   mp_negate1(a68_mp* z);                       /* `MP.negate1` */

int mp_is_nan(const a68_mp* z);
int mp_is_pinf(const a68_mp* z);
int mp_is_minf(const a68_mp* z);
int mp_is_inf(const a68_mp* z);
int mp_is_finite(const a68_mp* z);                  /* `A68G_FINITE_MP` */
int mp_is_zero(const a68_mp* z);
int mp_is_plus(const a68_mp* z);
int mp_is_minus(const a68_mp* z);

int mp_check_exp(const a68_mp* z, char* err);       /* `checkExp` */
int mp_catch_nan(const a68_mp* x, char* err);       /* `catchNaN` */

/* ---- shortening and lengthening ---- */

int mp_shorten(a68_mp* z, int digs, const a68_mp* x, int digs_x, char* err);
int mp_lengthen(a68_mp* z, int digs_z, const a68_mp* x, int digs_x, char* err);

/* ---- arithmetic ---- */

int mp_add(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err);
int mp_sub(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err);
int mp_mul(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err);
int mp_div(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err);
int mp_half(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_tenth(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_mul_digit(a68_mp* z, const a68_mp* x, int64_t y, int digs, char* err);
int mp_div_digit(a68_mp* z, const a68_mp* x, int64_t y, int digs, char* err);
int mp_rec(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_trunc(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_over(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err);
int mp_over_digit(a68_mp* z, const a68_mp* x, int64_t y, int digs, char* err);
int mp_mod(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err);
int mp_round(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_entier(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_minus(a68_mp* x, char* err);                 /* `minusMp`, in place */
int mp_abs(a68_mp* x, char* err);                   /* `absMp`, in place */
int mp_minus_one(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_plus_one(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_one_minus(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_pow_int(a68_mp* z, const a68_mp* x, int64_t n, int digs, char* err);

/* ---- comparison: 1 or 0, or -1 with `err` set ---- */

int mp_eq(const a68_mp* x, const a68_mp* y, int digs, char* err);
int mp_ne(const a68_mp* x, const a68_mp* y, int digs, char* err);
int mp_lt(const a68_mp* x, const a68_mp* y, int digs, char* err);
int mp_le(const a68_mp* x, const a68_mp* y, int digs, char* err);
int mp_gt(const a68_mp* x, const a68_mp* y, int digs, char* err);
int mp_ge(const a68_mp* x, const a68_mp* y, int digs, char* err);

/* ---- conversions ---- */

int    mp_int_to_mp(a68_mp* z, int64_t k, int digs, char* err);   /* `intToMp` */
a68_mp mp_of_i64(int64_t k, int digs);                             /* `ofInt` */
/* A decimal integer with an optional sign, as the exact `intToMp` of its value; fails with
   "value out of bounds" when it needs more than `digs` digits. */
int    mp_of_dec_string(const char* s, size_t n, int digs, a68_mp* out, char* err);
/* `toIntTrunc`; returns 1 when the integer does not fit in 64 bits. */
int    mp_to_i64_trunc(const a68_mp* z, int64_t* out);
int    mp_is_int_of_digits(const a68_mp* z, int digs);             /* `isIntOfDigits` */
int    mp_to_int32(const a68_mp* z, int digs, int32_t* out, char* err);  /* `toInt32` */
int    mp_ten_up(a68_mp* z, int64_t n, int digs, char* err);       /* `tenUpMp` */
/* `stringToMp`: `z` (of at least `digs` digits) receives the value; `*valid` is 0 where
   a68g returns NaN (bad syntax or too many digits). */
int    mp_string_to_mp(a68_mp* z, const char* s, size_t n, int digs, int* valid, char* err);
int    mp_ten_up_real(int64_t expo, double* out, char* err);       /* `tenUpReal` */
int    mp_real_to_mp(a68_mp* z, double x, int digs, char* err);    /* `realToMp` */
int    mp_to_double(const a68_mp* z, int digs, double* out, char* err); /* `mpToReal` */

/* ---- elementary functions (mpmath.c) ---- */

typedef int (*mp_fn)(a68_mp* z, const a68_mp* x, int digs, char* err);

int mp_must_reduce(const a68_mp* z, int digs, int* out, char* err);  /* `mustReduce` */
int mp_same(const a68_mp* x, const a68_mp* y, int digs);              /* `sameMp` */

int mp_sqrt(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_curt(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_exp(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_expm1(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_ln(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_log(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_ln_scale(a68_mp* z, int digs, char* err);
int mp_ln_10(a68_mp* z, int digs, char* err);
int mp_sin(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_cos(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_tan(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_cot(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_asin(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_acos(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_atan(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_sinh(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_cosh(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_tanh(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_asinh(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_acosh(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_atanh(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_csc(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_sec(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_arccsc(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_arcsec(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_arccot(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_sindg(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_cosdg(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_tandg(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_cotdg(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_cscdg(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_secdg(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_arcsindg(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_arccosdg(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_arctandg(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_arccotdg(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_arccscdg(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_arcsecdg(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_cas(a68_mp* z, const a68_mp* x, int digs, char* err);
int mp_pow(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err);
int mp_hypot(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err);
int mp_atan2(a68_mp* z, const a68_mp* x, const a68_mp* y, int digs, char* err);

/* `PiMod` and `piMp`. */
typedef enum { MP_PI, MP_HALF_PI, MP_TWO_PI, MP_SQRT_TWO_PI, MP_SQRT_PI, MP_LN_PI,
               MP_180_OVER_PI, MP_PI_OVER_180 } mp_pi_mod;
int mp_pi(a68_mp* api, mp_pi_mod md, int digs, char* err);

/* The caches of π, ln 10^7 and ln 10 (`Cache`, `mpCacheRef`): results depend on the
   history of requests exactly as in a68g. */
void mp_cache_reset(void);

/* ---- LONG COMPLEX: `a + b i` in place ---- */

int mp_cmul(a68_mp* a, a68_mp* b, const a68_mp* c, const a68_mp* d, int digs, char* err);
int mp_cdiv(a68_mp* a, a68_mp* b, const a68_mp* c, const a68_mp* d, int digs, char* err);
int mp_cpow_int(a68_mp* re, a68_mp* im, int64_t j, int digs, char* err);  /* `mpComplPow` */
int mp_csqrt(a68_mp* r, a68_mp* i, int digs, char* err);
int mp_cexp(a68_mp* r, a68_mp* i, int digs, char* err);
int mp_cln(a68_mp* r, a68_mp* i, int digs, char* err);
int mp_csin(a68_mp* r, a68_mp* i, int digs, char* err);
int mp_ccos(a68_mp* r, a68_mp* i, int digs, char* err);
int mp_ctan(a68_mp* r, a68_mp* i, int digs, char* err);
int mp_casin(a68_mp* r, a68_mp* i, int digs, char* err);
int mp_cacos(a68_mp* r, a68_mp* i, int digs, char* err);
int mp_catan(a68_mp* r, a68_mp* i, int digs, char* err);
int mp_csinh(a68_mp* r, a68_mp* i, int digs, char* err);
int mp_ccosh(a68_mp* r, a68_mp* i, int digs, char* err);
int mp_ctanh(a68_mp* r, a68_mp* i, int digs, char* err);
int mp_casinh(a68_mp* r, a68_mp* i, int digs, char* err);
int mp_cacosh(a68_mp* r, a68_mp* i, int digs, char* err);
int mp_catanh(a68_mp* r, a68_mp* i, int digs, char* err);

/* ---- formatting (mpfmt.c): malloc'd strings, NULL with `err` set on failure ---- */

/* `llw` is `A68G_LONG_LONG_REAL_WIDTH`, `(ll_digits - MP_GUARDS) * MP_LOG_RADIX`. */
int   mpfmt_ll_real_width(int ll_digits);
char* mpfmt_fixed(const a68_mp* x, int digits, int64_t width, int64_t after, int llw, char* err);
char* mpfmt_float(const a68_mp* x, int digits, int64_t width, int64_t after, int64_t expo,
                  int64_t frmt, int llw, char* err);
char* mpfmt_whole(const a68_mp* x, int digits, int64_t width, int llw, char* err);
/* The standard `print` layout of a `LONG` (`length` 1) or `LONG LONG` (`length` 2) REAL
   (`mpFloatStd`): `float (x, rw + ew + 4, rw - 1, ew + 1)`. */
char* mpfmt_std(const a68_mp* x, int length, int ll_digits, char* err);
/* `Numfmt.wholeInt` for a 64-bit integer (the exponent of `float`). */
char* mpfmt_whole_i64(int64_t n, int64_t width);
/* `MPFmt.checkFinite`. */
int   mpfmt_check_finite(const a68_mp* x, char* err);

/* ---- the runtime layer (mprt.c): `LONG` values of compiled programs ----
   A `LONG` / `LONG LONG REAL` value is an `a68_val` of tag T_MP whose payload is a leaf
   of EK_BYTES bytes laid out as `uint32_t st; int32_t digs; int64_t ex; double d[digs + 1]`
   (`d[0]` unused).  `longness` is 1 for `LONG`, 2 for `LONG LONG`.  Errors are a68g's
   run-time errors, reported through `die` with the evaluator's messages. */

extern int a68_ll_digits;                                   /* digits of `LONG LONG`, from `PR precision` */
int      mp_digits_of(int64_t longness);                    /* `Interp.mpDigitsOf` */
a68_mp   mp_view(a68_val v);                                /* the number a T_MP value holds (no copy) */
a68_val  mp_leaf(const a68_mp* x);                          /* a fresh T_MP value holding `x` */
a68_val  mp_of_int(const a68_big* k, int64_t longness);     /* `Interp.intToMP` */
a68_val  mp_of_real(double x, int64_t longness);            /* `Interp.realToLongReal` */
a68_val  mp_of_string(const uint8_t* s, size_t n, int64_t longness, int* ok); /* `MP.stringToMp` */
char*    mp_fmt_whole(a68_val z, int64_t longness, int64_t width);
char*    mp_fmt_fixed(a68_val z, int64_t longness, int64_t width, int64_t after);
char*    mp_fmt_float(a68_val z, int64_t longness, int64_t width, int64_t after, int64_t expo, int64_t frmt);
char*    mp_float_std(a68_val z, int64_t longness);         /* `Interp.mpFloatStd` */
void     mp_check_finite(a68_val z);                        /* `MPFmt.checkFinite` */
int      mp_to_dec(a68_val z, int64_t longness, a68_dec* out); /* `MP.toDecParts`: 1 if negative */
double   mp_to_real(a68_val z, int64_t longness);           /* `MP.mpToReal` */
a68_val  mp_dyadic(const char* op, int64_t longness, a68_val x, a68_val y);      /* `Interp.mpDyadic` */
a68_val  mp_monadic(const char* op, int64_t longness, a68_val x);               /* `Interp.mpMonadic` */
a68_val  mp_compl_dyadic(const char* op, int64_t longness, a68_val a, a68_val b); /* `Interp.mpComplDyadic` */
a68_val  mp_compl_pow(int64_t longness, a68_val a, int64_t j);                   /* `Interp.mpComplPow` */
a68_val  mp_compl_monadic(const char* op, int64_t longness, a68_val v);          /* `Interp.mpComplMonadic` */
int      mp_math_fn(const char* name, a68_val x, a68_val* out);   /* `Interp.mpMathFn` */
int      mp_compl_fn(const char* name, a68_val x, a68_val* out);  /* `Interp.mpComplFn` */
int      mp_const(const char* name, a68_val* out);                 /* `Interp.mpConst` */
a68_val  mp_arctan2(const char* name, a68_val a, a68_val b);       /* the `arctan2` arms of `callBuiltin` */
a68_val  mp_long_random(double r, int64_t longness);              /* `genie_long_next_random` */
a68_val  mp_widen(a68_val v, int64_t from_longness, int64_t to_longness); /* `Interp.widenValue` */

#ifdef __cplusplus
}
#endif
#endif
