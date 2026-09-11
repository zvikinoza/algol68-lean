/* fmt.c -- number formatting byte-compatible with Algol 68 Genie.

   This is a function-by-function transcription of A68/Numfmt.lean; each function
   names the Lean definition it reproduces.  The exact decimal kernel (`Dec`) is
   mantissa * 10^exp with an arbitrary-precision mantissa (bigint.h); the one
   floating-point step, `realToDec`, repeats a68g's double-precision digit
   extraction operation by operation so that the same 21 digits come out.

   Memory: every `a68_dec` produced by the internal helpers owns its mantissa and
   is released with dec_free; strings are malloc'ed and the helpers that take a
   `char*` argument consume (free) it. */
#include "fmt.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#pragma STDC FP_CONTRACT OFF

/* ------------------------------------------------------------- small helpers */

static void* xmalloc(size_t n) {
    void* p = malloc(n ? n : 1);
    if (!p) abort();
    return p;
}

/* Int.natAbs on the values that occur here (widths, exponents). */
static int64_t i64_abs(int64_t v) {
    if (v == INT64_MIN) return INT64_MAX;
    return v < 0 ? -v : v;
}

static int64_t sgn(int64_t v) { return v > 0 ? 1 : v < 0 ? -1 : 0; }

static a68_big* big_dup(const a68_big* a) {
    a68_big* z = big_from_i64(0);
    a68_big* r = big_add(a, z);
    big_free(z);
    return r;
}

/* m * 10^k for k >= 0 (Dec.pow10). */
static a68_big* big_scale10(const a68_big* m, int64_t k) {
    a68_big *p, *r;
    if (k <= 0) return big_dup(m);
    p = big_pow10((int)k);
    r = big_mul(m, p);
    big_free(p);
    return r;
}

/* ------------------------------------------------------------------- strings */

static char* str_fill(size_t n, char c) {
    char* r = xmalloc(n + 1);
    memset(r, c, n);
    r[n] = 0;
    return r;
}

/* c ++ s, consuming s */
static char* str_prepend(char c, char* s) {
    size_t n = strlen(s);
    char* r = xmalloc(n + 2);
    r[0] = c;
    memcpy(r + 1, s, n + 1);
    free(s);
    return r;
}

/* a ++ mid ++ b, consuming a and b */
static char* str_concat3(char* a, const char* mid, char* b) {
    size_t na = strlen(a), nm = strlen(mid), nb = strlen(b);
    char* r = xmalloc(na + nm + nb + 1);
    memcpy(r, a, na);
    memcpy(r + na, mid, nm);
    memcpy(r + na + nm, b, nb + 1);
    free(a);
    free(b);
    return r;
}

/* growable string builder for the digit loops */
typedef struct { char* s; size_t len, cap; } sb;

static void sb_init(sb* b) { b->cap = 32; b->len = 0; b->s = xmalloc(b->cap); b->s[0] = 0; }
static void sb_push(sb* b, char c) {
    if (b->len + 2 > b->cap) { b->cap *= 2; b->s = realloc(b->s, b->cap); if (!b->s) abort(); }
    b->s[b->len++] = c;
    b->s[b->len] = 0;
}

/* ------------------------------------------------------------- Numfmt.Dec */

typedef a68_dec dec;

static dec dec_mk(a68_big* m, int64_t e) { dec d; d.mant = m; d.exp = e; return d; }
static void dec_free(dec d) { big_free(d.mant); }

static dec dec_zero(void) { return dec_mk(big_from_i64(0), 0); }                /* Dec.zero */
static dec dec_of_i64(int64_t n) { return dec_mk(big_from_i64(n), 0); }         /* Dec.ofInt */
static dec dec_ten_up(int64_t n) { return dec_mk(big_from_i64(1), n); }         /* Dec.tenUp */

/* Numfmt.Dec.ofInt for a magnitude (public) */
a68_dec a68_dec_of_u64(uint64_t n) {
    char buf[32];
    int len = snprintf(buf, sizeof buf, "%llu", (unsigned long long)n);
    return dec_mk(big_from_dec(buf, (size_t)len), 0);
}
a68_dec a68_dec_of_big(const a68_big* n) { return dec_mk(big_abs(n), 0); }
void a68_dec_free(a68_dec* d) { big_free(d->mant); d->mant = NULL; }

/* Dec.align: bring two numbers to a common exponent. */
static void dec_align(dec a, dec b, a68_big** x, a68_big** y, int64_t* e) {
    *e = a.exp < b.exp ? a.exp : b.exp;
    *x = big_scale10(a.mant, a.exp - *e);
    *y = big_scale10(b.mant, b.exp - *e);
}

static dec dec_add(dec a, dec b) {                                               /* Dec.add */
    a68_big *x, *y, *s;
    int64_t e;
    dec_align(a, b, &x, &y, &e);
    s = big_add(x, y);
    big_free(x); big_free(y);
    return dec_mk(s, e);
}

static dec dec_sub(dec a, dec b) {                                               /* Dec.sub */
    a68_big *x, *y, *s;
    int64_t e;
    dec_align(a, b, &x, &y, &e);
    s = big_sub(x, y);
    big_free(x); big_free(y);
    return dec_mk(s, e);
}

static dec dec_mul10(dec a) { return dec_mk(big_dup(a.mant), a.exp + 1); }      /* Dec.mul10 */
static dec dec_div10(dec a) { return dec_mk(big_dup(a.mant), a.exp - 1); }      /* Dec.div10 */
static dec dec_half(dec a) { return dec_mk(big_mul_small(a.mant, 5), a.exp - 1); } /* Dec.half */
static int dec_is_zero(dec a) { return big_is_zero(a.mant); }                    /* Dec.isZero */
static int dec_sign(dec a) { return big_sign(a.mant); }                          /* Dec.sign */

/* Dec.cmp: sign of a - b */
static int dec_cmp(dec a, dec b) {
    dec d = dec_sub(a, b);
    int s = dec_sign(d);
    dec_free(d);
    return s;
}
static int dec_lt(dec a, dec b) { return dec_cmp(a, b) < 0; }                   /* Dec.lt */
static int dec_ge(dec a, dec b) { return dec_cmp(a, b) >= 0; }                  /* Dec.ge */
static int dec_gt(dec a, dec b) { return dec_cmp(a, b) > 0; }                   /* Dec.gt */

/* Dec.floorNat: integer part of a non-negative number (a negative result is
   clamped to 0 like Int.toNat; the division truncates, which agrees with the
   Lean floor division on all non-negative arguments). */
static a68_big* dec_floor_nat(dec a) {
    a68_big* r;
    if (a.exp >= 0) {
        r = big_scale10(a.mant, a.exp);
    } else {
        a68_big* p = big_pow10((int)(-a.exp));
        r = big_divmod(a.mant, p, NULL);
        big_free(p);
    }
    if (big_sign(r) < 0) { big_free(r); r = big_from_i64(0); }
    return r;
}

/* --------------------------------------------------------- Numfmt.realToDec */

/* Lean's Float.toUInt64: saturating, NaN and negatives give 0. */
static uint64_t float_to_uint64(double a) {
    return 0. <= a ? (a < 18446744073709551616. ? (uint64_t)a : UINT64_MAX) : 0;
}

/* Numfmt.truncInt: C-style truncation toward zero, as a big (the saturated
   2^64 - 1 of an infinite argument matters: a68g's ten_up overflows on subnormal
   inputs and the digit loop then extracts `inf`). */
static a68_big* trunc_int_big(double x) {
    char buf[32];
    int len;
    a68_big *m, *r;
    if (x >= 0) {
        len = snprintf(buf, sizeof buf, "%llu", (unsigned long long)float_to_uint64(x));
        return big_from_dec(buf, (size_t)len);
    }
    len = snprintf(buf, sizeof buf, "%llu", (unsigned long long)float_to_uint64(-x));
    m = big_from_dec(buf, (size_t)len);
    r = big_neg(m);
    big_free(m);
    return r;
}

/* Numfmt.truncInt where the result is known to be small (|x| < 2^63). */
static int64_t trunc_int(double x) {
    a68_big* b = trunc_int_big(x);
    int64_t r = big_to_i64(b);
    big_free(b);
    return r;
}

/* Numfmt.tenUpFloat: a68g's ten_up, 10^expo by binary exponentiation in doubles. */
static double ten_up_float(int64_t expo) {
    static const double table[9] = {10.0, 100.0, 1.0e4, 1.0e8, 1.0e16, 1.0e32, 1.0e64, 1.0e128, 1.0e256};
    int neg = expo < 0;
    uint64_t e = expo < 0 ? (uint64_t)0 - (uint64_t)expo : (uint64_t)expo;
    double r = 1.0;
    int i = 0;
    while (e != 0) {
        /* beyond the table Lean's `table[i]!` panics and yields the default 0.0 */
        if (e % 2 == 1) r = r * (i < 9 ? table[i] : 0.0);
        e = e / 2;
        i = i + 1;
    }
    return neg ? 1.0 / r : r;
}

/* Numfmt.realToDec: reproduce a68g's real_to_mp (generic build). */
int a68_real_to_dec(double x, a68_dec* out) {
    int neg;
    double a0, a;
    int64_t expo;
    a68_big* mant;
    int k;
    if (x == 0.0) { *out = dec_zero(); return 0; }
    neg = x < 0;
    if (!isfinite(x)) {
        /* Not reachable from a checked REAL.  The Lean extracts a zero mantissa here
           (for infinities after a panic on the table index of tenUpFloat, with an
           exponent of 2^64 that no later operation can align); a zero Dec formats
           the same whatever its exponent, so return plain zero. */
        *out = dec_zero();
        return neg;
    }
    a0 = fabs(x);
    /* small integers are converted exactly */
    if (a0 < 1.0e7 && floor(a0) == a0) {
        *out = dec_of_i64(trunc_int(a0));
        return neg;
    }
    expo = trunc_int(log10(a0));
    a = a0 / ten_up_float(expo);
    expo = expo - 1;
    if (a >= 1.0) {
        a = a / 10.0;
        expo = expo + 1;
    }
    /* three MP digits of radix 10^7 (k = 0, 7, 14 <= 15) */
    mant = big_from_i64(0);
    for (k = 0; k < 3; k++) {
        double t = a * 1.0e7;
        double dig = floor(t);
        a68_big *m1, *d, *m2;
        a = t - dig;
        m1 = big_mul_small(mant, 10000000);
        d = trunc_int_big(dig);
        m2 = big_add(m1, d);
        big_free(m1); big_free(d); big_free(mant);
        mant = m2;
    }
    /* value = 0.D1D2D3 * 10^(expo+1) */
    *out = dec_mk(mant, expo + 1 - 21);
    return neg;
}

/* ------------------------------------------------- error characters, padding */

/* Numfmt.errorChars */
static char* error_chars(int64_t width) {
    uint64_t k = width == 0 ? 1 : (width < 0 ? (uint64_t)0 - (uint64_t)width : (uint64_t)width);
    return str_fill((size_t)k, '*');
}

/* Numfmt.hasError */
int a68_fmt_has_error(const char* s) { return strchr(s, '*') != NULL; }

/* Numfmt.leadingSpaces (consumes s) */
static char* leading_spaces(char* s, uint64_t width) {
    size_t n = strlen(s);
    char* r;
    if (n >= width) return s;
    r = xmalloc((size_t)width + 1);
    memset(r, ' ', (size_t)(width - n));
    memcpy(r + (width - n), s, n + 1);
    free(s);
    return r;
}

/* ------------------------------------------------------------- Numfmt.whole */

/* Numfmt.subWhole on a big natural: its digits, or error chars if more than width. */
static char* sub_whole_big(const a68_big* n, int64_t width) {
    char* s = big_to_dec(n);
    if ((int64_t)strlen(s) > width) { free(s); return error_chars(width); }
    return s;
}

/* Numfmt.subWhole */
char* a68_fmt_sub_whole(uint64_t n, int64_t width) {
    char buf[32];
    int len = 0;
    char* s;
    /* toString n */
    do { buf[len++] = (char)('0' + n % 10); n /= 10; } while (n);
    if ((int64_t)len > width) return error_chars(width);
    s = xmalloc((size_t)len + 1);
    for (int i = 0; i < len; i++) s[i] = buf[len - 1 - i];
    s[len] = 0;
    return s;
}

/* Numfmt.wholeInt: `whole` for integral values (any length). */
char* a68_fmt_whole_int(const a68_big* n, int64_t width) {
    int ltz = big_sign(n) < 0;
    a68_big* an = big_abs(n);
    int64_t length = width == 0 ? (int64_t)big_ndigits(an)
                                : i64_abs(width) - ((ltz || width > 0) ? 1 : 0);
    char* s = sub_whole_big(an, length);
    big_free(an);
    if (length == 0 || a68_fmt_has_error(s)) {
        free(s);
        return error_chars(i64_abs(width));
    }
    if (ltz) s = str_prepend('-', s);
    else if (width > 0) s = str_prepend('+', s);
    if (width != 0) s = leading_spaces(s, (uint64_t)i64_abs(width));
    return s;
}

/* ------------------------------------------------------------- Numfmt.fixed */

/* Numfmt.chooseDig: y in [0, 1); returns the next decimal digit and replaces y by
   the remainder. */
static char choose_dig(dec* y) {
    dec y10 = dec_mul10(*y);
    a68_big* fl = dec_floor_nat(y10);
    a68_big* nine = big_from_i64(9);
    int64_t c = big_cmp(fl, nine) > 0 ? 9 : big_to_i64(fl);
    dec cd = dec_of_i64(c);
    dec rest = dec_sub(y10, cd);
    big_free(fl); big_free(nine);
    dec_free(cd); dec_free(y10); dec_free(*y);
    *y = rest;
    return (char)('0' + c);
}

/* Numfmt.longLongRealWidth: digits beyond this are printed as 0. */
#define LONG_LONG_REAL_WIDTH 70

/* Numfmt.subFixed: a68g sub_fixed_mp. */
char* a68_fmt_sub_fixed(dec x, int64_t width, int64_t after) {
    dec tu = dec_ten_up(-after);
    dec hf = dec_half(tu);
    dec y = dec_add(x, hf);
    dec one = dec_of_i64(1);
    int64_t before = 0, len = 0, i;
    sb str;
    dec_free(tu); dec_free(hf);
    while (dec_ge(y, one)) {
        dec y2 = dec_div10(y);
        dec_free(y);
        y = y2;
        before = before + 1;
    }
    dec_free(one);
    if (before + after + (after > 0 ? 1 : 0) > width) {
        dec_free(y);
        return error_chars(width);
    }
    sb_init(&str);
    for (i = 0; i < before; i++) {
        if (len < LONG_LONG_REAL_WIDTH) sb_push(&str, choose_dig(&y));
        else sb_push(&str, '0');
        len = len + 1;
    }
    if (after > 0) sb_push(&str, '.');
    for (i = 0; i < after; i++) {
        if (len < LONG_LONG_REAL_WIDTH) sb_push(&str, choose_dig(&y));
        else sb_push(&str, '0');
        len = len + 1;
    }
    dec_free(y);
    if ((int64_t)str.len > width) { free(str.s); return error_chars(width); }
    return str.s;
}

/* Numfmt.fixedDec: a68g `fixed` on a non-negative exact decimal x with sign flag
   ltz.  The Lean recursion on `after - 1` is the loop here. */
char* a68_fmt_fixed_dec(int ltz, a68_dec x, int64_t width, int64_t after) {
    for (;;) {
        int64_t length = i64_abs(width) - ((ltz || width > 0) ? 1 : 0);
        char* s;
        if (!(after >= 0 && (length > after || width == 0))) return error_chars(width);
        if (width == 0) {
            dec z0, z1, z0h;
            length = after == 0 ? 1 : 0;
            z0 = dec_ten_up(-after);
            z1 = dec_ten_up(length);
            z0h = dec_half(z0);
            for (;;) {
                dec sum = dec_add(z0h, x);
                dec diff = dec_sub(sum, z1);
                dec zero = dec_zero();
                int more = dec_gt(diff, zero);
                dec_free(sum); dec_free(diff); dec_free(zero);
                if (!more) break;
                length = length + 1;
                sum = dec_mul10(z1);
                dec_free(z1);
                z1 = sum;
            }
            dec_free(z0); dec_free(z1); dec_free(z0h);
            length = length + (after == 0 ? 0 : after + 1);
        }
        s = a68_fmt_sub_fixed(x, length, after);
        if (!a68_fmt_has_error(s)) {
            if (length > (int64_t)strlen(s) && (s[0] == 0 || s[0] == '.')) {
                dec one = dec_of_i64(1);
                int small = dec_lt(x, one);
                dec_free(one);
                if (small) s = str_prepend('0', s);
            }
            if (ltz) s = str_prepend('-', s);
            else if (width > 0) s = str_prepend('+', s);
            if (width != 0) s = leading_spaces(s, (uint64_t)i64_abs(width));
            return s;
        }
        free(s);
        if (after > 0) { after = after - 1; continue; }
        return error_chars(width);
    }
}

/* ------------------------------------------------------------- Numfmt.float */

/* Numfmt.standardize: a68g standardize_mp.  Scales y into [10^(before-1), 10^before)
   adjusting q, then pre-empts rounding overflow.  Consumes y; returns the new y. */
static dec standardize(dec y, int64_t before, int64_t after, int64_t* q) {
    dec g = dec_ten_up(before);
    dec h = dec_div10(g);
    dec zero = dec_zero();
    dec f, fh, sum, t;
    for (;;) {
        dec d = dec_sub(y, g);
        int ge = dec_ge(d, zero);
        dec_free(d);
        if (!ge) break;
        d = dec_div10(y);
        dec_free(y);
        y = d;
        *q = *q + 1;
    }
    if (!dec_is_zero(y)) {
        for (;;) {
            dec d = dec_sub(y, h);
            int lt = dec_lt(d, zero);
            dec_free(d);
            if (!lt) break;
            d = dec_mul10(y);
            dec_free(y);
            y = d;
            *q = *q - 1;
        }
    }
    f = dec_ten_up(-after);
    fh = dec_half(f);
    sum = dec_add(fh, y);
    t = dec_sub(sum, g);
    if (dec_ge(t, zero)) {
        dec_free(y);
        y = dec_mk(big_dup(h.mant), h.exp);
        *q = *q + 1;
    }
    dec_free(f); dec_free(fh); dec_free(sum); dec_free(t);
    dec_free(g); dec_free(h); dec_free(zero);
    return y;
}

/* Numfmt.standardize, public form: y is borrowed, *out receives a fresh value. */
void a68_fmt_standardize(a68_dec y, int64_t before, int64_t after, int64_t q, a68_dec* out, int64_t* qout) {
    *out = standardize(dec_mk(big_dup(y.mant), y.exp), before, after, &q);
    *qout = q;
}

/* Numfmt.floatDec: a68g `real` (the `float` routine, frmt = 1 for `float`, 3 for
   `h` patterns).  The Lean retry with a wider exponent is the loop here. */
char* a68_fmt_float_dec(int ltz, a68_dec x, int64_t width, int64_t after, int64_t expo, int64_t frmt) {
    for (;;) {
        int64_t before = i64_abs(width) - i64_abs(expo) - (after != 0 ? after + 1 : 0) - 2;
        int64_t q = 0, mwidth;
        dec z;
        char *s, *e;
        a68_big* qb;
        if (!(sgn(before) + sgn(after) > 0)) return error_chars(width);
        z = standardize(dec_mk(big_dup(x.mant), x.exp), before, after, &q);
        if (frmt > 0) {
            while (q % frmt != 0) {          /* Int.tmod */
                dec z2 = dec_mul10(z);
                dec_free(z);
                z = z2;
                q = q - 1;
                if (after > 0) after = after - 1;
            }
        } else {
            dec lim = dec_ten_up(-frmt - 1);
            dec zero = dec_zero();
            for (;;) {
                dec d = dec_sub(z, lim);
                int lt = dec_lt(d, zero);
                dec_free(d);
                if (!lt) break;
                d = dec_mul10(z);
                dec_free(z);
                z = d;
                q = q - 1;
                if (after > 0) after = after - 1;
            }
            {
                dec l2 = dec_mul10(lim);
                dec_free(lim);
                lim = l2;
            }
            for (;;) {
                dec d = dec_sub(z, lim);
                int gt = dec_gt(d, zero);
                dec_free(d);
                if (!gt) break;
                d = dec_div10(z);
                dec_free(z);
                z = d;
                q = q + 1;
                if (after > 0) after = after + 1;
            }
            dec_free(lim); dec_free(zero);
        }
        mwidth = sgn(width) * (i64_abs(width) - i64_abs(expo) - 1);
        s = a68_fmt_fixed_dec(ltz, z, mwidth, after);
        dec_free(z);
        qb = big_from_i64(q);
        e = a68_fmt_whole_int(qb, expo);
        big_free(qb);
        s = str_concat3(s, "e", e);
        if (expo == 0 || a68_fmt_has_error(s)) {
            free(s);
            after = after != 0 ? after - 1 : 0;
            expo = expo > 0 ? expo + 1 : expo - 1;
            continue;
        }
        return s;
    }
}

/* ------------------------------------------------------- public entry points */

/* Lean's Float.ofInt (correctly rounded to nearest, ties to even): the decimal
   digits go through strtod, which rounds the same way. */
static double big_to_double(const a68_big* n) {
    char* s = big_to_dec(n);
    double d = strtod(s, NULL);
    free(s);
    return d;
}

/* Numfmt.fixedReal */
char* a68_fmt_fixed_real(double x, int64_t width, int64_t after) {
    dec d;
    int neg = a68_real_to_dec(x, &d);
    char* s = a68_fmt_fixed_dec(neg, d, width, after);
    dec_free(d);
    return s;
}

/* Numfmt.fixedInt (a68g first converts the INT to a double) and Numfmt.fixedLongInt
   (exact integral value). */
char* a68_fmt_fixed_int(const a68_big* n, int64_t width, int64_t after, int is_long) {
    if (!is_long) return a68_fmt_fixed_real(big_to_double(n), width, after);
    {
        a68_big* an = big_abs(n);
        dec d = dec_mk(an, 0);
        char* s = a68_fmt_fixed_dec(big_sign(n) < 0, d, width, after);
        dec_free(d);
        return s;
    }
}

/* Numfmt.floatReal */
char* a68_fmt_float_real(double x, int64_t width, int64_t after, int64_t expo, int64_t frmt) {
    dec d;
    int neg = a68_real_to_dec(x, &d);
    char* s = a68_fmt_float_dec(neg, d, width, after, expo, frmt);
    dec_free(d);
    return s;
}

/* Numfmt.floatInt: a68g converts the INT exactly. */
char* a68_fmt_float_int(const a68_big* n, int64_t width, int64_t after, int64_t expo, int64_t frmt) {
    a68_big* an = big_abs(n);
    dec d = dec_mk(an, 0);
    char* s = a68_fmt_float_dec(big_sign(n) < 0, d, width, after, expo, frmt);
    dec_free(d);
    return s;
}

/* Numfmt.wholeReal: whole (REAL, width) = fixed (x, width, 0). */
char* a68_fmt_whole_real(double x, int64_t width) { return a68_fmt_fixed_real(x, width, 0); }

/* Numfmt.intWidthOf / realWidthOf / expWidthOf: standard widths of a68g on a
   32-bit-INT, 64-bit-REAL build (intWidth 10, realWidth 15, expWidth 3, longIntWidth
   50, longRealWidth 42, longExpWidth 3); LONG LONG widths depend on the MP digits
   `ll` (2 + ceil(N/7) for `PR precision N PR`, 12 by default). */
int a68_fmt_int_width(int64_t longness, int ll) {
    return longness <= 0 ? 10 : longness == 1 ? 50 : ll * 7 + 1;
}
int a68_fmt_real_width(int64_t longness, int ll) {
    return longness <= 0 ? 15 : longness == 1 ? 42 : (ll >= 2 ? (ll - 2) * 7 : 0);
}
int a68_fmt_exp_width(int64_t longness) { (void)longness; return 3; }

/* Numfmt.llDigitsOfPrecision */
int a68_fmt_ll_digits_of_precision(int n) { return 2 + (n + 6) / 7; }

/* Numfmt.mpBitsWidth: a68g's MP_BITS_WIDTH (k) = ceil (k * LOG_MP_RADIX * CONST_LOG2_10) - 1,
   computed in doubles as it is there. */
static int mp_bits_width(int k) {
    double c = ceil((double)(k * 7) * 3.321928094887362);
    return (int)(float_to_uint64(c) - 1);
}

/* Numfmt.bitsWidthOfLen: 32 bits, and for LONG and LONG LONG BITS the width of a68g's
   multi-precision representation (162 and, at the default precision, 279). */
int a68_fmt_bits_width(int64_t longness, int ll) {
    return longness <= 0 ? 32 : longness == 1 ? mp_bits_width(7) : mp_bits_width(ll);
}

/* Numfmt.maxIntOf: 2^31 - 1, 10^49 - 1, 10^(ll * 7) - 1. */
a68_big* a68_fmt_max_int(int64_t longness, int ll) {
    a68_big *p, *one, *r;
    if (longness <= 0) return big_from_i64(2147483647);
    p = big_pow10(longness == 1 ? 49 : ll * 7);
    one = big_from_i64(1);
    r = big_sub(p, one);
    big_free(p); big_free(one);
    return r;
}

/* Numfmt.printInt: default print of an integral value of the given length. */
char* a68_fmt_print_int(const a68_big* n, int64_t longness, int ll_digits) {
    int64_t w = a68_fmt_int_width(longness, ll_digits);
    return a68_fmt_whole_int(n, longness <= 0 ? w + 1 : w);
}

/* Numfmt.printReal: default print of a real value of the given length.  (`rw - 1`
   is evaluated in Int there, the arguments being coerced before the subtraction,
   so a zero real width gives `after = -1`, hence error characters.) */
char* a68_fmt_print_real(double x, int64_t longness, int ll_digits) {
    int64_t rw = a68_fmt_real_width(longness, ll_digits);
    int64_t ew = a68_fmt_exp_width(longness);
    return a68_fmt_float_real(x, rw + ew + 4, rw - 1, ew + 1, 1);
}

/* Numfmt.printBits: `width` flip/flop characters, most significant first. */
char* a68_fmt_print_bits(const a68_big* v, int width) {
    int nwords = width <= 0 ? 0 : (width + 31) / 32, w, i;
    uint32_t* words = xmalloc((size_t)(nwords ? nwords : 1) * sizeof(uint32_t));
    a68_big* m = big_abs(v);
    a68_big* base = big_from_i64((int64_t)1 << 32);
    char* s = str_fill(width <= 0 ? 0 : (size_t)width, 'F');
    for (w = 0; w < nwords; w++) {
        a68_big *rem, *q = big_divmod(m, base, &rem);
        words[w] = (uint32_t)big_to_i64(rem);
        big_free(rem); big_free(m);
        m = q;
    }
    big_free(m); big_free(base);
    for (i = 0; i < width; i++)
        if ((words[i / 32] >> (i % 32)) & 1u) s[width - 1 - i] = 'T';
    free(words);
    return s;
}

/* Numfmt.parseFloat: a decimal literal (`123`, `1.5`, `.5`, `1e-5`, `1.5E+3`) into a
   correctly rounded double.  The Lean scans mantissa digits and an exponent and
   then rounds m * 10^e to nearest-even (Float.ofScientific); strtod on the
   canonical `<digits>e<exp>` string performs that same rounding. */
double a68_fmt_parse_float(const char* s, size_t n) {
    size_t i = 0, ndig = 0;
    int64_t exp = 0;
    char* buf = xmalloc(n + 32);
    size_t len = 0;
    double r;
    while (i < n && s[i] >= '0' && s[i] <= '9') { buf[len++] = s[i]; ndig++; i++; }
    if (i < n && s[i] == '.') {
        i++;
        while (i < n && s[i] >= '0' && s[i] <= '9') { buf[len++] = s[i]; ndig++; exp--; i++; }
    }
    if (i < n && (s[i] == 'e' || s[i] == 'E')) {
        int neg = 0;
        int64_t e = 0;
        i++;
        if (i < n && (s[i] == '+' || s[i] == '-')) { neg = s[i] == '-'; i++; }
        while (i < n && s[i] >= '0' && s[i] <= '9') {
            if (e < 1000000000) e = e * 10 + (s[i] - '0');   /* beyond this only 0 or inf result */
            i++;
        }
        exp += neg ? -e : e;
    }
    if (ndig == 0) buf[len++] = '0';
    len += (size_t)snprintf(buf + len, 32, "e%lld", (long long)exp);
    buf[len] = 0;
    r = strtod(buf, NULL);
    free(buf);
    return r;
}
