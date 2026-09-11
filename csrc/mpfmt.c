/* mpfmt.c -- `whole`, `fixed` and `float` of multi-precision values: a transcription of
   A68/MPFmt.lean (`transput-formatting.c`: `sub_fixed_mp`, `choose_dig_mp`, `fixed`,
   `standardize_mp`, `real`).

   a68g formats LONG values with the multi-precision arithmetic of the value's own length,
   rounding at that precision — adding the rounding term, dividing by ten while counting
   digits before the point, multiplying by ten to extract each digit — so the digits
   printed are not the exact decimal expansion of the value.  Digits past
   `A68G_LONG_LONG_REAL_WIDTH` (`llw`, which depends on the LONG LONG precision, not on
   the value's) are printed as `0`. */
#include "mp.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define R 10000000.0
#define TRY(e) do { int rc__ = (e); if (rc__) return rc__; } while (0)
#define MP_TEMP(name, n) double name##_buf[(n) + 1]; a68_mp name = mp_temp(name##_buf, (n))

static a68_mp mp_temp(double* buf, int n) {
  a68_mp z;
  memset(buf, 0, ((size_t) n + 1) * sizeof(double));
  z.st = MP_INIT; z.ex = 0; z.digs = n; z.d = buf;
  return z;
}

static void* xmalloc_(size_t n) {
  void* p = malloc(n ? n : 1);
  if (!p) { fputs("a68: out of memory\n", stderr); abort(); }
  return p;
}

static void seterr(char* err, const char* msg) {
  if (err) { strncpy(err, msg, MP_ERR_LEN - 1); err[MP_ERR_LEN - 1] = 0; }
}

static inline int64_t iabs64(int64_t v) { return v < 0 ? -v : v; }
static inline int64_t sgn64(int64_t v) { return v > 0 ? 1 : v < 0 ? -1 : 0; }

int mpfmt_ll_real_width(int ll_digits) { return (ll_digits - MP_GUARDS) * MP_LOG_RADIX; }

/* ---------------------------------------------------------------- strings */

/* A growable byte string. */
typedef struct { char* s; size_t n, cap; } sb;

static void sb_init(sb* b) { b->cap = 64; b->n = 0; b->s = (char*) xmalloc_(b->cap); b->s[0] = 0; }
static void sb_push(sb* b, char c) {
  if (b->n + 2 > b->cap) { b->cap *= 2; b->s = (char*) realloc(b->s, b->cap); if (!b->s) abort(); }
  b->s[b->n++] = c; b->s[b->n] = 0;
}

/* `Numfmt.errorChars`. */
static char* error_chars(int64_t width) {
  int64_t k = width == 0 ? 1 : iabs64(width), i;
  char* s = (char*) xmalloc_((size_t) k + 1);
  for (i = 0; i < k; i++) s[i] = '*';
  s[k] = 0;
  return s;
}

/* `Numfmt.hasError`. */
static int has_error(const char* s) { return strchr(s, '*') != NULL; }

/* `Numfmt.leadingSpaces` (consumes `s`). */
static char* leading_spaces(char* s, int64_t width) {
  size_t len = strlen(s);
  char* r;
  if ((int64_t) len >= width) return s;
  r = (char*) xmalloc_((size_t) width + 1);
  memset(r, ' ', (size_t) width - len);
  memcpy(r + ((size_t) width - len), s, len + 1);
  free(s);
  return r;
}

/* A prefix character before `s` (consumes `s`). */
static char* prefix_char(char c, char* s) {
  size_t len = strlen(s);
  char* r = (char*) xmalloc_(len + 2);
  r[0] = c;
  memcpy(r + 1, s, len + 1);
  free(s);
  return r;
}

/* `Numfmt.wholeInt` for a 64-bit integer. */
char* mpfmt_whole_i64(int64_t n, int64_t width) {
  int ltz = n < 0;
  uint64_t an = n < 0 ? (uint64_t) (-(n + 1)) + 1 : (uint64_t) n;
  char digits[32];
  int64_t length, ndig;
  char* s;
  snprintf(digits, sizeof digits, "%llu", (unsigned long long) an);
  ndig = (int64_t) strlen(digits);
  length = width == 0 ? ndig : iabs64(width) - ((ltz || width > 0) ? 1 : 0);
  /* `subWhole an length` */
  if (ndig > length) s = error_chars(length);
  else { s = (char*) xmalloc_((size_t) ndig + 1); memcpy(s, digits, (size_t) ndig + 1); }
  if (length == 0 || has_error(s)) { free(s); return error_chars(iabs64(width)); }
  if (ltz) s = prefix_char('-', s);
  else if (width > 0) s = prefix_char('+', s);
  if (width != 0) s = leading_spaces(s, iabs64(width));
  return s;
}

/* ---------------------------------------------------------------- fixed */

/* `chooseDig`: multiply by ten and take the units digit. */
static int choose_dig(a68_mp* y, int digits, char* out, char* err) {
  double c0, c;
  MP_TEMP(t, digits);
  TRY(mp_mul_digit(y, y, 10, digits, err));
  c0 = y->ex == 0 ? mp_dig(y, 1) : 0.0;
  c = c0 > 9.0 ? 9.0 : c0;
  t.d[1] = c;
  TRY(mp_sub(y, y, &t, digits, err));
  *out = (char) ('0' + (c < 0.0 ? 0 : (int) c));
  return 0;
}

/* `subFixed (x, digits, width, after)` for non-negative `x`. */
static int sub_fixed(const a68_mp* x, int digits, int64_t width, int64_t after, int llw, char** out, char* err) {
  MP_TEMP(t, digits); MP_TEMP(y, digits); MP_TEMP(s, digits);
  int64_t before = 0, i, len = 0;
  sb b;
  TRY(mp_ten_up(&t, -after, digits, err));
  TRY(mp_half(&t, &t, digits, err));
  TRY(mp_add(&y, x, &t, digits, err));
  while (y.ex > 1) {
    int64_t k = y.ex - 1;
    y.ex = y.ex - k;
    before += k * MP_LOG_RADIX;
  }
  s.d[1] = 1.0;
  for (;;) {
    TRY(mp_sub(&t, &y, &s, digits, err));
    if (mp_dig(&t, 1) >= 0.0) {
      before++;
      TRY(mp_div_digit(&y, &y, 10, digits, err));
    } else break;
  }
  if (before + after + (after > 0 ? 1 : 0) > width) { *out = error_chars(width); return 0; }
  sb_init(&b);
  for (i = 0; i < before; i++) {
    if (len < llw) {
      char ch;
      if (choose_dig(&y, digits, &ch, err)) { free(b.s); return 1; }
      sb_push(&b, ch);
    } else sb_push(&b, '0');
    len++;
  }
  if (after > 0) sb_push(&b, '.');
  for (i = 0; i < after; i++) {
    if (len < llw) {
      char ch;
      if (choose_dig(&y, digits, &ch, err)) { free(b.s); return 1; }
      sb_push(&b, ch);
    } else sb_push(&b, '0');
    len++;
  }
  if ((int64_t) b.n > width) { free(b.s); *out = error_chars(width); return 0; }
  *out = b.s;
  return 0;
}

/* `checkFinite`: CHECK_LONG_REAL under strict maths. */
int mpfmt_check_finite(const a68_mp* x, char* err) {
  if (mp_is_nan(x)) { seterr(err, "LONG REAL value is not a number"); return 1; }
  if (mp_is_inf(x)) { seterr(err, "infinite LONG REAL value"); return 1; }
  return 0;
}

/* a68g `fixed (x, width, after)` for a multi-precision value. */
char* mpfmt_fixed(const a68_mp* x, int digits, int64_t width, int64_t after, int llw, char* err) {
  int ltz;
  int64_t length;
  if (mpfmt_check_finite(x, err)) return NULL;
  ltz = mp_dig(x, 1) < 0.0;
  {
    MP_TEMP(xa, x->digs);
    char* s;
    mp_move(&xa, x, x->digs);
    xa.d[1] = fabs(xa.d[1]);
    length = iabs64(width) - ((ltz || width > 0) ? 1 : 0);
    if (after >= 0 && (length > after || width == 0)) {
      if (width == 0) {
        MP_TEMP(z0, digits); MP_TEMP(z1, digits); MP_TEMP(t, digits);
        length = after == 0 ? 1 : 0;
        mp_set(&z0, R / 10.0, -1, digits);
        if (mp_pow_int(&z0, &z0, after, digits, err)) return NULL;
        mp_set(&z1, 10.0, 0, digits);
        if (mp_pow_int(&z1, &z1, length, digits, err)) return NULL;
        for (;;) {
          if (mp_div_digit(&t, &z0, 2, digits, err)) return NULL;
          if (mp_add(&t, &xa, &t, digits, err)) return NULL;
          if (mp_sub(&t, &t, &z1, digits, err)) return NULL;
          if (mp_dig(&t, 1) > 0.0) {
            length++;
            if (mp_mul_digit(&z1, &z1, 10, digits, err)) return NULL;
          } else break;
        }
        length += (after == 0 ? 0 : after + 1);
      }
      if (sub_fixed(&xa, digits, length, after, llw, &s, err)) return NULL;
      if (!has_error(s)) {
        if (length > (int64_t) strlen(s) && (s[0] == 0 || s[0] == '.') && (xa.ex < 0 || mp_dig(&xa, 1) == 0.0))
          s = prefix_char('0', s);
        if (ltz) s = prefix_char('-', s);
        else if (width > 0) s = prefix_char('+', s);
        if (width != 0) s = leading_spaces(s, iabs64(width));
        return s;
      } else if (after > 0) {
        free(s);
        return mpfmt_fixed(x, digits, width, after - 1, llw, err);
      } else {
        free(s);
        return error_chars(width);
      }
    }
    return error_chars(width);
  }
}

/* ---------------------------------------------------------------- float */

/* `standardize (y, digits, before, after, &q)`. */
static int standardize(a68_mp* y, int digits, int64_t before, int64_t after, int64_t* q, char* err) {
  MP_TEMP(g, digits); MP_TEMP(h, digits); MP_TEMP(t, digits); MP_TEMP(f, digits);
  TRY(mp_ten_up(&g, before, digits, err));
  TRY(mp_div_digit(&h, &g, 10, digits, err));
  if (y->ex - g.ex > 1) {
    *q += MP_LOG_RADIX * (y->ex - g.ex - 1);
    y->ex = g.ex + 1;
  }
  for (;;) {
    TRY(mp_sub(&t, y, &g, digits, err));
    if (mp_dig(&t, 1) >= 0.0) {
      TRY(mp_div_digit(y, y, 10, digits, err));
      (*q)++;
    } else break;
  }
  if (mp_dig(y, 1) != 0.0) {
    if (y->ex - h.ex < -1) {
      *q -= MP_LOG_RADIX * (h.ex - y->ex - 1);
      y->ex = h.ex - 1;
    }
    for (;;) {
      TRY(mp_sub(&t, y, &h, digits, err));
      if (mp_dig(&t, 1) < 0.0) {
        TRY(mp_mul_digit(y, y, 10, digits, err));
        (*q)--;
      } else break;
    }
  }
  TRY(mp_ten_up(&f, -after, digits, err));
  TRY(mp_div_digit(&t, &f, 2, digits, err));
  TRY(mp_add(&t, y, &t, digits, err));
  TRY(mp_sub(&t, &t, &g, digits, err));
  if (mp_dig(&t, 1) >= 0.0) {
    mp_move(y, &h, digits);
    (*q)++;
  }
  return 0;
}

/* a68g `real (x, width, after, expo, frmt)` — `float` is `frmt = 1`. */
char* mpfmt_float(const a68_mp* x, int digits, int64_t width, int64_t after, int64_t expo,
                  int64_t frmt, int llw, char* err) {
  int ltz;
  int64_t before, q = 0;
  if (mpfmt_check_finite(x, err)) return NULL;
  ltz = mp_dig(x, 1) < 0.0;
  before = iabs64(width) - iabs64(expo) - (after != 0 ? after + 1 : 0) - 2;
  if (sgn64(before) + sgn64(after) > 0) {
    MP_TEMP(z, digits);
    char* s; char* e; char* r;
    mp_move(&z, x, digits);
    z.d[1] = fabs(z.d[1]);
    if (standardize(&z, digits, before, after, &q, err)) return NULL;
    if (frmt > 0) {
      while (q % frmt != 0) {
        if (mp_mul_digit(&z, &z, 10, digits, err)) return NULL;
        q--;
        if (after > 0) after--;
      }
    } else {
      MP_TEMP(lim, digits); MP_TEMP(dif, digits);
      if (mp_ten_up(&lim, -frmt - 1, digits, err)) return NULL;
      if (mp_sub(&dif, &z, &lim, digits, err)) return NULL;
      while (mp_dig(&dif, 1) < 0.0) {
        if (mp_mul_digit(&z, &z, 10, digits, err)) return NULL;
        q--;
        if (after > 0) after--;
        if (mp_sub(&dif, &z, &lim, digits, err)) return NULL;
      }
      if (mp_mul_digit(&lim, &lim, 10, digits, err)) return NULL;
      if (mp_sub(&dif, &z, &lim, digits, err)) return NULL;
      while (mp_dig(&dif, 1) > 0.0) {
        if (mp_div_digit(&z, &z, 10, digits, err)) return NULL;
        q++;
        if (after > 0) after++;
        if (mp_sub(&dif, &z, &lim, digits, err)) return NULL;
      }
    }
    if (ltz) mp_negate1(&z);
    s = mpfmt_fixed(&z, digits, sgn64(width) * (iabs64(width) - iabs64(expo) - 1), after, llw, err);
    if (!s) return NULL;
    e = mpfmt_whole_i64(q, expo);
    r = (char*) xmalloc_(strlen(s) + strlen(e) + 2);
    strcpy(r, s); strcat(r, "e"); strcat(r, e);
    free(s); free(e);
    if (expo == 0 || has_error(r)) {
      free(r);
      return mpfmt_float(x, digits, width, after != 0 ? after - 1 : 0, expo > 0 ? expo + 1 : expo - 1,
                         frmt, llw, err);
    }
    return r;
  }
  return error_chars(width);
}

/* `whole` of a LONG REAL value is `fixed (x, width, 0)`. */
char* mpfmt_whole(const a68_mp* x, int digits, int64_t width, int llw, char* err) {
  return mpfmt_fixed(x, digits, width, 0, llw, err);
}

/* `mpFloatStd`: the standard layout of a LONG / LONG LONG REAL in `print`. */
char* mpfmt_std(const a68_mp* x, int length, int ll_digits, char* err) {
  int64_t rw = length <= 1 ? 42 : (int64_t) (ll_digits - 2) * MP_LOG_RADIX, ew = 3;
  int digits = length <= 1 ? MP_LONG_DIGITS : ll_digits;
  return mpfmt_float(x, digits, rw + ew + 4, rw - 1, ew + 1, 1, mpfmt_ll_real_width(ll_digits), err);
}
