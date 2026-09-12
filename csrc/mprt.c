/* mprt.c -- LONG and LONG LONG values of compiled programs: the `a68_val` layer over the
   multi-precision library, transcribing the `LONG` arms of A68/Interp.lean (`mpDyadic`,
   `mpMonadic`, `mpComplDyadic`, `mpComplPow`, `mpComplMonadic`, `mpMathFn`, `mpComplFn`,
   `mpConst`, `widenValue`, the `arctan2` arms of `callBuiltin`, and the conversions).

   A LONG REAL value is a T_MP value whose leaf holds `uint32_t st; int32_t digs;
   int64_t ex; double d[digs + 1]` (`mp_view` reads it in place, `mp_leaf` builds one).
   A LONG INT value is a T_INT, or a T_BIGINT whose leaf holds its decimal digits.  A
   LONG COMPLEX value is a T_STRUCT of two T_MP.  Every routine returns fresh values; the
   evaluator's operations write their first operand (`addMp x x y`), which here is a copy
   of it, so stale guard digits and status bits carry over exactly as in the Lean.
   Run-time errors are reported with `die` and the evaluator's messages. */
#include "mp.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define HDR 16   /* bytes before the digits in a T_MP leaf */

/* ------------------------------------------------------------ leaves and modes */

int mp_digits_of(int64_t longness) { return longness <= 1 ? MP_LONG_DIGITS : a68_ll_digits; }

static int llw(void) { return mpfmt_ll_real_width(a68_ll_digits); }

static const char* real_mode(int64_t n) { return n <= 1 ? "LONG REAL" : "LONG LONG REAL"; }
static const char* compl_mode(int64_t n) { return n <= 1 ? "LONG COMPL" : "LONG LONG COMPL"; }
static const char* int_mode(int64_t n) { return n <= 1 ? "LONG INT" : "LONG LONG INT"; }

__attribute__((noreturn)) static void die2(const char* mode, const char* rest) {
  char buf[160];
  snprintf(buf, sizeof buf, "%s %s", mode, rest);
  die(buf);
}

static void check(int rc, const char* err) { if (rc) die(err); }

a68_mp mp_view(a68_val v) {
  a68_mp z;
  a68_leaf* l;
  int32_t digs;
  if (v.tag == T_UNDEF) die("attempt to use an uninitialised LONG REAL value");
  if (v.tag != T_MP) die("internal: LONG REAL expected");
  l = (a68_leaf*) v.v.p;
  memcpy(&z.st, l->d, 4);
  memcpy(&digs, l->d + 4, 4);
  memcpy(&z.ex, l->d + 8, 8);
  z.digs = digs;
  z.d = (double*) (void*) (l->d + HDR);
  return z;
}

a68_val mp_leaf(const a68_mp* x) {
  int32_t digs = x->digs;
  a68_leaf* l = leaf_alloc(EK_BYTES, (uint32_t) (HDR + ((size_t) digs + 1) * sizeof(double)));
  memcpy(l->d, &x->st, 4);
  memcpy(l->d + 4, &digs, 4);
  memcpy(l->d + 8, &x->ex, 8);
  memcpy(l->d + HDR, x->d, ((size_t) digs + 1) * sizeof(double));
  return mk_ptr(T_MP, (a68_obj*) l, 0);
}

/* A view writes its digits into the leaf but keeps the status and exponent on the stack:
   they are written back with this before the fresh value is returned. */
static a68_val mp_commit(a68_val r, const a68_mp* x) {
  a68_leaf* l = (a68_leaf*) r.v.p;
  int32_t digs = x->digs;
  memcpy(l->d, &x->st, 4);
  memcpy(l->d + 4, &digs, 4);
  memcpy(l->d + 8, &x->ex, 8);
  return r;
}

/* A fresh value holding `x` extended to at least `digs` digits, viewed for writing. */
static a68_val fresh_copy(a68_val v, int digs, a68_mp* view) {
  a68_mp x = mp_view(v);
  a68_val r;
  if (x.digs >= digs) r = mp_leaf(&x);
  else { a68_mp w = mp_len(&x, x.digs, digs); r = mp_leaf(&w); mp_free(&w); }
  *view = mp_view(r);
  return r;
}

static a68_val fresh_nil(int digs, a68_mp* view) {
  a68_mp z = mp_nil(digs);
  a68_val r = mp_leaf(&z);
  mp_free(&z);
  *view = mp_view(r);
  return r;
}

static a68_val compl_of(a68_val re, a68_val im) {
  a68_slots* c = slots_alloc(2);
  c->s[0] = re; c->s[1] = im;
  return mk_ptr(T_STRUCT, (a68_obj*) c, 0);
}

static void compl_parts(a68_val v, a68_val* re, a68_val* im) {
  a68_slots* c;
  if (v.tag == T_UNDEF) die("attempt to use an uninitialised LONG COMPLEX value");
  if (v.tag != T_STRUCT) die("internal: LONG COMPLEX expected");
  c = (a68_slots*) v.v.p;
  *re = c->s[0]; *im = c->s[1];
}

/* An integer value (T_INT or T_BIGINT) as decimal text; caller frees. */
static char* int_text(a68_val v) {
  char* s;
  if (v.tag == T_INT) {
    s = (char*) xmalloc(32);
    snprintf(s, 32, "%lld", (long long) v.v.i);
  } else if (v.tag == T_BIGINT) {
    a68_leaf* l = (a68_leaf*) v.v.p;
    s = (char*) xmalloc((size_t) l->h.n + 1);
    memcpy(s, l->d, l->h.n);
    s[l->h.n] = 0;
  } else if (v.tag == T_UNDEF) {
    die("attempt to use an uninitialised value");
  } else {
    die("internal: INT expected");
  }
  return s;
}

/* A LONG INT value for an integral number (`toIntTrunc`): T_INT when it fits. */
static a68_val long_int_of(const a68_mp* z) {
  int64_t k;
  if (mp_to_i64_trunc(z, &k) == 0) return mk_int(k);
  {
    char buf[1024];
    size_t n = 0; int64_t j;
    if (mp_dig(z, 1) < 0.0) buf[n++] = '-';
    n += (size_t) snprintf(buf + n, sizeof buf - n, "%lld", (long long) fabs(mp_dig(z, 1)));
    for (j = 2; j <= z->ex + 1 && n + 8 < sizeof buf; j++)
      n += (size_t) snprintf(buf + n, sizeof buf - n, "%07lld", (long long) mp_dig(z, (int) j));
    {
      a68_leaf* l = leaf_alloc(EK_BYTES, (uint32_t) n);
      memcpy(l->d, buf, n);
      return mk_ptr(T_BIGINT, (a68_obj*) l, 0);
    }
  }
}

/* ------------------------------------------------------------------ conversions */

/* `Interp.intToMP`. */
a68_val mp_of_int(const a68_big* k, int64_t longness) {
  char* s = big_to_dec(k);
  char err[MP_ERR_LEN];
  a68_mp z;
  a68_val r;
  if (mp_of_dec_string(s, strlen(s), mp_digits_of(longness), &z, err)) { free(s); die2(int_mode(longness), "value out of bounds"); }
  free(s);
  r = mp_leaf(&z);
  mp_free(&z);
  return r;
}

/* `Interp.realToLongReal`: `real_to_mp` at LONG precision, zero-extended for LONG LONG. */
a68_val mp_of_real(double x, int64_t longness) {
  char err[MP_ERR_LEN];
  a68_mp z = mp_nil(MP_LONG_DIGITS);
  a68_val r;
  if (mp_real_to_mp(&z, x, MP_LONG_DIGITS, err)) { mp_free(&z); die(err); }
  if (longness >= 2) {
    a68_mp w = mp_len(&z, MP_LONG_DIGITS, a68_ll_digits);
    r = mp_leaf(&w);
    mp_free(&w);
  } else r = mp_leaf(&z);
  mp_free(&z);
  return r;
}

/* `MP.stringToMp`. */
a68_val mp_of_string(const uint8_t* s, size_t n, int64_t longness, int* ok) {
  char err[MP_ERR_LEN];
  int digs = mp_digits_of(longness);
  a68_mp z = mp_nil(digs);
  a68_val r;
  if (mp_string_to_mp(&z, (const char*) s, n, digs, ok, err)) { mp_free(&z); die(err); }
  r = mp_leaf(&z);
  mp_free(&z);
  return r;
}

/* `MP.toDecParts`: `|d1| d2 … d_digs` in radix R, times 10^((ex - digs + 1) · 7). */
int mp_to_dec(a68_val z, int64_t longness, a68_dec* out) {
  a68_mp x = mp_view(z);
  int digs = mp_digits_of(longness), j;
  char* buf = (char*) xmalloc((size_t) digs * 8 + 32);
  size_t n = 0;
  n += (size_t) snprintf(buf + n, 32, "%lld", (long long) fabs(mp_dig(&x, 1)));
  for (j = 2; j <= digs; j++) n += (size_t) snprintf(buf + n, 9, "%07lld", (long long) mp_dig(&x, j));
  out->mant = big_from_dec(buf, n);
  out->exp = (x.ex - digs + 1) * MP_LOG_RADIX;
  free(buf);
  return mp_dig(&x, 1) < 0.0;
}

/* `MP.mpToReal`. */
double mp_to_real(a68_val z, int64_t longness) {
  a68_mp x = mp_view(z);
  char err[MP_ERR_LEN];
  double r;
  if (mp_to_double(&x, mp_digits_of(longness), &r, err)) die(err);
  return r;
}

/* ------------------------------------------------------------------ formatting */

char* mp_fmt_whole(a68_val z, int64_t longness, int64_t width) {
  a68_mp x = mp_view(z);
  char err[MP_ERR_LEN];
  char* s = mpfmt_whole(&x, mp_digits_of(longness), width, llw(), err);
  if (!s) die(err);
  return s;
}

char* mp_fmt_fixed(a68_val z, int64_t longness, int64_t width, int64_t after) {
  a68_mp x = mp_view(z);
  char err[MP_ERR_LEN];
  char* s = mpfmt_fixed(&x, mp_digits_of(longness), width, after, llw(), err);
  if (!s) die(err);
  return s;
}

char* mp_fmt_float(a68_val z, int64_t longness, int64_t width, int64_t after, int64_t expo, int64_t frmt) {
  a68_mp x = mp_view(z);
  char err[MP_ERR_LEN];
  char* s = mpfmt_float(&x, mp_digits_of(longness), width, after, expo, frmt, llw(), err);
  if (!s) die(err);
  return s;
}

/* `Interp.mpFloatStd`. */
char* mp_float_std(a68_val z, int64_t longness) {
  a68_mp x = mp_view(z);
  char err[MP_ERR_LEN];
  char* s = mpfmt_std(&x, longness <= 1 ? 1 : 2, a68_ll_digits, err);
  if (!s) die(err);
  return s;
}

/* `MPFmt.checkFinite`. */
void mp_check_finite(a68_val z) {
  a68_mp x = mp_view(z);
  char err[MP_ERR_LEN];
  if (mpfmt_check_finite(&x, err)) die(err);
}

/* ------------------------------------------------------------------ operators */

/* `Interp.mpDyadic`. */
a68_val mp_dyadic(const char* op, int64_t longness, a68_val xv, a68_val yv) {
  int digs = mp_digits_of(longness);
  a68_mp y = mp_view(yv), x;
  char err[MP_ERR_LEN];
  a68_val r;
  int c = -2;
  x = mp_view(xv);
  if (strcmp(op, "=") == 0) c = mp_eq(&x, &y, digs, err);
  else if (strcmp(op, "/=") == 0) c = mp_ne(&x, &y, digs, err);
  else if (strcmp(op, "<") == 0) c = mp_lt(&x, &y, digs, err);
  else if (strcmp(op, "<=") == 0) c = mp_le(&x, &y, digs, err);
  else if (strcmp(op, ">") == 0) c = mp_gt(&x, &y, digs, err);
  else if (strcmp(op, ">=") == 0) c = mp_ge(&x, &y, digs, err);
  if (c != -2) { if (c < 0) die(err); return mk_bool(c); }
  r = fresh_copy(xv, digs, &x);
  if (strcmp(op, "+") == 0) check(mp_add(&x, &x, &y, digs, err), err);
  else if (strcmp(op, "-") == 0) check(mp_sub(&x, &x, &y, digs, err), err);
  else if (strcmp(op, "*") == 0) {
    check(mp_mul(&x, &x, &y, digs, err), err);
    if (!mp_is_finite(&x)) die2(real_mode(longness), "value is not finite");
  } else if (strcmp(op, "/") == 0) {
    check(mp_div(&x, &x, &y, digs, err), err);
    if (mp_is_nan(&x)) die2(real_mode(longness), "value is not a number");
  } else if (strcmp(op, "**") == 0) check(mp_pow(&x, &x, &y, digs, err), err);
  else die2("internal:", op);
  return mp_commit(r, &x);
}

/* `Interp.mpMonadic`. */
a68_val mp_monadic(const char* op, int64_t longness, a68_val xv) {
  int digs = mp_digits_of(longness);
  char err[MP_ERR_LEN];
  a68_mp x;
  a68_val r;
  if (strcmp(op, "+") == 0) { (void) mp_view(xv); return xv; }
  if (strcmp(op, "SIGN") == 0) {
    double d;
    x = mp_view(xv);
    d = mp_dig(&x, 1);
    return mk_int(d > 0.0 ? 1 : d < 0.0 ? -1 : 0);
  }
  if (strcmp(op, "SHORTEN") == 0) {
    if (longness <= 1) return mk_real(mp_to_real(xv, longness));
    x = mp_view(xv);
    {
      a68_mp z;
      r = fresh_nil(MP_LONG_DIGITS, &z);
      check(mp_shorten(&z, MP_LONG_DIGITS, &x, digs, err), err);
      return mp_commit(r, &z);
    }
  }
  r = fresh_copy(xv, digs, &x);
  if (strcmp(op, "-") == 0) check(mp_minus(&x, err), err);
  else if (strcmp(op, "ABS") == 0) check(mp_abs(&x, err), err);
  else if (strcmp(op, "ENTIER") == 0) { check(mp_entier(&x, &x, digs, err), err); return long_int_of(&x); }
  else if (strcmp(op, "ROUND") == 0) { check(mp_round(&x, &x, digs, err), err); return long_int_of(&x); }
  else die2("internal: monadic operator", op);
  return mp_commit(r, &x);
}

/* `Interp.mpComplDyadic`. */
a68_val mp_compl_dyadic(const char* op, int64_t longness, a68_val av, a68_val bv) {
  int digs = mp_digits_of(longness);
  char err[MP_ERR_LEN];
  a68_val arv, aiv, brv, biv, rr, ri;
  a68_mp ar, ai, br, bi;
  compl_parts(av, &arv, &aiv);
  compl_parts(bv, &brv, &biv);
  br = mp_view(brv); bi = mp_view(biv);
  rr = fresh_copy(arv, digs, &ar);
  ri = fresh_copy(aiv, digs, &ai);
  if (strcmp(op, "+") == 0) {
    check(mp_add(&ai, &ai, &bi, digs, err), err);
    check(mp_add(&ar, &ar, &br, digs, err), err);
  } else if (strcmp(op, "-") == 0) {
    check(mp_sub(&ai, &ai, &bi, digs, err), err);
    check(mp_sub(&ar, &ar, &br, digs, err), err);
  } else if (strcmp(op, "*") == 0) {
    check(mp_cmul(&ar, &ai, &br, &bi, digs, err), err);
  } else if (strcmp(op, "/") == 0) {
    check(mp_cdiv(&ar, &ai, &br, &bi, digs, err), err);
    if (mp_is_nan(&ar) || mp_is_nan(&ai)) die2(compl_mode(longness), "value is not finite");
  } else if (strcmp(op, "=") == 0 || strcmp(op, "/=") == 0) {
    int eq;
    check(mp_sub(&ai, &ai, &bi, digs, err), err);
    check(mp_sub(&ar, &ar, &br, digs, err), err);
    eq = mp_dig(&ar, 1) == 0.0 && mp_dig(&ai, 1) == 0.0;
    return mk_bool(strcmp(op, "=") == 0 ? eq : !eq);
  } else die2("internal: LONG COMPL operator", op);
  return compl_of(mp_commit(rr, &ar), mp_commit(ri, &ai));
}

/* `Interp.mpComplPow`: `LONG COMPLEX ** INT`. */
a68_val mp_compl_pow(int64_t longness, a68_val av, int64_t j) {
  int digs = mp_digits_of(longness);
  char err[MP_ERR_LEN];
  a68_val arv, aiv, rr, ri;
  a68_mp re, im;
  compl_parts(av, &arv, &aiv);
  rr = fresh_nil(digs, &re);
  ri = fresh_nil(digs, &im);
  { a68_mp x = mp_view(arv); mp_move(&re, &x, digs); }
  { a68_mp x = mp_view(aiv); mp_move(&im, &x, digs); }
  check(mp_cpow_int(&re, &im, j, digs, err), err);
  if (j < 0 && (mp_is_nan(&re) || mp_is_nan(&im))) die2(compl_mode(longness), "value is not finite");
  return compl_of(mp_commit(rr, &re), mp_commit(ri, &im));
}

/* `Interp.mpComplMonadic`. */
a68_val mp_compl_monadic(const char* op, int64_t longness, a68_val v) {
  int digs = mp_digits_of(longness);
  char err[MP_ERR_LEN];
  a68_val rev, imv, rr, ri;
  a68_mp re, im, t;
  compl_parts(v, &rev, &imv);
  if (strcmp(op, "+") == 0) return v;
  if (strcmp(op, "RE") == 0) return fresh_copy(rev, 0, &re);
  if (strcmp(op, "IM") == 0) return fresh_copy(imv, 0, &im);
  if (strcmp(op, "-") == 0) {
    rr = fresh_copy(rev, 0, &re); ri = fresh_copy(imv, 0, &im);
    mp_negate1(&re); mp_negate1(&im);
    return compl_of(mp_commit(rr, &re), mp_commit(ri, &im));
  }
  if (strcmp(op, "CONJ") == 0) {
    rr = fresh_copy(rev, 0, &re); ri = fresh_copy(imv, 0, &im);
    mp_negate1(&im);
    return compl_of(mp_commit(rr, &re), mp_commit(ri, &im));
  }
  if (strcmp(op, "ABS") == 0 || strcmp(op, "ARG") == 0) {
    a68_val r = fresh_nil(digs, &t);
    re = mp_view(rev); im = mp_view(imv);
    if (op[1] == 'B') check(mp_hypot(&t, &re, &im, digs, err), err);
    else check(mp_atan2(&t, &re, &im, digs, err), err);
    return mp_commit(r, &t);
  }
  if (strcmp(op, "SHORTEN") == 0) {
    if (longness <= 1) return compl_of(mk_real(mp_to_real(rev, longness)), mk_real(mp_to_real(imv, longness)));
    rr = fresh_nil(MP_LONG_DIGITS, &re); ri = fresh_nil(MP_LONG_DIGITS, &im);
    { a68_mp x = mp_view(rev); check(mp_shorten(&re, MP_LONG_DIGITS, &x, digs, err), err); }
    { a68_mp x = mp_view(imv); check(mp_shorten(&im, MP_LONG_DIGITS, &x, digs, err), err); }
    return compl_of(mp_commit(rr, &re), mp_commit(ri, &im));
  }
  die2("internal: monadic operator", op);
}

/* ------------------------------------------------------------------ functions */

/* `Interp.splitLong`: `(length, base name)` of a `long…` / `longlong…` name. */
static int split_long(const char* name, int64_t* n, const char** base) {
  if (strncmp(name, "longlong", 8) == 0) { *n = 2; *base = name + 8; return 1; }
  if (strncmp(name, "long", 4) == 0) { *n = 1; *base = name + 4; return 1; }
  return 0;
}

static mp_fn math_fn_of(const char* base) {
  static const struct { const char* n; mp_fn f; } tab[] = {
    { "sqrt", mp_sqrt }, { "curt", mp_curt }, { "cbrt", mp_curt }, { "exp", mp_exp }, { "ln", mp_ln },
    { "log", mp_log }, { "sinh", mp_sinh }, { "cosh", mp_cosh }, { "tanh", mp_tanh },
    { "arcsinh", mp_asinh }, { "arccosh", mp_acosh }, { "arctanh", mp_atanh },
    { "sin", mp_sin }, { "cos", mp_cos }, { "tan", mp_tan }, { "cot", mp_cot },
    { "arcsin", mp_asin }, { "arccos", mp_acos }, { "arctan", mp_atan },
    { "csc", mp_csc }, { "sec", mp_sec }, { "arccsc", mp_arccsc }, { "arcsec", mp_arcsec }, { "arccot", mp_arccot },
    { "sindg", mp_sindg }, { "cosdg", mp_cosdg }, { "tandg", mp_tandg }, { "cotdg", mp_cotdg },
    { "cscdg", mp_cscdg }, { "secdg", mp_secdg }, { "arcsindg", mp_arcsindg }, { "arccosdg", mp_arccosdg },
    { "arctandg", mp_arctandg }, { "arccotdg", mp_arccotdg }, { "arccscdg", mp_arccscdg },
    { "arcsecdg", mp_arcsecdg }, { "cas", mp_cas }, { NULL, NULL } };
  int i;
  for (i = 0; tab[i].n; i++) if (strcmp(tab[i].n, base) == 0) return tab[i].f;
  return NULL;
}

/* `Interp.mpMathFn`: the LONG versions of the functions of one real argument. */
int mp_math_fn(const char* name, a68_val xv, a68_val* out) {
  int64_t n; const char* base; mp_fn f;
  int digs;
  char err[MP_ERR_LEN];
  a68_mp x;
  a68_val r;
  if (!split_long(name, &n, &base)) return 0;
  f = math_fn_of(base);
  if (!f) return 0;
  digs = mp_digits_of(n);
  r = fresh_copy(xv, digs, &x);
  check(f(&x, &x, digs, err), err);
  if (mp_is_nan(&x)) die2(real_mode(n), "value is not a number");
  if (!mp_is_finite(&x)) die2(real_mode(n), "value is not finite");
  *out = mp_commit(r, &x);
  return 1;
}

typedef int (*mp_cfn)(a68_mp*, a68_mp*, int, char*);

/* `Interp.mpComplFn`: `long complex sqrt` and the other LONG COMPLEX functions. */
int mp_compl_fn(const char* name, a68_val xv, a68_val* out) {
  static const struct { const char* n; mp_cfn f; } tab[] = {
    { "sqrt", mp_csqrt }, { "exp", mp_cexp }, { "ln", mp_cln }, { "sin", mp_csin }, { "cos", mp_ccos },
    { "tan", mp_ctan }, { "arcsin", mp_casin }, { "arccos", mp_cacos }, { "arctan", mp_catan },
    { "sinh", mp_csinh }, { "cosh", mp_ccosh }, { "tanh", mp_ctanh }, { "arcsinh", mp_casinh },
    { "arccosh", mp_cacosh }, { "arctanh", mp_catanh }, { "atanh", mp_catanh }, { NULL, NULL } };
  int64_t n; const char* base; mp_cfn f = NULL;
  int i, digs;
  char err[MP_ERR_LEN];
  a68_val rev, imv, rr, ri;
  a68_mp re, im;
  if (!split_long(name, &n, &base)) return 0;
  if (strncmp(base, "complex", 7) != 0) return 0;
  base += 7;
  for (i = 0; tab[i].n; i++) if (strcmp(tab[i].n, base) == 0) f = tab[i].f;
  if (!f) return 0;
  digs = mp_digits_of(n);
  compl_parts(xv, &rev, &imv);
  rr = fresh_copy(rev, digs, &re);
  ri = fresh_copy(imv, digs, &im);
  check(f(&re, &im, digs, err), err);
  if (!mp_is_finite(&re) || !mp_is_finite(&im)) die2("math error in", compl_mode(n));
  *out = compl_of(mp_commit(rr, &re), mp_commit(ri, &im));
  return 1;
}

/* `Interp.mpConst`: the LONG constants of the prelude. */
int mp_const(const char* name, a68_val* out) {
  int64_t n; const char* base;
  int digs, k;
  char err[MP_ERR_LEN];
  a68_mp z;
  if (!split_long(name, &n, &base)) return 0;
  digs = mp_digits_of(n);
  if (strcmp(base, "pi") == 0) {
    *out = fresh_nil(digs, &z);
    check(mp_pi(&z, MP_PI, digs, err), err);
  } else if (strcmp(base, "maxreal") == 0) {
    *out = fresh_nil(digs, &z);
    for (k = 1; k <= digs; k++) z.d[k] = MP_RADIX - 1;
    z.ex = MP_MAX_EXPO - 1;
  } else if (strcmp(base, "minreal") == 0) {
    *out = fresh_nil(digs, &z);
    z.d[1] = 1.0; z.ex = -MP_MAX_EXPO;
  } else if (strcmp(base, "smallreal") == 0) {
    *out = fresh_nil(digs, &z);
    z.d[1] = 1.0; z.ex = 1 - digs;
  } else if (strcmp(base, "infinity") == 0 || strcmp(base, "inf") == 0 || strcmp(base, "plusinfinity") == 0
             || strcmp(base, "plusinf") == 0) {
    *out = fresh_nil(digs, &z);
    mp_set_pinf(&z);
  } else if (strcmp(base, "minusinfinity") == 0 || strcmp(base, "minusinf") == 0) {
    *out = fresh_nil(digs, &z);
    mp_set_minf(&z);
  } else if (strcmp(base, "nan") == 0) {
    *out = fresh_nil(digs, &z);
    mp_set_nan(&z);
  } else return 0;
  mp_commit(*out, &z);
  return 1;
}

/* The `longarctan2`, `longlongarctan2` and `…dg` arms of `Interp.callBuiltin`:
   `genie_atan2_mp` is `atan2_mp (p, x, y, x, digs)` with `x` the first argument. */
a68_val mp_arctan2(const char* name, a68_val av, a68_val bv) {
  int64_t n; const char* base;
  int digs;
  char err[MP_ERR_LEN];
  a68_mp x, y;
  a68_val r;
  if (!split_long(name, &n, &base)) die("internal: arctan2");
  digs = mp_digits_of(n);
  y = mp_view(bv);
  r = fresh_copy(av, digs, &x);
  check(mp_atan2(&x, &y, &x, digs, err), err);
  if (strcmp(base, "arctan2dg") == 0 && !mp_is_nan(&x)) {
    a68_mp g = mp_nil(digs);
    int rc = mp_pi(&g, MP_180_OVER_PI, digs, err) || mp_mul(&x, &x, &g, digs, err);
    mp_free(&g);
    check(rc, err);
  }
  if (mp_is_nan(&x)) die2(real_mode(n), "invalid argument");
  return mp_commit(r, &x);
}

/* `genie_long_next_random`: the REAL widened. */
a68_val mp_long_random(double r, int64_t longness) { return mp_of_real(r, longness); }

/* `Interp.widenValue` between REAL, LONG REAL, LONG LONG REAL and their INT
   counterparts (and the COMPL values built on them). */
a68_val mp_widen(a68_val v, int64_t from_longness, int64_t to_longness) {
  char err[MP_ERR_LEN];
  a68_mp z;
  if (v.tag == T_INT || v.tag == T_BIGINT) {
    /* an INT of any length to a REAL of length `to` */
    char* s = int_text(v);
    a68_mp x;
    a68_val r;
    if (to_longness <= 0) {
      a68_big* b = big_from_dec(s, strlen(s));
      double d = strtod(s, NULL);
      big_free(b);
      free(s);
      return mk_real(d);
    }
    if (mp_of_dec_string(s, strlen(s), mp_digits_of(to_longness), &x, err)) { free(s); die2(int_mode(to_longness), "value out of bounds"); }
    free(s);
    r = mp_leaf(&x);
    mp_free(&x);
    return r;
  }
  if (v.tag == T_REAL) {
    if (from_longness <= 0 && to_longness >= 1) return mp_of_real(v.v.r, to_longness);
    return v;
  }
  if (v.tag == T_MP) {
    if (from_longness == 1 && to_longness >= 2) {
      a68_mp x = mp_view(v);
      a68_val r = fresh_nil(a68_ll_digits, &z);
      mp_move(&z, &x, MP_LONG_DIGITS);
      return mp_commit(r, &z);
    }
    return v;
  }
  if (v.tag == T_STRUCT) {
    a68_val re, im;
    compl_parts(v, &re, &im);
    if (re.tag == T_REAL || re.tag == T_MP)
      return compl_of(mp_widen(re, from_longness, to_longness), mp_widen(im, from_longness, to_longness));
    return v;
  }
  if (v.tag == T_UNDEF) die("attempt to use an uninitialised value");
  return v;
}
