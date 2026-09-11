/* mp_test.c -- differential test driver for the multi-precision library.

   Reads an operations file (one operation per line, written by csrc/mp_gen.py together
   with the equivalent Algol 68 program) and prints, for each operation, exactly what the
   evaluator's `print` prints for it.  `diff` of the two outputs is the test:

     cc -std=c99 -O2 -ffp-contract=off -o mp_test mp.c mpmath.c mpfmt.c mp_test.c -lm
     python3 mp_gen.py SEED N [precision] > ops.txt      (also writes prog.a68)
     ./mp_test [ll_digits] < ops.txt > c.out
     .lake/build/bin/a68lean run prog.a68 > a68.out
     diff a68.out c.out

   Operand denotations are converted with `mp_string_to_mp` at the precision of the mode,
   as the evaluator converts a LONG denotation (`genie_denotation`); a leading '-' in the
   ops file stands for the monadic minus the program applies. */
#include "mp.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

static int ll_digits = MP_LONG_LONG_DIGITS;
static long line_no = 0;

static void fail(const char* what, const char* err) {
  printf("ERROR line %ld: %s: %s\n", line_no, what, err);
}

static int digits_of(const char* m) { return strcmp(m, "LL") == 0 ? ll_digits : MP_LONG_DIGITS; }
static int length_of(const char* m) { return strcmp(m, "LL") == 0 ? 2 : 1; }

/* A LONG denotation (with an optional leading '-') at `digs` digits. */
static a68_mp denot(const char* s, int digs) {
  a68_mp z = mp_nil(digs);
  char err[MP_ERR_LEN];
  int valid = 1, neg = s[0] == '-';
  if (mp_string_to_mp(&z, s + neg, strlen(s + neg), digs, &valid, err) || !valid) {
    printf("ERROR line %ld: bad denotation %s\n", line_no, s);
    exit(2);
  }
  if (neg) { mp_minus(&z, err); }
  return z;
}

static void print_std(const a68_mp* x, int length) {
  char err[MP_ERR_LEN];
  char* s = mpfmt_std(x, length, ll_digits, err);
  if (!s) { fail("print", err); return; }
  fputs(s, stdout);
  free(s);
}

/* `whole` of an exact integer given as a decimal magnitude. */
static void print_whole_digits(const char* mag, int neg, int64_t width) {
  int64_t ndig = (int64_t) strlen(mag), length = width == 0 ? ndig : llabs(width) - ((neg || width > 0) ? 1 : 0);
  int64_t pad;
  if (ndig > length || length == 0) { for (pad = 0; pad < (width == 0 ? 1 : llabs(width)); pad++) putchar('*'); return; }
  pad = width == 0 ? 0 : llabs(width) - ndig - ((neg || width > 0) ? 1 : 0);
  while (pad-- > 0) putchar(' ');
  if (neg) putchar('-'); else if (width > 0) putchar('+');
  fputs(mag, stdout);
}

/* The exact decimal magnitude of an integral number (`|d1| d2 … d(ex+1)`). */
static void int_digits(const a68_mp* z, char* buf, size_t cap) {
  size_t n = 0; int64_t j;
  if (z->ex < 0) { snprintf(buf, cap, "0"); return; }
  n += (size_t) snprintf(buf + n, cap - n, "%lld", (long long) fabs(mp_dig(z, 1)));
  for (j = 2; j <= z->ex + 1; j++) n += (size_t) snprintf(buf + n, cap - n, "%07lld", (long long) mp_dig(z, (int) j));
}

static void print_long_int(const a68_mp* z, const char* m) {
  char buf[512];
  int64_t width = length_of(m) == 1 ? 50 : (int64_t) ll_digits * 7 + 1;
  int_digits(z, buf, sizeof buf);
  print_whole_digits(buf, mp_dig(z, 1) < 0.0, width);
}

static void print_int(int64_t v) { char* s = mpfmt_whole_i64(v, 11); fputs(s, stdout); free(s); }

typedef int (*cfn)(a68_mp*, a68_mp*, int, char*);

static mp_fn lookup_fn(const char* name) {
  static const struct { const char* n; mp_fn f; } tab[] = {
    { "sqrt", mp_sqrt }, { "curt", mp_curt }, { "cbrt", mp_curt }, { "exp", mp_exp }, { "ln", mp_ln },
    { "log", mp_log }, { "sin", mp_sin }, { "cos", mp_cos }, { "tan", mp_tan }, { "cot", mp_cot },
    { "arcsin", mp_asin }, { "arccos", mp_acos }, { "arctan", mp_atan }, { "sinh", mp_sinh },
    { "cosh", mp_cosh }, { "tanh", mp_tanh }, { "arcsinh", mp_asinh }, { "arccosh", mp_acosh },
    { "arctanh", mp_atanh }, { "csc", mp_csc }, { "sec", mp_sec }, { "arccsc", mp_arccsc },
    { "arcsec", mp_arcsec }, { "arccot", mp_arccot }, { "sindg", mp_sindg }, { "cosdg", mp_cosdg },
    { "tandg", mp_tandg }, { "cotdg", mp_cotdg }, { "cscdg", mp_cscdg }, { "secdg", mp_secdg },
    { "arcsindg", mp_arcsindg }, { "arccosdg", mp_arccosdg }, { "arctandg", mp_arctandg },
    { "arccotdg", mp_arccotdg }, { "arccscdg", mp_arccscdg }, { "arcsecdg", mp_arcsecdg },
    { "cas", mp_cas }, { NULL, NULL } };
  int i;
  for (i = 0; tab[i].n; i++) if (strcmp(tab[i].n, name) == 0) return tab[i].f;
  return NULL;
}

static cfn lookup_cfn(const char* name) {
  static const struct { const char* n; cfn f; } tab[] = {
    { "sqrt", mp_csqrt }, { "exp", mp_cexp }, { "ln", mp_cln }, { "sin", mp_csin }, { "cos", mp_ccos },
    { "tan", mp_ctan }, { "arcsin", mp_casin }, { "arccos", mp_cacos }, { "arctan", mp_catan },
    { "sinh", mp_csinh }, { "cosh", mp_ccosh }, { "tanh", mp_ctanh }, { "arcsinh", mp_casinh },
    { "arccosh", mp_cacosh }, { "arctanh", mp_catanh }, { NULL, NULL } };
  int i;
  for (i = 0; tab[i].n; i++) if (strcmp(tab[i].n, name) == 0) return tab[i].f;
  return NULL;
}

/* `Interp.mpDyadic` and `mpComplDyadic` on two numbers; prints the result. */
static void do_bin(const char* m, const char* op, a68_mp* x, a68_mp* y) {
  int digs = digits_of(m), len = length_of(m), rc = 0;
  char err[MP_ERR_LEN];
  if (strcmp(op, "+") == 0) rc = mp_add(x, x, y, digs, err);
  else if (strcmp(op, "-") == 0) rc = mp_sub(x, x, y, digs, err);
  else if (strcmp(op, "*") == 0) rc = mp_mul(x, x, y, digs, err);
  else if (strcmp(op, "/") == 0) rc = mp_div(x, x, y, digs, err);
  else if (strcmp(op, "**") == 0) rc = mp_pow(x, x, y, digs, err);
  else {
    int r = -1;
    if (strcmp(op, "=") == 0) r = mp_eq(x, y, digs, err);
    else if (strcmp(op, "/=") == 0) r = mp_ne(x, y, digs, err);
    else if (strcmp(op, "<") == 0) r = mp_lt(x, y, digs, err);
    else if (strcmp(op, "<=") == 0) r = mp_le(x, y, digs, err);
    else if (strcmp(op, ">") == 0) r = mp_gt(x, y, digs, err);
    else if (strcmp(op, ">=") == 0) r = mp_ge(x, y, digs, err);
    if (r < 0) fail(op, err); else putchar(r ? 'T' : 'F');
    return;
  }
  if (rc) fail(op, err); else print_std(x, len);
}

int main(int argc, char** argv) {
  char line[4096];
  if (argc > 1) ll_digits = atoi(argv[1]);
  mp_cache_reset();
  while (fgets(line, sizeof line, stdin)) {
    char* tok[16]; int nt = 0;
    char* p = strtok(line, " \t\r\n");
    char err[MP_ERR_LEN];
    line_no++;
    while (p && nt < 16) { tok[nt++] = p; p = strtok(NULL, " \t\r\n"); }
    if (nt == 0) continue;
    if ((strcmp(tok[0], "bin") == 0 || strcmp(tok[0], "cmp") == 0) && nt == 5) {
      a68_mp x = denot(tok[3], digits_of(tok[1])), y = denot(tok[4], digits_of(tok[1]));
      do_bin(tok[1], tok[2], &x, &y);
      mp_free(&x); mp_free(&y);
    } else if (strcmp(tok[0], "powi") == 0 && nt == 4) {
      a68_mp x = denot(tok[2], digits_of(tok[1]));
      if (mp_pow_int(&x, &x, atoll(tok[3]), digits_of(tok[1]), err)) fail("**", err); else print_std(&x, length_of(tok[1]));
      mp_free(&x);
    } else if (strcmp(tok[0], "mon") == 0 && nt == 4) {
      int digs = digits_of(tok[1]);
      a68_mp x = denot(tok[3], digs);
      const char* op = tok[2];
      if (strcmp(op, "-") == 0) { if (mp_minus(&x, err)) fail(op, err); else print_std(&x, length_of(tok[1])); }
      else if (strcmp(op, "ABS") == 0) { if (mp_abs(&x, err)) fail(op, err); else print_std(&x, length_of(tok[1])); }
      else if (strcmp(op, "SIGN") == 0) { double d = mp_dig(&x, 1); print_int(d > 0 ? 1 : d < 0 ? -1 : 0); }
      else if (strcmp(op, "ENTIER") == 0) { if (mp_entier(&x, &x, digs, err)) fail(op, err); else print_long_int(&x, tok[1]); }
      else if (strcmp(op, "ROUND") == 0) { if (mp_round(&x, &x, digs, err)) fail(op, err); else print_long_int(&x, tok[1]); }
      mp_free(&x);
    } else if (strcmp(tok[0], "shorten") == 0 && nt == 2) {          /* SHORTEN of a LONG LONG REAL */
      a68_mp x = denot(tok[1], ll_digits), z = mp_nil(MP_LONG_DIGITS);
      if (mp_shorten(&z, MP_LONG_DIGITS, &x, ll_digits, err)) fail("SHORTEN", err); else print_std(&z, 1);
      mp_free(&x); mp_free(&z);
    } else if (strcmp(tok[0], "leng") == 0 && nt == 2) {             /* LENG of a LONG REAL */
      a68_mp x = denot(tok[1], MP_LONG_DIGITS), z = mp_len(&x, MP_LONG_DIGITS, ll_digits);
      print_std(&z, 2);
      mp_free(&x); mp_free(&z);
    } else if (strcmp(tok[0], "real") == 0 && nt == 3) {             /* LENG of a REAL, at length 1 or 2 */
      double r = strtod(tok[2], NULL);
      a68_mp z = mp_nil(MP_LONG_DIGITS);
      if (mp_real_to_mp(&z, r, MP_LONG_DIGITS, err)) fail("LENG", err);
      else if (length_of(tok[1]) == 2) { a68_mp w = mp_len(&z, MP_LONG_DIGITS, ll_digits); print_std(&w, 2); mp_free(&w); }
      else print_std(&z, 1);
      mp_free(&z);
    } else if (strcmp(tok[0], "roundtrip") == 0 && nt == 2) {        /* LENG SHORTEN of a LONG REAL */
      a68_mp x = denot(tok[1], MP_LONG_DIGITS), z = mp_nil(MP_LONG_DIGITS);
      double r;
      if (mp_to_double(&x, MP_LONG_DIGITS, &r, err) || mp_real_to_mp(&z, r, MP_LONG_DIGITS, err)) fail("SHORTEN", err);
      else print_std(&z, 1);
      mp_free(&x); mp_free(&z);
    } else if (strcmp(tok[0], "fn") == 0 && nt == 4) {
      mp_fn f = lookup_fn(tok[2]);
      a68_mp x = denot(tok[3], digits_of(tok[1]));
      if (!f) printf("ERROR unknown function %s", tok[2]);
      else if (f(&x, &x, digits_of(tok[1]), err)) fail(tok[2], err);
      else if (mp_is_nan(&x)) printf("ERROR %s value is not a number", tok[1]);
      else if (!mp_is_finite(&x)) printf("ERROR %s value is not finite", tok[1]);
      else print_std(&x, length_of(tok[1]));
      mp_free(&x);
    } else if ((strcmp(tok[0], "atan2") == 0 || strcmp(tok[0], "atan2dg") == 0) && nt == 4) {
      int digs = digits_of(tok[1]);
      /* `genie_atan2_mp`: `atan2_mp (p, x, y, x, digs)` with `x` the first argument */
      a68_mp x = denot(tok[2], digs), y = denot(tok[3], digs);
      int rc = mp_atan2(&x, &y, &x, digs, err);
      if (!rc && strcmp(tok[0], "atan2dg") == 0 && !mp_is_nan(&x)) {
        a68_mp g = mp_nil(digs);
        rc = mp_pi(&g, MP_180_OVER_PI, digs, err) || mp_mul(&x, &x, &g, digs, err);
        mp_free(&g);
      }
      if (rc) fail("arctan2", err); else print_std(&x, length_of(tok[1]));
      mp_free(&x); mp_free(&y);
    } else if (strcmp(tok[0], "pi") == 0 && nt == 2) {
      int digs = digits_of(tok[1]);
      a68_mp t = mp_nil(digs);
      if (mp_pi(&t, MP_PI, digs, err)) fail("pi", err); else print_std(&t, length_of(tok[1]));
      mp_free(&t);
    } else if (strcmp(tok[0], "fmt") == 0 && nt >= 5) {
      int digs = digits_of(tok[1]), llw = mpfmt_ll_real_width(ll_digits);
      a68_mp x = denot(tok[3], digs);
      char* s = NULL;
      if (strcmp(tok[2], "whole") == 0) s = mpfmt_whole(&x, digs, atoll(tok[4]), llw, err);
      else if (strcmp(tok[2], "fixed") == 0 && nt == 6) s = mpfmt_fixed(&x, digs, atoll(tok[4]), atoll(tok[5]), llw, err);
      else if (strcmp(tok[2], "float") == 0 && nt == 7) s = mpfmt_float(&x, digs, atoll(tok[4]), atoll(tok[5]), atoll(tok[6]), 1, llw, err);
      else if (strcmp(tok[2], "float2") == 0 && nt == 8) s = mpfmt_float(&x, digs, atoll(tok[4]), atoll(tok[5]), atoll(tok[6]), atoll(tok[7]), llw, err);
      if (!s) fail(tok[2], err); else { fputs(s, stdout); free(s); }
      mp_free(&x);
    } else if (strcmp(tok[0], "int") == 0 && nt == 5) {              /* LONG INT dyadic */
      int digs = digits_of(tok[1]);
      a68_mp x, y;
      if (mp_of_dec_string(tok[3], strlen(tok[3]), digs, &x, err) || mp_of_dec_string(tok[4], strlen(tok[4]), digs, &y, err)) { fail("int", err); continue; }
      if (strcmp(tok[2], "/") == 0) { if (mp_div(&x, &x, &y, digs, err)) fail("/", err); else print_std(&x, length_of(tok[1])); }
      else {
        int rc = 0;
        if (strcmp(tok[2], "+") == 0) rc = mp_add(&x, &x, &y, digs, err);
        else if (strcmp(tok[2], "-") == 0) rc = mp_sub(&x, &x, &y, digs, err);
        else if (strcmp(tok[2], "*") == 0) rc = mp_mul(&x, &x, &y, digs, err);
        else if (strcmp(tok[2], "%") == 0) rc = mp_over(&x, &x, &y, digs, err);
        else if (strcmp(tok[2], "%*") == 0) rc = mp_mod(&x, &x, &y, digs, err);
        else if (strcmp(tok[2], "**") == 0) rc = mp_pow_int(&x, &x, atoll(tok[4]), digs, err);
        if (rc) fail(tok[2], err); else print_long_int(&x, tok[1]);
      }
      mp_free(&x); mp_free(&y);
    } else if (strcmp(tok[0], "cbin") == 0 && nt == 7) {             /* LONG COMPL dyadic */
      int digs = digits_of(tok[1]), len = length_of(tok[1]), rc = 0;
      a68_mp a = denot(tok[3], digs), b = denot(tok[4], digs), c = denot(tok[5], digs), d = denot(tok[6], digs);
      if (strcmp(tok[2], "+") == 0) rc = mp_add(&b, &b, &d, digs, err) || mp_add(&a, &a, &c, digs, err);
      else if (strcmp(tok[2], "-") == 0) rc = mp_sub(&b, &b, &d, digs, err) || mp_sub(&a, &a, &c, digs, err);
      else if (strcmp(tok[2], "*") == 0) rc = mp_cmul(&a, &b, &c, &d, digs, err);
      else if (strcmp(tok[2], "/") == 0) rc = mp_cdiv(&a, &b, &c, &d, digs, err);
      else if (strcmp(tok[2], "=") == 0 || strcmp(tok[2], "/=") == 0) {
        rc = mp_sub(&b, &b, &d, digs, err) || mp_sub(&a, &a, &c, digs, err);
        if (!rc) { int eq = mp_dig(&a, 1) == 0.0 && mp_dig(&b, 1) == 0.0; putchar((strcmp(tok[2], "=") == 0 ? eq : !eq) ? 'T' : 'F'); }
        mp_free(&a); mp_free(&b); mp_free(&c); mp_free(&d);
        if (rc) fail(tok[2], err);
        putchar('\n'); continue;
      }
      if (rc) fail(tok[2], err); else { print_std(&a, len); print_std(&b, len); }
      mp_free(&a); mp_free(&b); mp_free(&c); mp_free(&d);
    } else if (strcmp(tok[0], "cpow") == 0 && nt == 5) {
      int digs = digits_of(tok[1]);
      a68_mp a = denot(tok[2], digs), b = denot(tok[3], digs);
      if (mp_cpow_int(&a, &b, atoll(tok[4]), digs, err)) fail("**", err);
      else { print_std(&a, length_of(tok[1])); print_std(&b, length_of(tok[1])); }
      mp_free(&a); mp_free(&b);
    } else if (strcmp(tok[0], "cmon") == 0 && nt == 5) {
      int digs = digits_of(tok[1]), len = length_of(tok[1]);
      a68_mp a = denot(tok[3], digs), b = denot(tok[4], digs), t = mp_nil(digs);
      const char* op = tok[2];
      if (strcmp(op, "-") == 0) { mp_negate1(&a); mp_negate1(&b); print_std(&a, len); print_std(&b, len); }
      else if (strcmp(op, "CONJ") == 0) { mp_negate1(&b); print_std(&a, len); print_std(&b, len); }
      else if (strcmp(op, "RE") == 0) print_std(&a, len);
      else if (strcmp(op, "IM") == 0) print_std(&b, len);
      else if (strcmp(op, "ABS") == 0) { if (mp_hypot(&t, &a, &b, digs, err)) fail(op, err); else print_std(&t, len); }
      else if (strcmp(op, "ARG") == 0) { if (mp_atan2(&t, &a, &b, digs, err)) fail(op, err); else print_std(&t, len); }
      mp_free(&a); mp_free(&b); mp_free(&t);
    } else if (strcmp(tok[0], "cfn") == 0 && nt == 5) {
      int digs = digits_of(tok[1]), len = length_of(tok[1]);
      cfn f = lookup_cfn(tok[2]);
      a68_mp a = denot(tok[3], digs), b = denot(tok[4], digs);
      if (!f) printf("ERROR unknown complex function %s", tok[2]);
      else if (f(&a, &b, digs, err)) fail(tok[2], err);
      else if (!mp_is_finite(&a) || !mp_is_finite(&b)) printf("ERROR math error in %s COMPL", tok[1]);
      else { print_std(&a, len); print_std(&b, len); }
      mp_free(&a); mp_free(&b);
    } else {
      printf("ERROR unknown op %s", tok[0]);
    }
    putchar('\n');
  }
  return 0;
}
