/* Native helpers of the LLVM back end: the pieces of a68g's arithmetic that are more than
   one instruction and a check.  Each reproduces the check its interpreted counterpart
   performs (`Interp.powIntInt`, `powRealInt`, the REAL standard functions), reporting a
   failure through a68rt_arith_error like the C back end's inline helpers. */
#include <stdint.h>
#include <stdio.h>
#include <math.h>
#include "io.h"

void a68rt_arith_error(uint32_t kind, int w);

static int64_t die_i(uint32_t k) { a68rt_arith_error(k, 0); return 0; }
static double die_r(uint32_t k) { a68rt_arith_error(k, 0); return 0.0; }

static int64_t rng(int64_t v) {
  if (v > 2147483647LL || v < -2147483647LL) return die_i(0);
  return v;
}
static double chk_r(double x) {
  if (x != x) return die_r(3);
  if (x > 1.7976931348623157e308 || x < -1.7976931348623157e308) return die_r(2);
  return x;
}

int64_t a68n_pow_i(int64_t m, int64_t n) {
  if (n < 0) return die_i(8);
  if (m == 0 && n == 0) return 1;
  if (m == 0 || m == 1) return m;
  if (m == -1) return (n % 2 == 0) ? 1 : -1;
  uint64_t nn = (uint64_t) n, bit = 1; int64_t mm = m, p = 1;
  for (;;) {
    if (nn & bit) p = rng(p * mm);
    bit <<= 1;
    if (bit <= nn) mm = rng(mm * mm);
    if (!(bit <= nn)) break;
  }
  return p;
}

double a68n_pow_ri(double x, int64_t n) {
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
    if (p != p || p > 1.7976931348623157e308 || p < -1.7976931348623157e308) return die_r(2);
  }
  return n < 0 ? 1.0 / p : p;
}

double a68n_pow_rr(double x, double y) {
  if (y == 0.0) return 1.0;
  if (x < 0.0) return die_r(7);
  if (x == 0.0) { if (y < 0.0) return die_r(7); return 0.0; }
  return exp(y * log(x));
}

int64_t a68n_entier(double x) {
  if (x < -2147483647.0 || x > 2147483647.0) return die_i(4);
  return (int64_t) floor(x);
}

int64_t a68n_round(double x) {
  if (x < -2147483647.0 || x > 2147483647.0) return die_i(4);
  double ax = x < 0 ? -x : x;
  int64_t n = (int64_t) floor(ax + 0.5);
  return x < 0 ? -n : n;
}

#define DOM1(f, e) double a68n_m_##f(double x) { if (x < -1.0 || x > 1.0) return die_r(3); return chk_r(e(x)); }
#define DOMP(f, e) double a68n_m_##f(double x) { if (x < 0.0) return die_r(3); return chk_r(e(x)); }
#define PLAIN(f, e) double a68n_m_##f(double x) { return chk_r(e(x)); }
DOM1(acos, acos) DOM1(arccos, acos) DOM1(arcsin, asin) DOM1(asin, asin)
PLAIN(arccosh, acosh) PLAIN(arcsinh, asinh) PLAIN(arctan, atan) PLAIN(arctanh, atanh) PLAIN(atan, atan)
PLAIN(cbrt, cbrt) PLAIN(curt, cbrt) PLAIN(cos, cos) PLAIN(cosh, cosh)
double a68n_m_exp(double x) { return exp(x); }
double a68n_m_exp2(double x) { return exp2(x); }
DOMP(ln, log) DOMP(log, log10) DOMP(log10, log10) PLAIN(log2, log2)
PLAIN(sin, sin) PLAIN(sinh, sinh) DOMP(sqrt, sqrt) PLAIN(tan, tan) PLAIN(tanh, tanh)

/* `PR echo` texts are printed when the program is read, before anything it prints */
void a68n_echo(const char* s) { fputs(s, stdout); fflush(stdout); }
