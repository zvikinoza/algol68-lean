/* Hand-written C equivalent of progs/num_real.a68. */
#pragma STDC FP_CONTRACT OFF
#include <stdio.h>
#include <math.h>
int main(void) {
  double x = 0.0, y = 1.0, s = 0.0;
  for (long long i = 1; i <= 5000000; i++) {
    double t = x * 0.6 + y * 0.8;
    y = y * 0.6 - x * 0.8;
    x = t;
    s = s + x * x;
  }
  printf("%lld\n", (long long) llround(s * 1000000.0 / 5000000.0));
  return 0;
}
