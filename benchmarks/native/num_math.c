/* Hand-written C equivalent of progs/num_math.a68. */
#pragma STDC FP_CONTRACT OFF
#include <stdio.h>
#include <math.h>
int main(void) {
  const long long n = 6000000;
  double s = 0.0;
  for (long long i = 1; i <= n; i++) {
    double t = (double) i / (double) n;
    s = s + sqrt(t) + sin(t) * exp(-t) + log(t + 1.0);
  }
  printf("%lld\n", (long long) llround(s / (double) n * 1000000.0));
  return 0;
}
