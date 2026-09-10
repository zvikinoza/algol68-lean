/* Hand-written C equivalent of progs/num_horner.a68. */
#pragma STDC FP_CONTRACT OFF
#include <stdio.h>
#include <math.h>
int main(void) {
  const long long n = 650000, deg = 15;
  double total = 0.0;
  for (long long i = 1; i <= n; i++) {
    double x = (double) i / (double) n;
    double p = 0.0;
    for (long long k = 1; k <= deg; k++)
      p = p * x + (double) (k % 7 + 1);
    total = total + p;
  }
  printf("%lld\n", (long long) llround(total / (double) n * 1000000.0));
  return 0;
}
