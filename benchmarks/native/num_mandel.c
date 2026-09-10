/* Hand-written C equivalent of progs/num_mandel.a68.
   FP_CONTRACT is off so that x*x - y*y + x0 is not fused; the operation
   order must match the Algol 68 source bit for bit. */
#pragma STDC FP_CONTRACT OFF
#include <stdio.h>
int main(void) {
  const int w = 400, h = 300, maxit = 200;
  long long total = 0;
  for (int py = 0; py <= h - 1; py++) {
    double y0 = -1.25 + (double) py * 2.5 / (double) h;
    for (int px = 0; px <= w - 1; px++) {
      double x0 = -2.2 + (double) px * 3.0 / (double) w;
      double x = 0.0, y = 0.0;
      int it = 0;
      while (x * x + y * y <= 4.0 && it < maxit) {
        double xt = x * x - y * y + x0;
        y = 2.0 * x * y + y0;
        x = xt;
        it += 1;
      }
      total += it;
    }
  }
  printf("%lld\n", total);
  return 0;
}
