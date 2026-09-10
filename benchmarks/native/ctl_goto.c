/* Hand-written C equivalent of progs/ctl_goto.a68. */
#include <stdio.h>
static long long steps(long long n) {
  long long x = n, c = 0;
  while (x != 1 && x < 100000000) {
    if (x % 2 == 0) x = x / 2; else x = 3 * x + 1;
    c++;
    if (c >= 250 || (c > 100 && x % 16 == 0)) goto done;
  }
done:
  return c;
}
int main(void) {
  long long t = 0;
  for (long long rep = 1; rep <= 6; rep++)
    for (long long n = 2; n <= 20000; n++) t = (t + steps(n)) % 1000003;
  printf("%lld\n", t);
  return 0;
}
