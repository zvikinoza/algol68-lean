/* Hand-written C equivalent of progs/ctl_fib.a68. */
#include <stdio.h>
static long long fib(long long n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }
int main(void) {
  long long s = 0;
  for (long long k = 25; k <= 32; k++) s = (s + fib(k)) % 1000003;
  printf("%lld\n", s);
  return 0;
}
