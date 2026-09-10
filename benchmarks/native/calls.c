/* Hand-written C equivalent of progs/calls.a68. */
#include <stdio.h>
static long long f(long long x, long long y) { return (x + y) % 1000003; }
int main(void) {
  long long s = 0;
  for (long long i = 1; i <= 5000000; i++) s = f(s, i);
  printf("%lld\n", s);
  return 0;
}
