/* Hand-written C equivalent of progs/ctl_hof.a68. */
#include <stdio.h>
typedef long long (*binop)(long long, long long);
static long long reduce(binop f, long long seed, long long n) {
  long long acc = seed;
  for (long long i = 1; i <= n; i++) acc = f(acc, i);
  return acc;
}
static long long step1(long long x, long long y) { return (x + y * 7) % 1000003; }
static long long step2(long long x, long long y) { return (x * 3 + y) % 1000003; }
int main(void) {
  long long s = 1;
  for (long long r = 1; r <= 60000; r++)
    s = (reduce(step1, s, 100) + reduce(step2, s, 100)) % 1000003;
  printf("%lld\n", s);
  return 0;
}
