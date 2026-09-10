/* Hand-written C equivalent of progs/num_power.a68.
   ipow mirrors Algol 68's INT ** INT: exact integer exponentiation. */
#include <stdio.h>
static long long ipow(long long b, long long e) {
  long long r = 1;
  while (e-- > 0) r *= b;
  return r;
}
int main(void) {
  const long long n = 5000000;
  long long s = 0;
  for (long long i = 1; i <= n; i++)
    s = (s + ipow(i % 10, 3) + ipow(i % 5 + 2, 4) + ipow(2, i % 20)) % 1000003;
  printf("%lld\n", s);
  return 0;
}
