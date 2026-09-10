/* Hand-written C equivalent of progs/ctl_ops.a68: the OPerators become functions. */
#include <stdio.h>
static long long rot(long long a, long long b)  { return (a * 31 + b) % 1000003; }
static long long mash(long long a, long long b) { return (a + b * b) % 1000003; }
static long long inv(long long a)               { return (1000003 - a) % 1000003; }
int main(void) {
  long long s = 1;
  for (long long i = 1; i <= 8000000; i++) {
    s = mash(rot(s, i), i % 97);
    if (i % 5 == 0) s = inv(s);
  }
  printf("%lld\n", s);
  return 0;
}
