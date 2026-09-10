/* Hand-written C equivalent of progs/ctl_mutual.a68. */
#include <stdio.h>
static long long f(long long n);
static long long g(long long n);
static long long h(long long n);
static long long f(long long n) { return n == 0 ? 1 : (n + g(n - 1)) % 1000003; }
static long long g(long long n) { return n == 0 ? 2 : (n + h(n - 1)) % 1000003; }
static long long h(long long n) { return n == 0 ? 3 : (n + f(n - 1)) % 1000003; }
int main(void) {
  long long s = 0;
  for (long long i = 1; i <= 40000; i++) s = (s + f(200 + i % 101)) % 1000003;
  printf("%lld\n", s);
  return 0;
}
