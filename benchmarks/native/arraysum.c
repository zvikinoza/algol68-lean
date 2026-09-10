/* Hand-written C equivalent of progs/arraysum.a68. */
#include <stdio.h>
int main(void) {
  static long long a[1001];
  long long total = 0;
  for (long long r = 1; r <= 20000; r++) {
    for (long long i = 1; i <= 1000; i++) a[i] = i + r;
    for (long long i = 1; i <= 1000; i++) total = (total + a[i]) % 1000003;
  }
  printf("%lld\n", total);
  return 0;
}
