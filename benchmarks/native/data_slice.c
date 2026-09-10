/* Hand-written C equivalent of progs/data_slice.a68. */
#include <stdio.h>
#define N 1000
static long long a[N + 1];
int main(void) {
  for (long long i = 1; i <= N; i++) a[i] = i % 251;
  long long total = 0;
  for (long long r = 1; r <= 40000; r++) {
    long long lo = 1 + r % 101;
    const long long *w = &a[lo];             /* window a[lo:lo+499], w[0] first */
    for (long long i = 0; i <= 499; i++) total = (total + w[i]) % 1000003;
    a[lo] = (total + r) % 251;               /* v[1] of the REF slice a[lo:lo+499] */
  }
  printf("%lld\n", total);
  return 0;
}
