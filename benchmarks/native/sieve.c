/* Hand-written C equivalent of progs/sieve.a68. */
#include <stdio.h>
#include <stdlib.h>
int main(void) {
  int n = 2000000, count = 0;
  char *prime = malloc(n + 1);
  for (int rep = 1; rep <= 2; rep++) {
    for (int i = 1; i <= n; i++) prime[i] = 1;
    count = 0;
    for (int i = 2; i <= n; i++)
      if (prime[i]) { count++; for (long long j = (long long)i + i; j <= n; j += i) prime[j] = 0; }
  }
  printf("%d\n", count);
  return 0;
}
