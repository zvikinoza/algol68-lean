/* Hand-written C equivalent of progs/data_matmul.a68. */
#include <stdio.h>
#define N 250
static long long a[N + 1][N + 1], b[N + 1][N + 1], c[N + 1][N + 1];
int main(void) {
  for (long long i = 1; i <= N; i++)
    for (long long j = 1; j <= N; j++) {
      a[i][j] = (i * 3 + j) % 97;
      b[i][j] = (i + j * 5) % 89;
    }
  for (long long i = 1; i <= N; i++)
    for (long long j = 1; j <= N; j++) {
      long long s = 0;
      for (long long k = 1; k <= N; k++) s = (s + a[i][k] * b[k][j]) % 1000003;
      c[i][j] = s;
    }
  long long total = 0;
  for (long long i = 1; i <= N; i++)
    for (long long j = 1; j <= N; j++) total = (total + c[i][j]) % 1000003;
  printf("%lld\n", total);
  return 0;
}
