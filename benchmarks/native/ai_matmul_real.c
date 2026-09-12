/* Hand-written C equivalent of progs/ai_matmul_real.a68. */
#include <stdio.h>
#define N 400
static double a[N + 1][N + 1], b[N + 1][N + 1], c[N + 1][N + 1];
int main(void) {
  for (long long i = 1; i <= N; i++) for (long long j = 1; j <= N; j++) {
    a[i][j] = (double)((i * 7 + j) % 23) / 23;
    b[i][j] = (double)((i + j * 11) % 19) / 19;
  }
  for (long long i = 1; i <= N; i++) for (long long j = 1; j <= N; j++) {
    double s = 0;
    for (long long k = 1; k <= N; k++) s += a[i][k] * b[k][j];
    c[i][j] = s;
  }
  double total = 0;
  for (long long i = 1; i <= N; i++) for (long long j = 1; j <= N; j++) total += c[i][j];
  printf("%16.4f\n", total);
  return 0;
}
