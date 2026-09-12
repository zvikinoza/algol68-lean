/* Hand-written C equivalent of progs/ai_dense.a68. */
#include <stdio.h>
#define N 256
static double w[N + 1][N + 1], b[N + 1], x[N + 1], y[N + 1];
int main(void) {
  long long batch = 1000;
  for (long long i = 1; i <= N; i++) for (long long j = 1; j <= N; j++) w[i][j] = (double)((i * 3 + j * 7) % 31 - 15) / 64;
  for (long long i = 1; i <= N; i++) b[i] = (double)(i % 11 - 5) / 10;
  double check = 0;
  for (long long s = 1; s <= batch; s++) {
    for (long long j = 1; j <= N; j++) x[j] = (double)((j * s) % 37) / 37;
    for (long long i = 1; i <= N; i++) {
      double acc = b[i];
      for (long long j = 1; j <= N; j++) acc += w[i][j] * x[j];
      y[i] = acc > 0 ? acc : 0;
    }
    for (long long i = 1; i <= N; i++) check += y[i];
  }
  printf("%16.4f\n", check);
  return 0;
}
