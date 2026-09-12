/* Hand-written C equivalent of progs/ai_sgd.a68. */
#include <stdio.h>
#define N 20000
#define F 8
static double xs[N + 1][F + 1], ys[N + 1], wt[F + 1], tru[F + 1];
int main(void) {
  long long epochs = 200;
  for (long long j = 1; j <= F; j++) { tru[j] = (double)(j % 3 - 1) / 2; wt[j] = 0; }
  for (long long i = 1; i <= N; i++) {
    double y = 0.5;
    for (long long j = 1; j <= F; j++) { xs[i][j] = (double)((i * j + 5 * j) % 23) / 23 - 0.5; y += tru[j] * xs[i][j]; }
    ys[i] = y;
  }
  double lr = 0.01;
  for (long long e = 1; e <= epochs; e++)
    for (long long i = 1; i <= N; i++) {
      double pred = 0;
      for (long long j = 1; j <= F; j++) pred += wt[j] * xs[i][j];
      double err = pred - ys[i];
      for (long long j = 1; j <= F; j++) wt[j] -= lr * err * xs[i][j];
    }
  double check = 0;
  for (long long j = 1; j <= F; j++) check += wt[j] * j;
  printf("%14.8f\n", check);
  return 0;
}
