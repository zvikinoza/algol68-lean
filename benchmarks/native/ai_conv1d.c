/* Hand-written C equivalent of progs/ai_conv1d.a68. */
#include <stdio.h>
#define N 100000
#define K 16
static double sig[N + 1], out[N + 1], w[K + 1];
int main(void) {
  long long passes = 50;
  for (long long i = 1; i <= N; i++) sig[i] = (double)((i * 13) % 29) / 29;
  for (long long j = 1; j <= K; j++) w[j] = (double)(j % 5 - 2) / 8;
  for (long long pass = 1; pass <= passes; pass++) {
    for (long long i = 1; i <= N - K + 1; i++) {
      double s = 0;
      for (long long j = 1; j <= K; j++) s += sig[i + j - 1] * w[j];
      out[i] = s;
    }
    for (long long i = 1; i <= N - K + 1; i++) sig[i] = out[i] / 2 + sig[i] / 2;
  }
  double total = 0;
  for (long long i = 1; i <= N; i++) total += sig[i];
  printf("%16.6f\n", total);
  return 0;
}
