/* Hand-written C equivalent of progs/ai_layernorm.a68. */
#include <stdio.h>
#include <math.h>
#define N 1024
static double v[N + 1], g[N + 1], beta[N + 1], o[N + 1];
int main(void) {
  long long rounds = 30000;
  for (long long i = 1; i <= N; i++) { g[i] = 1 + (double)(i % 7) / 100; beta[i] = (double)(i % 5) / 50; }
  double check = 0;
  for (long long r = 1; r <= rounds; r++) {
    for (long long i = 1; i <= N; i++) v[i] = (double)((i * 17 + r * 3) % 97) / 10;
    double mean = 0;
    for (long long i = 1; i <= N; i++) mean += v[i];
    mean = mean / N;
    double var = 0;
    for (long long i = 1; i <= N; i++) var += (v[i] - mean) * (v[i] - mean);
    var = var / N;
    double inv = 1 / sqrt(var + 0.00001);
    for (long long i = 1; i <= N; i++) o[i] = (v[i] - mean) * inv * g[i] + beta[i];
    check += o[r % N + 1];
  }
  printf("%14.6f\n", check);
  return 0;
}
