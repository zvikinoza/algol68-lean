/* Hand-written C equivalent of progs/ai_attention.a68. */
#include <stdio.h>
#include <math.h>
#define S 64
#define D 64
static double q[S + 1][D + 1], k[S + 1][D + 1], v[S + 1][D + 1], o[S + 1][D + 1], p[S + 1][S + 1];
int main(void) {
  long long rounds = 150;
  double check = 0;
  for (long long r = 1; r <= rounds; r++) {
    for (long long i = 1; i <= S; i++) for (long long j = 1; j <= D; j++) {
      q[i][j] = (double)((i * 3 + j * 5 + r) % 17) / 17;
      k[i][j] = (double)((i * 7 + j + r) % 13) / 13;
      v[i][j] = (double)((i + j * 11 + r) % 19) / 19;
    }
    for (long long i = 1; i <= S; i++) {
      double m = -1.0e30;
      for (long long j = 1; j <= S; j++) {
        double acc = 0;
        for (long long t = 1; t <= D; t++) acc += q[i][t] * k[j][t];
        p[i][j] = acc / 8;
        if (p[i][j] > m) m = p[i][j];
      }
      double sum = 0;
      for (long long j = 1; j <= S; j++) { p[i][j] = exp(p[i][j] - m); sum += p[i][j]; }
      for (long long j = 1; j <= S; j++) p[i][j] = p[i][j] / sum;
    }
    for (long long i = 1; i <= S; i++) for (long long t = 1; t <= D; t++) {
      double acc = 0;
      for (long long j = 1; j <= S; j++) acc += p[i][j] * v[j][t];
      o[i][t] = acc;
    }
    for (long long i = 1; i <= S; i++) check += o[i][r % D + 1];
  }
  printf("%14.6f\n", check);
  return 0;
}
