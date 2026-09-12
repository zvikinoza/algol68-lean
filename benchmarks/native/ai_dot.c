/* Hand-written C equivalent of progs/ai_dot.a68. */
#include <stdio.h>
#define N 4096
static double x[N + 1], y[N + 1];
int main(void) {
  long long rounds = 20000;
  for (long long i = 1; i <= N; i++) { x[i] = (double)(i % 17) / 16; y[i] = (double)(i % 13) / 12; }
  double acc = 0;
  for (long long r = 1; r <= rounds; r++) {
    double s = 0;
    for (long long i = 1; i <= N; i++) s += x[i] * y[i];
    acc += s / rounds;
    x[r % N + 1] = (double)(r % 7) / 8;
  }
  printf("%14.6f\n", acc);
  return 0;
}
