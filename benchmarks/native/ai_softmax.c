/* Hand-written C equivalent of progs/ai_softmax.a68. */
#include <stdio.h>
#include <math.h>
#define N 512
static double z[N + 1], p[N + 1];
int main(void) {
  long long rounds = 40000;
  double check = 0;
  for (long long r = 1; r <= rounds; r++) {
    for (long long i = 1; i <= N; i++) z[i] = (double)((i * 31 + r) % 101) / 10 - 5;
    double m = z[1];
    for (long long i = 2; i <= N; i++) if (z[i] > m) m = z[i];
    double s = 0;
    for (long long i = 1; i <= N; i++) { p[i] = exp(z[i] - m); s += p[i]; }
    for (long long i = 1; i <= N; i++) p[i] = p[i] / s;
    check += p[r % N + 1];
  }
  printf("%14.8f\n", check);
  return 0;
}
