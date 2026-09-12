/* Hand-written C equivalent of progs/ai_conv2d.a68. */
#include <stdio.h>
#define N 256
static double img[N + 2][N + 2], tmp[N + 2][N + 2], kern[3][3];
int main(void) {
  long long passes = 100;
  for (long long i = 1; i <= N; i++) for (long long j = 1; j <= N; j++) img[i][j] = (double)((i * 5 + j * 3) % 41) / 41;
  for (long long a = -1; a <= 1; a++) for (long long b = -1; b <= 1; b++) kern[a + 1][b + 1] = (a == 0 && b == 0) ? 0.5 : 0.0625;
  for (long long pass = 1; pass <= passes; pass++) {
    for (long long i = 2; i <= N - 1; i++) for (long long j = 2; j <= N - 1; j++) {
      double s = 0;
      for (long long a = -1; a <= 1; a++) for (long long b = -1; b <= 1; b++) s += img[i + a][j + b] * kern[a + 1][b + 1];
      tmp[i][j] = s;
    }
    for (long long i = 2; i <= N - 1; i++) for (long long j = 2; j <= N - 1; j++) img[i][j] = tmp[i][j];
  }
  double total = 0;
  for (long long i = 1; i <= N; i++) for (long long j = 1; j <= N; j++) total += img[i][j];
  printf("%20.6f\n", total);
  return 0;
}
