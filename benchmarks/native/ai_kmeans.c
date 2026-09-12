/* Hand-written C equivalent of progs/ai_kmeans.a68. */
#include <stdio.h>
#define N 5000
#define DIM 8
#define KK 8
static double pt[N + 1][DIM + 1], cen[KK + 1][DIM + 1], acc[KK + 1][DIM + 1];
static long long cnt[KK + 1], lab[N + 1];
int main(void) {
  long long iters = 100;
  for (long long i = 1; i <= N; i++) for (long long j = 1; j <= DIM; j++) pt[i][j] = (double)((i * (j + 3) + j * 7) % 101) / 10;
  for (long long c = 1; c <= KK; c++) for (long long j = 1; j <= DIM; j++) cen[c][j] = pt[c * 37][j];
  for (long long it = 1; it <= iters; it++) {
    for (long long i = 1; i <= N; i++) {
      long long best = 1; double bd = 1.0e30;
      for (long long c = 1; c <= KK; c++) {
        double dd = 0;
        for (long long j = 1; j <= DIM; j++) { double df = pt[i][j] - cen[c][j]; dd += df * df; }
        if (dd < bd) { bd = dd; best = c; }
      }
      lab[i] = best;
    }
    for (long long c = 1; c <= KK; c++) { cnt[c] = 0; for (long long j = 1; j <= DIM; j++) acc[c][j] = 0; }
    for (long long i = 1; i <= N; i++) {
      long long c = lab[i]; cnt[c] += 1;
      for (long long j = 1; j <= DIM; j++) acc[c][j] += pt[i][j];
    }
    for (long long c = 1; c <= KK; c++) if (cnt[c] > 0) for (long long j = 1; j <= DIM; j++) cen[c][j] = acc[c][j] / cnt[c];
  }
  double check = 0;
  for (long long c = 1; c <= KK; c++) for (long long j = 1; j <= DIM; j++) check += cen[c][j] * (c + j);
  printf("%14.6f\n", check);
  return 0;
}
