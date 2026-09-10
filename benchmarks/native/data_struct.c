/* Hand-written C equivalent of progs/data_struct.a68. */
#include <stdio.h>
#define N 1000
typedef struct { long long x, y, vx, vy; } particle;
static particle p[N + 1];
int main(void) {
  for (long long i = 1; i <= N; i++) {
    p[i].x = i % 10007;
    p[i].y = (i * 3) % 10007;
    p[i].vx = 1 + i % 7;
    p[i].vy = 1 + i % 5;
  }
  for (long long step = 1; step <= 8000; step++)
    for (long long i = 1; i <= N; i++) {
      p[i].x = (p[i].x + p[i].vx) % 10007;
      p[i].y = (p[i].y + p[i].vy) % 10007;
    }
  long long total = 0;
  for (long long i = 1; i <= N; i++) total = (total + p[i].x + p[i].y) % 1000003;
  printf("%lld\n", total);
  return 0;
}
