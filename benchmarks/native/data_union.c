/* Hand-written C equivalent of progs/data_union.a68. */
#include <stdio.h>
#include <math.h>
#define N 1000
enum tag { T_INT, T_REAL, T_BOOL, T_CHAR };
typedef struct {
  enum tag t;
  union { long long i; double r; int b; char c; } u;
} item;
static item a[N + 1];
int main(void) {
  for (long long i = 1; i <= N; i++) {
    switch (i % 4 + 1) {
      case 1: a[i].t = T_INT;  a[i].u.i = i % 1009; break;
      case 2: a[i].t = T_REAL; a[i].u.r = (double)i / 4.0; break;
      case 3: a[i].t = T_BOOL; a[i].u.b = (int)(i & 1); break;
      default: a[i].t = T_CHAR; a[i].u.c = (char)(65 + i % 26); break;
    }
  }
  long long total = 0;
  for (long long r = 1; r <= 8000; r++)
    for (long long i = 1; i <= N; i++)
      switch (a[i].t) {
        case T_INT:  total = (total + a[i].u.i) % 1000003; break;
        case T_REAL: total = (total + (long long)llround(a[i].u.r * 4.0)) % 1000003; break;
        case T_BOOL: total = (total + (a[i].u.b ? 3 : 5)) % 1000003; break;
        default:     total = (total + (unsigned char)a[i].u.c) % 1000003; break;
      }
  printf("%lld\n", total);
  return 0;
}
