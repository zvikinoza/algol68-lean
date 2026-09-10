/* Hand-written C equivalent of progs/num_divmod.a68.
   All operands stay non-negative, so C's truncating / and % agree with
   Algol 68's OVER and MOD. */
#include <stdio.h>
int main(void) {
  const long long n = 8000000;
  long long s = 0;
  for (long long i = 1; i <= n; i++)
    s = (s + i / 7 + i % 13 + (i * 3) / 11) % 1000003;
  printf("%lld\n", s);
  return 0;
}
