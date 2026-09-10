/* Hand-written C equivalent of progs/intloop.a68: the roofline ceiling. */
#include <stdio.h>
int main(void) {
  long long s = 0;
  for (long long i = 1; i <= 20000000; i++) s = (s + i * 3) % 1000003;
  printf("%lld\n", s);
  return 0;
}
