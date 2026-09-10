/* Hand-written C equivalent of progs/ctl_case.a68: the CASE becomes a switch. */
#include <stdio.h>
int main(void) {
  long long s = 1;
  for (long long i = 1; i <= 8000000; i++) {
    switch (i % 12 + 1) {
      case 1:  s = (s + i) % 1000003; break;
      case 2:  s = (s + 2 * i) % 1000003; break;
      case 3:  s = (s * 3 + 1) % 1000003; break;
      case 4:  s = (s + (i % 1000) * (i % 1000)) % 1000003; break;
      case 5:  s = (s + 17) % 1000003; break;
      case 6:  s = (s * 5 + i) % 1000003; break;
      case 7:  s = (s + i / 3) % 1000003; break;
      case 8:  s = (1000003 - s) % 1000003; break;
      case 9:  s = (s * 7 + 3) % 1000003; break;
      case 10: s = (s + i % 251) % 1000003; break;
      case 11: s = (s * 11 + i) % 1000003; break;
      case 12: s = (s + 1000000) % 1000003; break;
      default: s = 0; break;
    }
  }
  printf("%lld\n", s);
  return 0;
}
