/* Hand-written C equivalent of progs/data_string.a68. */
#include <stdio.h>
#include <string.h>
#define REPS 15000
#define LEN 120
int main(void) {
  const int a0 = 'a';
  long long total = 0;
  char s[LEN + 1], t[LEN + 1];
  for (long long r = 1; r <= REPS; r++) {
    int ls = 0, lt = 0;
    for (long long i = 1; i <= LEN; i++) {
      char c = (char)(a0 + (i * 7 + r) % 26);
      s[ls++] = c;
      t[lt++] = (i == 60 && r % 5 == 0) ? (char)(a0 + (c - a0 + 1) % 26) : c;
    }
    s[ls] = t[lt] = '\0';
    int cmp = memcmp(s, t, LEN);       /* equal lengths: plain lexicographic */
    if (cmp == 0) total += 1;
    else if (cmp < 0) total += 2;
    else total += 3;
    for (int i = 0; i < LEN; i++) total = (total + (unsigned char)s[i]) % 1000003;
  }
  printf("%lld\n", total);
  return 0;
}
