/* Hand-written C equivalent of progs/data_list.a68. */
#include <stdio.h>
#include <stdlib.h>
typedef struct node { long long val; struct node *next; } node;
int main(void) {
  long long n = 40000;
  node *head = NULL;
  for (long long i = 1; i <= n; i++) {
    node *q = malloc(sizeof *q);
    q->val = (i * 7) % 1009;
    q->next = head;
    head = q;
  }
  long long total = 0;
  for (long long r = 1; r <= 250; r++)
    for (node *p = head; p != NULL; p = p->next)
      total = (total + p->val) % 1000003;
  printf("%lld\n", total);
  return 0;
}
