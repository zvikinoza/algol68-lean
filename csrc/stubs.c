/* The evaluator's side of the hooks compiled programs supply.

   `a68_dispatch_proc` and `a68_dispatch_hole` are defined by every compiled program; the
   `a68lean` executable links the runtime archive too (for the services the evaluator
   shares with compiled programs), so it needs definitions that are never reached. */
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

__attribute__((weak))
void a68_dispatch_proc(size_t fn) {
  (void) fn;
  fprintf(stderr, "a68lean: internal: compiled procedure called in interpreted mode\n");
  exit(1);
}

__attribute__((weak))
void a68_dispatch_hole(size_t idx) {
  (void) idx;
  fprintf(stderr, "a68lean: internal: compiled format hole reached in interpreted mode\n");
  exit(1);
}
