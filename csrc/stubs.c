/* Default definitions of the hooks that compiled programs provide.
   The interpreter never reaches them: `Value.cproc` and `Core.hole` only occur
   in code produced by `a68lean compile`, which supplies its own definitions. */
#include <lean/lean.h>
#include <stdlib.h>
#include <stdio.h>

lean_object* a68_dispatch_proc(size_t fn, lean_object* env, lean_object* args, lean_object* w) {
  (void) fn; (void) env; (void) args; (void) w;
  fprintf(stderr, "a68lean: internal: compiled procedure called in interpreted mode\n");
  exit(1);
}

lean_object* a68_dispatch_hole(size_t fn, size_t idx, lean_object* env, lean_object* w) {
  (void) fn; (void) idx; (void) env; (void) w;
  fprintf(stderr, "a68lean: internal: compiled format hole reached in interpreted mode\n");
  exit(1);
}
