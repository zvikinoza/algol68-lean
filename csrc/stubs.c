/* State holder and default hooks for the a68lean runtime.

   The runtime state is created by `a68rt_boot` at run time and held here, in a C
   variable: state kept in a Lean global would be marked shared between threads, and
   then every push onto the operand stack would copy it.

   `a68_dispatch_proc` and `a68_dispatch_hole` are supplied by compiled programs; the
   interpreter never reaches them, since `Value.cproc` and `Core.hole` only occur in
   code produced by `a68lean compile`. */
#include <lean/lean.h>
#include <stdlib.h>
#include <stdio.h>

/* The source line a compiled program last reached.  Compiled code records it with a
   plain store to this variable rather than a call into the runtime, so that reaching a
   statement costs nothing at all when the statement does not fail.  It stays zero while
   the evaluator runs, which is how the error reporter knows to use its own position. */
uint32_t a68_line_no = 0;

uint32_t a68_get_line(lean_object* w) {
  (void) w;
  return a68_line_no;
}

/* Holds `some state`, so that the accessor need not allocate. */
static lean_object* a68_state = NULL;

void a68_set_state(lean_object* s) {
  lean_object* opt = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(opt, 0, s);
  a68_state = opt;
}

lean_object* a68_get_state(lean_object* a) {
  (void) a;
  if (a68_state == NULL) return lean_box(0);   /* none */
  lean_inc(a68_state);
  return a68_state;                            /* some state */
}

__attribute__((weak))
lean_object* a68_dispatch_proc(size_t fn, lean_object* env, lean_object* args, lean_object* w) {
  (void) fn; (void) env; (void) args; (void) w;
  fprintf(stderr, "a68lean: internal: compiled procedure called in interpreted mode\n");
  exit(1);
}

__attribute__((weak))
lean_object* a68_dispatch_hole(size_t fn, size_t idx, lean_object* env, lean_object* w) {
  (void) fn; (void) idx; (void) env; (void) w;
  fprintf(stderr, "a68lean: internal: compiled format hole reached in interpreted mode\n");
  exit(1);
}

/* The label a compiled program is jumping to, plus one; zero when no jump is pending.
   Every call site in compiled code tests this, so it lives here as a plain variable that
   the generated C reads directly, rather than behind a runtime entry point that would
   allocate an IO result for each test. */
uint32_t a68_jump_flag = 0;

uint32_t a68_get_jump(lean_object* u) {
  (void) u;
  return a68_jump_flag;
}

uint32_t a68_set_jump(uint32_t v) {
  a68_jump_flag = v;
  return v;
}
