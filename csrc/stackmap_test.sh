#!/bin/bash
# End-to-end test of csrc/stackmap.c: a hand-written LLVM module in which three
# statepoint-using functions hold heap pointers live across calls, with plain C frames
# between them, and a C leaf that asks stackmap_roots for the roots and checks that it
# gets exactly the live pointers — and none of the pointers the functions also keep on the
# native stack but did not declare live.  Run at -O0 and -O2, plus a build without any
# stack map to check the no-op path.  Usage: bash csrc/stackmap_test.sh
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# The call chain: main (C) -> top (LLVM) -> outer (LLVM) -> c_mid (C) -> inner (LLVM)
# -> c_leaf (C) -> stackmap_roots.  Allocation order numbers the objects: top gets #0 (h),
# outer #1..#4 (a b c d), inner #5..#7 (e f g).  Live at the statepoints: h; a b c; e f.
# Dead but still on the native stack or in callee-saved registers: d and g, which are
# used after the call *without* relocation, so LLVM keeps them somewhere across it.
cat > "$work/sp.ll" <<'EOF'
declare ptr addrspace(1) @a68_alloc(i64)
declare i64 @c_mid(i64)
declare i64 @c_leaf(i64)
declare token @llvm.experimental.gc.statepoint.p0(i64, i32, ptr, i32, i32, ...)
declare ptr addrspace(1) @llvm.experimental.gc.relocate.p1(token, i32, i32)
declare i64 @llvm.experimental.gc.result.i64(token)

define i64 @top(i64 %n) #0 gc "statepoint-example" {
entry:
  %h = call ptr addrspace(1) @a68_alloc(i64 %n)
  %tok = call token (i64, i32, ptr, i32, i32, ...) @llvm.experimental.gc.statepoint.p0(i64 1, i32 0, ptr elementtype(i64 (i64)) @outer, i32 1, i32 0, i64 %n, i32 0, i32 0) ["gc-live"(ptr addrspace(1) %h)]
  %r = call i64 @llvm.experimental.gc.result.i64(token %tok)
  %h2 = call ptr addrspace(1) @llvm.experimental.gc.relocate.p1(token %tok, i32 0, i32 0)
  %vh = load i64, ptr addrspace(1) %h2
  %s = add i64 %r, %vh
  ret i64 %s
}

define i64 @outer(i64 %n) #0 gc "statepoint-example" {
entry:
  %a = call ptr addrspace(1) @a68_alloc(i64 %n)
  %b = call ptr addrspace(1) @a68_alloc(i64 %n)
  %c = call ptr addrspace(1) @a68_alloc(i64 %n)
  %d = call ptr addrspace(1) @a68_alloc(i64 %n)
  %tok = call token (i64, i32, ptr, i32, i32, ...) @llvm.experimental.gc.statepoint.p0(i64 2, i32 0, ptr elementtype(i64 (i64)) @c_mid, i32 1, i32 0, i64 %n, i32 0, i32 0) ["gc-live"(ptr addrspace(1) %a, ptr addrspace(1) %b, ptr addrspace(1) %c)]
  %r = call i64 @llvm.experimental.gc.result.i64(token %tok)
  %a2 = call ptr addrspace(1) @llvm.experimental.gc.relocate.p1(token %tok, i32 0, i32 0)
  %b2 = call ptr addrspace(1) @llvm.experimental.gc.relocate.p1(token %tok, i32 1, i32 1)
  %c2 = call ptr addrspace(1) @llvm.experimental.gc.relocate.p1(token %tok, i32 2, i32 2)
  %va = load i64, ptr addrspace(1) %a2
  %vb = load i64, ptr addrspace(1) %b2
  %vc = load i64, ptr addrspace(1) %c2
  %vd = load i64, ptr addrspace(1) %d
  %s1 = add i64 %va, %vb
  %s2 = add i64 %s1, %vc
  %s3 = add i64 %s2, %vd
  %s4 = add i64 %s3, %r
  ret i64 %s4
}

define i64 @inner(i64 %n) #0 gc "statepoint-example" {
entry:
  %e = call ptr addrspace(1) @a68_alloc(i64 %n)
  %f = call ptr addrspace(1) @a68_alloc(i64 %n)
  %g = call ptr addrspace(1) @a68_alloc(i64 %n)
  %tok = call token (i64, i32, ptr, i32, i32, ...) @llvm.experimental.gc.statepoint.p0(i64 3, i32 0, ptr elementtype(i64 (i64)) @c_leaf, i32 1, i32 0, i64 %n, i32 0, i32 0) ["gc-live"(ptr addrspace(1) %e, ptr addrspace(1) %f)]
  %r = call i64 @llvm.experimental.gc.result.i64(token %tok)
  %e2 = call ptr addrspace(1) @llvm.experimental.gc.relocate.p1(token %tok, i32 0, i32 0)
  %f2 = call ptr addrspace(1) @llvm.experimental.gc.relocate.p1(token %tok, i32 1, i32 1)
  %ve = load i64, ptr addrspace(1) %e2
  %vf = load i64, ptr addrspace(1) %f2
  %vg = load i64, ptr addrspace(1) %g
  %s1 = add i64 %ve, %vf
  %s2 = add i64 %s1, %vg
  %s3 = add i64 %s2, %r
  ret i64 %s3
}

; the collector walks the frame-pointer chain, so the functions must keep x29
attributes #0 = { "frame-pointer"="non-leaf" }
EOF

cat > "$work/test.c" <<'EOF'
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "stackmap.h"

#define NOBJ 8
static int64_t heap[NOBJ];
static int nalloc = 0;
static int seen[NOBJ];
static int foreign = 0, calls = 0;

void* a68_alloc(int64_t n) {
  if (nalloc >= NOBJ) { fprintf(stderr, "too many allocations\n"); exit(1); }
  heap[nalloc] = n * 100 + nalloc;
  return &heap[nalloc++];
}

static void record(void* p) {
  calls++;
  for (int i = 0; i < NOBJ; i++) if (p == &heap[i]) { seen[i]++; return; }
  foreign++;
  fprintf(stderr, "root %p is not a heap object\n", p);
}

int64_t top(int64_t), inner(int64_t);
extern int64_t c_mid(int64_t), c_leaf(int64_t);

/* a plain C frame between two LLVM frames */
int64_t c_mid(int64_t n) {
  int64_t r = inner(n);
  return r + 1;
}

/* the leaf: the roots must be h a b c e f (#0 #1 #2 #3 #5 #6), and never d g (#4 #7) */
int64_t c_leaf(int64_t n) {
  static const int live[NOBJ] = { 1, 1, 1, 1, 0, 1, 1, 0 };
  if (nalloc != NOBJ) { fprintf(stderr, "expected %d allocations before the leaf, got %d\n", NOBJ, nalloc); exit(1); }
  memset(seen, 0, sizeof seen); foreign = 0; calls = 0;
  stackmap_roots(record);
  int bad = 0;
  for (int i = 0; i < NOBJ; i++) {
    if (seen[i] != live[i]) {
      fprintf(stderr, "object #%d: reported %d time(s), expected %d\n", i, seen[i], live[i]);
      bad = 1;
    }
  }
  if (foreign) bad = 1;
  if (bad) { fprintf(stderr, "FAIL: wrong root set (%d reports)\n", calls); exit(1); }
  printf("roots: %d reported, exactly the live ones\n", calls);
  return n;
}

int main(void) {
  stackmap_init();
  size_t nrec = stackmap_record_count();
  printf("stack map records: %zu\n", nrec);
  if (nrec != 3) { fprintf(stderr, "FAIL: expected 3 statepoint records\n"); return 1; }
  int64_t n = 7;
  int64_t r = top(n);
  /* every load happened: the sum of all eight objects' values plus the C increments */
  int64_t want = 0;
  for (int i = 0; i < NOBJ; i++) want += n * 100 + i;
  want += 1 + n;  /* c_mid's +1, c_leaf returns n */
  if (r != want) { fprintf(stderr, "FAIL: result %lld, expected %lld\n", (long long) r, (long long) want); return 1; }
  printf("ok\n");
  return 0;
}
EOF

# a binary with no stack map at all: the walk must be a no-op
cat > "$work/none.c" <<'EOF'
#include <stdio.h>
#include <stdlib.h>
#include "stackmap.h"
static int n = 0;
static void record(void* p) { (void) p; n++; }
int main(void) {
  stackmap_init();
  if (stackmap_record_count() != 0) { fprintf(stderr, "FAIL: records in a binary without stack maps\n"); return 1; }
  stackmap_roots(record);
  if (n != 0) { fprintf(stderr, "FAIL: roots reported without stack maps\n"); return 1; }
  printf("no stack maps: no roots, ok\n");
  return 0;
}
EOF

status=0
for opt in -O0 -O2; do
  echo "== $opt"
  clang $opt -Wall -Wextra -Wno-override-module -I"$HERE" "$work/sp.ll" "$work/test.c" "$HERE/stackmap.c" -o "$work/t" || { echo "FAIL: compile $opt"; status=1; continue; }
  "$work/t" || { echo "FAIL: run $opt"; status=1; }
done
echo "== no stack maps"
clang -O2 -Wall -Wextra -I"$HERE" "$work/none.c" "$HERE/stackmap.c" -o "$work/n" || { echo "FAIL: compile none"; status=1; }
[ $status = 0 ] && { "$work/n" || status=1; }
[ $status = 0 ] && echo "stackmap_test: PASS" || echo "stackmap_test: FAIL"
exit $status
