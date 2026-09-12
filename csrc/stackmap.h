/* LLVM stack maps: the collector's view of heap pointers that LLVM-compiled code keeps in
   native stack slots across calls (docs/LLVM-DESIGN.md §3, milestone 2).  Plain C99; no
   dependence on the rest of the runtime, so that stackmap_test.sh can link it alone. */
#ifndef A68_STACKMAP_H
#define A68_STACKMAP_H

#include <stddef.h>

/* Locate and parse the executable's `__LLVM_StackMaps` section.  Called once, from
   `a68rt_boot`.  A binary without the section (the C back end) has no stack maps, and
   every later call of `stackmap_roots` then returns at once.  A malformed section is a
   fatal error with a message, never a silent crash. */
void stackmap_init(void);

/* Walk the native stack from the caller's frame and call `mark` with every non-NULL
   heap pointer that a stack map record holds for a frame on it.  Each pointer is
   reported once per frame. */
void stackmap_roots(void (*mark)(void* obj));

/* The number of statepoint records parsed; 0 when the binary has no stack maps. */
size_t stackmap_record_count(void);

#endif
