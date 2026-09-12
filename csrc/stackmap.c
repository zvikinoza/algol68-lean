/* LLVM stack maps: finding the heap pointers LLVM-compiled code holds across calls.

   The LLVM back end (docs/LLVM-DESIGN.md) keeps heap pointers in native registers, and at
   every call that may collect it emits a `gc.statepoint`.  LLVM's statepoint lowering
   spills each live pointer to a stack slot around the call and describes the slot in a
   stack map record keyed by the return address of the call.  This file reads the maps
   at start-up and, at collection time, walks the native stack and reports every pointer
   the records name for the frames found.

   Format (https://llvm.org/docs/StackMaps.html, version 3; everything little-endian,
   natural alignment, verified against what Apple clang 21 emits, see stackmap_test.sh):

     Header    u8 version (3), u8 reserved, u16 reserved
               u32 NumFunctions, u32 NumConstants, u32 NumRecords
     StkSize   NumFunctions × { u64 FunctionAddress, u64 StackSize, u64 RecordCount }
     Constants NumConstants × u64
     Records   NumRecords × { u64 PatchPointID, u32 InstructionOffset, u16 reserved,
                              u16 NumLocations,
                              NumLocations × { u8 Type, u8 reserved, u16 Size,
                                               u16 DwarfRegNum, u16 reserved,
                                               i32 OffsetOrSmallConstant },
                              pad to 8, u16 padding, u16 NumLiveOuts,
                              NumLiveOuts × { u16 DwarfRegNum, u8 reserved, u8 Size },
                              pad to 8 }

   The records of the first function come first (RecordCount of them), then those of the
   second, and so on; a record's return address is FunctionAddress + InstructionOffset,
   the label LLVM places right after the call instruction.  A statepoint record's
   locations are (https://llvm.org/docs/Statepoints.html#stack-map-format): three
   constants — the calling convention, the statepoint flags, the number D of deopt
   locations — then D deopt locations, then the gc pointers as (base, derived) pairs.

   Empirical findings on this machine (macOS arm64, Apple clang 21), which the code and
   its checks rely on:

   * Section names: segment `__LLVM_STACKMAPS`, section `__llvm_stackmaps` (otool -l).
     The linker concatenates the section of every object file that has one, so the data
     is a sequence of complete stack maps, each starting with its own header, each a
     multiple of 8 bytes long (LLVM pads every record to 8).  The parser loops over them;
     constant indices are relative to the map they occur in.
   * The function addresses are rebased by dyld (they carry relocations), so they compare
     directly with the return addresses read from the stack under ASLR.
   * Every gc pointer location LLVM produced, at -O0 and at -O2, with the pointers in
     callee-saved registers before the call, is Indirect off DWARF register 31, which is
     SP on AArch64: `[sp + offset]`.  Statepoint lowering spills all gc pointers (the
     option that lets them stay in callee-saved registers defaults to off), so Register
     locations do not occur for gc pointers and are rejected here, since their value
     would have to be recovered from the save area of some deeper frame.  Register 29 (the
     frame pointer, used by LLVM when a frame has variable-sized objects) is accepted too.
   * A frame is found through the frame-pointer chain, so the gc functions must be
     emitted with the attribute "frame-pointer"="non-leaf" (or "all"); the clang flag
     -fno-omit-frame-pointer does nothing for `.ll` input.  With the attribute LLVM lays
     the frame out Darwin-style: `sub sp, sp, #S` (S the map's StackSize), the frame
     record x29/x30 at the top of the frame, `add x29, sp, #S-16`.  Hence for a frame
     with frame pointer FP the SP of the function body is FP + 16 - S, and every spill
     slot lies in [SP, FP + 16), which the walk checks.
   * The C runtime's own frames sit between LLVM frames (an LLVM routine calls an entry
     point, which calls back a compiled routine).  Apple clang keeps frame pointers in all
     non-leaf C functions, so the chain passes through them; their return addresses
     match no record and they are skipped.

   The frame record on AArch64: at [fp] the caller's fp, at [fp + 8] the return address
   into the caller.  So the return address in a frame identifies the record of its
   *parent*, whose frame pointer is the saved fp. */

#include "stackmap.h"

#include <inttypes.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <mach-o/getsect.h>
#include <mach-o/ldsyms.h>

#if defined(__has_feature)
#if __has_feature(ptrauth_calls)
#include <ptrauth.h>
#define STRIP_PAC(p) ((uintptr_t) ptrauth_strip((void*) (p), ptrauth_key_return_address))
#endif
#endif
#ifndef STRIP_PAC
#define STRIP_PAC(p) ((uintptr_t) (p))
#endif

enum { LOC_REGISTER = 1, LOC_DIRECT = 2, LOC_INDIRECT = 3, LOC_CONSTANT = 4, LOC_CONST_INDEX = 5 };
enum { REG_FP = 29, REG_SP = 31 };  /* DWARF register numbers on AArch64 */
#define STACK_SIZE_UNKNOWN UINT64_MAX   /* LLVM's StackSize for a variable-sized frame */

/* one gc pointer location of a record */
typedef struct {
  uint8_t type;
  uint16_t reg;
  int32_t off;      /* offset from the register, or the small constant */
  uint64_t konst;   /* the value of a ConstIndex location, resolved at parse time */
} sm_loc;

/* one statepoint record: the frames whose parent returns to `ret` */
typedef struct {
  uintptr_t ret;
  uint64_t stack_size;
  uint32_t first_loc, nloc;
} sm_rec;

static sm_rec* recs = NULL;
static size_t nrecs = 0, recs_cap = 0;
static sm_loc* locs = NULL;
static size_t nlocs = 0, locs_cap = 0;
static int trace = 0;

static void fatal(const char* what) {
  fprintf(stderr, "a68lean: malformed LLVM stack map: %s\n", what);
  exit(1);
}

static void* grow(void* p, size_t* cap, size_t elt) {
  *cap = *cap ? *cap * 2 : 256;
  p = realloc(p, *cap * elt);
  if (!p) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  return p;
}

/* ---------------------------------------------------------------- bounds-checked reading */

typedef struct { const uint8_t* p; size_t n; size_t off; } reader;

static void need(reader* r, size_t k, const char* what) {
  if (k > r->n - r->off) fatal(what);
}
static uint8_t rd_u8(reader* r, const char* what) { need(r, 1, what); return r->p[r->off++]; }
static uint16_t rd_u16(reader* r, const char* what) { uint16_t v; need(r, 2, what); memcpy(&v, r->p + r->off, 2); r->off += 2; return v; }
static uint32_t rd_u32(reader* r, const char* what) { uint32_t v; need(r, 4, what); memcpy(&v, r->p + r->off, 4); r->off += 4; return v; }
static uint64_t rd_u64(reader* r, const char* what) { uint64_t v; need(r, 8, what); memcpy(&v, r->p + r->off, 8); r->off += 8; return v; }
static int32_t rd_i32(reader* r, const char* what) { int32_t v; need(r, 4, what); memcpy(&v, r->p + r->off, 4); r->off += 4; return v; }
static void rd_align8(reader* r, const char* what) {
  size_t pad = (8 - (r->off & 7)) & 7;
  need(r, pad, what);
  r->off += pad;
}

/* ---------------------------------------------------------------- parsing */

/* Parse one complete stack map starting at r->off (one object file's contribution). */
static void parse_map(reader* r) {
  if (rd_u8(r, "truncated header") != 3) fatal("unsupported version (expected 3)");
  rd_u8(r, "truncated header"); rd_u16(r, "truncated header");
  uint32_t nfunc = rd_u32(r, "truncated header");
  uint32_t nconst = rd_u32(r, "truncated header");
  uint32_t nrec = rd_u32(r, "truncated header");

  need(r, (size_t) nfunc * 24, "function table exceeds the section");
  const uint8_t* funcs = r->p + r->off;
  r->off += (size_t) nfunc * 24;
  need(r, (size_t) nconst * 8, "constant table exceeds the section");
  const uint8_t* consts = r->p + r->off;
  r->off += (size_t) nconst * 8;

  /* the records are grouped by function, RecordCount of each in turn */
  uint32_t fi = 0;         /* the function whose records are being read */
  uint64_t left = 0;       /* records of that function still to read */
  uint64_t faddr = 0, fsize = 0;
  uint64_t seen_total = 0;
  for (uint32_t i = 0; i < nfunc; i++) {
    uint64_t c; memcpy(&c, funcs + i * 24 + 16, 8);
    seen_total += c;
    if (seen_total < c || seen_total > nrec) fatal("record counts of the functions exceed NumRecords");
  }
  if (seen_total != nrec) fatal("record counts of the functions do not sum to NumRecords");

  for (uint32_t i = 0; i < nrec; i++) {
    while (left == 0) {
      if (fi >= nfunc) fatal("more records than the functions account for");
      memcpy(&faddr, funcs + fi * 24, 8);
      memcpy(&fsize, funcs + fi * 24 + 8, 8);
      memcpy(&left, funcs + fi * 24 + 16, 8);
      fi++;
    }
    left--;

    rd_u64(r, "truncated record");                       /* patchpoint id: unused */
    uint32_t ioff = rd_u32(r, "truncated record");
    rd_u16(r, "truncated record");
    uint16_t nloc = rd_u16(r, "truncated record");
    if (nloc < 3) fatal("statepoint record with fewer than three locations");

    /* the three leading constants; the third is the deopt count */
    uint64_t ndeopt = 0;
    for (int k = 0; k < 3; k++) {
      uint8_t type = rd_u8(r, "truncated location");
      rd_u8(r, "truncated location"); rd_u16(r, "truncated location");
      uint16_t reg = rd_u16(r, "truncated location");
      rd_u16(r, "truncated location");
      int32_t val = rd_i32(r, "truncated location");
      (void) reg;
      uint64_t v;
      if (type == LOC_CONSTANT) v = (uint64_t) (int64_t) val;
      else if (type == LOC_CONST_INDEX) {
        if (val < 0 || (uint64_t) val >= nconst) fatal("constant index out of range");
        memcpy(&v, consts + (size_t) val * 8, 8);
      } else fatal("statepoint record whose leading locations are not constants");
      if (k == 2) ndeopt = v;
    }
    if (ndeopt > (uint64_t) nloc - 3) fatal("deopt count exceeds the record's locations");
    uint64_t npairs2 = (uint64_t) nloc - 3 - ndeopt;
    if (npairs2 & 1) fatal("odd number of gc pointer locations (expected base/derived pairs)");

    /* deopt locations: not used by this collector, skipped */
    for (uint64_t k = 0; k < ndeopt; k++) { need(r, 12, "truncated location"); r->off += 12; }

    if (nrecs == recs_cap) recs = (sm_rec*) grow(recs, &recs_cap, sizeof(sm_rec));
    sm_rec* rec = &recs[nrecs++];
    rec->ret = (uintptr_t) faddr + ioff;
    rec->stack_size = fsize;
    rec->first_loc = (uint32_t) nlocs;
    rec->nloc = 0;

    for (uint64_t k = 0; k < npairs2; k++) {
      sm_loc l;
      l.type = rd_u8(r, "truncated location");
      rd_u8(r, "truncated location");
      uint16_t size = rd_u16(r, "truncated location");
      l.reg = rd_u16(r, "truncated location");
      rd_u16(r, "truncated location");
      l.off = rd_i32(r, "truncated location");
      l.konst = 0;
      switch (l.type) {
        case LOC_INDIRECT:
          if (size != 8) fatal("gc pointer spill slot that is not 8 bytes");
          /* fall through */
        case LOC_DIRECT:
          if (l.reg != REG_SP && l.reg != REG_FP) fatal("gc pointer location relative to a register other than SP or FP");
          if (l.reg == REG_SP && fsize == STACK_SIZE_UNKNOWN) fatal("SP-relative gc pointer in a frame of unknown size");
          break;
        case LOC_REGISTER:
          fatal("gc pointer held in a register across a call (not recoverable from the frame chain)");
          break;
        case LOC_CONSTANT:
          break;
        case LOC_CONST_INDEX:
          if (l.off < 0 || (uint64_t) l.off >= nconst) fatal("constant index out of range");
          memcpy(&l.konst, consts + (size_t) l.off * 8, 8);
          break;
        default:
          fatal("unknown location type");
      }
      /* a derived pointer at the same place as its base is the same pointer: keep it once */
      if ((k & 1) && locs[nlocs - 1].type == l.type && locs[nlocs - 1].reg == l.reg
          && locs[nlocs - 1].off == l.off && locs[nlocs - 1].konst == l.konst) continue;
      if (nlocs == locs_cap) locs = (sm_loc*) grow(locs, &locs_cap, sizeof(sm_loc));
      locs[nlocs++] = l;
      rec->nloc++;
    }

    rd_align8(r, "truncated record padding");
    rd_u16(r, "truncated live-outs");
    uint16_t nlive = rd_u16(r, "truncated live-outs");
    need(r, (size_t) nlive * 4, "live-outs exceed the section");
    r->off += (size_t) nlive * 4;
    rd_align8(r, "truncated record padding");
  }
  if (left != 0) fatal("fewer records than the functions account for");
}

static int cmp_rec(const void* a, const void* b) {
  uintptr_t x = ((const sm_rec*) a)->ret, y = ((const sm_rec*) b)->ret;
  return x < y ? -1 : x > y ? 1 : 0;
}

void stackmap_init(void) {
  unsigned long size = 0;
  const uint8_t* data = getsectiondata(&_mh_execute_header, "__LLVM_STACKMAPS", "__llvm_stackmaps", &size);
  if (!data || size == 0) return;                /* the C back end: no maps, no walk */
  const char* t = getenv("A68LEAN_STACKMAP");
  trace = t && strcmp(t, "trace") == 0;

  reader r = { data, (size_t) size, 0 };
  while (r.off < r.n) {
    parse_map(&r);
    rd_align8(&r, "truncated padding between stack maps");
  }
  qsort(recs, nrecs, sizeof(sm_rec), cmp_rec);
  for (size_t i = 1; i < nrecs; i++)
    if (recs[i].ret == recs[i - 1].ret) fatal("two records with the same return address");
  if (trace) fprintf(stderr, "stackmap: %zu records, %zu gc locations\n", nrecs, nlocs);
}

size_t stackmap_record_count(void) { return nrecs; }

/* ---------------------------------------------------------------- the walk */

static const sm_rec* find_rec(uintptr_t ret) {
  size_t lo = 0, hi = nrecs;
  while (lo < hi) {
    size_t mid = lo + (hi - lo) / 2;
    if (recs[mid].ret < ret) lo = mid + 1;
    else if (recs[mid].ret > ret) hi = mid;
    else return &recs[mid];
  }
  return NULL;
}

void stackmap_roots(void (*mark)(void* obj)) {
  if (nrecs == 0) return;

  /* the walk goes up from the current frame towards the top of the stack; the pointer
     of every frame must lie strictly above the previous one and below the stack's top */
  uintptr_t fp = (uintptr_t) __builtin_frame_address(0);
  uintptr_t top = (uintptr_t) pthread_get_stackaddr_np(pthread_self());
  if (fp == 0 || fp >= top) fatal("frame pointer outside the stack");

  while (fp != 0) {
    if ((fp & 7) != 0 || fp + 16 > top) fatal("frame pointer out of bounds during the walk");
    uintptr_t next = *(const uintptr_t*) fp;
    uintptr_t ret = STRIP_PAC(*(const uintptr_t*) (fp + 8));
    if (next != 0 && next <= fp) fatal("frame chain does not ascend");

    const sm_rec* rec = find_rec(ret);
    if (rec) {
      /* `ret` returns into an LLVM function at a statepoint; that function's frame is
         the parent, at `next` */
      uintptr_t ffp = next;
      if (ffp == 0) fatal("statepoint frame without a frame pointer");
      uintptr_t cfa = ffp + 16;
      uintptr_t sp = 0;
      if (rec->stack_size != STACK_SIZE_UNKNOWN) {
        if (rec->stack_size > ffp) fatal("stack size larger than the stack");
        sp = cfa - rec->stack_size;
        if (sp & 15) fatal("frame's SP not 16-byte aligned");
      }
      if (trace) fprintf(stderr, "stackmap: frame fp=%#" PRIxPTR " ret=%#" PRIxPTR " size=%" PRIu64 " locs=%u\n",
                         ffp, ret, rec->stack_size, rec->nloc);
      for (uint32_t i = 0; i < rec->nloc; i++) {
        const sm_loc* l = &locs[rec->first_loc + i];
        uintptr_t v = 0;
        switch (l->type) {
          case LOC_INDIRECT:
          case LOC_DIRECT: {
            uintptr_t base = l->reg == REG_SP ? sp : ffp;
            uintptr_t addr = base + (uintptr_t) (intptr_t) l->off;
            if (l->type == LOC_INDIRECT) {
              if (addr < sp || addr + 8 > cfa || (addr & 7)) fatal("gc pointer slot outside its frame");
              v = *(const uintptr_t*) addr;
            } else v = addr;   /* Direct: the location itself is the object (an alloca) */
            break;
          }
          case LOC_CONSTANT: v = (uintptr_t) (intptr_t) l->off; break;
          case LOC_CONST_INDEX: v = (uintptr_t) l->konst; break;
          default: fatal("unexpected location type at collection time");
        }
        if (trace) fprintf(stderr, "stackmap:   loc %u type %u reg %u off %d -> %#" PRIxPTR "\n", i, l->type, l->reg, l->off, v);
        if (v) mark((void*) v);
      }
    }
    fp = next;
  }
}
