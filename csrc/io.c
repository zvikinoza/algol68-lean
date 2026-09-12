/* Transput of compiled programs: files, the output buffer, unformatted and formatted
   reading and writing, binary transput, and the end of a run.  A transcription of the
   transput part of A68/Interp.lean; the Lean definition each function reproduces is
   named at its definition, and the a68g routine where the Lean one names it. */
#include "io.h"
#include "tables.h"
#include "fmt.h"
#include "bigint.h"
#include "os.h"
#include "mp.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

int a68_ll_digits = 12;
int a68_regression = 0;
int a68_argc = 0;
char** a68_argv = NULL;

/* ---------------------------------------------------------------- small helpers */

static void* xm(size_t n) { return xmalloc(n); }

typedef struct { char* p; size_t n, cap; } sbuf;
static void sb_put(sbuf* b, const char* s, size_t n) {
  if (b->n + n + 1 > b->cap) {
    b->cap = (b->n + n + 1) * 2 + 32;
    b->p = (char*) realloc(b->p, b->cap);
    if (!b->p) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  }
  memcpy(b->p + b->n, s, n);
  b->n += n;
  b->p[b->n] = 0;
}
static void sb_putc(sbuf* b, char c) { sb_put(b, &c, 1); }
static void sb_puts(sbuf* b, const char* s) { sb_put(b, s, strlen(s)); }
static char* sb_take(sbuf* b) { if (!b->p) sb_put(b, "", 0); return b->p; }

static char* dup_n(const char* s, size_t n) {
  char* d = (char*) xm(n + 1);
  memcpy(d, s, n);
  d[n] = 0;
  return d;
}

/* an error message about a mode: "prefix<mode>suffix" */
__attribute__((noreturn)) static void die_mode(const char* pre, uint32_t m, const char* post) {
  char* ms = mode_string(m);
  sbuf b = {0};
  sb_puts(&b, pre); sb_puts(&b, ms); sb_puts(&b, post);
  free(ms);
  die(b.p);
}

__attribute__((noreturn)) static void die_mode_str(const char* pre, uint32_t m, const char* mid, const char* s, size_t n, const char* post) {
  char* ms = mode_string(m);
  sbuf b = {0};
  sb_puts(&b, pre); sb_puts(&b, ms); sb_puts(&b, mid); sb_put(&b, s, n); sb_puts(&b, post);
  free(ms);
  die(b.p);
}

/* ---------------------------------------------------------------- widths (A68/Numfmt.lean) */

/* a68g `MP_BITS_WIDTH (k)`, computed in doubles as it is there */
static int mp_bits_width(int k) { return (int) ceil((double) (k * 7) * 3.321928094887362) - 1; }
static int bits_width_of(int64_t longness) {   /* Numfmt.bitsWidthOfLen */
  return longness <= 0 ? 32 : longness == 1 ? mp_bits_width(7) : mp_bits_width(a68_ll_digits);
}
static int real_width_of(int64_t longness) {   /* Numfmt.realWidthOf */
  return longness <= 0 ? 15 : longness == 1 ? 42 : (a68_ll_digits - 2) * 7;
}
static int exp_width_of(int64_t longness) { (void) longness; return 3; }   /* Numfmt.expWidthOf */

/* Numfmt.maxIntOf, fresh */
static a68_big* max_int_of(int64_t longness) {
  if (longness <= 0) return big_from_i64(2147483647);
  a68_big* p = big_pow10(longness == 1 ? 49 : a68_ll_digits * 7);
  a68_big* one = big_from_i64(1);
  a68_big* r = big_sub(p, one);
  big_free(p); big_free(one);
  return r;
}

/* 2^w - 1 */
static a68_big* bits_mask(int64_t longness) {
  int w = bits_width_of(longness);
  a68_big* r = big_from_i64(1);
  while (w > 0) {
    int k = w > 30 ? 30 : w;
    a68_big* t = big_mul_small(r, (int64_t) 1 << k);
    big_free(r); r = t;
    w -= k;
  }
  a68_big* one = big_from_i64(1);
  a68_big* m = big_sub(r, one);
  big_free(r); big_free(one);
  return m;
}

/* ---------------------------------------------------------------- values */

/* the a68_big of an integral or bits value: T_INT, T_BITS, T_BIGINT, T_BIGBITS */
static a68_big* big_of_val(a68_val v) {
  switch (v.tag) {
    case T_INT: return big_from_i64(v.v.i);
    case T_BITS: {
      if (v.v.u <= (uint64_t) INT64_MAX) return big_from_i64((int64_t) v.v.u);
      char t[32]; snprintf(t, sizeof t, "%llu", (unsigned long long) v.v.u);
      return big_from_dec(t, strlen(t));
    }
    case T_BIGINT: case T_BIGBITS: { a68_leaf* l = (a68_leaf*) v.v.p; return big_from_dec((const char*) l->d, l->h.n); }
    case T_UNDEF: die("attempt to use an uninitialised INT value");
    default: die("internal: INT expected");
  }
}

static a68_val leaf_of_dec(uint32_t tag, const char* s) {
  size_t n = strlen(s);
  a68_leaf* l = leaf_alloc(EK_BYTES, (uint32_t) n);
  memcpy(l->d, s, n);
  return mk_ptr(tag, (a68_obj*) l, 0);
}

/* an integral value: T_INT when it fits, otherwise T_BIGINT (as `A68.Blob` decides) */
static a68_val val_of_big(const a68_big* b) {
  if (big_fits_i64(b)) return mk_int(big_to_i64(b));
  char* s = big_to_dec(b);
  a68_val v = leaf_of_dec(T_BIGINT, s);
  free(s);
  return v;
}

static a68_val bits_of_big(const a68_big* b) {
  if (big_ndigits(b) <= 20 && big_sign(b) >= 0) {
    char* s = big_to_dec(b);
    size_t n = strlen(s);
    int fits = n < 20 || strcmp(s, "18446744073709551615") <= 0;
    unsigned long long u = fits ? strtoull(s, NULL, 10) : 0;
    free(s);
    if (fits) return mk_bits((uint64_t) u);
  }
  char* s = big_to_dec(b);
  a68_val v = leaf_of_dec(T_BIGBITS, s);
  free(s);
  return v;
}

a68_val of_string(const char* s, size_t n) { return string_row((const uint8_t*) s, (int64_t) n, 1); }

/* `Interp.strOf` */
uint8_t* str_of(a68_val v, int64_t* n) {
  if (v.tag == T_ROW) return string_bytes(v, n);
  if (v.tag == T_CHAR) { uint8_t* b = (uint8_t*) xm(2); b[0] = (uint8_t) v.v.u; b[1] = 0; *n = 1; return b; }
  if (v.tag == T_UNDEF) die("attempt to use an uninitialised STRING value");
  die("internal: STRING expected");
}

/* `Interp.readRef` */
a68_val ref_load_checked(a68_val r) {
  switch (r.tag) {
    case T_REF: return ref_load(r);
    case T_FILE: return r;
    case T_NIL: die("attempt to dereference NIL");
    case T_UNDEF: die("attempt to use an uninitialised REF value");
    default: die("internal: dereferencing a non-REF");
  }
}

a68_val row_of_values(const a68_val* vs, int64_t n) {
  a68_rowd* d = rowd_alloc(1);
  a68_obj* st = n > 0 ? store_alloc_for((uint32_t) n, &vs[0]) : store_alloc_slots(0);
  for (int64_t i = 0; i < n; i++) store_set(st, i, vs[i]);
  st->rc = 1;
  d->base = st;
  d->off = 0;
  d->dim[0].l = 1; d->dim[0].u = n; d->dim[0].stride = 1;
  return mk_ptr(T_ROW, (a68_obj*) d, 0);
}

int mode_is_file_proc(uint32_t m) {
  const a68_mode* p = mode_at(m);
  if (p->k != M_PROC || p->n != 1 || mode_at(p->sub)->k != M_VOID) return 0;
  const a68_mode* a = mode_at(p->modes[0]);
  return a->k == M_REF && mode_at(a->sub)->k == M_FILE;
}

int mode_is_string(uint32_t m) {
  const a68_mode* p = mode_at(m);
  return p->k == M_ROW && p->dims == 1 && mode_at(p->sub)->k == M_CHAR;
}

static int mode_is_flex_string(uint32_t m) { return mode_is_string(m) && mode_at(m)->flex; }

double check_real(double x) {
  if (isnan(x)) die("REAL value is not a number");
  if (isinf(x)) die("infinite REAL value");
  return x;
}

static int64_t expect_int(a68_val v) { return as_int(v); }

/* the pieces of a COMPL value */
static int compl_parts(a68_val v, a68_val* re, a68_val* im) {
  if (v.tag != T_STRUCT) return 0;
  a68_slots* s = (a68_slots*) v.v.p;
  if (s->h.n != 2) return 0;
  *re = s->s[0]; *im = s->s[1];
  return 1;
}

/* ---------------------------------------------------------------- the operand stack as a root stack */

static void root(a68_val v) { push(v); }

/* ---------------------------------------------------------------- unwinding */

static io_catch* io_top = NULL;
size_t env_saved_depth(void);
void env_saved_truncate(size_t n);
static size_t arena_n = 0;
static void arena_free_to(size_t mark);

void io_catch_push(io_catch* c) {
  c->sp0 = sp; c->env0 = env_saved_depth(); c->arena0 = arena_n; c->prev = io_top;
  io_top = c;
}
void io_catch_pop(io_catch* c) { io_top = c->prev; }

void io_raise(int kind) {
  io_catch* c = io_top;
  if (!c) die("internal: transput event with no handler");
  io_top = c->prev;
  sp = c->sp0;
  env_saved_truncate(c->env0);
  arena_free_to(c->arena0);
  longjmp(c->jb, kind);
}

void io_check_jump(void) { if (a68_jump_flag) io_raise(IO_JUMP); }

/* ---------------------------------------------------------------- files */

a68_file* files = NULL;
size_t nfiles = 0;
static size_t files_cap = 0;

a68_file file_default(void) {
  a68_file f;
  memset(&f, 0, sizeof f);
  f.assoc = mk_tag(T_UNDEF); f.on_end = mk_tag(T_UNDEF); f.on_value = mk_tag(T_UNDEF); f.on_line = mk_tag(T_UNDEF);
  f.fd = -1;
  f.channel = 3;
  return f;
}

a68_file* file_get(uint32_t fid) {
  if (fid >= nfiles) die("file is not open");
  return &files[fid];
}

uint32_t file_push(a68_file f) {
  if (nfiles == files_cap) {
    files_cap = files_cap ? files_cap * 2 : 16;
    files = (a68_file*) realloc(files, files_cap * sizeof(a68_file));
    if (!files) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  }
  files[nfiles] = f;
  return (uint32_t) nfiles++;
}

void file_pop(uint32_t fid) {
  if (nfiles == (size_t) fid + 1) {
    free(files[fid].buf); free(files[fid].name); free(files[fid].term);
    nfiles--;
  }
}

static void file_set(uint32_t fid, a68_file f) {
  if (fid < nfiles) { free(files[fid].buf); free(files[fid].name); free(files[fid].term); files[fid] = f; }
}

/* `Interp.newFile` */
uint32_t file_new(a68_val fv, a68_file f) {
  if (fv.tag == T_FILE) { file_set(fv.aux, f); return fv.aux; }
  uint32_t fid = file_push(f);
  a68_val v = mk_tag(T_FILE); v.aux = fid;
  store_ref(fv, v);
  return fid;
}

uint32_t file_id_of(a68_val f) {
  if (f.tag == T_FILE) return f.aux;
  if (f.tag == T_REF) {
    a68_val v = ref_load(f);
    if (v.tag == T_FILE) return v.aux;
  }
  die("internal: file expected");
}

uint32_t file_channel(a68_val f) {
  uint32_t fid = file_id_of(f);
  a68_file* fs = file_get(fid);
  return fid <= 2 ? fid : (uint32_t) fs->channel;
}

void file_flush(uint32_t fid) {
  a68_file* f = file_get(fid);
  if (f->ondisk && f->dirty && f->writing) {
    os_write_file(f->name, f->buf, f->len);
    f->dirty = 0;
  }
}

void io_gc_roots(void (*mark)(const a68_val*)) {
  for (size_t i = 0; i < nfiles; i++) {
    mark(&files[i].assoc); mark(&files[i].on_end); mark(&files[i].on_value); mark(&files[i].on_line);
  }
}

static void buf_append(a68_file* f, const uint8_t* p, size_t n) {
  if (f->len + n > f->cap) {
    f->cap = (f->len + n) * 2 + 64;
    f->buf = (uint8_t*) realloc(f->buf, f->cap);
    if (!f->buf) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  }
  memcpy(f->buf + f->len, p, n);
  f->len += n;
}

static void buf_set(a68_file* f, const uint8_t* p, size_t n) {
  f->len = 0;
  buf_append(f, p, n);
}

/* ---------------------------------------------------------------- output */

static uint8_t* outbuf = NULL;
static size_t outlen = 0, outcap = 0;
int io_nul_cut = 0;
int64_t io_col = 0;

static void out_append(const uint8_t* p, size_t n) {
  if (outlen + n > outcap) {
    outcap = (outlen + n) * 2 + 4096;
    outbuf = (uint8_t*) realloc(outbuf, outcap);
    if (!outbuf) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  }
  memcpy(outbuf + outlen, p, n);
  outlen += n;
}

void emit_bytes(const uint8_t* p, size_t n) { out_append(p, n); }
size_t out_size(void) { return outlen; }

void io_flush_out(void) {
  if (outlen) fwrite(outbuf, 1, outlen, stdout);
  outlen = 0;
  fflush(stdout);
}

/* `Runtime.flushOut`: in regression mode a68g terminates an unfinished last line */
static void flush_final(void) {
  if (a68_regression && outlen > 0 && outbuf[outlen - 1] != '\n') { uint8_t nl = '\n'; out_append(&nl, 1); }
  io_flush_out();
}

uint32_t io_finish(void) {
  flush_final();
  for (size_t i = 0; i < nfiles; i++) {
    a68_file* f = &files[i];
    if (f->ondisk && f->dirty && f->writing) os_write_file(f->name, f->buf, f->len);
  }
  return 0;
}

void io_stop(void) { flush_final(); exit(0); }

/* the formatted call in progress on standard output, whose unpurged output an error drops
   (`Interp.discardUnpurged`) */
static int pf_active = 0;
static size_t pf_start = 0, pf_item = 0;

static void discard_unpurged(size_t start, size_t item_mark) {
  size_t cut = start;
  size_t lim = item_mark < outlen ? item_mark : outlen;
  for (size_t i = start; i < lim; i++) if (outbuf[i] == 10 || outbuf[i] == 12) cut = i + 1;
  if (cut < outlen) outlen = cut;
}

void io_die(const char* msg) {
  if (pf_active) discard_unpurged(pf_start, pf_item);
  flush_final();
  fprintf(stderr, "a68lean: runtime error: %u: %s.\n", (unsigned) a68_line_no, msg);
  exit(1);
}

/* append text to the string an associated file writes (`Interp.fileOut`) */
int ref_append_values(a68_val r, const a68_val* vs, int64_t n);

static void assoc_append(a68_val r, const uint8_t* s, size_t n) {
  a68_val* tmp = (a68_val*) xm((n ? n : 1) * sizeof(a68_val));
  for (size_t i = 0; i < n; i++) tmp[i] = mk_char(s[i]);
  int ok = ref_append_values(r, tmp, (int64_t) n);
  free(tmp);
  if (ok) return;
  int64_t on;
  uint8_t* old = str_of(ref_load_checked(r), &on);
  uint8_t* cat = (uint8_t*) xm((size_t) on + n + 1);
  memcpy(cat, old, (size_t) on);
  memcpy(cat + on, s, n);
  store_ref(r, string_row(cat, on + (int64_t) n, 1));
  free(old); free(cat);
}

/* `Interp.fileOut` */
void file_out(uint32_t fid, const char* s, size_t n) {
  for (size_t i = 0; i < n; i++) { if (s[i] == '\n') io_col = 0; else io_col++; }
  if (fid == 0 || fid == 2) {
    if (io_nul_cut) return;
    const char* z = (const char*) memchr(s, 0, n);
    if (z) { io_nul_cut = 1; n = (size_t) (z - s); }
    if (fid == 0) out_append((const uint8_t*) s, n);
    else { fwrite(s, 1, n, stderr); fflush(stderr); }
    return;
  }
  a68_file* f = file_get(fid);
  if (f->fd >= 0) {
    os_write_fd((int) f->fd, (const uint8_t*) s, n);
    f->writing = 1;
    return;
  }
  if (f->assoc.tag != T_UNDEF) {
    /* a68g empties the string when an associated file turns to writing
       (`open_physical_file`), and each write appends to what the string then holds */
    if (!f->writing) {
      store_ref(f->assoc, of_string("", 0));
      f = file_get(fid);
      f->writing = 1; f->reading = 0;
    }
    assoc_append(f->assoc, (const uint8_t*) s, n);
    return;
  }
  buf_append(f, (const uint8_t*) s, n);
  f->writing = 1; f->dirty = 1; f->loaded = 1;
}

void file_out_str(uint32_t fid, const char* s) { file_out(fid, s, strlen(s)); }

/* `Interp.fileOutByte` */
void file_out_byte(uint32_t fid, uint8_t b) {
  if (fid == 0) {
    if (!io_nul_cut) { if (b == 0) io_nul_cut = 1; else out_append(&b, 1); }
  } else file_out(fid, (const char*) &b, 1);
}

/* put a malloc'ed string and free it */
static void file_out_take(uint32_t fid, char* s) { file_out(fid, s, strlen(s)); free(s); }

/* ---------------------------------------------------------------- numbers as text */

/* `Numfmt.printInt` of an INT / LONG INT value */
char* fmt_int_of(a68_val v, int64_t longness) {
  a68_big* b = big_of_val(v);
  char* s = a68_fmt_print_int(b, longness, a68_ll_digits);
  big_free(b);
  return s;
}

static char* fmt_bits_of(a68_val v, int64_t longness) {
  a68_big* b = big_of_val(v);
  char* s = a68_fmt_print_bits(b, bits_width_of(longness));
  big_free(b);
  return s;
}

/* `Interp.mpFloatStd` and the `MPFmt` routines go through mp.h */

/* ---------------------------------------------------------------- printing values */

static void call_file_proc(uint32_t fid, a68_val f) {
  if (f.tag == T_BUILTIN) {
    const char* n = strtab[f.aux];
    if (strcmp(n, "newline") == 0) file_out(fid, "\n", 1);
    else if (strcmp(n, "newpage") == 0) file_out(fid, "\x0c", 1);
    else if (strcmp(n, "space") == 0) file_out(fid, " ", 1);
    else if (strcmp(n, "backspace") == 0) file_out(fid, "\x08", 1);
    else { sbuf b = {0}; sb_puts(&b, "cannot print procedure "); sb_puts(&b, n); die(b.p); }
  } else die("cannot print a procedure value");
}

/* `Interp.printValue` */
void print_value(uint32_t fid, uint32_t m, a68_val v) {
  uint32_t mr = mode_resolve(m);
  const a68_mode* p = mode_at(mr);
  if (v.tag == T_UNION) { a68_slots* s = (a68_slots*) v.v.p; print_value(fid, v.aux, s->s[0]); return; }
  switch (p->k) {
    case M_INT:
      if (v.tag == T_INT || v.tag == T_BIGINT) { file_out_take(fid, fmt_int_of(v, p->len)); return; }
      if (v.tag == T_REAL) { file_out_take(fid, a68_fmt_print_real(v.v.r, 0, a68_ll_digits)); return; }
      break;
    case M_REAL:
      if (v.tag == T_MP) { file_out_take(fid, mp_float_std(v, p->len)); return; }
      if (v.tag == T_REAL) { check_real(v.v.r); file_out_take(fid, a68_fmt_print_real(v.v.r, p->len, a68_ll_digits)); return; }
      if (v.tag == T_INT) { file_out_take(fid, a68_fmt_print_real((double) v.v.i, p->len, a68_ll_digits)); return; }
      break;
    case M_COMPL: {
      a68_val re, im;
      if (compl_parts(v, &re, &im)) {
        if (re.tag == T_MP && im.tag == T_MP) {
          file_out_take(fid, mp_float_std(re, p->len));
          file_out_take(fid, mp_float_std(im, p->len));
          return;
        }
        if (re.tag == T_REAL && im.tag == T_REAL) {
          check_real(re.v.r); check_real(im.v.r);
          file_out_take(fid, a68_fmt_print_real(re.v.r, p->len, a68_ll_digits));
          file_out_take(fid, a68_fmt_print_real(im.v.r, p->len, a68_ll_digits));
          return;
        }
      }
      break;
    }
    case M_BOOL: if (v.tag == T_BOOL) { file_out(fid, v.v.u ? "T" : "F", 1); return; } break;
    case M_CHAR: if (v.tag == T_CHAR) { file_out_byte(fid, (uint8_t) v.v.u); return; } break;
    case M_BITS: if (v.tag == T_BITS || v.tag == T_BIGBITS) { file_out_take(fid, fmt_bits_of(v, p->len)); return; } break;
    case M_BYTES:
      if (v.tag == T_ROW) {
        a68_rowd* d = (a68_rowd*) v.v.p;
        int64_t n = row_count(d);
        for (int64_t i = 0; i < n; i++) file_out_byte(fid, (uint8_t) as_char(rowd_get(d, row_store_index(d, i))));
        return;
      }
      break;
    case M_ROW:
      if (v.tag == T_ROW) {
        a68_rowd* d = (a68_rowd*) v.v.p;
        int64_t n = row_count(d);
        for (int64_t i = 0; i < n; i++) {
          a68_val e = rowd_get(d, row_store_index(d, i));
          if (e.tag == T_UNDEF) die_mode("attempt to use an uninitialised ", p->sub, " value");
          print_value(fid, p->sub, e);
        }
        return;
      }
      break;
    case M_STRUCT:
      if (v.tag == T_STRUCT) {
        a68_slots* s = (a68_slots*) v.v.p;
        uint32_t n = p->n < s->h.n ? p->n : s->h.n;
        for (uint32_t i = 0; i < n; i++) {
          if (s->s[i].tag == T_UNDEF) die_mode("attempt to use an uninitialised ", p->modes[i], " value");
          print_value(fid, p->modes[i], s->s[i]);
        }
        return;
      }
      break;
    case M_PROC: if (mode_is_file_proc(mr)) { call_file_proc(fid, v); return; } break;
    case M_FORMAT: die("cannot print a FORMAT value");
    default: break;
  }
  if (v.tag == T_UNDEF) die_mode("attempt to use an uninitialised ", m, " value");
  if (v.tag == T_NIL) die("cannot print NIL");
  die_mode("cannot print a value of mode ", m, "");
}

/* the `print`/`put` loop of `Interp.callBuiltin` */
void print_items(uint32_t fid, a68_val row) {
  if (row.tag != T_ROW) die("internal: print argument");
  a68_rowd* d = (a68_rowd*) row.v.p;
  int64_t n = row_count(d);
  for (int64_t i = 0; i < n; i++) {
    a68_val e = rowd_get(d, row_store_index(d, i));
    if (e.tag != T_UNION) die("internal: print argument");
    print_value(fid, e.aux, ((a68_slots*) e.v.p)->s[0]);
    io_nul_cut = 0;
  }
}

/* ---------------------------------------------------------------- input */

/* `Interp.loadFile` */
a68_file* load_file(uint32_t fid) {
  a68_file* f = file_get(fid);
  if (f->fd >= 0) {
    /* the end of a pipe: take what one read gives when the characters so far are used up */
    if (f->pos < f->len || f->eof) return f;
    io_flush_out();
    os_bytes ch = os_read_fd((int) f->fd);
    if (ch.n == 0) f->eof = 1; else buf_append(f, ch.p, ch.n);
    free(ch.p);
    f->loaded = 1; f->reading = 1;
    return f;
  }
  if (fid == 1) {
    /* standard input is read a line at a time so that interactive programs work:
       pending output is flushed first, and more input is fetched only when needed */
    if (f->pos < f->len || f->eof) return f;
    io_flush_out();
    char* line = NULL; size_t cap = 0;
    ssize_t n = getline(&line, &cap, stdin);
    if (n <= 0) f->eof = 1; else buf_append(f, (const uint8_t*) line, (size_t) n);
    free(line);
    f->loaded = 1; f->reading = 1;
    return f;
  }
  if (f->loaded) return f;
  if (f->assoc.tag != T_UNDEF) {
    int64_t n;
    uint8_t* s = str_of(ref_load_checked(f->assoc), &n);
    f = file_get(fid);
    buf_set(f, s, (size_t) n);
    free(s);
    f->pos = 0; f->loaded = 1;
    return f;
  }
  f->loaded = 1;
  return f;
}

int read_char(uint32_t fid) {
  a68_file* f = load_file(fid);
  if (f->pos < f->len) { f->reading = 1; return f->buf[f->pos++]; }
  return -1;
}

int peek_char(uint32_t fid) {
  a68_file* f = load_file(fid);
  return f->pos < f->len ? f->buf[f->pos] : -1;
}

int at_end(uint32_t fid) {
  a68_file* f = load_file(fid);
  return f->pos >= f->len;
}

/* apply an event routine to the file; its BOOL result */
int io_call_handler(a68_val h, uint32_t fid) {
  a68_val fv = mk_tag(T_FILE); fv.aux = fid;
  push(fv);
  call_value(h, 1);
  a68_val r = pop();
  io_check_jump();
  return r.tag == T_BOOL && r.v.u != 0;
}

/* `Interp.valueError`: the mender if any (TRUE = abandon the transput call), else an error */
__attribute__((noreturn)) static void value_error(uint32_t fid, const char* msg) {
  a68_file* f = file_get(fid);
  if (f->on_value.tag != T_UNDEF) {
    if (io_call_handler(f->on_value, fid)) io_raise(IO_FILE_END);
    die(msg);
  }
  die(msg);
}

__attribute__((noreturn)) static void value_error_mode(uint32_t fid, uint32_t tm, const char* s, size_t n) {
  char* ms = mode_string(tm);
  sbuf b = {0};
  sb_puts(&b, "cannot read "); sb_puts(&b, ms); sb_puts(&b, " from \""); sb_put(&b, s, n); sb_puts(&b, "\"");
  free(ms);
  value_error(fid, b.p);
}

/* `Interp.skipChar` */
static void skip_char(uint32_t fid) {
  int c = peek_char(fid);
  if (c == 10) {
    a68_file* f = file_get(fid);
    if (f->on_line.tag != T_UNDEF) {
      if (io_call_handler(f->on_line, fid)) read_char(fid);
      else die("end of line reached while reading");
    } else read_char(fid);
  } else if (c >= 0) read_char(fid);
  /* a68g: skipping a character at end of file is not an event */
}

/* `Interp.refreshAssoc` */
static void refresh_assoc(uint32_t fid) {
  a68_file* f = file_get(fid);
  if (f->assoc.tag == T_UNDEF) return;
  int64_t n;
  uint8_t* s = str_of(ref_load_checked(f->assoc), &n);
  f = file_get(fid);
  /* a68g reads the string's current value at the position reached so far */
  if ((size_t) n != f->len || memcmp(s, f->buf, (size_t) n) != 0) { buf_set(f, s, (size_t) n); f->loaded = 1; }
  free(s);
}

/* `Interp.logicalEnd`: never returns */
void logical_end(uint32_t fid) {
  a68_file* f = file_get(fid);
  if (f->on_end.tag != T_UNDEF) {
    if (io_call_handler(f->on_end, fid)) io_raise(IO_FILE_END);
    die("logical file end");
  }
  die("attempt to read past logical end of file");
}

static int is_space(int c) { return c == 32 || c == 9 || c == 10 || c == 13; }

static void skip_spaces(uint32_t fid) {
  for (;;) {
    int c = peek_char(fid);
    if (c >= 0 && is_space(c)) read_char(fid); else break;
  }
}

char* read_token(uint32_t fid, size_t* n) {
  skip_spaces(fid);
  if (at_end(fid)) logical_end(fid);
  sbuf b = {0};
  for (;;) {
    int c = peek_char(fid);
    if (c < 0 || is_space(c)) break;
    read_char(fid);
    sb_putc(&b, (char) c);
  }
  *n = b.n;
  return sb_take(&b);
}

/* `Interp.readNumber`: optional sign, digits, and for reals an optional fraction and exponent */
static char* read_number(uint32_t fid, int real, size_t* n) {
  skip_spaces(fid);
  if (at_end(fid)) logical_end(fid);
  sbuf b = {0};
  int c;
  #define PEEK_IS(cond) ((c = peek_char(fid)) >= 0 && (cond))
  #define TAKE() sb_putc(&b, (char) read_char(fid))
  if (PEEK_IS(c == '+' || c == '-')) TAKE();
  while (PEEK_IS(c >= '0' && c <= '9')) TAKE();
  if (real) {
    if (PEEK_IS(c == '.')) {
      TAKE();
      while (PEEK_IS(c >= '0' && c <= '9')) TAKE();
    }
    if (PEEK_IS(c == 'e' || c == 'E')) {
      TAKE();
      /* a68g writes an exponent as `e -51`, and reads it back so */
      while (PEEK_IS(c == ' ')) read_char(fid);
      if (PEEK_IS(c == '+' || c == '-')) TAKE();
      while (PEEK_IS(c == ' ')) read_char(fid);
      while (PEEK_IS(c >= '0' && c <= '9')) TAKE();
    }
  }
  #undef PEEK_IS
  #undef TAKE
  if (b.n == 0 || (b.n == 1 && (b.p[0] == '+' || b.p[0] == '-'))) value_error(fid, "invalid numeral in input");
  *n = b.n;
  return sb_take(&b);
}

/* `Interp.readLineStr`: up to (not including) the end of line or a terminator character */
char* read_line_str(uint32_t fid, size_t* n) {
  if (at_end(fid)) logical_end(fid);
  sbuf b = {0};
  for (;;) {
    int c = peek_char(fid);
    if (c < 0 || c == 10) break;
    a68_file* f = file_get(fid);
    int term = 0;
    for (size_t k = 0; k < f->nterm; k++) if (f->term[k] == c) term = 1;
    if (term) break;
    read_char(fid);
    sb_putc(&b, (char) c);
  }
  *n = b.n;
  return sb_take(&b);
}

void skip_line(uint32_t fid) {
  for (;;) {
    int c = read_char(fid);
    if (c < 0 || c == 10) break;
  }
}

/* what a68g's `strtol` accepts when it converts the characters a C-style pattern read:
   blanks, a sign and digits, with nothing after them (`Interp.parseIntText`) */
static a68_big* parse_int_text(const char* s, size_t n) {
  size_t i = 0;
  while (i < n && (s[i] == ' ' || s[i] == '\t' || s[i] == '\n')) i++;
  int neg = 0;
  if (i < n && (s[i] == '-' || s[i] == '+')) { neg = s[i] == '-'; i++; }
  if (i >= n) return NULL;
  for (size_t k = i; k < n; k++) if (s[k] < '0' || s[k] > '9') return NULL;
  a68_big* v = big_from_dec(s + i, n - i);
  if (neg) { a68_big* t = big_neg(v); big_free(v); v = t; }
  return v;
}

/* `Interp.parseRealText` */
static int parse_real_text(const char* s, size_t n, double* out) {
  size_t i = 0;
  while (i < n && (s[i] == ' ' || s[i] == '\t' || s[i] == '\n')) i++;
  int neg = 0;
  if (i < n && (s[i] == '-' || s[i] == '+')) { neg = s[i] == '-'; i++; }
  size_t body = i;
  size_t ip = 0;
  while (i < n && s[i] >= '0' && s[i] <= '9') { i++; ip++; }
  size_t fp = 0;
  if (i < n && s[i] == '.') { i++; while (i < n && s[i] >= '0' && s[i] <= '9') { i++; fp++; } }
  int exp_ok = 1;
  if (i < n) {
    if (s[i] != 'e' && s[i] != 'E') exp_ok = 0;
    else {
      i++;
      if (i < n && (s[i] == '+' || s[i] == '-')) i++;
      if (i >= n) exp_ok = 0;
      for (size_t k = i; k < n; k++) if (s[k] < '0' || s[k] > '9') exp_ok = 0;
    }
  }
  if ((ip == 0 && fp == 0) || !exp_ok) return 0;
  double x = a68_fmt_parse_float(s + body, n - body);
  *out = neg ? -x : x;
  return 1;
}

/* the value of the digits a bits pattern or C-style pattern read, in base `radix`; a digit
   outside the radix, or a value too wide for the mode, is an error (a68g `bits_to_int`) */
static a68_val radix_value(uint32_t fid, const char* s, size_t n, int radix, int64_t longness) {
  (void) fid;
  a68_big* v = big_from_i64(0);
  size_t i = 0;
  /* `strtoul` passes over leading white space */
  while (i < n && (s[i] == ' ' || s[i] == '\t' || s[i] == '\n')) i++;
  for (; i < n; i++) {
    char c = s[i];
    int d = c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 87 : c >= 'A' && c <= 'F' ? c - 55 : 99;
    if (d >= radix) { big_free(v); die_mode("error in ", mode_simple(M_BITS, longness), " denotation"); }
    a68_big* t = big_mul_small(v, radix);
    a68_big* dd = big_from_i64(d);
    a68_big* u = big_add(t, dd);
    big_free(v); big_free(t); big_free(dd);
    v = u;
  }
  a68_big* mask = bits_mask(longness);
  int over = big_cmp(v, mask) > 0;
  big_free(mask);
  if (over) { big_free(v); die_mode("", mode_simple(M_BITS, longness), " value out of range"); }
  a68_val r = bits_of_big(v);
  big_free(v);
  return r;
}

/* an integral value read as text, stored as `Lean` stores the `Int` it parsed */
static a68_val int_of_text(const char* s, size_t n) {
  a68_big* b = big_from_dec(s, n);
  a68_val v = val_of_big(b);
  big_free(b);
  return v;
}

/* `String.toInt?`: an optional minus sign and digits */
static int is_int_text(const char* s, size_t n) {
  size_t i = 0;
  if (i < n && s[i] == '-') i++;
  if (i >= n) return 0;
  for (; i < n; i++) if (s[i] < '0' || s[i] > '9') return 0;
  return 1;
}

static a68_val real_of_text(const char* s, size_t n) {
  int neg = n > 0 && s[0] == '-';
  size_t i = (n > 0 && (s[0] == '-' || s[0] == '+')) ? 1 : 0;
  double x = a68_fmt_parse_float(s + i, n - i);
  return mk_real(neg ? -x : x);
}

static a68_val undef_pair(void) {
  a68_slots* s = slots_alloc(2);
  s->s[0] = mk_tag(T_UNDEF); s->s[1] = mk_tag(T_UNDEF);
  return mk_ptr(T_STRUCT, (a68_obj*) s, 0);
}

/* read into a united name: a value of the mode the united value currently has, through a
   temporary cell (`Interp.readInto`, the `.union` arm) */
static void read_union(uint32_t fid, uint32_t t, a68_val r, void (*rd)(uint32_t, void*, uint32_t, a68_val), void* st) {
  a68_val cur = ref_load(r);
  if (cur.tag != T_UNION) die_mode("attempt to use an uninitialised ", t, " value");
  uint32_t um = cur.aux;
  a68_slots* tmp = slots_alloc(1);
  tmp->s[0] = ((a68_slots*) cur.v.p)->s[0];
  a68_val tr = mk_ptr(T_REF, (a68_obj*) tmp, 0);
  root(tr);
  rd(fid, st, mode_ref(um), tr);
  a68_slots* u = slots_alloc(1);
  u->s[0] = tmp->s[0];
  store_ref(r, mk_ptr(T_UNION, (a68_obj*) u, um));
  (void) pop();
}

static void read_into_cb(uint32_t fid, void* st, uint32_t m, a68_val r) { (void) st; read_into(fid, m, r); }

/* `Interp.readInto` */
void read_into(uint32_t fid, uint32_t m, a68_val r) {
  uint32_t mr = mode_resolve(m);
  const a68_mode* p = mode_at(mr);
  if (p->k == M_REF) {
    uint32_t tsub = p->sub;
    uint32_t t = mode_resolve(tsub);
    const a68_mode* q = mode_at(t);
    switch (q->k) {
      case M_INT: {
        size_t n; char* tok = read_number(fid, 0, &n);
        const char* s = tok; if (n > 0 && s[0] == '+') { s++; n--; }
        if (!is_int_text(s, n)) { sbuf b = {0}; sb_puts(&b, "cannot read INT from \""); sb_put(&b, s, n); sb_puts(&b, "\""); die(b.p); }
        store_ref(r, int_of_text(s, n));
        free(tok);
        return;
      }
      case M_STRUCT:
        for (uint32_t i = 0; i < q->n; i++) read_into(fid, mode_ref(q->modes[i]), ref_field(r, i));
        return;
      case M_REAL: {
        size_t n; char* tok = read_number(fid, 1, &n);
        if (q->len >= 1) {
          /* `genie_string_to_value_internal`: `string_to_mp` at the length's precision */
          int ok;
          a68_val z = mp_of_string((const uint8_t*) tok, n, q->len, &ok);
          if (!ok) die_mode_str("cannot read ", t, " from \"", tok, n, "\"");
          store_ref(r, z);
          free(tok);
          return;
        }
        store_ref(r, real_of_text(tok, n));
        free(tok);
        return;
      }
      case M_BOOL: {
        size_t n; char* tok = read_token(fid, &n);
        store_ref(r, mk_bool((n == 1 && tok[0] == 'T') || (n == 4 && memcmp(tok, "TRUE", 4) == 0)));
        free(tok);
        return;
      }
      case M_CHAR: {
        int c = read_char(fid);
        if (c >= 0) store_ref(r, mk_char((uint32_t) c)); else logical_end(fid);
        return;
      }
      case M_ROW:
        if (mode_is_flex_string(t)) {
          size_t n; char* line = read_line_str(fid, &n);
          store_ref(r, of_string(line, n));
          free(line);
          return;
        }
        if (q->dims == 1) {
          a68_val row = ref_load(r);
          if (row.tag == T_UNDEF) die("attempt to use an uninitialised row");
          if (row.tag != T_ROW) die("internal: row expected");
          int64_t n = row_count((a68_rowd*) row.v.p);
          uint32_t em = mode_ref(q->sub);
          for (int64_t i = 0; i < n; i++) read_into(fid, em, ref_elem(r, (uint32_t) i));
          return;
        }
        break;
      case M_COMPL: {
        a68_val cur = ref_load(r);
        if (cur.tag != T_STRUCT) store_ref(r, undef_pair());
        uint32_t rm = mode_ref(mode_simple(M_REAL, q->len));
        read_into(fid, rm, ref_field(r, 0));
        read_into(fid, rm, ref_field(r, 1));
        return;
      }
      case M_UNION:
        /* a68g reads a value of the mode the united value currently has */
        read_union(fid, tsub, r, read_into_cb, NULL);
        return;
      default: break;
    }
    die_mode("cannot read a value of mode ", tsub, "");
  }
  if (mode_is_file_proc(mr)) {
    if (r.tag == T_BUILTIN) {
      const char* n = strtab[r.aux];
      if (strcmp(n, "newline") == 0 || strcmp(n, "newpage") == 0) skip_line(fid);
      else if (strcmp(n, "space") == 0) skip_char(fid);
    }
    return;
  }
  die_mode("cannot read into a value of mode ", m, "");
}

/* ---------------------------------------------------------------- formats */

/* An arena for the pictures of the formatted calls in progress: everything allocated
   for a call is released when it ends, or when an event unwinds through it. */
static void** arena = NULL;
static size_t arena_cap = 0;

static void* arena_alloc(size_t n) {
  void* p = xm(n);
  if (arena_n == arena_cap) {
    arena_cap = arena_cap ? arena_cap * 2 : 256;
    arena = (void**) realloc(arena, arena_cap * sizeof(void*));
    if (!arena) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  }
  arena[arena_n++] = p;
  return p;
}

static void arena_free_to(size_t mark) {
  while (arena_n > mark) free(arena[--arena_n]);
}

/* `Interp.Frame`: a flattened format picture */
enum { FR_Z, FR_D, FR_PLUS, FR_MINUS, FR_POINT, FR_E, FR_A, FR_INS, FR_RADIX };
typedef struct { uint8_t k; const char* s; size_t n; int64_t radix; } frame_t;

/* `Interp.Pic` */
enum { P_INS, P_PATTERN, P_GENERAL, P_BOOL, P_CHOICE, P_INCLUDE, P_COL, P_CPAT, P_HGEN };
typedef struct {
  uint8_t k;
  const char* s; size_t n;              /* INS: the text; CPAT: the flags */
  frame_t* fr; size_t nfr;              /* PATTERN */
  int64_t* args; size_t nargs;          /* GENERAL, HGEN */
  int has_texts; const char* flip; size_t nflip; const char* flop; size_t nflop;   /* BOOL */
  const char** alts; size_t* altn; size_t nalts;   /* CHOICE */
  a68_frame* env; uint32_t skel;        /* INCLUDE */
  int64_t col;                          /* COL */
  int has_w, has_a; int64_t w, a;       /* CPAT */
} pic_t;

typedef struct { pic_t* pics; size_t npics; size_t cursor; int embedded; } fmt_frame_t;
typedef struct { fmt_frame_t* fr; size_t n, cap; } fmt_state_t;   /* innermost last */

static void st_push(fmt_state_t* st, fmt_frame_t f) {
  if (st->n == st->cap) {
    st->cap = st->cap ? st->cap * 2 : 4;
    fmt_frame_t* nf = (fmt_frame_t*) arena_alloc(st->cap * sizeof(fmt_frame_t));
    if (st->n) memcpy(nf, st->fr, st->n * sizeof(fmt_frame_t));
    st->fr = nf;
  }
  st->fr[st->n++] = f;
}

/* `Interp.FmtBuild` */
typedef struct {
  pic_t* pics; size_t n, cap;
  frame_t* pend; size_t npend, pcap;
  frame_t* pins; size_t npins, picap;
} build_t;

static void vec_grow(void** p, size_t* cap, size_t n, size_t esz) {
  if (n < *cap) return;
  size_t nc = *cap ? *cap * 2 : 8;
  void* np = arena_alloc(nc * esz);
  if (*cap) memcpy(np, *p, *cap * esz);
  *p = np; *cap = nc;
}

static pic_t* b_add_pic(build_t* b) {
  vec_grow((void**) &b->pics, &b->cap, b->n, sizeof(pic_t));
  pic_t* p = &b->pics[b->n++];
  memset(p, 0, sizeof *p);
  return p;
}

static void b_ins(build_t* b, const char* s, size_t n) { pic_t* p = b_add_pic(b); p->k = P_INS; p->s = s; p->n = n; }

static void b_col(build_t* b, int64_t k) { pic_t* p = b_add_pic(b); p->k = P_COL; p->col = k; }

/* `FmtBuild.flush`, which every caller follows by clearing the pending frames */
static void b_flush(build_t* b) {
  if (b->npend) {
    frame_t* fr = (frame_t*) arena_alloc(b->npend * sizeof(frame_t));
    memcpy(fr, b->pend, b->npend * sizeof(frame_t));
    size_t nfr = b->npend;
    pic_t* p = b_add_pic(b); p->k = P_PATTERN; p->fr = fr; p->nfr = nfr;
  }
  for (size_t i = 0; i < b->npins; i++) if (b->pins[i].k == FR_INS) b_ins(b, b->pins[i].s, b->pins[i].n);
  b->npend = 0; b->npins = 0;
}

static void b_add_frame(build_t* b, frame_t fr) {
  for (size_t i = 0; i < b->npins; i++) {
    vec_grow((void**) &b->pend, &b->pcap, b->npend, sizeof(frame_t));
    b->pend[b->npend++] = b->pins[i];
  }
  b->npins = 0;
  vec_grow((void**) &b->pend, &b->pcap, b->npend, sizeof(frame_t));
  b->pend[b->npend++] = fr;
}

static void b_add_ins(build_t* b, const char* s, size_t n) {
  if (b->npend == 0) b_ins(b, s, n);
  else {
    vec_grow((void**) &b->pins, &b->picap, b->npins, sizeof(frame_t));
    frame_t f; memset(&f, 0, sizeof f); f.k = FR_INS; f.s = s; f.n = n;
    b->pins[b->npins++] = f;
  }
}

/* `FmtBuild.addPic`: flush, then the picture */
static pic_t* b_pic(build_t* b, uint8_t k) {
  b_flush(b);
  pic_t* p = b_add_pic(b);
  p->k = k;
  return p;
}

static frame_t frame_of(uint8_t k) { frame_t f; memset(&f, 0, sizeof f); f.k = k; return f; }

/* `Interp.evalFmtExpr` for a compiled program: a hole calls into the compiled code */
static a68_val eval_core(a68_frame* env, const a68_core* c) {
  if (!c->is_hole) return mk_int(c->lit);
  env_set(env);
  a68_dispatch_hole(c->idx);
  env_restore();
  if (a68_jump_flag) io_raise(IO_JUMP);
  return pop();
}

static int64_t eval_int(a68_frame* env, uint32_t core) { return expect_int(eval_core(env, &cores[core])); }

static int64_t nat_of(int64_t k) { return k < 0 ? 0 : k; }

/* the environment and items of a format value (`Interp.fmtOf`) */
static void fmt_of(a68_val v, a68_frame** env, uint32_t* skel) {
  if (v.tag != T_FMT) die("format expected");
  *env = (a68_frame*) v.v.p;
  *skel = v.aux;
}

static void walk_format(a68_frame* env, const uint32_t* items, size_t nitems, build_t* b);

static void walk_one(a68_frame* env, uint32_t fi, build_t* b) {
  const a68_fmt* f = &fmts[fi];
  switch (f->k) {
    case F_LIT: b_add_ins(b, strtab[f->str], strlen_tab[f->str]); break;
    case F_NL: b_flush(b); b_ins(b, "\n", 1); break;
    case F_NP: b_flush(b); b_ins(b, "\x0c", 1); break;
    case F_SP: case F_BS: b_add_ins(b, " ", 1); break;
    case F_DIG: b_add_frame(b, frame_of(f->flag ? FR_Z : FR_D)); break;
    case F_SIGN: b_add_frame(b, frame_of(f->flag ? FR_PLUS : FR_MINUS)); break;
    case F_POINT: b_add_frame(b, frame_of(FR_POINT)); break;
    case F_EXP: b_add_frame(b, frame_of(FR_E)); break;
    case F_CHAR: b_add_frame(b, frame_of(FR_A)); break;
    case F_REP: {
      const a68_fmt* inner = &fmts[f->item];
      int64_t k = f->dyn ? nat_of(eval_int(env, f->dyn - 1)) : f->rep;
      if (inner->k == F_COL) { b_flush(b); b_col(b, k); }
      else if (inner->k == F_RADIX) { frame_t fr = frame_of(FR_RADIX); fr.radix = k; b_add_frame(b, fr); }
      else for (int64_t i = 0; i < k; i++) walk_one(env, f->item, b);
      break;
    }
    case F_RADIX: die("radix frame without a radix");
    case F_COL: b_flush(b); b_col(b, 1); break;
    case F_GROUP: {
      if (f->n > 0 && fmts[f->list[0]].k == F_HMARK) {
        pic_t* p;
        int64_t* args = NULL; size_t nargs = 0;
        if (f->n == 2 && fmts[f->list[1]].k == F_GEN) {
          const a68_fmt* g = &fmts[f->list[1]];
          nargs = g->n;
          args = (int64_t*) arena_alloc((nargs ? nargs : 1) * sizeof(int64_t));
          for (size_t i = 0; i < nargs; i++) args[i] = eval_int(env, g->list[i]);
        }
        p = b_pic(b, P_HGEN); p->args = args; p->nargs = nargs;
        break;
      }
      if (f->n > 0 && fmts[f->list[0]].k == F_CPAT) {
        int has_w = 0, has_a = 0; int64_t w = 0, a = 0;
        for (uint32_t i = 1; i < f->n; i++) {
          const a68_fmt* it = &fmts[f->list[i]];
          if (it->k != F_REP) continue;
          int64_t k = it->dyn ? nat_of(eval_int(env, it->dyn - 1)) : it->rep;
          if (fmts[it->item].k == F_CWIDTH) { has_w = 1; w = k; } else { has_a = 1; a = k; }
        }
        pic_t* p = b_pic(b, P_CPAT);
        p->s = strtab[fmts[f->list[0]].str]; p->n = strlen_tab[fmts[f->list[0]].str];
        p->has_w = has_w; p->w = w; p->has_a = has_a; p->a = a;
        break;
      }
      /* a collection is a picture boundary: frames inside it never merge with frames outside */
      b_flush(b);
      walk_format(env, f->list, f->n, b);
      b_flush(b);
      break;
    }
    case F_HMARK: case F_CPAT: case F_CWIDTH: case F_CAFTER: break;
    case F_GEN: {
      size_t nargs = f->n;
      int64_t* args = (int64_t*) arena_alloc((nargs ? nargs : 1) * sizeof(int64_t));
      for (size_t i = 0; i < nargs; i++) args[i] = eval_int(env, f->list[i]);
      pic_t* p = b_pic(b, P_GENERAL); p->args = args; p->nargs = nargs;
      break;
    }
    case F_BOOL: {
      pic_t* p = b_pic(b, P_BOOL);
      p->has_texts = f->flag;
      if (f->flag) { p->flip = strtab[f->str]; p->nflip = strlen_tab[f->str]; p->flop = strtab[f->str2]; p->nflop = strlen_tab[f->str2]; }
      break;
    }
    case F_CHOICE: {
      pic_t* p = b_pic(b, P_CHOICE);
      p->nalts = f->n;
      p->alts = (const char**) arena_alloc((f->n ? f->n : 1) * sizeof(char*));
      p->altn = (size_t*) arena_alloc((f->n ? f->n : 1) * sizeof(size_t));
      for (uint32_t i = 0; i < f->n; i++) { p->alts[i] = strtab[f->list[i]]; p->altn[i] = strlen_tab[f->list[i]]; }
      break;
    }
    case F_STRINGS: case F_SEP: b_flush(b); break;
    case F_INCL: {
      a68_val v = eval_core(env, &cores[f->dyn - 1]);
      root(v);   /* its frame stays reachable while the pictures refer to it */
      pic_t* p = b_pic(b, P_INCLUDE);
      fmt_of(v, &p->env, &p->skel);
      break;
    }
    default: die("internal: bad format item");
  }
}

static void walk_format(a68_frame* env, const uint32_t* items, size_t nitems, build_t* b) {
  for (size_t i = 0; i < nitems; i++) walk_one(env, items[i], b);
}

/* `Interp.expandFormat`: the flat picture list of a format text */
static fmt_frame_t expand_format(a68_frame* env, uint32_t skel, int embedded) {
  build_t b; memset(&b, 0, sizeof b);
  const a68_fmtlist* l = &fmtlists[skel];
  walk_format(env, l->items, l->n, &b);
  b_flush(&b);
  fmt_frame_t f = { b.pics, b.n, 0, embedded };
  return f;
}

/* `Interp.nextPattern`: the next pattern, writing insertions passed on the way.  Embedded
   formats are entered as new frames and popped when exhausted; the outermost format
   restarts at its end when a pattern is wanted. */
static pic_t* next_pattern(uint32_t fid, fmt_state_t* st, int want) {
  int restarts = 0;
  for (;;) {
    if (st->n == 0) return NULL;
    fmt_frame_t* fr = &st->fr[st->n - 1];
    size_t i = fr->cursor;
    int pushed = 0;
    while (i < fr->npics) {
      pic_t* p = &fr->pics[i];
      if (p->k == P_INS) {
        file_out(fid, p->s, p->n);
        /* a new line or page purges a68g's buffer (see `io_nul_cut`) */
        for (size_t k = 0; k < p->n; k++) if (p->s[k] == '\n' || p->s[k] == '\x0c') io_nul_cut = 0;
        i++;
      } else if (p->k == P_COL) {
        int64_t pos = io_col;
        if (p->col > pos + 1) {
          int64_t k = p->col - pos - 1;
          char* sp_ = (char*) xm((size_t) k);
          memset(sp_, ' ', (size_t) k);
          file_out(fid, sp_, (size_t) k);
          free(sp_);
        }
        i++;
      } else if (p->k == P_INCLUDE) {
        fr->cursor = i + 1;
        fmt_frame_t nf = expand_format(p->env, p->skel, 1);
        st_push(st, nf);
        pushed = 1;
        break;
      } else {
        fr->cursor = i + 1;
        return p;
      }
    }
    if (pushed) continue;
    if (fr->embedded) { st->n--; continue; }
    if (want) {
      if (restarts > 0 || fr->npics == 0) die("format exhausted");
      fr->cursor = 0;
      st->n = 1;
      restarts++;
      continue;
    }
    fr->cursor = i;
    return NULL;
  }
}

/* ---------------------------------------------------------------- writing with patterns */

static size_t count_zd(const frame_t* fr, size_t n) {
  size_t k = 0;
  for (size_t i = 0; i < n; i++) if (fr[i].k == FR_Z || fr[i].k == FR_D) k++;
  return k;
}

static int has_frame(const frame_t* fr, size_t n, uint8_t k) {
  for (size_t i = 0; i < n; i++) if (fr[i].k == k) return 1;
  return 0;
}

/* a68g `shift_sign`: move a leading sign right through leading `z` frames over zeros
   (`Interp.shiftSign`); `buf` is edited in place, `*len` updated */
static void shift_sign(const frame_t* fr, size_t nfr, char* buf, size_t* len) {
  /* pre ++ q: the zeros the sign has passed over are moved in front of it */
  size_t pre = 0;
  for (size_t i = 0; i < nfr; i++) {
    if (fr[i].k == FR_Z) {
      if (*len - pre >= 2) {
        char s = buf[pre], z0 = buf[pre + 1];
        if ((s == '+' || s == '-') && z0 == '0') { buf[pre] = '0'; buf[pre + 1] = s; pre++; }
      }
    } else if (fr[i].k == FR_D) return;
  }
}

/* a68g `write_mould` (`Interp.writeMould`): `normal_mood` starts without zero suppression */
static void write_mould(uint32_t fid, const frame_t* fr, size_t nfr, const char* buf, size_t len, int normal_mood) {
  size_t q = 0;
  int digit_blank = !normal_mood;
  int ins_blank = 0;
  for (size_t i = 0; i < nfr; i++) {
    switch (fr[i].k) {
      case FR_INS:
        if (ins_blank) { for (size_t k = 0; k < fr[i].n; k++) file_out(fid, " ", 1); }
        else file_out(fid, fr[i].s, fr[i].n);
        break;
      case FR_Z:
        if (q < len && (buf[q] == '+' || buf[q] == '-' || buf[q] == ' ')) { file_out_byte(fid, (uint8_t) buf[q]); q++; }
        if (q < len) {
          if (buf[q] == '0') {
            if (digit_blank) { file_out(fid, " ", 1); ins_blank = 1; q++; }
            else { file_out(fid, "0", 1); q++; }
          } else { file_out(fid, &buf[q], 1); q++; digit_blank = 0; ins_blank = 0; }
        }
        break;
      case FR_D:
        if (q < len && (buf[q] == '+' || buf[q] == '-' || buf[q] == ' ')) { file_out_byte(fid, (uint8_t) buf[q]); q++; }
        if (q < len) { file_out(fid, &buf[q], 1); q++; }
        digit_blank = 0; ins_blank = 0;
        break;
      default: break;
    }
  }
}

/* `Interp.writeIntegralPattern`: `digits` is the magnitude in decimal */
static void write_integral_pattern(uint32_t fid, const frame_t* fr, size_t nfr, int neg, const char* digits, size_t nd) {
  int has_sign = has_frame(fr, nfr, FR_PLUS) || has_frame(fr, nfr, FR_MINUS);
  size_t width = count_zd(fr, nfr);
  if (nd > width) die("error transputting INT value");
  if (neg && !has_sign) die("error transputting INT value: negative value without sign frame");
  char* buf = (char*) xm(width + 2);
  size_t len = 0;
  if (has_sign) buf[len++] = has_frame(fr, nfr, FR_PLUS) ? (neg ? '-' : '+') : (neg ? '-' : ' ');
  for (size_t i = nd; i < width; i++) buf[len++] = '0';
  memcpy(buf + len, digits, nd); len += nd;
  if (has_sign) {
    /* shift the sign through the sign mould only (the z frames before the sign frame) */
    size_t sm = 0;
    while (sm < nfr && fr[sm].k != FR_PLUS && fr[sm].k != FR_MINUS) sm++;
    shift_sign(fr, sm, buf, &len);
  }
  write_mould(fid, fr, nfr, buf, len, 0);
  free(buf);
}

/* `Interp.writeRealPattern`: `x` is the magnitude as an exact decimal */
static void write_real_pattern(uint32_t fid, const frame_t* fr, size_t nfr, int neg, a68_dec x) {
  /* dissect: sign mould, stag mould, point, frac mould, exponent */
  size_t ie = nfr;
  for (size_t i = 0; i < nfr; i++) if (fr[i].k == FR_E) { ie = i; break; }
  const frame_t* before = fr; size_t nbefore = ie;
  const frame_t* after = ie < nfr ? fr + ie + 1 : NULL; size_t nafter = ie < nfr ? nfr - ie - 1 : 0;
  size_t ip = nbefore;
  for (size_t i = 0; i < nbefore; i++) if (before[i].k == FR_POINT) { ip = i; break; }
  const frame_t* mant = before; size_t nmant = ip;
  int point = ip < nbefore;
  const frame_t* frac = point ? before + ip + 1 : NULL; size_t nfrac = point ? nbefore - ip - 1 : 0;
  int has_sign = has_frame(mant, nmant, FR_PLUS) || has_frame(mant, nmant, FR_MINUS);
  int64_t stag = (int64_t) count_zd(mant, nmant);
  int64_t fracd = (int64_t) count_zd(frac, nfrac);
  int64_t mant_length = point ? 1 + stag + fracd : stag;
  a68_dec z = x;
  int z_fresh = 0;
  int64_t exp_value = 0;
  if (nafter > 0) {
    a68_dec z2; int64_t q;
    a68_fmt_standardize(x, stag, fracd, 0, &z2, &q);
    z = z2; z_fresh = 1; exp_value = q;
  }
  char* str = a68_fmt_sub_fixed(z, mant_length, fracd);
  if (z_fresh) a68_dec_free(&z);
  if (a68_fmt_has_error(str)) { free(str); die("error transputting REAL value"); }
  char* dot = strchr(str, '.');
  size_t nstag = dot ? (size_t) (dot - str) : strlen(str);
  const char* fracs = dot ? dot + 1 : "";
  size_t nfracs = strlen(fracs);
  if (neg && !has_sign) { free(str); die("error transputting REAL value: negative value without sign frame"); }
  size_t cap = (size_t) (stag > 0 ? stag : 0) + nstag + 4;
  char* buf = (char*) xm(cap);
  size_t len = 0;
  if (has_sign) buf[len++] = has_frame(mant, nmant, FR_PLUS) ? (neg ? '-' : '+') : (neg ? '-' : ' ');
  for (int64_t i = (int64_t) nstag; i < stag; i++) buf[len++] = '0';
  memcpy(buf + len, str, nstag); len += nstag;
  if (has_sign) shift_sign(mant, nmant, buf, &len);
  write_mould(fid, mant, nmant, buf, len, 0);
  if (point) file_out(fid, ".", 1);
  if (nfrac > 0) write_mould(fid, frac, nfrac, fracs, nfracs, 1);
  if (nafter > 0) {
    file_out(fid, "e", 1);
    char d[32];
    int64_t a = exp_value < 0 ? -exp_value : exp_value;
    snprintf(d, sizeof d, "%lld", (long long) a);
    write_integral_pattern(fid, after, nafter, exp_value < 0, d, strlen(d));
  }
  free(buf); free(str);
}

static void write_string_pattern(uint32_t fid, const frame_t* fr, size_t nfr, const uint8_t* s, size_t n) {
  size_t i = 0;
  for (size_t k = 0; k < nfr; k++) {
    if (fr[k].k == FR_A) {
      if (i < n) { file_out_byte(fid, s[i]); i++; }
      else die("error transputting STRING value");
    } else if (fr[k].k == FR_INS) file_out(fid, fr[k].s, fr[k].n);
  }
  if (i < n) die("error transputting STRING value");
}

/* `Interp.toDec`: a value as the exact decimal patterns use; 1 when negative */
static int to_dec(uint32_t m, a68_val v, a68_dec* out) {
  const a68_mode* p = mode_at(mode_resolve(m));
  if (p->k == M_INT && (v.tag == T_INT || v.tag == T_BIGINT)) {
    a68_big* b = big_of_val(v);
    int neg = big_sign(b) < 0;
    a68_big* ab = big_abs(b);
    *out = a68_dec_of_big(ab);
    big_free(b); big_free(ab);
    return neg;
  }
  if (p->k == M_REAL && v.tag == T_REAL) { check_real(v.v.r); return a68_real_to_dec(v.v.r, out); }
  if (p->k == M_REAL && v.tag == T_MP) { mp_check_finite(v); return mp_to_dec(v, p->len, out); }
  if (v.tag == T_UNDEF) die("attempt to use an uninitialised value");
  die("cannot transput this value with a numeric pattern");
}

/* a68g `convert_radix` (`Interp.convertRadix`): the digits of `v` in base `radix`, most
   significant first, padded to `width` digits (as many as it takes when `width` is 0);
   NULL if `v` does not fit */
static char* convert_radix(const a68_big* v, int radix, size_t width) {
  const char* dig = "0123456789abcdef";
  sbuf b = {0};   /* least significant first, reversed at the end */
  a68_big* z = big_abs(v);
  a68_big* r = big_from_i64(radix);
  if (width == 0) {
    for (;;) {
      a68_big* rem;
      a68_big* q = big_divmod(z, r, &rem);
      sb_putc(&b, dig[big_to_i64(rem)]);
      big_free(rem); big_free(z); z = q;
      if (big_is_zero(z)) break;
    }
  } else {
    for (size_t i = 0; i < width; i++) {
      a68_big* rem;
      a68_big* q = big_divmod(z, r, &rem);
      sb_putc(&b, dig[big_to_i64(rem)]);
      big_free(rem); big_free(z); z = q;
    }
  }
  int fits = big_is_zero(z);
  big_free(z); big_free(r);
  if (!fits) { free(b.p); return NULL; }
  char* s = sb_take(&b);
  for (size_t i = 0, j = b.n; i + 1 < j; i++, j--) { char t = s[i]; s[i] = s[j - 1]; s[j - 1] = t; }
  return s;
}

/* the exponent C `strtol` reads after the `e` of a `float` string (0 when there is none) */
static int64_t exponent_of(const char* s) {
  const char* e = strchr(s, 'e');
  if (!e) return 0;
  e++;
  while (*e == ' ') e++;
  int neg = 0;
  if (*e == '-') { neg = 1; e++; } else if (*e == '+') e++;
  int64_t n = 0;
  while (*e >= '0' && *e <= '9') { n = n * 10 + (*e - '0'); e++; }
  return neg ? -n : n;
}

/* the string an a68g C-style pattern `%[-][+][w][.a]letter` makes of a value, with the width
   it is aligned to (`Interp.cPatternText`) */
static char* c_pattern_text(const char* flags, size_t nflags, int has_w, int64_t w, int has_a, int64_t a,
                            uint32_t mr, a68_val v, int64_t* width_out) {
  char letter = nflags ? flags[nflags - 1] : 0;
  int plus = memchr(flags, '+', nflags) != NULL;
  const a68_mode* p = mode_at(mr);
  #define SIGNED(width) (plus ? (width) : -(width))
  if ((letter == 'd' || letter == 'i') && p->k == M_INT && (v.tag == T_INT || v.tag == T_BIGINT)) {
    int64_t width = has_w ? w : 0;
    a68_big* b = big_of_val(v);
    char* s = a68_fmt_whole_int(b, SIGNED(width));
    big_free(b);
    *width_out = width;
    return s;
  }
  if ((letter == 'f' || letter == 'e' || letter == 'g') && (p->k == M_INT || p->k == M_REAL)) {
    int64_t longness = p->len;
    int64_t rw = real_width_of(longness), ew = exp_width_of(longness);
    int64_t digits = has_w ? w : 0;
    int64_t after = has_a ? a : rw - 1;
    int64_t width = 0; char* res = NULL;
    int use_fixed = letter == 'f';
    if (letter != 'f') {
      int64_t expo = ew + 1;
      width = (digits == 0 && after > 0) ? after + expo + 4 : digits > 0 ? digits : rw + ew + 4;
      if (v.tag == T_INT || v.tag == T_BIGINT) { a68_big* b = big_of_val(v); res = a68_fmt_float_int(b, SIGNED(width), after, expo, 1); big_free(b); }
      else if (v.tag == T_REAL) { check_real(v.v.r); res = a68_fmt_float_real(v.v.r, SIGNED(width), after, expo, 1); }
      else die("internal: C-style pattern");
      if (letter == 'g') { int64_t ev = exponent_of(res); use_fixed = ev > -4 && ev <= after; }
    }
    if (use_fixed) {
      free(res);
      width = digits == 0 ? 0 : digits + after + 2;
      if (p->k == M_INT && (v.tag == T_INT || v.tag == T_BIGINT)) { a68_big* b = big_of_val(v); res = a68_fmt_fixed_int(b, SIGNED(width), after, longness > 0); big_free(b); }
      else if (v.tag == T_REAL) { check_real(v.v.r); res = a68_fmt_fixed_real(v.v.r, SIGNED(width), after); }
      else die("internal: C-style pattern");
    }
    *width_out = width;
    return res;
  }
  if ((letter == 'b' || letter == 'o' || letter == 'x') && p->k == M_BITS && (v.tag == T_BITS || v.tag == T_BIGBITS)) {
    int radix = letter == 'b' ? 2 : letter == 'o' ? 8 : 16, nibble = letter == 'b' ? 1 : letter == 'o' ? 3 : 4;
    int64_t dflt = (bits_width_of(p->len) + nibble - 1) / nibble;
    int64_t width = has_w ? (w > 0 ? w : dflt) : dflt;
    a68_big* b = big_of_val(v);
    char* s = convert_radix(b, radix, (size_t) width);
    big_free(b);
    if (!s) die_mode("error transputting ", mr, " value");
    *width_out = width;
    return s;
  }
  if (letter == 's' && p->k == M_CHAR && v.tag == T_CHAR) {
    *width_out = has_w ? w : 1;
    char* s = (char*) xm(2); s[0] = (char) v.v.u; s[1] = 0;
    return s;
  }
  if (letter == 's' && mode_is_string(mr)) {
    int64_t n; uint8_t* s = str_of(v, &n);
    *width_out = has_w ? w : n;
    return (char*) s;
  }
  #undef SIGNED
  die_mode("cannot transput ", mr, " value with a C-style pattern");
}

/* `Interp.writeCPattern`: blanks the conversion put in front are dropped, and the rest is
   aligned right, or left when the pattern says `-` */
static void write_c_pattern(uint32_t fid, const pic_t* p, uint32_t mr, a68_val v) {
  int64_t width;
  char* str = c_pattern_text(p->s, p->n, p->has_w, p->w, p->has_a, p->a, mr, v, &width);
  char letter = p->n ? p->s[p->n - 1] : 0;
  if (letter != 's' && a68_fmt_has_error(str)) { free(str); die_mode("error transputting ", mr, " value"); }
  if (width == 0) { file_out_take(fid, str); return; }
  const char* s = str;
  while (*s == ' ') s++;
  int64_t len = (int64_t) strlen(s);
  int64_t blanks = width - len;
  if (blanks < 0) { free(str); die_mode("error transputting ", mr, " value"); }
  int left = memchr(p->s, '-', p->n) != NULL;
  if (left) file_out(fid, s, (size_t) len);
  for (int64_t i = 0; i < blanks; i++) file_out(fid, " ", 1);
  if (!left) file_out(fid, s, (size_t) len);
  free(str);
}

/* the `real` arguments of an `h` pattern: width, after, exponent and exponent multiple
   (a68g `write_number_generic`, `Interp.hArguments`) */
static void h_arguments(int64_t longness, const int64_t* args, size_t n, int64_t* w, int64_t* a, int64_t* e, int64_t* m) {
  int64_t rw = real_width_of(longness), ew = exp_width_of(longness), de = ew + 1;
  switch (n) {
    case 0: *w = rw + ew + 4; *a = rw - 1; *e = de; *m = 3; break;
    case 1: *w = args[0] + de + 4; *a = args[0]; *e = de; *m = 3; break;
    case 2: *w = args[0] + de + 4; *a = args[0]; *e = de; *m = args[1]; break;
    case 3: *w = args[0]; *a = args[1]; *e = de; *m = args[2]; break;
    case 4: *w = args[0]; *a = args[1]; *e = args[2]; *m = args[3]; break;
    default: die("INT arguments required for a general pattern");
  }
}

static int64_t find_radix(const frame_t* fr, size_t n, int* found) {
  for (size_t i = 0; i < n; i++) if (fr[i].k == FR_RADIX) { *found = 1; return fr[i].radix; }
  *found = 0;
  return 0;
}

static void write_scalar_formatted(uint32_t fid, fmt_state_t* st, uint32_t m, a68_val v);

/* `Interp.writeFormatted`: straighten a value into scalars, each written with a pattern */
static void write_formatted(uint32_t fid, fmt_state_t* st, uint32_t m, a68_val v) {
  uint32_t mr = mode_resolve(m);
  const a68_mode* p = mode_at(mr);
  if (v.tag == T_UNION) { write_formatted(fid, st, v.aux, ((a68_slots*) v.v.p)->s[0]); return; }
  if (mode_is_string(mr) && v.tag == T_ROW) { write_scalar_formatted(fid, st, m, v); return; }
  a68_val re, im;
  if (p->k == M_COMPL && compl_parts(v, &re, &im)) {
    /* a68g writes a COMPL as two REAL values, each with a pattern of its own */
    uint32_t rm = mode_simple(M_REAL, p->len);
    write_formatted(fid, st, rm, re);
    write_formatted(fid, st, rm, im);
    return;
  }
  if (p->k == M_ROW && v.tag == T_ROW) {
    a68_rowd* d = (a68_rowd*) v.v.p;
    int64_t n = row_count(d);
    for (int64_t i = 0; i < n; i++) {
      a68_val e = rowd_get(d, row_store_index(d, i));
      if (e.tag == T_UNDEF) die_mode("attempt to use an uninitialised ", p->sub, " value");
      write_formatted(fid, st, p->sub, e);
    }
    return;
  }
  if (p->k == M_STRUCT && v.tag == T_STRUCT) {
    a68_slots* s = (a68_slots*) v.v.p;
    uint32_t n = p->n < s->h.n ? p->n : s->h.n;
    for (uint32_t i = 0; i < n; i++) write_formatted(fid, st, p->modes[i], s->s[i]);
    return;
  }
  if (v.tag == T_UNDEF) die_mode("attempt to use an uninitialised ", m, " value");
  write_scalar_formatted(fid, st, m, v);
}

__attribute__((noreturn)) static void cannot_general(uint32_t m, int with_args) {
  die_mode("cannot transput ", m, with_args ? " value with a general pattern with arguments" : " value with a general pattern");
}

/* `Interp.writeScalarFormatted` */
static void write_scalar_formatted(uint32_t fid, fmt_state_t* st, uint32_t m, a68_val v) {
  uint32_t mr = mode_resolve(m);
  const a68_mode* p = mode_at(mr);
  pic_t* pat = next_pattern(fid, st, 1);
  if (!pat) die("format exhausted");
  switch (pat->k) {
    case P_INCLUDE: die("internal: include as pattern");
    case P_GENERAL: {
      const int64_t* a = pat->args; size_t n = pat->nargs;
      int is_int = p->k == M_INT && (v.tag == T_INT || v.tag == T_BIGINT);
      a68_val re, im;
      if (is_int) {
        a68_big* b = big_of_val(v);
        char* s;
        if (n == 0) s = a68_fmt_print_int(b, p->len, a68_ll_digits);
        else if (n == 1) s = a68_fmt_whole_int(b, a[0]);
        else if (n == 2) {
          if (p->len <= 0) s = a68_fmt_fixed_int(b, a[0], a[1], 0);
          else { a68_val z = mp_of_int(b, p->len); s = mp_fmt_fixed(z, p->len, a[0], a[1]); }
        } else if (n == 3) {
          if (p->len <= 0) s = a68_fmt_float_int(b, a[0], a[1], a[2], 1);
          else { a68_val z = mp_of_int(b, p->len); s = mp_fmt_float(z, p->len, a[0], a[1], a[2], 1); }
        } else { big_free(b); cannot_general(m, 1); }
        big_free(b);
        file_out_take(fid, s);
        return;
      }
      if (p->k == M_REAL && v.tag == T_MP) {
        if (n == 0) file_out_take(fid, mp_float_std(v, p->len));
        else if (n == 1) file_out_take(fid, mp_fmt_whole(v, p->len, a[0]));
        else if (n == 2) file_out_take(fid, mp_fmt_fixed(v, p->len, a[0], a[1]));
        else if (n == 3) file_out_take(fid, mp_fmt_float(v, p->len, a[0], a[1], a[2], 1));
        else cannot_general(m, 1);
        return;
      }
      if (p->k == M_COMPL && compl_parts(v, &re, &im) && re.tag == T_MP && im.tag == T_MP) {
        if (n == 0) { file_out_take(fid, mp_float_std(re, p->len)); file_out_take(fid, mp_float_std(im, p->len)); return; }
        cannot_general(m, 1);
      }
      if (p->k == M_REAL && v.tag == T_REAL) {
        double x = check_real(v.v.r);
        if (n == 0) file_out_take(fid, a68_fmt_print_real(x, p->len, a68_ll_digits));
        else if (n == 1) file_out_take(fid, a68_fmt_whole_real(x, a[0]));
        else if (n == 2) file_out_take(fid, a68_fmt_fixed_real(x, a[0], a[1]));
        else if (n == 3) file_out_take(fid, a68_fmt_float_real(x, a[0], a[1], a[2], 1));
        else cannot_general(m, 1);
        return;
      }
      if (p->k == M_COMPL && compl_parts(v, &re, &im) && re.tag == T_REAL && im.tag == T_REAL) {
        double x = re.v.r, y = im.v.r;
        if (n == 0) { file_out_take(fid, a68_fmt_print_real(x, p->len, a68_ll_digits)); file_out_take(fid, a68_fmt_print_real(y, p->len, a68_ll_digits)); }
        else if (n == 1) { file_out_take(fid, a68_fmt_whole_real(x, a[0])); file_out_take(fid, a68_fmt_whole_real(y, a[0])); }
        else if (n == 2) { file_out_take(fid, a68_fmt_fixed_real(x, a[0], a[1])); file_out_take(fid, a68_fmt_fixed_real(y, a[0], a[1])); }
        else if (n == 3) { file_out_take(fid, a68_fmt_float_real(x, a[0], a[1], a[2], 1)); file_out_take(fid, a68_fmt_float_real(y, a[0], a[1], a[2], 1)); }
        else cannot_general(m, 1);
        return;
      }
      if (n != 0) cannot_general(m, 1);
      if (p->k == M_BOOL && v.tag == T_BOOL) { file_out(fid, v.v.u ? "T" : "F", 1); return; }
      if (p->k == M_CHAR && v.tag == T_CHAR) { file_out_byte(fid, (uint8_t) v.v.u); return; }
      if (p->k == M_BITS && (v.tag == T_BITS || v.tag == T_BIGBITS)) { file_out_take(fid, fmt_bits_of(v, p->len)); return; }
      if (mode_is_string(mr) && v.tag == T_ROW) { int64_t sn; uint8_t* s = str_of(v, &sn); file_out(fid, (const char*) s, (size_t) sn); free(s); return; }
      if (mode_is_file_proc(mr)) { print_value(fid, mr, v); return; }
      cannot_general(m, 0);
    }
    case P_PATTERN: {
      const frame_t* fr = pat->fr; size_t nfr = pat->nfr;
      int has_radix;
      int64_t rdx = find_radix(fr, nfr, &has_radix);
      if (has_radix) {
        if (p->k == M_BITS && (v.tag == T_BITS || v.tag == T_BIGBITS)) {
          if (rdx < 2 || rdx > 16) dief("invalid radix %lld", rdx, 0, 0);
          a68_big* b = big_of_val(v);
          char* s = convert_radix(b, (int) rdx, count_zd(fr, nfr));
          big_free(b);
          if (!s) die_mode("error transputting ", m, " value");
          write_mould(fid, fr, nfr, s, strlen(s), 0);
          free(s);
          return;
        }
        die_mode("cannot transput ", m, " value with a bits pattern");
      }
      int is_str = has_frame(fr, nfr, FR_A);
      int is_real = has_frame(fr, nfr, FR_POINT) || has_frame(fr, nfr, FR_E);
      if (is_str) {
        if (p->k == M_CHAR && v.tag == T_CHAR) { uint8_t c = (uint8_t) v.v.u; write_string_pattern(fid, fr, nfr, &c, 1); return; }
        if (mode_is_string(mr)) { int64_t sn; uint8_t* s = str_of(v, &sn); write_string_pattern(fid, fr, nfr, s, (size_t) sn); free(s); return; }
        die_mode("cannot transput ", m, " value with a string pattern");
      }
      if (is_real) {
        a68_dec d;
        int neg = to_dec(m, v, &d);
        write_real_pattern(fid, fr, nfr, neg, d);
        a68_dec_free(&d);
        return;
      }
      if (p->k == M_INT && (v.tag == T_INT || v.tag == T_BIGINT)) {
        a68_big* b = big_of_val(v);
        int neg = big_sign(b) < 0;
        a68_big* ab = big_abs(b);
        char* ds = big_to_dec(ab);
        big_free(b); big_free(ab);
        write_integral_pattern(fid, fr, nfr, neg, ds, strlen(ds));
        free(ds);
        return;
      }
      if (p->k == M_REAL) die("cannot transput REAL value with an integral pattern");
      die_mode("cannot transput ", m, " value with an integral pattern");
    }
    case P_BOOL:
      if (v.tag == T_BOOL) {
        if (pat->has_texts) { if (v.v.u) file_out(fid, pat->flip, pat->nflip); else file_out(fid, pat->flop, pat->nflop); }
        else file_out(fid, v.v.u ? "T" : "F", 1);
        return;
      }
      die_mode("cannot transput ", m, " value with a boolean pattern");
    case P_CHOICE:
      if (v.tag == T_INT) {
        int64_t k = v.v.i;
        if (k >= 1 && k <= (int64_t) pat->nalts) file_out(fid, pat->alts[k - 1], pat->altn[k - 1]);
        return;
      }
      die_mode("cannot transput ", m, " value with a choice pattern");
    case P_CPAT: write_c_pattern(fid, pat, mr, v); return;
    case P_HGEN: {
      const int64_t* a = pat->args; size_t n = pat->nargs;
      if (p->k == M_INT && (v.tag == T_INT || v.tag == T_BIGINT)) {
        int64_t w, af, e, mult;
        h_arguments(p->len, a, n, &w, &af, &e, &mult);
        a68_big* b = big_of_val(v);
        file_out_take(fid, a68_fmt_float_int(b, w, af, e, mult));
        big_free(b);
        return;
      }
      if (p->k == M_REAL && v.tag == T_REAL) {
        double x = check_real(v.v.r);
        int64_t w, af, e, mult;
        h_arguments(p->len, a, n, &w, &af, &e, &mult);
        file_out_take(fid, a68_fmt_float_real(x, w, af, e, mult));
        return;
      }
      /* without arguments `h` writes other values as `g` does */
      if (n == 0) {
        if (p->k == M_BOOL && v.tag == T_BOOL) { file_out(fid, v.v.u ? "T" : "F", 1); return; }
        if (p->k == M_CHAR && v.tag == T_CHAR) { file_out_byte(fid, (uint8_t) v.v.u); return; }
        if (p->k == M_BITS && (v.tag == T_BITS || v.tag == T_BIGBITS)) { file_out_take(fid, fmt_bits_of(v, p->len)); return; }
        if (mode_is_string(mr) && v.tag == T_ROW) { int64_t sn; uint8_t* s = str_of(v, &sn); file_out(fid, (const char*) s, (size_t) sn); free(s); return; }
      }
      cannot_general(m, 0);
    }
    case P_INS: die("internal: insertion as pattern");
    case P_COL: die("internal: column alignment as pattern");
    default: die("internal: bad pattern");
  }
}

static int is_format_union(a68_val e, a68_val* inner) {
  if (e.tag != T_UNION) return 0;
  if (mode_at(mode_resolve(e.aux))->k != M_FORMAT) return 0;
  *inner = ((a68_slots*) e.v.p)->s[0];
  return 1;
}

/* `Interp.printf` */
void printf_items(uint32_t fid, a68_val row) {
  if (row.tag != T_ROW) die("internal: printf argument");
  size_t mark = arena_n;
  io_col = 0;
  size_t start = outlen;
  fmt_state_t st; memset(&st, 0, sizeof st);
  int have = 0;
  a68_rowd* d = (a68_rowd*) row.v.p;
  int64_t n = row_count(d);
  for (int64_t i = 0; i < n; i++) {
    a68_val e = rowd_get(d, row_store_index(d, i));
    a68_val f;
    if (is_format_union(e, &f)) {
      /* purge the previous format */
      if (have) next_pattern(fid, &st, 0);
      a68_frame* env; uint32_t skel;
      fmt_of(f, &env, &skel);
      st.n = 0;
      st_push(&st, expand_format(env, skel, 0));
      have = 1;
    } else if (e.tag == T_UNION) {
      if (!have) die("no format active in printf");
      int was = pf_active; size_t ws = pf_start, wi = pf_item;
      if (fid == 0) { pf_active = 1; pf_start = start; pf_item = outlen; }
      write_formatted(fid, &st, e.aux, ((a68_slots*) e.v.p)->s[0]);
      pf_active = was; pf_start = ws; pf_item = wi;
    } else die("internal: printf argument");
  }
  if (have) {
    pic_t* left = next_pattern(fid, &st, 0);
    if (left) die("format has unused patterns");
  }
  io_nul_cut = 0;
  arena_free_to(mark);
}

/* ---------------------------------------------------------------- reading with patterns */

/* insertions are skipped on input, character by character (`Interp.readInsertion`) */
static void read_insertion(uint32_t fid, const char* s, size_t n) {
  for (size_t i = 0; i < n; i++) { if (s[i] == '\n') skip_line(fid); else skip_char(fid); }
}

/* `Interp.readScalarFormatted` */
static void read_scalar_formatted(uint32_t fid, fmt_state_t* st, uint32_t m, a68_val r) {
  /* pull the next pattern, consuming insertions from the input */
  pic_t* pat = NULL;
  for (;;) {
    if (st->n == 0) break;
    fmt_frame_t* fr = &st->fr[st->n - 1];
    if (fr->cursor < fr->npics) {
      pic_t* p = &fr->pics[fr->cursor];
      if (p->k == P_INS) { read_insertion(fid, p->s, p->n); fr->cursor++; }
      else if (p->k == P_COL) fr->cursor++;
      else if (p->k == P_INCLUDE) {
        fr->cursor++;
        fmt_frame_t nf = expand_format(p->env, p->skel, 1);
        st_push(st, nf);
      } else { pat = p; fr->cursor++; break; }
    } else if (fr->embedded) st->n--;
    else {
      if (fr->npics == 0) die("format exhausted");
      fr->cursor = 0; st->n = 1;
    }
  }
  if (!pat) die("format exhausted");
  uint32_t mr = mode_resolve(m);
  uint32_t tm = mode_at(mr)->k == M_REF ? mode_resolve(mode_at(mr)->sub) : mr;
  const a68_mode* q = mode_at(tm);
  switch (pat->k) {
    case P_GENERAL: case P_HGEN: read_into(fid, m, r); return;
    case P_CPAT: {
      /* a68g `read_c_pattern`: without a width the value is read as `get` reads it, with one
         exactly that many characters are taken and converted */
      char letter = pat->n ? pat->s[pat->n - 1] : 0;
      int64_t width = pat->has_w ? pat->w : 0;
      int plus = memchr(pat->s, '+', pat->n) != NULL, minus = memchr(pat->s, '-', pat->n) != NULL;
      #define READ_N(k, b) do { for (int64_t _i = 0; _i < (k); _i++) { int _c = read_char(fid); if (_c < 0) logical_end(fid); sb_putc(&(b), (char) _c); } } while (0)
      if (q->k == M_CHAR && letter == 'c') {
        if (width == 0) { read_into(fid, m, r); return; }
        sbuf b = {0}; READ_N(width, b);
        size_t off = (width > 1 && !minus) ? (size_t) width - 1 : 0;
        store_ref(r, mk_char(off < b.n ? (uint8_t) b.p[off] : ' '));
        free(b.p);
        return;
      }
      if (mode_is_string(tm) && letter == 's') {
        if (width == 0) { read_into(fid, m, r); return; }
        sbuf b = {0}; READ_N(width, b);
        store_ref(r, of_string(b.p, b.n));
        free(b.p);
        return;
      }
      if (q->k == M_INT && (letter == 'd' || letter == 'i')) {
        if (width == 0) { read_into(fid, m, r); return; }
        sbuf b = {0}; READ_N(plus ? width + 1 : width, b);
        a68_big* k = parse_int_text(b.p, b.n);
        if (!k) value_error_mode(fid, tm, b.p, b.n);
        a68_big* lim = max_int_of(q->len);
        a68_big* ak = big_abs(k);
        int over = big_cmp(ak, lim) > 0;
        big_free(lim); big_free(ak);
        if (over) { big_free(k); value_error_mode(fid, tm, b.p, b.n); }
        store_ref(r, val_of_big(k));
        big_free(k); free(b.p);
        return;
      }
      if (q->k == M_REAL && (letter == 'f' || letter == 'e' || letter == 'g')) {
        if (width == 0) { read_into(fid, m, r); return; }
        sbuf b = {0}; READ_N(plus ? width + 1 : width, b);
        double x;
        if (!parse_real_text(b.p, b.n, &x)) value_error_mode(fid, tm, b.p, b.n);
        store_ref(r, mk_real(x));
        free(b.p);
        return;
      }
      if (q->k == M_BITS && (letter == 'b' || letter == 'o' || letter == 'x')) {
        int radix = letter == 'b' ? 2 : letter == 'o' ? 8 : 16;
        sbuf b = {0};
        if (width == 0) {
          skip_spaces(fid);
          for (;;) {
            int c = peek_char(fid);
            if (c >= 0 && ((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F'))) { read_char(fid); sb_putc(&b, (char) c); }
            else break;
          }
        } else READ_N(width, b);
        if (!b.p) sb_put(&b, "", 0);
        store_ref(r, radix_value(fid, b.p, b.n, radix, q->len));
        free(b.p);
        return;
      }
      #undef READ_N
      die_mode("cannot transput ", tm, " value with a C-style pattern");
    }
    case P_PATTERN: {
      const frame_t* fr = pat->fr; size_t nfr = pat->nfr;
      int has_radix;
      int64_t rdx = find_radix(fr, nfr, &has_radix);
      if (has_radix) {
        /* a bits pattern: digits of the radix, a `z` frame also taking a blank for a zero */
        if (q->k != M_BITS) die_mode("cannot transput ", tm, " value with a bits pattern");
        if (rdx < 2 || rdx > 16) dief("invalid radix %lld", rdx, 0, 0);
        sbuf b = {0};
        for (size_t i = 0; i < nfr; i++) {
          if (fr[i].k == FR_INS) read_insertion(fid, fr[i].s, fr[i].n);
          else if (fr[i].k == FR_Z || fr[i].k == FR_D) {
            int c = read_char(fid);
            if (c < 0) logical_end(fid);
            if (fr[i].k == FR_Z && c == ' ') sb_putc(&b, '0');
            else if ((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) sb_putc(&b, (char) c);
            else {
              sbuf t = {0}; sb_put(&t, b.p ? b.p : "", b.n); sb_putc(&t, (char) c);
              value_error_mode(fid, tm, t.p, t.n);
            }
          }
        }
        if (!b.p) sb_put(&b, "", 0);
        store_ref(r, radix_value(fid, b.p, b.n, (int) rdx, q->len));
        free(b.p);
        return;
      }
      if (has_frame(fr, nfr, FR_A)) {
        /* string pattern: read exactly as many characters as there are `a` frames */
        sbuf b = {0};
        for (size_t i = 0; i < nfr; i++) {
          if (fr[i].k == FR_A) { int c = read_char(fid); if (c < 0) logical_end(fid); sb_putc(&b, (char) c); }
          else if (fr[i].k == FR_INS) read_insertion(fid, fr[i].s, fr[i].n);
        }
        if (!b.p) sb_put(&b, "", 0);
        if (q->k == M_CHAR) store_ref(r, mk_char(b.n ? (uint8_t) b.p[0] : ' '));
        else store_ref(r, of_string(b.p, b.n));
        free(b.p);
        return;
      }
      /* numeric pattern: read the characters covered by the frames and convert */
      sbuf b = {0};
      for (size_t i = 0; i < nfr; i++) {
        uint8_t k = fr[i].k;
        if (k == FR_INS) read_insertion(fid, fr[i].s, fr[i].n);
        else if (k == FR_Z || k == FR_D || k == FR_PLUS || k == FR_MINUS || k == FR_POINT || k == FR_E) {
          int c = read_char(fid);
          if (c < 0) logical_end(fid);
          sb_putc(&b, (char) c);
        }
      }
      if (!b.p) sb_put(&b, "", 0);
      /* without the blanks */
      size_t tn = 0;
      for (size_t i = 0; i < b.n; i++) if (b.p[i] != ' ') b.p[tn++] = b.p[i];
      b.p[tn] = 0; b.n = tn;
      if (q->k == M_INT) {
        if (!is_int_text(b.p, b.n)) { sbuf e = {0}; sb_puts(&e, "cannot read INT from \""); sb_put(&e, b.p, b.n); sb_puts(&e, "\""); die(e.p); }
        store_ref(r, int_of_text(b.p, b.n));
      } else if (q->k == M_REAL) {
        if (q->len >= 1) {
          /* a LONG value read with a pattern is converted by `string_to_mp` too */
          int ok;
          a68_val z = mp_of_string((const uint8_t*) b.p, b.n, q->len, &ok);
          if (!ok) die_mode_str("cannot read ", tm, " from \"", b.p, b.n, "\"");
          store_ref(r, z);
        } else store_ref(r, real_of_text(b.p, b.n));
      } else die("numeric pattern on non-numeric value");
      free(b.p);
      return;
    }
    case P_BOOL: {
      size_t n; char* tok = read_token(fid, &n);
      int val;
      if (pat->has_texts) {
        if (n == pat->nflip && memcmp(tok, pat->flip, n) == 0) val = 1;
        else if (n == pat->nflop && memcmp(tok, pat->flop, n) == 0) val = 0;
        else val = n == 1 && tok[0] == 'T';
      } else val = n == 1 && tok[0] == 'T';
      store_ref(r, mk_bool(val));
      free(tok);
      return;
    }
    case P_CHOICE: {
      /* match the longest alternative at the current position */
      a68_file* fs = load_file(fid);
      const uint8_t* rest = fs->buf + fs->pos;
      size_t nrest = fs->len - fs->pos;
      int best = -1; size_t bl = 0;
      for (size_t i = 0; i < pat->nalts; i++) {
        size_t al = pat->altn[i];
        if (al <= nrest && memcmp(rest, pat->alts[i], al) == 0) {
          if (best < 0 || al > bl) { best = (int) i; bl = al; }
        }
      }
      if (best >= 0) {
        fs->pos += bl;
        store_ref(r, mk_int(best + 1));
      } else value_error(fid, "no alternative of the choice pattern matches the input");
      return;
    }
    default: die("internal: pattern expected");
  }
}

static void read_formatted(uint32_t fid, fmt_state_t* st, uint32_t m, a68_val r);

static void read_formatted_cb(uint32_t fid, void* st, uint32_t m, a68_val r) { read_formatted(fid, (fmt_state_t*) st, m, r); }

/* `Interp.readFormatted`: one value with the next input pattern */
static void read_formatted(uint32_t fid, fmt_state_t* st, uint32_t m, a68_val r) {
  uint32_t mr = mode_resolve(m);
  const a68_mode* p = mode_at(mr);
  uint32_t tsub = mr, tm;
  if (p->k == M_REF) { tsub = p->sub; tm = mode_resolve(tsub); }
  else if (mode_is_file_proc(mr)) tm = mode_simple(M_VOID, 0);
  else tm = mr;
  const a68_mode* q = mode_at(tm);
  switch (q->k) {
    case M_VOID: read_into(fid, m, r); return;
    case M_STRUCT:
      for (uint32_t i = 0; i < q->n; i++) read_formatted(fid, st, mode_ref(q->modes[i]), ref_field(r, i));
      return;
    case M_COMPL: {
      a68_val cur = ref_load(r);
      if (cur.tag != T_STRUCT) store_ref(r, undef_pair());
      uint32_t rm = mode_ref(mode_simple(M_REAL, q->len));
      read_formatted(fid, st, rm, ref_field(r, 0));
      read_formatted(fid, st, rm, ref_field(r, 1));
      return;
    }
    case M_UNION: read_union(fid, tm, r, read_formatted_cb, st); return;
    case M_ROW:
      if (mode_is_string(tm)) { read_scalar_formatted(fid, st, m, r); return; }
      if (q->dims == 1) {
        a68_val row = ref_load(r);
        if (row.tag == T_UNDEF) die("attempt to use an uninitialised row");
        if (row.tag != T_ROW) die("internal: row expected");
        int64_t n = row_count((a68_rowd*) row.v.p);
        uint32_t em = mode_ref(q->sub);
        for (int64_t i = 0; i < n; i++) read_formatted(fid, st, em, ref_elem(r, (uint32_t) i));
        return;
      }
      break;
    default: break;
  }
  read_scalar_formatted(fid, st, m, r);
}

/* consume the insertions that follow the last pattern used (a68g's purge on input) */
static void purge_read(uint32_t fid, fmt_state_t* st) {
  for (;;) {
    if (st->n == 0) break;
    fmt_frame_t* fr = &st->fr[st->n - 1];
    if (fr->cursor < fr->npics) {
      pic_t* p = &fr->pics[fr->cursor];
      if (p->k == P_INS) { read_insertion(fid, p->s, p->n); fr->cursor++; }
      else if (p->k == P_COL) fr->cursor++;
      else break;
    } else if (fr->embedded) st->n--;
    else break;
  }
}

/* `Interp.getfItems` */
void getf_items(uint32_t fid, a68_val row) {
  if (row.tag != T_ROW) die("internal: read argument");
  refresh_assoc(fid);
  size_t mark = arena_n;
  io_catch c;
  io_catch_push(&c);
  if (setjmp(c.jb) == 0) {
    fmt_state_t st; memset(&st, 0, sizeof st);
    int have = 0;
    a68_rowd* d = (a68_rowd*) row.v.p;
    int64_t n = row_count(d);
    for (int64_t i = 0; i < n; i++) {
      a68_val e = rowd_get(d, row_store_index(d, i));
      a68_val f;
      if (is_format_union(e, &f)) {
        if (have) purge_read(fid, &st);
        a68_frame* env; uint32_t skel;
        fmt_of(f, &env, &skel);
        st.n = 0;
        st_push(&st, expand_format(env, skel, 0));
        have = 1;
      } else if (e.tag == T_UNION) {
        a68_val v = ((a68_slots*) e.v.p)->s[0];
        if (have) read_formatted(fid, &st, e.aux, v); else read_into(fid, e.aux, v);
      } else die("internal: read argument");
    }
    if (have) purge_read(fid, &st);
    io_catch_pop(&c);
  } else {
    /* a mended logical file end abandons the rest of the call */
  }
  arena_free_to(mark);
}

/* `Interp.getItems` */
void get_items(uint32_t fid, a68_val row) {
  if (row.tag != T_ROW) die("internal: read argument");
  refresh_assoc(fid);
  io_catch c;
  io_catch_push(&c);
  if (setjmp(c.jb) == 0) {
    a68_rowd* d = (a68_rowd*) row.v.p;
    int64_t n = row_count(d);
    for (int64_t i = 0; i < n; i++) {
      a68_val e = rowd_get(d, row_store_index(d, i));
      if (e.tag != T_UNION) die("internal: read argument");
      read_into(fid, e.aux, ((a68_slots*) e.v.p)->s[0]);
    }
    io_catch_pop(&c);
  }
}

/* ---------------------------------------------------------------- string files */

/* run some transput on a fresh string file and give what it wrote (a68g's `puts` and
   `string`); the column of the current formatted line is left as it was */
char* with_string_file(void (*act)(uint32_t fid, void* ctx), void* ctx, size_t* n) {
  int64_t col = io_col;
  int cut = io_nul_cut;
  io_nul_cut = 0;
  a68_file f = file_default();
  f.loaded = 1; f.channel = 4;
  uint32_t fid = file_push(f);
  act(fid, ctx);
  a68_file* g = file_get(fid);
  char* s = dup_n((const char*) (g->buf ? g->buf : (const uint8_t*) ""), g->len);
  *n = g->len;
  file_pop(fid);
  io_col = col;
  io_nul_cut = cut;
  return s;
}

/* ---------------------------------------------------------------- binary transput */

static void read_bin_bytes(uint32_t fid, size_t n, uint8_t* out) {
  for (size_t i = 0; i < n; i++) {
    int c = read_char(fid);
    if (c < 0) logical_end(fid);
    out[i] = (uint8_t) c;
  }
}

static uint32_t u32_at(const uint8_t* b) { return (uint32_t) b[0] | ((uint32_t) b[1] << 8) | ((uint32_t) b[2] << 16) | ((uint32_t) b[3] << 24); }

/* `Interp.readBin`: a value laid out as a68g's C object is */
void read_bin(uint32_t fid, uint32_t m, a68_val r) {
  uint32_t mr = mode_resolve(m);
  const a68_mode* p = mode_at(mr);
  if (p->k == M_REF) {
    uint32_t t = mode_resolve(p->sub);
    const a68_mode* q = mode_at(t);
    uint8_t b[8];
    switch (q->k) {
      case M_INT: if (q->len == 0) { read_bin_bytes(fid, 4, b); store_ref(r, mk_int((int32_t) u32_at(b))); return; } break;
      case M_BITS: if (q->len == 0) { read_bin_bytes(fid, 4, b); store_ref(r, mk_bits(u32_at(b))); return; } break;
      case M_BOOL: read_bin_bytes(fid, 4, b); store_ref(r, mk_bool(u32_at(b) != 0)); return;
      case M_CHAR: read_bin_bytes(fid, 4, b); store_ref(r, mk_char(b[0])); return;
      case M_REAL:
        if (q->len == 0) {
          read_bin_bytes(fid, 8, b);
          uint64_t u = 0;
          for (int i = 7; i >= 0; i--) u = u * 256 + b[i];
          double x; memcpy(&x, &u, 8);
          store_ref(r, mk_real(x));
          return;
        }
        break;
      case M_STRUCT:
        for (uint32_t i = 0; i < q->n; i++) read_bin(fid, mode_ref(q->modes[i]), ref_field(r, i));
        return;
      case M_ROW:
        if (mode_is_string(t)) {
          read_bin_bytes(fid, 4, b);
          int32_t n = (int32_t) u32_at(b);
          size_t nn = n > 0 ? (size_t) n : 0;
          uint8_t* s = (uint8_t*) xm(nn + 1);
          read_bin_bytes(fid, nn, s);
          store_ref(r, string_row(s, (int64_t) nn, 1));
          free(s);
          return;
        }
        if (q->dims == 1) {
          a68_val row = ref_load(r);
          if (row.tag == T_UNDEF) die("attempt to use an uninitialised row");
          if (row.tag != T_ROW) die("internal: row expected");
          int64_t n = row_count((a68_rowd*) row.v.p);
          uint32_t em = mode_ref(q->sub);
          for (int64_t i = 0; i < n; i++) read_bin(fid, em, ref_elem(r, (uint32_t) i));
          return;
        }
        break;
      default: break;
    }
    die_mode("cannot read a value of mode ", t, " in binary");
  }
  if (mode_is_file_proc(mr)) { read_into(fid, m, r); return; }
  die_mode("cannot read into a value of mode ", m, "");
}

static void out_le(uint32_t fid, uint64_t v, int n) {
  char b[8];
  for (int i = 0; i < n; i++) { b[i] = (char) (v & 255); v >>= 8; }
  file_out(fid, b, (size_t) n);
}

/* `Interp.writeBin`, the converse */
void write_bin(uint32_t fid, uint32_t m, a68_val v) {
  uint32_t mr = mode_resolve(m);
  const a68_mode* p = mode_at(mr);
  if (v.tag == T_UNION) { write_bin(fid, v.aux, ((a68_slots*) v.v.p)->s[0]); return; }
  switch (p->k) {
    case M_INT: if (p->len == 0 && v.tag == T_INT) { out_le(fid, (uint64_t) v.v.i, 4); return; } break;
    case M_BITS: if (p->len == 0 && v.tag == T_BITS) { out_le(fid, v.v.u, 4); return; } break;
    case M_BOOL: if (v.tag == T_BOOL) { out_le(fid, v.v.u ? 1 : 0, 4); return; } break;
    case M_CHAR: if (v.tag == T_CHAR) { out_le(fid, v.v.u, 4); return; } break;
    case M_REAL: if (p->len == 0 && v.tag == T_REAL) { out_le(fid, v.v.u, 8); return; } break;
    case M_ROW:
      if (mode_is_string(mr) && v.tag == T_ROW) {
        int64_t n; uint8_t* s = str_of(v, &n);
        out_le(fid, (uint64_t) n, 4);
        file_out(fid, (const char*) s, (size_t) n);
        free(s);
        return;
      }
      if (v.tag == T_ROW) {
        a68_rowd* d = (a68_rowd*) v.v.p;
        int64_t n = row_count(d);
        for (int64_t i = 0; i < n; i++) write_bin(fid, p->sub, rowd_get(d, row_store_index(d, i)));
        return;
      }
      break;
    case M_STRUCT:
      if (v.tag == T_STRUCT) {
        a68_slots* s = (a68_slots*) v.v.p;
        uint32_t n = p->n < s->h.n ? p->n : s->h.n;
        for (uint32_t i = 0; i < n; i++) write_bin(fid, p->modes[i], s->s[i]);
        return;
      }
      break;
    case M_PROC: if (mode_is_file_proc(mr)) { print_value(fid, mr, v); return; } break;
    default: break;
  }
  if (v.tag == T_UNDEF) die_mode("attempt to use an uninitialised ", m, " value");
  die_mode("cannot write a value of mode ", mr, " in binary");
}

/* ---------------------------------------------------------------- start-up */

void io_init(int argc, char** argv, const char* src, int regression, int ll) {
  a68_regression = regression;
  a68_ll_digits = ll;
  /* the arguments as a68g sees them: its own name, the source, then the rest */
  a68_argc = argc + 1;
  a68_argv = (char**) xm((size_t) (argc + 2) * sizeof(char*));
  a68_argv[0] = "a68g";
  a68_argv[1] = (char*) src;
  for (int i = 1; i < argc; i++) a68_argv[i + 1] = argv[i];
  a68_argv[argc + 1] = NULL;
  for (int i = 0; i < 4; i++) file_push(file_default());
}
