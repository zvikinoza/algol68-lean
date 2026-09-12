/* Transput and the standard prelude of compiled programs: the files, the output buffer,
   formatted and unformatted reading and writing, and the run's end (io.c, prelude.c).
   Everything here transcribes A68/Interp.lean; the Lean definition each function
   reproduces is named at its definition. */
#ifndef A68_IO_H
#define A68_IO_H
#include <stdint.h>
#include <stddef.h>
#include <setjmp.h>
#include "a68rt.h"

/* ---------------------------------------------------------------- the run */

extern int a68_ll_digits;        /* `PR precision`: digits of LONG LONG modes (Numfmt.defaultLLDigits) */
extern int a68_regression;       /* `PR regression PR`: end standard output with a newline */
extern int a68_argc; extern char** a68_argv;   /* the program's arguments: a68g, the source, the rest */

void io_init(int argc, char** argv, const char* src, int regression, int ll);
void io_flush_out(void);         /* Interp.flushOut */
uint32_t io_finish(void);        /* Runtime.finish */
__attribute__((noreturn)) void io_stop(void);              /* Runtime.doStop */
__attribute__((noreturn)) void io_die(const char* msg);    /* Runtime.die */

/* ---------------------------------------------------------------- unwinding
   `Ctrl.fileEnd` (a mended logical file end abandons the transput call) and a jump raised
   by an event routine or a format hole (`fromCompiled`) unwind through the transput
   with longjmp.  A handler frame records where the operand and environment stacks were. */
enum { IO_FILE_END = 1, IO_JUMP = 2 };
typedef struct io_catch { jmp_buf jb; size_t sp0; size_t env0; size_t arena0; struct io_catch* prev; } io_catch;
void io_catch_push(io_catch* c);
void io_catch_pop(io_catch* c);
__attribute__((noreturn)) void io_raise(int kind);
/* After a call into compiled code: propagate the jump it left pending. */
void io_check_jump(void);

/* ---------------------------------------------------------------- files (Interp.FileSt) */

typedef struct {
  char* name;
  uint8_t* buf; size_t len, cap;   /* contents (reading) or accumulated output (writing) */
  size_t pos;
  a68_val assoc;                   /* REF STRING of an associated file; T_UNDEF when none */
  a68_val on_end, on_value, on_line;   /* event routines; T_UNDEF when none */
  uint8_t* term; size_t nterm;
  int writing, reading, loaded, eof, dirty, ondisk;
  int64_t fd;                      /* an operating-system descriptor: an end of a pipe */
  int channel;                     /* 0 stand out, 1 stand in, 2 stand error, 3 stand back, 4 associate */
} a68_file;

extern a68_file* files; extern size_t nfiles;
a68_file* file_get(uint32_t fid);                /* Interp.getFile */
uint32_t file_new(a68_val fv, a68_file f);       /* Interp.newFile */
uint32_t file_push(a68_file f);                  /* a temporary file at the end of the table */
void file_pop(uint32_t fid);                     /* remove it again when it is still the last */
a68_file file_default(void);
uint32_t file_id_of(a68_val f);                  /* Interp.fileIdOf */
uint32_t file_channel(a68_val f);                /* Interp.fileChannel */
void file_flush(uint32_t fid);                   /* Interp.flushFile */
void io_gc_roots(void (*mark)(const a68_val*)); /* the values the file table holds */

/* ---------------------------------------------------------------- output */

extern int io_nul_cut;      /* Interp.nulCut */
extern int64_t io_col;      /* Interp.Rt.col */
void file_out(uint32_t fid, const char* s, size_t n);     /* Interp.fileOut */
void file_out_str(uint32_t fid, const char* s);
void file_out_byte(uint32_t fid, uint8_t b);              /* Interp.fileOutByte */
void emit_bytes(const uint8_t* p, size_t n);              /* Interp.emit */
size_t out_size(void);
void print_value(uint32_t fid, uint32_t m, a68_val v);    /* Interp.printValue */
void print_items(uint32_t fid, a68_val row);              /* the `print`/`put` loop */
void printf_items(uint32_t fid, a68_val row);             /* Interp.printf */
void write_bin(uint32_t fid, uint32_t m, a68_val v);      /* Interp.writeBin */
char* with_string_file(void (*act)(uint32_t fid, void* ctx), void* ctx, size_t* n);  /* Interp.withStringFile */

/* ---------------------------------------------------------------- input */

a68_file* load_file(uint32_t fid);               /* Interp.loadFile */
int read_char(uint32_t fid);                     /* Interp.readChar: -1 at the end */
int peek_char(uint32_t fid);                     /* Interp.peekChar */
int at_end(uint32_t fid);                        /* Interp.atEnd */
void logical_end(uint32_t fid);                  /* Interp.logicalEnd */
void skip_line(uint32_t fid);                    /* Interp.skipLine */
char* read_token(uint32_t fid, size_t* n);       /* Interp.readToken */
char* read_line_str(uint32_t fid, size_t* n);    /* Interp.readLineStr */
void read_into(uint32_t fid, uint32_t m, a68_val r);      /* Interp.readInto */
void get_items(uint32_t fid, a68_val row);       /* Interp.getItems */
void getf_items(uint32_t fid, a68_val row);      /* Interp.getfItems */
void read_bin(uint32_t fid, uint32_t m, a68_val r);       /* Interp.readBin */
int io_call_handler(a68_val h, uint32_t fid);    /* call an event routine, giving its BOOL */

/* ---------------------------------------------------------------- values */

a68_val of_string(const char* s, size_t n);      /* Value.ofString */
uint8_t* str_of(a68_val v, int64_t* n);          /* Interp.strOf: malloc'ed, NUL-terminated */
a68_val ref_load_checked(a68_val r);             /* Interp.readRef with its NIL/undef checks */
a68_val row_of_values(const a68_val* vs, int64_t n);   /* Value.rowOfList */
int mode_is_file_proc(uint32_t m);               /* `.proc [.ref .file] .void` */
int mode_is_string(uint32_t m);                  /* `.row 1 _ .char` */
char* fmt_int_of(a68_val v, int64_t longness);   /* Numfmt.printInt of an INT / LONG INT value */
double check_real(double x);                     /* Interp.checkReal */

/* ---------------------------------------------------------------- the prelude (prelude.c) */

/* `Interp.callBuiltin`: the arguments are the `nargs` values on top of the operand stack,
   which stay there (rooted) until the call returns; the result is left in `*res`. */
void call_builtin(uint32_t name, uint32_t nargs, a68_val* res);
double next_random(void);                        /* Interp.nextRandom */
void taus_seed(uint32_t seed);                   /* Interp.tausSet */

#endif
