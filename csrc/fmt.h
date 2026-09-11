/* fmt.h -- number formatting of compiled Algol 68 programs, byte-compatible with
   Algol 68 Genie.  A transcription of A68/Numfmt.lean (the Lean definition each
   function reproduces is named in fmt.c).

   All returned strings are malloc'ed and NUL-terminated; characters are bytes. */
#ifndef A68_FMT_H
#define A68_FMT_H

#include <stddef.h>
#include <stdint.h>
#include "bigint.h"

/* Numfmt.Dec: the exact decimal number mant * 10^exp.  A value returned by this
   module owns its mantissa; release it with a68_dec_free. */
typedef struct { a68_big* mant; int64_t exp; } a68_dec;

a68_dec a68_dec_of_u64(uint64_t n);            /* Numfmt.Dec.ofInt for a magnitude */
a68_dec a68_dec_of_big(const a68_big* n);      /* the same for a LONG INT magnitude (copies) */
void    a68_dec_free(a68_dec* d);

/* Numfmt.realToDec: returns the sign flag (1 if x < 0) and fills *out with |x|. */
int a68_real_to_dec(double x, a68_dec* out);

/* Numfmt.subFixed (x borrowed). */
char* a68_fmt_sub_fixed(a68_dec x, int64_t width, int64_t after);
/* Numfmt.standardize (y borrowed; out->mant is fresh). */
void  a68_fmt_standardize(a68_dec y, int64_t before, int64_t after, int64_t q, a68_dec* out, int64_t* qout);

/* Standard widths and limits (Numfmt.intWidthOf, realWidthOf, expWidthOf,
   bitsWidthOfLen, maxIntOf, llDigitsOfPrecision, defaultLLDigits). */
#define A68_DEFAULT_LL_DIGITS 12
int      a68_fmt_int_width(int64_t longness, int ll);
int      a68_fmt_real_width(int64_t longness, int ll);
int      a68_fmt_exp_width(int64_t longness);
int      a68_fmt_bits_width(int64_t longness, int ll);
a68_big* a68_fmt_max_int(int64_t longness, int ll);     /* fresh */
int      a68_fmt_ll_digits_of_precision(int n);

char* a68_fmt_whole_int(const a68_big* n, int64_t width);                 /* Numfmt.whole / wholeInt */
char* a68_fmt_fixed_real(double x, int64_t width, int64_t after);         /* Numfmt.fixedReal */
char* a68_fmt_fixed_int(const a68_big* n, int64_t width, int64_t after, int is_long); /* fixedInt (is_long 0) / fixedLongInt (1) */
char* a68_fmt_float_real(double x, int64_t width, int64_t after, int64_t expo, int64_t frmt); /* Numfmt.floatReal */
char* a68_fmt_float_int(const a68_big* n, int64_t width, int64_t after, int64_t expo, int64_t frmt); /* Numfmt.floatInt */
char* a68_fmt_whole_real(double x, int64_t width);                        /* Numfmt.wholeReal */
char* a68_fmt_print_int(const a68_big* n, int64_t longness, int ll_digits);  /* Numfmt.printInt */
char* a68_fmt_print_real(double x, int64_t longness, int ll_digits);         /* Numfmt.printReal */
char* a68_fmt_print_bits(const a68_big* v, int width);                       /* Numfmt.printBits */
double a68_fmt_parse_float(const char* s, size_t n);                         /* Numfmt.parseFloat */
int a68_fmt_has_error(const char* s);                                        /* Numfmt.hasError */

/* The kernel, for the formatted-transput module.  `x` is borrowed, not consumed. */
char* a68_fmt_fixed_dec(int ltz, a68_dec x, int64_t width, int64_t after);            /* Numfmt.fixedDec */
char* a68_fmt_float_dec(int ltz, a68_dec x, int64_t width, int64_t after, int64_t expo, int64_t frmt); /* Numfmt.floatDec */
char* a68_fmt_sub_whole(uint64_t n, int64_t width);                                   /* Numfmt.subWhole */

#endif
