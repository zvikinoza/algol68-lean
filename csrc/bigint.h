/* bigint.h -- arbitrary-precision signed integers for the C runtime of compiled
   Algol 68 programs (plain C99, malloc-based, no global state).

   A value is immutable once built; every operation returns a fresh value that the
   caller releases with big_free.  Magnitudes are little-endian arrays of 32-bit
   limbs; the sign is kept separately, so all operations follow C semantics on the
   mathematical integers (division truncates toward zero, the remainder takes the
   sign of the dividend). */
#ifndef A68_BIGINT_H
#define A68_BIGINT_H

#include <stddef.h>
#include <stdint.h>

typedef struct a68_big a68_big;                  /* opaque, immutable once built */

a68_big* big_from_i64(int64_t v);
a68_big* big_from_dec(const char* s, size_t n);  /* optional leading '-', decimal digits */
char*    big_to_dec(const a68_big* a);           /* malloc'ed decimal string, '-' if negative */
int      big_fits_i64(const a68_big* a);
int64_t  big_to_i64(const a68_big* a);           /* the low 64 bits (two's complement) if it does not fit */
a68_big* big_add(const a68_big* a, const a68_big* b);
a68_big* big_sub(const a68_big* a, const a68_big* b);
a68_big* big_mul(const a68_big* a, const a68_big* b);
a68_big* big_mul_small(const a68_big* a, int64_t k);
a68_big* big_divmod(const a68_big* a, const a68_big* b, a68_big** rem); /* truncating (C semantics); NULL if b = 0 */
a68_big* big_pow10(int n);                       /* 10^n for n >= 0 (1 for n < 0) */
int      big_cmp(const a68_big* a, const a68_big* b);  /* -1, 0, 1 */
int      big_sign(const a68_big* a);             /* -1, 0, 1 */
int      big_is_zero(const a68_big* a);
size_t   big_ndigits(const a68_big* a);          /* decimal digits of |a|, 1 for 0 */
a68_big* big_neg(const a68_big* a);
a68_big* big_abs(const a68_big* a);
void     big_free(a68_big* a);                   /* accepts NULL */

#endif
