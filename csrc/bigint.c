/* bigint.c -- arbitrary-precision signed integers (see bigint.h).

   Representation: sign + magnitude.  The magnitude is a little-endian array of
   32-bit limbs with no leading zero limbs (`n == 0` for zero, which is never
   negative).  Intermediate arithmetic uses 64-bit unsigned integers, so the code
   is plain C99 without compiler extensions. */
#include "bigint.h"

#include <stdlib.h>
#include <string.h>

struct a68_big {
    int      neg;     /* 1 if the value is negative; 0 for zero */
    size_t   n;       /* limbs in use */
    uint32_t limb[];  /* magnitude, little-endian base 2^32 */
};

#define LIMB_BITS 32
#define LIMB_MASK 0xFFFFFFFFu

/* ------------------------------------------------------------------ allocation */

static void* xmalloc(size_t n) {
    void* p = malloc(n ? n : 1);
    if (!p) abort();
    return p;
}

/* A zero-filled value with room for `n` limbs (trimmed by big_trim before use). */
static a68_big* big_alloc(size_t n) {
    a68_big* r = xmalloc(sizeof(a68_big) + n * sizeof(uint32_t));
    r->neg = 0;
    r->n = n;
    if (n) memset(r->limb, 0, n * sizeof(uint32_t));
    return r;
}

/* Drop leading zero limbs and normalise the sign of zero. */
static a68_big* big_trim(a68_big* r) {
    while (r->n > 0 && r->limb[r->n - 1] == 0) r->n--;
    if (r->n == 0) r->neg = 0;
    return r;
}

static a68_big* big_copy_mag(const a68_big* a, int neg) {
    a68_big* r = big_alloc(a->n);
    if (a->n) memcpy(r->limb, a->limb, a->n * sizeof(uint32_t));
    r->neg = a->n ? neg : 0;
    return r;
}

void big_free(a68_big* a) { free(a); }

/* ------------------------------------------------------------ magnitude helpers */

static int mag_cmp(const uint32_t* a, size_t an, const uint32_t* b, size_t bn) {
    if (an != bn) return an < bn ? -1 : 1;
    while (an > 0) {
        an--;
        if (a[an] != b[an]) return a[an] < b[an] ? -1 : 1;
    }
    return 0;
}

/* r = a + b (magnitudes); r has room for max(an, bn) + 1 limbs. */
static void mag_add(const uint32_t* a, size_t an, const uint32_t* b, size_t bn, uint32_t* r) {
    uint64_t carry = 0;
    size_t i, n = an > bn ? an : bn;
    for (i = 0; i < n; i++) {
        uint64_t s = carry;
        if (i < an) s += a[i];
        if (i < bn) s += b[i];
        r[i] = (uint32_t)(s & LIMB_MASK);
        carry = s >> LIMB_BITS;
    }
    r[n] = (uint32_t)carry;
}

/* r = a - b (magnitudes), requires a >= b; r has room for an limbs. */
static void mag_sub(const uint32_t* a, size_t an, const uint32_t* b, size_t bn, uint32_t* r) {
    uint64_t borrow = 0;
    size_t i;
    for (i = 0; i < an; i++) {
        uint64_t d = (uint64_t)a[i] - borrow - (i < bn ? b[i] : 0);
        r[i] = (uint32_t)(d & LIMB_MASK);
        borrow = (d >> LIMB_BITS) ? 1 : 0;   /* the subtraction wrapped */
    }
}

/* r = a * b (magnitudes), schoolbook; r has an + bn limbs, zero-filled on entry. */
static void mag_mul(const uint32_t* a, size_t an, const uint32_t* b, size_t bn, uint32_t* r) {
    size_t i, j;
    for (i = 0; i < an; i++) {
        uint64_t carry = 0;
        for (j = 0; j < bn; j++) {
            uint64_t t = (uint64_t)a[i] * b[j] + r[i + j] + carry;
            r[i + j] = (uint32_t)(t & LIMB_MASK);
            carry = t >> LIMB_BITS;
        }
        r[i + bn] = (uint32_t)carry;
    }
}

/* In place: a = a * k + c for a small k; a has room for an + 1 limbs.  Returns the new length. */
static size_t mag_mul_add_small(uint32_t* a, size_t an, uint32_t k, uint32_t c) {
    uint64_t carry = c;
    size_t i;
    for (i = 0; i < an; i++) {
        uint64_t t = (uint64_t)a[i] * k + carry;
        a[i] = (uint32_t)(t & LIMB_MASK);
        carry = t >> LIMB_BITS;
    }
    if (carry) { a[an] = (uint32_t)carry; return an + 1; }
    return an;
}

/* In place: a = a / d, returns the remainder (short division). */
static uint32_t mag_div_small(uint32_t* a, size_t an, uint32_t d) {
    uint64_t rem = 0;
    size_t i = an;
    while (i > 0) {
        i--;
        uint64_t cur = (rem << LIMB_BITS) | a[i];
        a[i] = (uint32_t)(cur / d);
        rem = cur % d;
    }
    return (uint32_t)rem;
}

static int clz32(uint32_t x) {
    int n = 0;
    if (x == 0) return 32;
    while (!(x & 0x80000000u)) { x <<= 1; n++; }
    return n;
}

/* Long division (Knuth, TAOCP 4.3.1 algorithm D) on magnitudes.
   Requires m >= n >= 2 and v[n-1] != 0.  q receives m - n + 1 limbs, r receives n limbs. */
static void mag_divmod(const uint32_t* u, size_t m, const uint32_t* v, size_t n, uint32_t* q, uint32_t* r) {
    const uint64_t B = (uint64_t)1 << LIMB_BITS;
    int s = clz32(v[n - 1]);
    uint32_t* vn = xmalloc(n * sizeof(uint32_t));
    uint32_t* un = xmalloc((m + 1) * sizeof(uint32_t));
    size_t i, j;

    /* normalise so that the top limb of the divisor has its high bit set */
    for (i = n - 1; i > 0; i--) vn[i] = (v[i] << s) | (s ? v[i - 1] >> (LIMB_BITS - s) : 0);
    vn[0] = v[0] << s;
    un[m] = s ? u[m - 1] >> (LIMB_BITS - s) : 0;
    for (i = m - 1; i > 0; i--) un[i] = (u[i] << s) | (s ? u[i - 1] >> (LIMB_BITS - s) : 0);
    un[0] = u[0] << s;

    for (j = m - n + 1; j > 0; j--) {
        size_t jj = j - 1;
        uint64_t num = ((uint64_t)un[jj + n] << LIMB_BITS) | un[jj + n - 1];
        uint64_t qhat = num / vn[n - 1];
        uint64_t rhat = num % vn[n - 1];
        uint64_t carry, borrow, t;
        while (qhat >= B || qhat * vn[n - 2] > ((rhat << LIMB_BITS) | un[jj + n - 2])) {
            qhat--;
            rhat += vn[n - 1];
            if (rhat >= B) break;
        }
        /* multiply and subtract */
        carry = 0; borrow = 0;
        for (i = 0; i < n; i++) {
            uint64_t p = qhat * vn[i] + carry;
            carry = p >> LIMB_BITS;
            t = (uint64_t)un[i + jj] - (p & LIMB_MASK) - borrow;
            un[i + jj] = (uint32_t)(t & LIMB_MASK);
            borrow = (t >> LIMB_BITS) ? 1 : 0;
        }
        t = (uint64_t)un[jj + n] - carry - borrow;
        un[jj + n] = (uint32_t)(t & LIMB_MASK);
        q[jj] = (uint32_t)qhat;
        if (t >> LIMB_BITS) {
            /* qhat was one too large: add the divisor back */
            q[jj]--;
            carry = 0;
            for (i = 0; i < n; i++) {
                uint64_t a = (uint64_t)un[i + jj] + vn[i] + carry;
                un[i + jj] = (uint32_t)(a & LIMB_MASK);
                carry = a >> LIMB_BITS;
            }
            un[jj + n] = (uint32_t)((un[jj + n] + carry) & LIMB_MASK);
        }
    }
    /* the remainder is the normalised residue shifted back */
    for (i = 0; i < n; i++) r[i] = (un[i] >> s) | (s ? un[i + 1] << (LIMB_BITS - s) : 0);
    free(vn);
    free(un);
}

/* ------------------------------------------------------------------ conversions */

a68_big* big_from_i64(int64_t v) {
    a68_big* r = big_alloc(2);
    uint64_t mag = v < 0 ? (uint64_t)0 - (uint64_t)v : (uint64_t)v;
    r->limb[0] = (uint32_t)(mag & LIMB_MASK);
    r->limb[1] = (uint32_t)(mag >> LIMB_BITS);
    r->neg = v < 0;
    return big_trim(r);
}

a68_big* big_from_dec(const char* s, size_t n) {
    int neg = 0;
    size_t i = 0, limbs = 0;
    a68_big* r;
    if (n > 0 && (s[0] == '-' || s[0] == '+')) { neg = s[0] == '-'; i = 1; }
    /* ten digits need at most 33.3 bits: n/9 + 1 limbs suffice */
    r = big_alloc((n - i) / 9 + 2);
    for (; i < n; i++) {
        if (s[i] < '0' || s[i] > '9') break;
        limbs = mag_mul_add_small(r->limb, limbs, 10, (uint32_t)(s[i] - '0'));
    }
    r->n = limbs;
    r->neg = neg;
    return big_trim(r);
}

char* big_to_dec(const a68_big* a) {
    /* peel off nine decimal digits at a time with short division */
    size_t cap = a->n * 10 + 3, len = 0, i, k;
    char* buf = xmalloc(cap);
    uint32_t* tmp = xmalloc((a->n ? a->n : 1) * sizeof(uint32_t));
    size_t tn = a->n;
    char* out;
    if (a->n) memcpy(tmp, a->limb, a->n * sizeof(uint32_t));
    while (tn > 0) {
        uint32_t chunk = mag_div_small(tmp, tn, 1000000000u);
        while (tn > 0 && tmp[tn - 1] == 0) tn--;
        for (k = 0; k < 9; k++) {          /* digits, least significant first */
            buf[len++] = (char)('0' + chunk % 10);
            chunk /= 10;
            if (tn == 0 && chunk == 0) break;
        }
    }
    if (len == 0) buf[len++] = '0';
    out = xmalloc(len + 2);
    k = 0;
    if (a->neg) out[k++] = '-';
    for (i = len; i > 0; i--) out[k++] = buf[i - 1];
    out[k] = 0;
    free(buf);
    free(tmp);
    return out;
}

int big_fits_i64(const a68_big* a) {
    uint64_t mag;
    if (a->n > 2) return 0;
    mag = (a->n > 0 ? a->limb[0] : 0) | (a->n > 1 ? (uint64_t)a->limb[1] << LIMB_BITS : 0);
    return a->neg ? mag <= (uint64_t)1 << 63 : mag < (uint64_t)1 << 63;
}

int64_t big_to_i64(const a68_big* a) {
    uint64_t mag = (a->n > 0 ? a->limb[0] : 0) | (a->n > 1 ? (uint64_t)a->limb[1] << LIMB_BITS : 0);
    int64_t r;
    if (a->neg) mag = (uint64_t)0 - mag;
    memcpy(&r, &mag, sizeof r);   /* two's complement reinterpretation of the low 64 bits */
    return r;
}

/* --------------------------------------------------------------------- arithmetic */

/* (a with sign aneg) + (b with sign bneg) */
static a68_big* add_signed(const a68_big* a, int aneg, const a68_big* b, int bneg) {
    a68_big* r;
    if (aneg == bneg) {
        r = big_alloc((a->n > b->n ? a->n : b->n) + 1);
        mag_add(a->limb, a->n, b->limb, b->n, r->limb);
        r->neg = aneg;
    } else if (mag_cmp(a->limb, a->n, b->limb, b->n) >= 0) {
        r = big_alloc(a->n);
        mag_sub(a->limb, a->n, b->limb, b->n, r->limb);
        r->neg = aneg;
    } else {
        r = big_alloc(b->n);
        mag_sub(b->limb, b->n, a->limb, a->n, r->limb);
        r->neg = bneg;
    }
    return big_trim(r);
}

a68_big* big_add(const a68_big* a, const a68_big* b) { return add_signed(a, a->neg, b, b->neg); }
a68_big* big_sub(const a68_big* a, const a68_big* b) { return add_signed(a, a->neg, b, !b->neg); }

a68_big* big_mul(const a68_big* a, const a68_big* b) {
    a68_big* r = big_alloc(a->n + b->n);
    mag_mul(a->limb, a->n, b->limb, b->n, r->limb);
    r->neg = a->neg != b->neg;
    return big_trim(r);
}

a68_big* big_mul_small(const a68_big* a, int64_t k) {
    a68_big* kb = big_from_i64(k);
    a68_big* r = big_mul(a, kb);
    big_free(kb);
    return r;
}

a68_big* big_divmod(const a68_big* a, const a68_big* b, a68_big** rem) {
    a68_big *q, *r;
    if (b->n == 0) { if (rem) *rem = NULL; return NULL; }
    if (mag_cmp(a->limb, a->n, b->limb, b->n) < 0) {
        q = big_alloc(0);
        r = big_copy_mag(a, a->neg);
    } else if (b->n == 1) {
        q = big_copy_mag(a, 0);
        r = big_alloc(1);
        r->limb[0] = mag_div_small(q->limb, q->n, b->limb[0]);
    } else {
        q = big_alloc(a->n - b->n + 1);
        r = big_alloc(b->n);
        mag_divmod(a->limb, a->n, b->limb, b->n, q->limb, r->limb);
    }
    q->neg = a->neg != b->neg;
    r->neg = a->neg;
    big_trim(q);
    big_trim(r);
    if (rem) *rem = r; else big_free(r);
    return q;
}

a68_big* big_pow10(int n) {
    /* 10^n by repeated small multiplications (10^9 per step): 32 * n / 9 bits suffice */
    size_t limbs = 1;
    a68_big* r = big_alloc((size_t)(n > 0 ? n : 0) / 9 + 3);
    r->limb[0] = 1;
    while (n >= 9) { limbs = mag_mul_add_small(r->limb, limbs, 1000000000u, 0); n -= 9; }
    while (n > 0) { limbs = mag_mul_add_small(r->limb, limbs, 10u, 0); n--; }
    r->n = limbs;
    return big_trim(r);
}

/* ----------------------------------------------------------------------- queries */

int big_sign(const a68_big* a) { return a->n == 0 ? 0 : a->neg ? -1 : 1; }
int big_is_zero(const a68_big* a) { return a->n == 0; }

int big_cmp(const a68_big* a, const a68_big* b) {
    int sa = big_sign(a), sb = big_sign(b);
    if (sa != sb) return sa < sb ? -1 : 1;
    if (sa == 0) return 0;
    return sa * mag_cmp(a->limb, a->n, b->limb, b->n);
}

size_t big_ndigits(const a68_big* a) {
    char* s = big_to_dec(a);
    size_t n = strlen(s) - (a->neg ? 1 : 0);
    free(s);
    return n;
}

a68_big* big_neg(const a68_big* a) { return big_copy_mag(a, !a->neg); }
a68_big* big_abs(const a68_big* a) { return big_copy_mag(a, 0); }
