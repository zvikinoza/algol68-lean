/* fmt_test.c -- differential test driver for csrc/fmt.c.

   Reads a case file (one case per line, the format of tests/fmt/cases.txt) and
   prints one result line per case, in the format of `a68lean fmttest` so that the
   two outputs can be diffed.  Build:

       cc -O2 -Wall -Wextra csrc/fmt_test.c csrc/fmt.c csrc/bigint.c -lm -o fmt_test

   Case kinds (the first eight are those of `a68lean fmttest`; the rest are
   evaluated on the Lean side by tests/fmt/fmtlong.lean):

       w n width                 whole (INT)                 fr x width after      fixed (REAL)
       fi n width after          fixed (INT via double)      fl x width after exp  float (REAL)
       fli n width after exp     float (INT)                 pi n                  print (INT)
       pr x                      print (REAL)                wr x width            whole (REAL)
       pin n long ll             printInt n long ll          prn x long ll         printReal x long ll
       fil n width after         fixedLongInt                pb v width            printBits
       flf x width after exp frmt  floatReal with frmt       flif n width after exp frmt  floatInt with frmt
       sf x width after          subFixed of |x|             st x before after q   standardize |x| (result as subFixed, and q)
       widths long ll            int/real/exp/bits widths and max int of a length
       llp n                     llDigitsOfPrecision n

   Reals are written as decimal literals with an optional leading '-'. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "fmt.h"

/* Main.pf: parse a literal with an optional leading minus. */
static double pf(const char* s) {
    if (s[0] == '-') return -a68_fmt_parse_float(s + 1, strlen(s + 1));
    return a68_fmt_parse_float(s, strlen(s));
}

static int64_t pi64(const char* s) { return strtoll(s, NULL, 10); }

/* the integral cases take an arbitrary-length decimal integer as their first argument */
static a68_big* bign(const char* s) { return big_from_dec(s, strlen(s)); }

/* Main.fmtLine */
static char* fmt_line(int argc, char** argv) {
    const char* k = argc > 0 ? argv[0] : "";
    a68_big* n = NULL;
    char* r = NULL;
    int integral = !strcmp(k, "w") || !strcmp(k, "fi") || !strcmp(k, "fli") || !strcmp(k, "pi")
                || !strcmp(k, "pin") || !strcmp(k, "fil") || !strcmp(k, "pb") || !strcmp(k, "flif");
    if (integral && argc >= 2) n = bign(argv[1]);
    if (!strcmp(k, "w") && argc == 3) r = a68_fmt_whole_int(n, pi64(argv[2]));
    else if (!strcmp(k, "fr") && argc == 4) r = a68_fmt_fixed_real(pf(argv[1]), pi64(argv[2]), pi64(argv[3]));
    else if (!strcmp(k, "fi") && argc == 4) r = a68_fmt_fixed_int(n, pi64(argv[2]), pi64(argv[3]), 0);
    else if (!strcmp(k, "fl") && argc == 5) r = a68_fmt_float_real(pf(argv[1]), pi64(argv[2]), pi64(argv[3]), pi64(argv[4]), 1);
    else if (!strcmp(k, "fli") && argc == 5) r = a68_fmt_float_int(n, pi64(argv[2]), pi64(argv[3]), pi64(argv[4]), 1);
    else if (!strcmp(k, "pi") && argc == 2) r = a68_fmt_print_int(n, 0, 12);
    else if (!strcmp(k, "pr") && argc == 2) r = a68_fmt_print_real(pf(argv[1]), 0, 12);
    else if (!strcmp(k, "wr") && argc == 3) r = a68_fmt_whole_real(pf(argv[1]), pi64(argv[2]));
    else if (!strcmp(k, "pin") && argc == 4) r = a68_fmt_print_int(n, pi64(argv[2]), (int)pi64(argv[3]));
    else if (!strcmp(k, "prn") && argc == 4) r = a68_fmt_print_real(pf(argv[1]), pi64(argv[2]), (int)pi64(argv[3]));
    else if (!strcmp(k, "fil") && argc == 4) r = a68_fmt_fixed_int(n, pi64(argv[2]), pi64(argv[3]), 1);
    else if (!strcmp(k, "pb") && argc == 3) r = a68_fmt_print_bits(n, (int)pi64(argv[2]));
    else if (!strcmp(k, "flf") && argc == 6) r = a68_fmt_float_real(pf(argv[1]), pi64(argv[2]), pi64(argv[3]), pi64(argv[4]), pi64(argv[5]));
    else if (!strcmp(k, "flif") && argc == 6) r = a68_fmt_float_int(n, pi64(argv[2]), pi64(argv[3]), pi64(argv[4]), pi64(argv[5]));
    else if (!strcmp(k, "sf") && argc == 4) {
        /* subFixed on |x| */
        a68_dec d;
        a68_real_to_dec(pf(argv[1]), &d);
        r = a68_fmt_sub_fixed(d, pi64(argv[2]), pi64(argv[3]));
        a68_dec_free(&d);
    }
    else if (!strcmp(k, "st") && argc == 5) {
        /* standardize |x| before after q, shown as subFixed of the result and the new q */
        a68_dec d, z;
        int64_t q, before = pi64(argv[2]), after = pi64(argv[3]);
        char *s, *qs;
        a68_big* qb;
        a68_real_to_dec(pf(argv[1]), &d);
        a68_fmt_standardize(d, before, after, pi64(argv[4]), &z, &q);
        s = a68_fmt_sub_fixed(z, (before > 0 ? before : 0) + (after > 0 ? after : 0) + 2, after);
        qb = big_from_i64(q);
        qs = big_to_dec(qb);
        size_t cap = strlen(s) + strlen(qs) + 2;
        r = malloc(cap);
        snprintf(r, cap, "%s %s", s, qs);
        free(s); free(qs); big_free(qb);
        a68_dec_free(&z); a68_dec_free(&d);
    }
    else if (!strcmp(k, "widths") && argc == 3) {
        /* intWidthOf realWidthOf expWidthOf bitsWidthOfLen maxIntOf */
        int64_t l = pi64(argv[1]);
        int ll = (int)pi64(argv[2]);
        a68_big* mx = a68_fmt_max_int(l, ll);
        char* ms = big_to_dec(mx);
        size_t cap = strlen(ms) + 64;
        r = malloc(cap);
        snprintf(r, cap, "%d %d %d %d %s", a68_fmt_int_width(l, ll), a68_fmt_real_width(l, ll),
                 a68_fmt_exp_width(l), a68_fmt_bits_width(l, ll), ms);
        free(ms); big_free(mx);
    }
    else if (!strcmp(k, "llp") && argc == 2) {
        r = malloc(32);
        snprintf(r, 32, "%d", a68_fmt_ll_digits_of_precision((int)pi64(argv[1])));
    }
    big_free(n);
    if (!r) { r = malloc(2); r[0] = '?'; r[1] = 0; }
    return r;
}

int main(int argc, char** argv) {
    FILE* f = argc > 1 ? fopen(argv[1], "r") : stdin;
    char line[4096];
    if (!f) { perror(argv[1]); return 1; }
    while (fgets(line, sizeof line, f)) {
        char* toks[16];
        int nt = 0;
        char* p = strtok(line, " \t\r\n");
        while (p && nt < 16) { toks[nt++] = p; p = strtok(NULL, " \t\r\n"); }
        if (nt == 0) continue;
        char* r = fmt_line(nt, toks);
        puts(r);
        free(r);
    }
    if (f != stdin) fclose(f);
    return 0;
}
