/* The standard prelude of compiled programs: `Interp.callBuiltin` in C.  Each arm
   transcribes the arm of the same name; a68g's routine is named where the Lean names it. */
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
#include <time.h>

/* ---------------------------------------------------------------- names */

enum {
  B_UNKNOWN = 0, B_PRINT, B_PUT, B_PRINTF, B_PUTF, B_READ, B_READF, B_GET, B_GETF,
  B_NEWLINE, B_NEWPAGE, B_SPACE, B_BACKSPACE, B_OPEN, B_ESTABLISH, B_CREATE, B_ASSOCIATE,
  B_CLOSE, B_SCRATCH, B_RESET, B_MAKETERM, B_ONFILEEND, B_ONVALUEERROR, B_ONLINEEND,
  B_WHOLE, B_FIXED, B_FLOAT, B_REAL, B_CHARINSTRING, B_LASTCHARINSTRING, B_STRINGINSTRING,
  B_TOUPPER, B_TOLOWER, B_ISUPPER, B_ISLOWER, B_ISDIGIT, B_ISALPHA, B_ISALNUM, B_ISSPACE,
  B_ISPUNCT, B_ISPRINT, B_ISGRAPH, B_ISCNTRL, B_ISXDIGIT, B_ODD, B_ABS, B_STOP, B_RANDOM,
  B_FIRSTRANDOM, B_RANDOMINT, B_GC_SWEEP, B_GC_COLLECTIONS, B_GC_GARBAGE, B_GC_REFUSED,
  B_GC_SECONDS, B_CLOCK, B_COMPLEXFN, B_LONGARCTAN2, B_ARCTAN2, B_READINT, B_READREAL,
  B_READSTRING, B_READCHAR, B_READBOOL, B_PRINTINT, B_PRINTREAL, B_PRINTSTRING, B_PRINTCHAR,
  B_PRINTBOOL, B_NOOP1, B_ARGC, B_ARGV, B_NOOP2, B_BITSPACK, B_BYTESPACK, B_LONGBYTESPACK,
  B_EVALUATE, B_ABEND, B_SYSTEM, B_FORK, B_GETENV, B_EXECVE, B_EXECVECHILD, B_EXECVECHILDPIPE,
  B_EXECVEOUTPUT, B_CREATEPIPE, B_WAITPID, B_UTCTIME, B_LOCALTIME, B_GETDIRECTORY, B_FILEIS,
  B_FILEMODE, B_GREPINSTRING, B_GREPINSUBSTRING, B_SUBINSTRING, B_STRERROR, B_ERRNO,
  B_RESETERRNO, B_GETPWD, B_SETPWD, B_REALPATH, B_SLEEP, B_ROWS, B_COLUMNS, B_WALLCLOCK,
  B_NAN, B_INF, B_MINUSINF, B_ISFINITE, B_ISINF, B_ISPLUSINF, B_ISMINUSINF, B_ISNAN,
  B_RESETPOSSIBLE, B_GETPOSSIBLE, B_PUTPOSSIBLE, B_FALSE, B_TRUE, B_IDF, B_TERM, B_EOF, B_EOLN,
  B_SET, B_PUTS, B_STRING, B_PUTSF, B_STRINGF, B_GETS, B_GETSF, B_READLINE, B_GETBIN, B_PUTBIN,
  B_READBIN, B_PRINTBIN, B_LONGRANDOM
};

typedef struct { const char* name; int id; int sub; } bname;

/* `sub` distinguishes the members of a family (the complex function, the file kind …) */
static const bname names[] = {
  {"print", B_PRINT, 0}, {"write", B_PRINT, 0}, {"put", B_PUT, 0}, {"printf", B_PRINTF, 0}, {"writef", B_PRINTF, 0},
  {"putf", B_PUTF, 0}, {"read", B_READ, 0}, {"readf", B_READF, 0}, {"get", B_GET, 0}, {"getf", B_GETF, 0},
  {"newline", B_NEWLINE, 0}, {"newpage", B_NEWPAGE, 0}, {"space", B_SPACE, 0}, {"backspace", B_BACKSPACE, 0},
  {"open", B_OPEN, 0}, {"append", B_OPEN, 0}, {"establish", B_ESTABLISH, 0}, {"create", B_CREATE, 0},
  {"associate", B_ASSOCIATE, 0}, {"close", B_CLOSE, 0}, {"lock", B_CLOSE, 0}, {"scratch", B_SCRATCH, 0},
  {"erase", B_SCRATCH, 0}, {"rewind", B_RESET, 0}, {"reset", B_RESET, 0}, {"maketerm", B_MAKETERM, 0},
  {"onlogicalfileend", B_ONFILEEND, 0}, {"onfileend", B_ONFILEEND, 0}, {"onphysicalfileend", B_ONFILEEND, 0},
  {"onvalueerror", B_ONVALUEERROR, 0}, {"onlineend", B_ONLINEEND, 0},
  {"whole", B_WHOLE, 0}, {"fixed", B_FIXED, 0}, {"float", B_FLOAT, 0}, {"real", B_REAL, 0},
  {"charinstring", B_CHARINSTRING, 0}, {"lastcharinstring", B_LASTCHARINSTRING, 0}, {"stringinstring", B_STRINGINSTRING, 0},
  {"toupper", B_TOUPPER, 0}, {"tolower", B_TOLOWER, 0}, {"isupper", B_ISUPPER, 0}, {"islower", B_ISLOWER, 0},
  {"isdigit", B_ISDIGIT, 0}, {"isalpha", B_ISALPHA, 0}, {"isalnum", B_ISALNUM, 0}, {"isspace", B_ISSPACE, 0},
  {"ispunct", B_ISPUNCT, 0}, {"isprint", B_ISPRINT, 0}, {"isgraph", B_ISGRAPH, 0}, {"iscntrl", B_ISCNTRL, 0},
  {"isxdigit", B_ISXDIGIT, 0}, {"odd", B_ODD, 0}, {"abs", B_ABS, 0}, {"stop", B_STOP, 0},
  {"random", B_RANDOM, 0}, {"longrandom", B_RANDOM, 0}, {"nextrandom", B_RANDOM, 0},
  {"firstrandom", B_FIRSTRANDOM, 0}, {"randomint", B_RANDOMINT, 0},
  {"sweepheap", B_GC_SWEEP, 0}, {"gcheap", B_GC_SWEEP, 0}, {"preemptivegc", B_GC_SWEEP, 0},
  {"preemptivesweep", B_GC_SWEEP, 0}, {"preemptivesweepheap", B_GC_SWEEP, 0},
  {"collections", B_GC_COLLECTIONS, 0}, {"sweeps", B_GC_COLLECTIONS, 0}, {"garbagecollections", B_GC_COLLECTIONS, 0},
  {"garbage", B_GC_GARBAGE, 0}, {"garbagefreed", B_GC_GARBAGE, 0},
  {"garbagerefused", B_GC_REFUSED, 0}, {"sweepsrefused", B_GC_REFUSED, 0},
  {"garbageseconds", B_GC_SECONDS, 0}, {"collectseconds", B_GC_SECONDS, 0},
  {"clock", B_CLOCK, 0}, {"seconds", B_CLOCK, 0}, {"cputime", B_CLOCK, 0},
  {"complexsqrt", B_COMPLEXFN, 0}, {"csqrt", B_COMPLEXFN, 0}, {"complexexp", B_COMPLEXFN, 1}, {"cexp", B_COMPLEXFN, 1},
  {"complexln", B_COMPLEXFN, 2}, {"cln", B_COMPLEXFN, 2}, {"complexsin", B_COMPLEXFN, 3}, {"csin", B_COMPLEXFN, 3},
  {"complexcos", B_COMPLEXFN, 4}, {"ccos", B_COMPLEXFN, 4}, {"complextan", B_COMPLEXFN, 5}, {"ctan", B_COMPLEXFN, 5},
  {"complexarcsin", B_COMPLEXFN, 6}, {"casin", B_COMPLEXFN, 6}, {"complexarccos", B_COMPLEXFN, 7}, {"cacos", B_COMPLEXFN, 7},
  {"complexarctan", B_COMPLEXFN, 8}, {"catan", B_COMPLEXFN, 8}, {"complexsinh", B_COMPLEXFN, 9}, {"csinh", B_COMPLEXFN, 9},
  {"complexcosh", B_COMPLEXFN, 10}, {"ccosh", B_COMPLEXFN, 10}, {"complextanh", B_COMPLEXFN, 11}, {"ctanh", B_COMPLEXFN, 11},
  {"complexarcsinh", B_COMPLEXFN, 12}, {"casinh", B_COMPLEXFN, 12}, {"complexarccosh", B_COMPLEXFN, 13}, {"cacosh", B_COMPLEXFN, 13},
  {"complexarctanh", B_COMPLEXFN, 14}, {"catanh", B_COMPLEXFN, 14},
  {"longarctan2", B_LONGARCTAN2, 0}, {"longlongarctan2", B_LONGARCTAN2, 0}, {"longarctan2dg", B_LONGARCTAN2, 0}, {"longlongarctan2dg", B_LONGARCTAN2, 0},
  {"arctan2", B_ARCTAN2, 0}, {"atan2", B_ARCTAN2, 0},
  {"readint", B_READINT, 0}, {"readreal", B_READREAL, 0}, {"readstring", B_READSTRING, 0}, {"readchar", B_READCHAR, 0},
  {"readbool", B_READBOOL, 0}, {"printint", B_PRINTINT, 0}, {"printreal", B_PRINTREAL, 0}, {"printstring", B_PRINTSTRING, 0},
  {"printchar", B_PRINTCHAR, 0}, {"printbool", B_PRINTBOOL, 0}, {"setexitcode", B_NOOP1, 0}, {"setexit", B_NOOP1, 0},
  {"argc", B_ARGC, 0}, {"argv", B_ARGV, 0},
  {"onpageend", B_NOOP2, 0}, {"onformatend", B_NOOP2, 0}, {"onformaterror", B_NOOP2, 0}, {"ontransputerror", B_NOOP2, 0},
  {"onopenerror", B_NOOP2, 0}, {"makeconv", B_NOOP1, 0},
  {"bitspack", B_BITSPACK, 0}, {"bytespack", B_BYTESPACK, 0}, {"longbytespack", B_LONGBYTESPACK, 0},
  {"evaluate", B_EVALUATE, 0}, {"abend", B_ABEND, 0}, {"system", B_SYSTEM, 0}, {"fork", B_FORK, 0}, {"getenv", B_GETENV, 0},
  {"execve", B_EXECVE, 0}, {"exec", B_EXECVE, 0}, {"execvechild", B_EXECVECHILD, 0}, {"execsub", B_EXECVECHILD, 0},
  {"execvechildpipe", B_EXECVECHILDPIPE, 0}, {"execsubpipeline", B_EXECVECHILDPIPE, 0},
  {"execveoutput", B_EXECVEOUTPUT, 0}, {"execsuboutput", B_EXECVEOUTPUT, 0}, {"createpipe", B_CREATEPIPE, 0},
  {"waitpid", B_WAITPID, 0}, {"utctime", B_UTCTIME, 0}, {"localtime", B_LOCALTIME, 0}, {"getdirectory", B_GETDIRECTORY, 0},
  {"fileisdirectory", B_FILEIS, 0040000}, {"fileisregular", B_FILEIS, 0100000}, {"fileisblockdevice", B_FILEIS, 0060000},
  {"fileischardevice", B_FILEIS, 0020000}, {"fileisfifo", B_FILEIS, 0010000}, {"fileislink", B_FILEIS, 0120000},
  {"filemode", B_FILEMODE, 0}, {"grepinstring", B_GREPINSTRING, 0}, {"grepinsubstring", B_GREPINSUBSTRING, 0},
  {"subinstring", B_SUBINSTRING, 0}, {"strerror", B_STRERROR, 0}, {"errno", B_ERRNO, 0}, {"reseterrno", B_RESETERRNO, 0},
  {"getpwd", B_GETPWD, 0}, {"setpwd", B_SETPWD, 0}, {"realpath", B_REALPATH, 0}, {"sleep", B_SLEEP, 0},
  {"rows", B_ROWS, 0}, {"columns", B_COLUMNS, 0}, {"a68gargc", B_ARGC, 0}, {"a68gargv", B_ARGV, 0},
  {"wallclock", B_WALLCLOCK, 0}, {"wallseconds", B_WALLCLOCK, 0}, {"walltime", B_WALLCLOCK, 0},
  {"nan", B_NAN, 0}, {"inf", B_INF, 0}, {"infinity", B_INF, 0}, {"plusinf", B_INF, 0}, {"plusinfinity", B_INF, 0},
  {"minusinf", B_MINUSINF, 0}, {"minusinfinity", B_MINUSINF, 0},
  {"isfinite", B_ISFINITE, 0}, {"isinf", B_ISINF, 0}, {"isinfinite", B_ISINF, 0}, {"isplusinf", B_ISPLUSINF, 0},
  {"isminusinf", B_ISMINUSINF, 0}, {"isnan", B_ISNAN, 0},
  {"resetpossible", B_RESETPOSSIBLE, 0}, {"rewindpossible", B_RESETPOSSIBLE, 0}, {"setpossible", B_RESETPOSSIBLE, 0},
  {"binpossible", B_RESETPOSSIBLE, 0}, {"getpossible", B_GETPOSSIBLE, 0}, {"putpossible", B_PUTPOSSIBLE, 0},
  {"reidfpossible", B_FALSE, 0}, {"drawpossible", B_FALSE, 0}, {"compressible", B_TRUE, 0},
  {"idf", B_IDF, 0}, {"term", B_TERM, 0}, {"eof", B_EOF, 0}, {"endoffile", B_EOF, 0}, {"eoln", B_EOLN, 0}, {"endofline", B_EOLN, 0},
  {"set", B_SET, 0}, {"seek", B_SET, 0},
  {"puts", B_PUTS, 0}, {"string", B_STRING, 0}, {"putsf", B_PUTSF, 0}, {"stringf", B_STRINGF, 0},
  {"gets", B_GETS, 0}, {"getsf", B_GETSF, 0}, {"readline", B_READLINE, 0},
  {"getbin", B_GETBIN, 0}, {"putbin", B_PUTBIN, 0}, {"readbin", B_READBIN, 0}, {"printbin", B_PRINTBIN, 0},
  {"writebin", B_PRINTBIN, 0},
  {"longnextrandom", B_LONGRANDOM, 1}, {"longlongnextrandom", B_LONGRANDOM, 2}, {"longlongrandom", B_LONGRANDOM, 2},
};

/* the resolved id of each string-table entry, found once */
static int16_t* id_cache = NULL;
static int16_t* sub_cache = NULL;
static size_t cache_n = 0;

static int resolve(uint32_t si, int* sub) {
  if (si >= cache_n) {
    size_t nn = (size_t) si + 1024;
    id_cache = (int16_t*) realloc(id_cache, nn * sizeof(int16_t));
    sub_cache = (int16_t*) realloc(sub_cache, nn * sizeof(int16_t));
    if (!id_cache || !sub_cache) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
    for (size_t i = cache_n; i < nn; i++) id_cache[i] = -1;
    cache_n = nn;
  }
  if (id_cache[si] < 0) {
    id_cache[si] = B_UNKNOWN; sub_cache[si] = 0;
    for (size_t i = 0; i < sizeof names / sizeof names[0]; i++)
      if (strcmp(names[i].name, strtab[si]) == 0) { id_cache[si] = (int16_t) names[i].id; sub_cache[si] = (int16_t) names[i].sub; break; }
  }
  *sub = sub_cache[si];
  return id_cache[si];
}

/* ---------------------------------------------------------------- helpers */

static a68_val vvoid(void) { return mk_tag(T_VOID); }

static a68_val str_val(const char* s) { return of_string(s, strlen(s)); }

/* a NUL-terminated copy of a string value */
static char* cstr_of(a68_val v) { int64_t n; return (char*) str_of(v, &n); }

/* the resolved mode of a united value; ~0u when the value is not a union */
static uint32_t union_mode(a68_val v) { return v.tag == T_UNION ? mode_resolve(v.aux) : ~0u; }
static a68_val union_inner(a68_val v) { return ((a68_slots*) v.v.p)->s[0]; }

/* the lower bound of a row */
static int64_t row_lwb(a68_val r) {
  if (r.tag == T_UNDEF) die("attempt to use an uninitialised row");
  if (r.tag != T_ROW) die("internal: row expected");
  return ((a68_rowd*) r.v.p)->dim[0].l;
}

static a68_rowd* row_of(a68_val r) {
  if (r.tag == T_UNDEF) die("attempt to use an uninitialised row");
  if (r.tag != T_ROW) die("internal: row expected");
  return (a68_rowd*) r.v.p;
}

static a68_val elem(a68_rowd* d, int64_t i) { return rowd_get(d, row_store_index(d, i)); }

static int32_t signed32(uint32_t u) { return (int32_t) u; }

/* ---------------------------------------------------------------- random numbers (taus113, as in a68g / GSL) */

static uint32_t z1, z2, z3, z4;

static uint32_t taus_get(void) {
  uint32_t b1 = (((z1 << 6) ^ z1) >> 13);
  z1 = (((z1 & 4294967294u) << 18) ^ b1);
  uint32_t b2 = (((z2 << 2) ^ z2) >> 27);
  z2 = (((z2 & 4294967288u) << 2) ^ b2);
  uint32_t b3 = (((z3 << 13) ^ z3) >> 21);
  z3 = (((z3 & 4294967280u) << 7) ^ b3);
  uint32_t b4 = (((z4 << 3) ^ z4) >> 12);
  z4 = (((z4 & 4294967168u) << 13) ^ b4);
  return z1 ^ z2 ^ z3 ^ z4;
}

void taus_seed(uint32_t seed) {
  uint32_t s = seed == 0 ? 1 : seed;
  z1 = 69069u * s; if (z1 < 2) z1 += 2;
  z2 = 69069u * z1; if (z2 < 8) z2 += 8;
  z3 = 69069u * z2; if (z3 < 16) z3 += 16;
  z4 = 69069u * z3; if (z4 < 128) z4 += 128;
  for (int i = 0; i < 10; i++) taus_get();
}

double next_random(void) {
  if (z1 == 0 && z2 == 0 && z3 == 0 && z4 == 0) taus_seed(1);
  return (double) taus_get() / 4294967296.0;
}

/* ---------------------------------------------------------------- the collector's counters (rt.c) */

double a68_gc_query(uint32_t what);

/* ---------------------------------------------------------------- mathematics */

static const double pi_over_180 = 0.0174532925199432957692369076848861271344287188854172545609719144;
static const double d180_over_pi = 57.2957795130823208767981548141051703324054724665643215491602438;

/* a68g `a68g_sinpi_real` and `a68g_cospi_real`: exact at the multiples of a half */
static double sin_pi(double x) {
  x = fmod(x, 2.0);
  x = x <= -1.0 ? x + 2.0 : x > 1.0 ? x - 2.0 : x;
  if (x == 0.0 || x == 1.0) return 0.0;
  if (x == 0.5) return 1.0;
  if (x == -0.5) return -1.0;
  return sin(3.141592653589793 * x);
}

static double cos_pi(double x) {
  x = fmod(fabs(x), 2.0);
  if (x == 0.5 || x == 1.5) return 0.0;
  if (x == 0.0) return 1.0;
  if (x == 1.0) return -1.0;
  return cos(3.141592653589793 * x);
}

static int name_in(const char* n, const char* const* list) {
  for (size_t i = 0; list[i]; i++) if (strcmp(n, list[i]) == 0) return 1;
  return 0;
}

#define NOT_NUMBER() die("REAL value is not a number")
#define MATH_EXC() die("math exception")

/* `Interp.mathFn`; 0 when the name is not one of these */
static int math_fn(const char* n, double x, double* out) {
  static const char* const sqrts[] = {"sqrt", "longsqrt", "longlongsqrt", NULL};
  static const char* const exps[] = {"exp", "longexp", "longlongexp", NULL};
  static const char* const lns[] = {"ln", "longln", "longlongln", NULL};
  static const char* const logs[] = {"log", "longlog", "log10", NULL};
  static const char* const sins[] = {"sin", "longsin", "longlongsin", NULL};
  static const char* const coss[] = {"cos", "longcos", "longlongcos", NULL};
  static const char* const tans[] = {"tan", "longtan", "longlongtan", NULL};
  static const char* const asins[] = {"arcsin", "asin", "longarcsin", "longlongarcsin", NULL};
  static const char* const acoss[] = {"arccos", "acos", "longarccos", "longlongarccos", NULL};
  static const char* const atans[] = {"arctan", "atan", "longarctan", "longlongarctan", NULL};
  double r;
  if (name_in(n, sqrts)) { if (x < 0) NOT_NUMBER(); r = sqrt(x); }
  else if (name_in(n, exps)) r = exp(x);   /* a68g: overflow yields infinity silently */
  else if (name_in(n, lns)) { if (x < 0) NOT_NUMBER(); r = log(x); }
  else if (name_in(n, logs)) { if (x < 0) NOT_NUMBER(); r = log10(x); }
  else if (strcmp(n, "log2") == 0) r = log2(x);
  else if (strcmp(n, "exp2") == 0) r = exp2(x);
  else if (name_in(n, sins)) r = sin(x);
  else if (name_in(n, coss)) r = cos(x);
  else if (name_in(n, tans)) r = tan(x);
  else if (name_in(n, asins)) { if (x < -1 || x > 1) NOT_NUMBER(); r = asin(x); }
  else if (name_in(n, acoss)) { if (x < -1 || x > 1) NOT_NUMBER(); r = acos(x); }
  else if (name_in(n, atans)) r = atan(x);
  else if (strcmp(n, "sinh") == 0) r = sinh(x);
  else if (strcmp(n, "cosh") == 0) r = cosh(x);
  else if (strcmp(n, "tanh") == 0) r = tanh(x);
  else if (strcmp(n, "arcsinh") == 0) r = asinh(x);
  else if (strcmp(n, "arccosh") == 0) r = acosh(x);
  else if (strcmp(n, "arctanh") == 0) r = atanh(x);
  else if (strcmp(n, "cbrt") == 0 || strcmp(n, "curt") == 0) r = cbrt(x);
  else if (strcmp(n, "gamma") == 0) r = tgamma(x);
  else if (strcmp(n, "lngamma") == 0) r = lgamma(x);
  else if (strcmp(n, "erf") == 0) r = erf(x);
  else if (strcmp(n, "erfc") == 0) r = erfc(x);
  else if (strcmp(n, "ln1p") == 0) r = log1p(x);
  /* a68g single-math.c, with its constants for pi / 180 and 180 / pi */
  else if (strcmp(n, "sindg") == 0) r = sin(x * pi_over_180);
  else if (strcmp(n, "cosdg") == 0) r = cos(x * pi_over_180);
  else if (strcmp(n, "tandg") == 0) r = tan(x * pi_over_180);
  else if (strcmp(n, "arcsindg") == 0 || strcmp(n, "asindg") == 0) r = asin(x) * d180_over_pi;
  else if (strcmp(n, "arccosdg") == 0 || strcmp(n, "acosdg") == 0) r = acos(x) * d180_over_pi;
  else if (strcmp(n, "arctandg") == 0 || strcmp(n, "atandg") == 0) r = atan(x) * d180_over_pi;
  else if (strcmp(n, "cot") == 0) { double z = sin(x); if (z == 0.0) MATH_EXC(); r = cos(x) / z; }
  else if (strcmp(n, "sec") == 0) { double z = cos(x); if (z == 0.0) MATH_EXC(); r = 1.0 / z; }
  else if (strcmp(n, "csc") == 0) { double z = sin(x); if (z == 0.0) MATH_EXC(); r = 1.0 / z; }
  else if (strcmp(n, "cotdg") == 0) { double z = sin(x * pi_over_180); if (z == 0.0) MATH_EXC(); r = cos(x * pi_over_180) / z; }
  else if (strcmp(n, "secdg") == 0) { double z = cos(x * pi_over_180); if (z == 0.0) MATH_EXC(); r = 1.0 / z; }
  else if (strcmp(n, "cscdg") == 0) { double z = sin(x * pi_over_180); if (z == 0.0) MATH_EXC(); r = 1.0 / z; }
  else if (strcmp(n, "cas") == 0) r = cos(x) + sin(x);
  else if (strcmp(n, "sinpi") == 0) r = sin_pi(x);
  else if (strcmp(n, "cospi") == 0) r = cos_pi(x);
  else if (strcmp(n, "tanpi") == 0 || strcmp(n, "cotpi") == 0) {
    double y = fmod(x, 1.0);
    y = y <= -0.5 ? y + 1.0 : y > 0.5 ? y - 1.0 : y;
    if (n[0] == 't') {
      if (y == 0.5) MATH_EXC();
      r = y == -0.25 ? -1.0 : y == 0.0 ? 0.0 : y == 0.25 ? 1.0 : sin_pi(y) / cos_pi(y);
    } else {
      if (y == 0.0) MATH_EXC();
      r = y == -0.25 ? -1.0 : y == 0.25 ? 1.0 : y == 0.5 ? 0.0 : cos_pi(y) / sin_pi(y);
    }
  }
  else return 0;
  *out = check_real(r);
  return 1;
}

static const char* const math_names[] = {
  "sqrt","exp","ln","log","log10","log2","exp2","sin","cos","tan","arcsin","arccos","arctan",
  "asin","acos","atan","sinh","cosh","tanh","arcsinh","arccosh","arctanh","cbrt","curt",
  "longsqrt","longexp","longln","longlog","longsin","longcos","longtan","longarcsin","longarccos",
  "longarctan","longlongsqrt","longlongexp","longlongln","longlongsin","longlongcos","longlongtan",
  "longlongarctan","longlongarcsin","longlongarccos","gamma","lngamma","erf","erfc","ln1p",
  "sindg","cosdg","tandg","arcsindg","asindg","arccosdg","acosdg","arctandg","atandg",
  "cot","sec","csc","cotdg","secdg","cscdg","cas","sinpi","cospi","tanpi","cotpi", NULL };

/* ---------------------------------------------------------------- pieces of arms */

/* the program, arguments and environment of an `execve` call; a68g refuses an argument
   row whose strings are all empty (`Interp.execArgs`); vectors of the non-empty strings */
static char** cvec(a68_val row, int* any) {
  a68_rowd* d = row_of(row);
  int64_t n = row_count(d);
  char** v = (char**) xmalloc((size_t) (n + 1) * sizeof(char*));
  size_t k = 0;
  *any = 0;
  for (int64_t i = 0; i < n; i++) {
    char* s = cstr_of(elem(d, i));
    if (s[0]) { v[k++] = s; *any = 1; } else free(s);
  }
  v[k] = NULL;
  return v;
}

static void free_cvec(char** v) { for (size_t k = 0; v[k]; k++) free(v[k]); free(v); }

static void exec_args(a68_val p, a68_val as, a68_val en, char** prog, char*** av, char*** ev) {
  *prog = cstr_of(p);
  int any_a, any_e;
  *av = cvec(as, &any_a);
  *ev = cvec(en, &any_e);
  if (!any_a) die("empty argument row");
}

/* a fresh cell holding a value, as a name (`.ref (← alloc v) []`) */
static a68_val cell_ref(a68_val v) {
  a68_slots* s = slots_alloc(1);
  s->s[0] = v;
  return mk_ptr(T_REF, (a68_obj*) s, 0);
}

static a68_val file_val(uint32_t fid) { a68_val v = mk_tag(T_FILE); v.aux = fid; return v; }

static a68_val struct3(a68_val a, a68_val b, a68_val c) {
  a68_slots* s = slots_alloc(3);
  s->s[0] = a; s->s[1] = b; s->s[2] = c;
  return mk_ptr(T_STRUCT, (a68_obj*) s, 0);
}

typedef struct { a68_val row; int formatted; } sf_ctx;
static void sf_act(uint32_t fid, void* ctx) {
  sf_ctx* c = (sf_ctx*) ctx;
  if (c->formatted) printf_items(fid, c->row); else print_items(fid, c->row);
}

/* a value formatted by `whole`, `fixed`, `float` and `real`: which representation the
   united argument holds */
enum { NUM_INT, NUM_LONG_INT, NUM_MP, NUM_REAL };
static int number_kind(a68_val x, a68_val* v, int64_t* longness, const char* what) {
  uint32_t m = union_mode(x);
  if (m == ~0u) die(what);
  const a68_mode* p = mode_at(m);
  *v = union_inner(x);
  *longness = p->len;
  if (v->tag == T_UNDEF) die("attempt to use an uninitialised value");
  if (p->k == M_INT && (v->tag == T_INT || v->tag == T_BIGINT)) return p->len <= 0 ? NUM_INT : NUM_LONG_INT;
  if (p->k == M_REAL && v->tag == T_MP) return NUM_MP;
  if (p->k == M_REAL && v->tag == T_REAL) { check_real(v->v.r); return NUM_REAL; }
  die(what);
}

static a68_val take_str(char* s) { a68_val v = str_val(s); free(s); return v; }

static a68_big* big_of(a68_val v) {
  if (v.tag == T_INT) return big_from_i64(v.v.i);
  a68_leaf* l = (a68_leaf*) v.v.p;
  return big_from_dec((const char*) l->d, l->h.n);
}

static int64_t clock_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (int64_t) ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

static int chan_in(uint32_t c, int a, int b, int d) { return c == (uint32_t) a || c == (uint32_t) b || c == (uint32_t) d; }

/* ---------------------------------------------------------------- the dispatch */

__attribute__((noreturn)) static void unsupported(const char* name, uint32_t nargs) {
  char buf[256];
  snprintf(buf, sizeof buf, "unsupported standard procedure %s/%u", name, (unsigned) nargs);
  die(buf);
}

static void builtin(uint32_t si, int id, int sub, a68_val* a, uint32_t n, a68_val* res);

void call_builtin(uint32_t si, uint32_t nargs, a68_val* res) {
  int sub;
  int id = resolve(si, &sub);
  a68_val a[8];
  if (nargs > 8) die("internal: too many arguments to a standard procedure");
  for (uint32_t i = 0; i < nargs; i++) a[i] = stack[sp - nargs + i];
  *res = mk_tag(T_UNDEF);
  io_catch c;
  io_catch_push(&c);
  int kind = setjmp(c.jb);
  if (kind == 0) {
    builtin(si, id, sub, a, nargs, res);
    io_catch_pop(&c);
  } else {
    /* a jump raised by an event routine or a format hole, or a mended file end escaping
       the call: `Runtime.run` gives `.undef`, which nothing looks at */
    *res = mk_tag(T_UNDEF);
  }
}

#define ARGS(k) if (n != (k)) unsupported(name, n)

static void builtin(uint32_t si, int id, int sub, a68_val* a, uint32_t n, a68_val* res) {
  const char* name = strtab[si];
  switch (id) {
    case B_PRINT: ARGS(1); print_items(0, a[0]); *res = vvoid(); return;
    case B_PUT: ARGS(2); print_items(file_id_of(a[0]), a[1]); *res = vvoid(); return;
    case B_PRINTF: ARGS(1); printf_items(0, a[0]); *res = vvoid(); return;
    case B_PUTF: ARGS(2); printf_items(file_id_of(a[0]), a[1]); *res = vvoid(); return;
    case B_READ: ARGS(1); get_items(1, a[0]); *res = vvoid(); return;
    case B_READF: ARGS(1); getf_items(1, a[0]); *res = vvoid(); return;
    case B_GET: ARGS(2); get_items(file_id_of(a[0]), a[1]); *res = vvoid(); return;
    case B_GETF: ARGS(2); getf_items(file_id_of(a[0]), a[1]); *res = vvoid(); return;
    case B_NEWLINE: case B_NEWPAGE: case B_SPACE: case B_BACKSPACE: {
      ARGS(1);
      uint32_t fid = file_id_of(a[0]);
      a68_file* fs = file_get(fid);
      if (fid == 1 || (fs->reading && !fs->writing)) {
        if (id == B_NEWLINE || id == B_NEWPAGE) skip_line(fid); else read_char(fid);
      } else file_out(fid, id == B_NEWLINE ? "\n" : id == B_NEWPAGE ? "\x0c" : id == B_SPACE ? " " : "\x08", 1);
      *res = vvoid();
      return;
    }
    case B_OPEN: {
      /* a68g opens the file when it is first used; the result says whether it is a regular
         file (0), and otherwise gives the error number */
      ARGS(3);
      char* path = cstr_of(a[1]);
      int chan = a[2].tag == T_INT ? (int) a[2].v.i : 3;
      uint32_t status = os_open_status(path);
      a68_file f = file_default();
      f.name = path; f.loaded = 1; f.ondisk = 1; f.channel = chan;
      if (status == 0) {
        os_bytes b;
        if (os_read_file(path, &b) == 0) { f.buf = b.p; f.len = b.n; f.cap = b.n; }
      }
      file_new(a[0], f);
      *res = mk_int(signed32(status));
      return;
    }
    case B_ESTABLISH: {
      ARGS(6);
      a68_file f = file_default();
      f.name = cstr_of(a[1]); f.loaded = 1; f.ondisk = 1; f.writing = 1;
      f.channel = a[2].tag == T_INT ? (int) a[2].v.i : 3;
      file_new(a[0], f);
      *res = mk_int(0);
      return;
    }
    case B_CREATE: {
      ARGS(2);
      a68_file f = file_default();
      f.name = strdup(""); f.loaded = 1;
      f.channel = a[1].tag == T_INT ? (int) a[1].v.i : 3;
      file_new(a[0], f);
      *res = mk_int(0);
      return;
    }
    case B_ASSOCIATE: {
      ARGS(2);
      a68_file f = file_default();
      f.assoc = a[1]; f.channel = 4;
      file_new(a[0], f);
      *res = vvoid();
      return;
    }
    case B_CLOSE: {
      ARGS(1);
      uint32_t fid = file_id_of(a[0]);
      a68_file* fs = file_get(fid);
      if (fs->fd >= 0) { os_close_fd((int) fs->fd); fs->fd = -1; fs->eof = 1; }
      file_flush(fid);
      *res = vvoid();
      return;
    }
    case B_SCRATCH: {
      /* a68g `genie_erase`: a file that has been used is removed */
      ARGS(1);
      uint32_t fid = file_id_of(a[0]);
      file_flush(fid);
      a68_file* fs = file_get(fid);
      if (fs->ondisk && fs->name && fs->name[0] && (fs->reading || fs->writing)) {
        if (os_remove_file(fs->name) == 0) { fs->ondisk = 0; fs->dirty = 0; }
        else die("cannot scratch the file");
      }
      *res = vvoid();
      return;
    }
    case B_RESET: {
      ARGS(1);
      uint32_t fid = file_id_of(a[0]);
      uint32_t ch = file_channel(a[0]);
      if (ch != 3 && ch != 4) die("the channel does not allow resetting the file");
      file_flush(fid);
      a68_file* fs = file_get(fid);
      fs->pos = 0; fs->reading = 0; fs->writing = 0;
      fs->loaded = fs->assoc.tag == T_UNDEF && fid != 1;
      *res = vvoid();
      return;
    }
    case B_MAKETERM: {
      ARGS(2);
      uint32_t fid = file_id_of(a[0]);
      int64_t tn; uint8_t* ts = str_of(a[1], &tn);
      a68_file* fs = file_get(fid);
      free(fs->term);
      fs->term = ts; fs->nterm = (size_t) tn;
      *res = vvoid();
      return;
    }
    case B_ONFILEEND: { ARGS(2); file_get(file_id_of(a[0]))->on_end = a[1]; *res = vvoid(); return; }
    case B_ONVALUEERROR: { ARGS(2); file_get(file_id_of(a[0]))->on_value = a[1]; *res = vvoid(); return; }
    case B_ONLINEEND: { ARGS(2); file_get(file_id_of(a[0]))->on_line = a[1]; *res = vvoid(); return; }
    case B_WHOLE: {
      ARGS(2);
      int64_t width = as_int(a[1]);
      a68_val v; int64_t ln;
      switch (number_kind(a[0], &v, &ln, "internal: whole argument")) {
        case NUM_INT: case NUM_LONG_INT: { a68_big* b = big_of(v); *res = take_str(a68_fmt_whole_int(b, width)); big_free(b); return; }
        case NUM_MP: *res = take_str(mp_fmt_whole(v, ln, width)); return;
        default: *res = take_str(a68_fmt_whole_real(v.v.r, width)); return;
      }
    }
    case B_FIXED: {
      ARGS(3);
      int64_t width = as_int(a[1]), after = as_int(a[2]);
      a68_val v; int64_t ln;
      switch (number_kind(a[0], &v, &ln, "internal: fixed argument")) {
        case NUM_INT: { a68_big* b = big_of(v); *res = take_str(a68_fmt_fixed_int(b, width, after, 0)); big_free(b); return; }
        case NUM_LONG_INT: {
          /* a68g relabels the LONG INT as a LONG REAL of the same digits */
          a68_big* b = big_of(v); a68_val z = mp_of_int(b, ln); big_free(b);
          *res = take_str(mp_fmt_fixed(z, ln, width, after)); return;
        }
        case NUM_MP: *res = take_str(mp_fmt_fixed(v, ln, width, after)); return;
        default: *res = take_str(a68_fmt_fixed_real(v.v.r, width, after)); return;
      }
    }
    case B_FLOAT: case B_REAL: {
      if (id == B_FLOAT) { ARGS(4); } else { ARGS(5); }
      int64_t width = as_int(a[1]), after = as_int(a[2]), expo = as_int(a[3]);
      int64_t frmt = id == B_REAL ? as_int(a[4]) : 1;
      a68_val v; int64_t ln;
      switch (number_kind(a[0], &v, &ln, id == B_FLOAT ? "internal: float argument" : "internal: real argument")) {
        case NUM_INT: { a68_big* b = big_of(v); *res = take_str(a68_fmt_float_int(b, width, after, expo, frmt)); big_free(b); return; }
        case NUM_LONG_INT: {
          a68_big* b = big_of(v); a68_val z = mp_of_int(b, ln); big_free(b);
          *res = take_str(mp_fmt_float(z, ln, width, after, expo, frmt)); return;
        }
        case NUM_MP: *res = take_str(mp_fmt_float(v, ln, width, after, expo, frmt)); return;
        default: *res = take_str(a68_fmt_float_real(v.v.r, width, after, expo, frmt)); return;
      }
    }
    case B_CHARINSTRING: case B_LASTCHARINSTRING: {
      ARGS(3);
      uint32_t ch = as_char(a[0]);
      a68_rowd* d = row_of(a[2]);
      int64_t l = d->dim[0].l, cnt = row_count(d);
      int64_t found = -1;
      for (int64_t k = 0; k < cnt; k++) {
        if (as_char(elem(d, k)) == ch) { found = k; if (id == B_CHARINSTRING) break; }
      }
      if (found >= 0) {
        if (a[1].tag != T_NIL) store_ref(a[1], mk_int(l + found));
        *res = mk_bool(1);
      } else *res = mk_bool(0);
      return;
    }
    case B_STRINGINSTRING: {
      ARGS(3);
      int64_t pn; uint8_t* p = str_of(a[0], &pn);
      int64_t l = row_lwb(a[2]);
      int64_t tn; uint8_t* t = str_of(a[2], &tn);
      *res = mk_bool(0);
      for (int64_t k = 0; k <= tn; k++) {
        if (k + pn <= tn && memcmp(t + k, p, (size_t) pn) == 0) {
          if (a[1].tag != T_NIL) store_ref(a[1], mk_int(l + k));
          *res = mk_bool(1);
          break;
        }
      }
      free(p); free(t);
      return;
    }
    case B_TOUPPER: { ARGS(1); uint32_t c = as_char(a[0]); *res = mk_char(c >= 97 && c <= 122 ? c - 32 : c); return; }
    case B_TOLOWER: { ARGS(1); uint32_t c = as_char(a[0]); *res = mk_char(c >= 65 && c <= 90 ? c + 32 : c); return; }
    case B_ISUPPER: { ARGS(1); uint32_t c = as_char(a[0]); *res = mk_bool(c >= 65 && c <= 90); return; }
    case B_ISLOWER: { ARGS(1); uint32_t c = as_char(a[0]); *res = mk_bool(c >= 97 && c <= 122); return; }
    case B_ISDIGIT: { ARGS(1); uint32_t c = as_char(a[0]); *res = mk_bool(c >= 48 && c <= 57); return; }
    case B_ISALPHA: { ARGS(1); uint32_t c = as_char(a[0]); *res = mk_bool((c >= 65 && c <= 90) || (c >= 97 && c <= 122)); return; }
    case B_ISALNUM: { ARGS(1); uint32_t c = as_char(a[0]); *res = mk_bool((c >= 65 && c <= 90) || (c >= 97 && c <= 122) || (c >= 48 && c <= 57)); return; }
    case B_ISSPACE: { ARGS(1); uint32_t c = as_char(a[0]); *res = mk_bool(c == 32 || (c >= 9 && c <= 13)); return; }
    case B_ISPUNCT: { ARGS(1); uint32_t c = as_char(a[0]); *res = mk_bool(c > 32 && c < 127 && !((c >= 65 && c <= 90) || (c >= 97 && c <= 122) || (c >= 48 && c <= 57))); return; }
    case B_ISPRINT: { ARGS(1); uint32_t c = as_char(a[0]); *res = mk_bool(c >= 32 && c < 127); return; }
    case B_ISGRAPH: { ARGS(1); uint32_t c = as_char(a[0]); *res = mk_bool(c > 32 && c < 127); return; }
    case B_ISCNTRL: { ARGS(1); uint32_t c = as_char(a[0]); *res = mk_bool(c < 32 || c == 127); return; }
    case B_ISXDIGIT: { ARGS(1); uint32_t c = as_char(a[0]); *res = mk_bool((c >= 48 && c <= 57) || (c >= 65 && c <= 70) || (c >= 97 && c <= 102)); return; }
    case B_ODD: { ARGS(1); int64_t k = as_int(a[0]); *res = mk_bool(k % 2 != 0); return; }
    case B_ABS: { ARGS(1); int64_t k = as_int(a[0]); *res = mk_int(k < 0 ? -k : k); return; }
    case B_STOP: ARGS(0); io_stop();
    case B_RANDOM: ARGS(0); *res = mk_real(next_random()); return;
    case B_FIRSTRANDOM: { ARGS(1); int64_t k = as_int(a[0]); taus_seed((uint32_t) ((k < 0 ? 0 : (uint64_t) k) % 4294967296ull)); *res = vvoid(); return; }
    case B_RANDOMINT: {
      ARGS(1);
      int64_t k = as_int(a[0]);
      double r = next_random();
      double x = r * (double) k;
      uint64_t u = x <= 0 ? 0 : x >= 18446744073709551615.0 ? UINT64_MAX : (uint64_t) x;
      *res = mk_int(1 + (int64_t) u);
      return;
    }
    case B_GC_SWEEP: ARGS(0); a68_gc_query(0); *res = vvoid(); return;
    case B_GC_COLLECTIONS: ARGS(0); *res = mk_int((int64_t) a68_gc_query(1)); return;
    case B_GC_GARBAGE: ARGS(0); *res = mk_int((int64_t) a68_gc_query(2)); return;
    case B_GC_REFUSED: ARGS(0); *res = mk_int(0); return;
    case B_GC_SECONDS: ARGS(0); *res = mk_real(a68_gc_query(3)); return;
    case B_CLOCK: ARGS(0); *res = mk_real((double) clock_ms() / 1000.0); return;
    case B_COMPLEXFN: {
      ARGS(1);
      a68_val re, im;
      if (a[0].tag != T_STRUCT || ((a68_slots*) a[0].v.p)->h.n != 2) die("COMPL expected");
      re = ((a68_slots*) a[0].v.p)->s[0]; im = ((a68_slots*) a[0].v.p)->s[1];
      if (re.tag != T_REAL || im.tag != T_REAL) die("COMPL expected");
      /* a68g calls the C library's function (single.c, C_C_FUNCTION) */
      double r = a68_compl_fn((uint8_t) sub, 0, re.v.r, im.v.r), i = a68_compl_fn((uint8_t) sub, 1, re.v.r, im.v.r);
      /* a68g's CHECK_COMPLEX: the real part is tested, then the imaginary part */
      double parts[2] = { r, i };
      for (int k = 0; k < 2; k++) {
        if (isnan(parts[k])) die("COMPL value is not a number");
        if (isinf(parts[k])) die("infinite COMPL value");
      }
      a68_slots* s = slots_alloc(2);
      s->s[0] = mk_real(r); s->s[1] = mk_real(i);
      *res = mk_ptr(T_STRUCT, (a68_obj*) s, 0);
      return;
    }
    case B_LONGARCTAN2: ARGS(2); *res = mp_arctan2(name, a[0], a[1]); return;
    case B_ARCTAN2: { ARGS(2); double y = as_real(a[0]), x = as_real(a[1]); *res = mk_real(check_real(atan2(y, x))); return; }
    case B_READINT: {
      ARGS(0);
      size_t tn; char* t = read_token(1, &tn);
      size_t i = tn > 0 && t[0] == '-' ? 1 : 0;
      if (i >= tn) die("cannot read INT");
      for (size_t k = i; k < tn; k++) if (t[k] < '0' || t[k] > '9') die("cannot read INT");
      a68_big* b = big_from_dec(t, tn);
      if (big_fits_i64(b)) *res = mk_int(big_to_i64(b));
      else { char* d = big_to_dec(b); a68_leaf* l = leaf_alloc(EK_BYTES, (uint32_t) strlen(d)); memcpy(l->d, d, strlen(d)); free(d); *res = mk_ptr(T_BIGINT, (a68_obj*) l, 0); }
      big_free(b); free(t);
      return;
    }
    case B_READREAL: {
      ARGS(0);
      size_t tn; char* t = read_token(1, &tn);
      int neg = tn > 0 && t[0] == '-';
      double x = a68_fmt_parse_float(t + (neg ? 1 : 0), tn - (neg ? 1 : 0));
      *res = mk_real(neg ? -x : x);
      free(t);
      return;
    }
    case B_READSTRING: case B_READLINE: {
      ARGS(0);
      size_t sn; char* s = read_line_str(1, &sn);
      skip_line(1);
      *res = of_string(s, sn);
      free(s);
      return;
    }
    case B_READCHAR: { ARGS(0); int c = read_char(1); if (c < 0) die("end of file"); *res = mk_char((uint32_t) c); return; }
    case B_READBOOL: {
      ARGS(0);
      size_t tn; char* t = read_token(1, &tn);
      *res = mk_bool((tn == 1 && t[0] == 'T') || (tn == 4 && memcmp(t, "TRUE", 4) == 0));
      free(t);
      return;
    }
    case B_PRINTINT: { ARGS(1); char* s = fmt_int_of(a[0], 0); emit_bytes((const uint8_t*) s, strlen(s)); free(s); *res = vvoid(); return; }
    case B_PRINTREAL: { ARGS(1); char* s = a68_fmt_print_real(as_real(a[0]), 0, a68_ll_digits); emit_bytes((const uint8_t*) s, strlen(s)); free(s); *res = vvoid(); return; }
    case B_PRINTSTRING: { ARGS(1); int64_t sn; uint8_t* s = str_of(a[0], &sn); emit_bytes(s, (size_t) sn); free(s); *res = vvoid(); return; }
    case B_PRINTCHAR: { ARGS(1); uint8_t c = (uint8_t) as_char(a[0]); emit_bytes(&c, 1); *res = vvoid(); return; }
    case B_PRINTBOOL: { ARGS(1); emit_bytes((const uint8_t*) (as_bool(a[0]) ? "T" : "F"), 1); *res = vvoid(); return; }
    case B_NOOP1: ARGS(1); *res = vvoid(); return;
    case B_NOOP2: ARGS(2); *res = vvoid(); return;
    case B_ARGC: ARGS(0); *res = mk_int(a68_argc); return;
    case B_ARGV: {
      ARGS(1);
      int64_t k = as_int(a[0]);
      if (k < 1 || k > a68_argc) *res = of_string("", 0);
      else *res = str_val(a68_argv[k - 1]);
      return;
    }
    case B_BITSPACK: {
      ARGS(1);
      a68_rowd* d = row_of(a[0]);
      int64_t cnt = row_count(d);
      uint64_t v = 0;
      for (int64_t i = 0; i < cnt; i++) v = v * 2 + (as_bool(elem(d, i)) ? 1 : 0);
      *res = mk_bits(v);
      return;
    }
    case B_BYTESPACK: case B_LONGBYTESPACK: {
      ARGS(1);
      int64_t sn; uint8_t* s = str_of(a[0], &sn);
      int64_t w = id == B_BYTESPACK ? 32 : 256;
      if (sn > w) { free(s); dief("the string is longer than %lld characters", w, 0, 0); }
      uint8_t* b = (uint8_t*) xmalloc((size_t) w);
      memcpy(b, s, (size_t) sn);
      memset(b + sn, 0, (size_t) (w - sn));
      *res = string_row(b, w, 1);
      free(s); free(b);
      return;
    }
    case B_EVALUATE: die("evaluate is not available in a compiled program");
    case B_ABEND: { ARGS(1); char* s = cstr_of(a[0]); die(s); }
    case B_SYSTEM: { ARGS(1); char* c = cstr_of(a[0]); io_flush_out(); *res = mk_int(os_system(c)); free(c); return; }
    case B_FORK: ARGS(0); io_flush_out(); *res = mk_int(os_fork()); return;
    case B_GETENV: { ARGS(1); char* nm = cstr_of(a[0]); *res = str_val(os_getenv(nm)); free(nm); return; }
    case B_EXECVE: case B_EXECVECHILD: {
      ARGS(3);
      char* prog; char** av; char** ev;
      exec_args(a[0], a[1], a[2], &prog, &av, &ev);
      io_flush_out();
      int32_t r = id == B_EXECVE ? os_execve(prog, av, ev) : os_execve_child(prog, av, ev);
      free(prog); free_cvec(av); free_cvec(ev);
      *res = mk_int(r);
      return;
    }
    case B_EXECVECHILDPIPE: {
      ARGS(3);
      char* prog; char** av; char** ev;
      exec_args(a[0], a[1], a[2], &prog, &av, &ev);
      io_flush_out();
      int32_t r[3];
      os_execve_child_pipe(prog, av, ev, r);
      free(prog); free_cvec(av); free_cvec(ev);
      a68_file fr = file_default(); fr.fd = r[0]; fr.channel = 1; fr.reading = 1;
      a68_file fw = file_default(); fw.fd = r[1]; fw.channel = 0; fw.writing = 1;
      uint32_t ir = file_push(fr), iw = file_push(fw);
      a68_val cr = cell_ref(file_val(ir));
      push(cr);
      a68_val cw = cell_ref(file_val(iw));
      *res = struct3(cr, cw, mk_int(r[2]));
      (void) pop();
      return;
    }
    case B_EXECVEOUTPUT: {
      ARGS(4);
      char* prog; char** av; char** ev;
      exec_args(a[0], a[1], a[2], &prog, &av, &ev);
      io_flush_out();
      int collected; os_bytes out;
      int32_t code = os_execve_output(prog, av, ev, &collected, &out);
      free(prog); free_cvec(av); free_cvec(ev);
      if (collected) {
        if (a[3].tag != T_NIL) store_ref(a[3], of_string((const char*) out.p, out.n));
        free(out.p);
      }
      *res = mk_int(code);
      return;
    }
    case B_CREATEPIPE: ARGS(0); *res = struct3(file_val(1), file_val(0), mk_int(-1)); return;
    case B_WAITPID: { ARGS(1); int64_t k = as_int(a[0]); *res = mk_int(os_waitpid((int32_t) (uint32_t) k)); return; }
    case B_UTCTIME: case B_LOCALTIME: {
      ARGS(0);
      int32_t v[8];
      if (!os_time(id == B_UTCTIME, v)) { *res = row_of_values(NULL, 0); return; }
      a68_val vs[8];
      for (int i = 0; i < 8; i++) vs[i] = mk_int(v[i]);
      *res = row_of_values(vs, 8);
      return;
    }
    case B_GETDIRECTORY: {
      ARGS(1);
      char* p = cstr_of(a[0]);
      size_t cnt;
      char** names_ = os_readdir(p, &cnt);
      free(p);
      if (!names_) die("cannot read the directory");
      a68_val* vs = (a68_val*) xmalloc((cnt ? cnt : 1) * sizeof(a68_val));
      /* every string is rooted on the stack until the row holds them */
      for (size_t i = 0; i < cnt; i++) { vs[i] = str_val(names_[i]); push(vs[i]); free(names_[i]); }
      free(names_);
      *res = row_of_values(vs, (int64_t) cnt);
      sp -= cnt;
      free(vs);
      return;
    }
    case B_FILEIS: {
      ARGS(1);
      char* p = cstr_of(a[0]);
      uint32_t mode = os_stat_mode(p);
      free(p);
      *res = mk_bool(mode != 0 && (mode & 0170000) == (uint32_t) sub);
      return;
    }
    case B_FILEMODE: { ARGS(1); char* p = cstr_of(a[0]); *res = mk_bits(os_stat_mode(p)); free(p); return; }
    case B_GREPINSTRING: case B_GREPINSUBSTRING: {
      ARGS(4);
      char* p = cstr_of(a[0]);
      int64_t l = row_lwb(a[1]);
      char* s = cstr_of(a[1]);
      int32_t so, eo;
      int32_t ret = os_regex(p, s, id == B_GREPINSUBSTRING, &so, &eo);
      free(p); free(s);
      if (ret == 0) {
        if (a[2].tag != T_NIL) store_ref(a[2], mk_int(so + l));
        if (a[3].tag != T_NIL) store_ref(a[3], mk_int(eo + l - 1));
      }
      *res = mk_int(ret);
      return;
    }
    case B_SUBINSTRING: {
      ARGS(3);
      if (a[2].tag == T_NIL) { *res = mk_int(3); return; }
      int64_t sn; uint8_t* s = str_of(ref_load_checked(a[2]), &sn);
      char* p = cstr_of(a[0]);
      int32_t so, eo;
      int32_t ret = os_regex(p, (const char*) s, 0, &so, &eo);
      free(p);
      if (ret != 0) { free(s); *res = mk_int(ret); return; }
      int64_t tn; uint8_t* t = str_of(a[1], &tn);
      size_t so_ = (size_t) so > (size_t) sn ? (size_t) sn : (size_t) so;
      size_t eo_ = (size_t) eo > (size_t) sn ? (size_t) sn : (size_t) eo;
      size_t rn = so_ + (size_t) tn + ((size_t) sn - eo_);
      uint8_t* r = (uint8_t*) xmalloc(rn + 1);
      memcpy(r, s, so_); memcpy(r + so_, t, (size_t) tn); memcpy(r + so_ + tn, s + eo_, (size_t) sn - eo_);
      store_ref(a[2], string_row(r, (int64_t) rn, 1));
      free(s); free(t); free(r);
      *res = mk_int(0);
      return;
    }
    case B_STRERROR: { ARGS(1); int64_t e = as_int(a[0]); *res = str_val(os_strerror((int) (uint32_t) e)); return; }
    case B_ERRNO: ARGS(0); *res = mk_int(os_errno()); return;
    case B_RESETERRNO: ARGS(0); os_set_errno(0); *res = vvoid(); return;
    case B_GETPWD: { ARGS(0); char* d = os_getcwd(); *res = take_str(d); return; }
    case B_SETPWD: { ARGS(1); char* p = cstr_of(a[0]); int r = os_chdir(p); free(p); if (r == 0) { *res = mk_int(0); return; } die("cannot change to the directory"); }
    case B_REALPATH: { ARGS(1); char* p = cstr_of(a[0]); char* r = os_realpath(p); free(p); *res = take_str(r); return; }
    case B_SLEEP: {
      ARGS(1);
      uint32_t m = union_mode(a[0]);
      const a68_mode* p = m != ~0u ? mode_at(m) : NULL;
      a68_val v = m != ~0u ? union_inner(a[0]) : a[0];
      if (p && p->k == M_INT && v.tag == T_INT) { int64_t k = v.v.i < 0 ? -v.v.i : v.v.i; *res = mk_int(signed32(os_sleep((uint32_t) k))); return; }
      if (p && p->k == M_REAL && v.tag == T_REAL) { os_sleep_ms((uint32_t) (fabs(v.v.r) * 1000.0)); *res = mk_int(0); return; }
      *res = mk_int(-1);
      return;
    }
    case B_ROWS: ARGS(0); *res = mk_int(24); return;      /* a68g's defaults when standard output is not a terminal */
    case B_COLUMNS: ARGS(0); *res = mk_int(500); return;
    case B_WALLCLOCK: ARGS(0); *res = mk_real(os_walltime()); return;
    case B_NAN: ARGS(0); *res = mk_real(0.0 / 0.0); return;
    case B_INF: ARGS(0); *res = mk_real(1.0 / 0.0); return;
    case B_MINUSINF: ARGS(0); *res = mk_real(-1.0 / 0.0); return;
    case B_ISFINITE: { ARGS(1); double r = as_real(a[0]); *res = mk_bool(!isnan(r) && !isinf(r)); return; }
    case B_ISINF: { ARGS(1); double r = as_real(a[0]); *res = mk_bool(isinf(r)); return; }
    case B_ISPLUSINF: { ARGS(1); double r = as_real(a[0]); *res = mk_bool(isinf(r) && r > 0); return; }
    case B_ISMINUSINF: { ARGS(1); double r = as_real(a[0]); *res = mk_bool(isinf(r) && r < 0); return; }
    case B_ISNAN: { ARGS(1); double r = as_real(a[0]); *res = mk_bool(isnan(r)); return; }
    case B_RESETPOSSIBLE: { ARGS(1); uint32_t c = file_channel(a[0]); *res = mk_bool(c == 3 || c == 4); return; }
    case B_GETPOSSIBLE: { ARGS(1); uint32_t c = file_channel(a[0]); *res = mk_bool(chan_in(c, 1, 3, 4)); return; }
    case B_PUTPOSSIBLE: { ARGS(1); uint32_t c = file_channel(a[0]); *res = mk_bool(c == 0 || c == 2 || c == 3 || c == 4); return; }
    case B_FALSE: ARGS(1); *res = mk_bool(0); return;
    case B_TRUE: ARGS(1); *res = mk_bool(1); return;
    case B_IDF: {
      ARGS(1);
      a68_file* fs = file_get(file_id_of(a[0]));
      if (!fs->name || !fs->name[0]) die("attempt to use NIL");
      *res = str_val(fs->name);
      return;
    }
    case B_TERM: { ARGS(1); a68_file* fs = file_get(file_id_of(a[0])); *res = of_string((const char*) (fs->term ? fs->term : (const uint8_t*) ""), fs->nterm); return; }
    case B_EOF: case B_EOLN: {
      ARGS(1);
      uint32_t fid = file_id_of(a[0]);
      a68_file* fs = file_get(fid);
      if (fs->writing && fid != 1) die("the file is in write mood");
      if (!(fs->reading || fid == 1 || fs->fd >= 0)) die("the file is in undetermined mood");
      if (id == B_EOF) { *res = mk_bool(at_end(fid)); return; }
      if (at_end(fid)) logical_end(fid);
      *res = mk_bool(peek_char(fid) == 10);
      return;
    }
    case B_SET: {
      /* a68g `genie_set` moves relative to the current position */
      ARGS(2);
      uint32_t fid = file_id_of(a[0]);
      uint32_t ch = file_channel(a[0]);
      if (ch != 3 && ch != 4) die("the channel does not allow setting the file");
      int64_t k = as_int(a[1]);
      a68_file* fs = load_file(fid);
      int64_t np = (int64_t) fs->pos + k;
      if (fs->len == 0 || np < 0 || np >= (int64_t) fs->len) {
        if (fs->on_end.tag != T_UNDEF) {
          if (io_call_handler(fs->on_end, fid)) { *res = mk_int(np); return; }
          die("the file has ended");
        }
        die("the file has ended");
      }
      fs->pos = (size_t) np;
      *res = mk_int(np);
      return;
    }
    case B_PUTS: case B_STRING: case B_PUTSF: case B_STRINGF: {
      ARGS(2);
      a68_rowd* d = row_of(a[1]);
      if (row_count(d) > 0) {
        sf_ctx c = { a[1], id == B_PUTSF || id == B_STRINGF };
        size_t tn;
        char* text = with_string_file(sf_act, &c, &tn);
        store_ref(a[0], of_string(text, tn));
        free(text);
      }
      *res = (id == B_STRING || id == B_STRINGF) ? a[0] : vvoid();
      return;
    }
    case B_GETS: case B_GETSF: {
      ARGS(2);
      a68_file f = file_default();
      f.assoc = a[0]; f.channel = 4;
      uint32_t fid = file_push(f);
      if (id == B_GETS) get_items(fid, a[1]); else getf_items(fid, a[1]);
      file_pop(fid);
      *res = vvoid();
      return;
    }
    case B_GETBIN: case B_PUTBIN: case B_READBIN: case B_PRINTBIN: {
      uint32_t fid; a68_val row;
      if (id == B_GETBIN || id == B_PUTBIN) { ARGS(2); fid = file_id_of(a[0]); row = a[1]; }
      else { ARGS(1); fid = 3; row = a[0]; }
      a68_rowd* d = row_of(row);
      int64_t cnt = row_count(d);
      for (int64_t i = 0; i < cnt; i++) {
        a68_val e = elem(d, i);
        if (e.tag != T_UNION) die("internal: binary transput argument");
        if (id == B_GETBIN || id == B_READBIN) read_bin(fid, e.aux, union_inner(e)); else write_bin(fid, e.aux, union_inner(e));
      }
      *res = vvoid();
      return;
    }
    case B_LONGRANDOM: ARGS(0); *res = mp_long_random(next_random(), sub); return;
    default: break;
  }
  if (n == 0) {
    if (mp_const(name, res)) return;
    unsupported(name, 0);
  }
  if (n == 1) {
    if (mp_math_fn(name, a[0], res)) return;
    if (mp_compl_fn(name, a[0], res)) return;
    if (name_in(name, math_names)) { double r; math_fn(name, as_real(a[0]), &r); *res = mk_real(r); return; }
    unsupported(name, 1);
  }
  unsupported(name, n);
}
