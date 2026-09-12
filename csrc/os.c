/* Operating-system services of the a68g standard environment: processes and pipes,
   directories and file status, time, regular expressions and error texts, in plain C.
   Each routine follows the a68g routine named in its comment (genie-unix.c,
   genie-regex.c, genie-misc.c). */
#include "os.h"
#include <dirent.h>
#include <errno.h>
#include <limits.h>
#include <regex.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/wait.h>

static void* xm(size_t n) {
  void* p = malloc(n ? n : 1);
  if (!p) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  return p;
}

/* PROC fork = INT (genie_fork) */
int32_t os_fork(void) { return (int32_t) fork(); }

/* PROC system = (STRING) INT (genie_system): the status system () returns. */
int32_t os_system(const char* cmd) { return (int32_t) system(cmd); }

/* PROC execve = (STRING, [] STRING, [] STRING) INT (genie_exec): returns only on failure. */
int32_t os_execve(const char* prog, char** args, char** env) { return (int32_t) execve(prog, args, env); }

static void exec_child(const char* prog, char** args, char** env) {
  (void) execve(prog, args, env);
  _exit(EXIT_FAILURE);
}

/* PROC execve child = (STRING, [] STRING, [] STRING) INT (genie_exec_sub) */
int32_t os_execve_child(const char* prog, char** args, char** env) {
  pid_t pid = fork();
  if (pid == 0) exec_child(prog, args, env);
  return (int32_t) pid;
}

/* Fork a child whose standard input and output are two pipes; the child runs the program. */
static pid_t piped_child(const char* prog, char** args, char** env, int* rd, int* wr) {
  int ptoc[2], ctop[2];
  if (pipe(ptoc) == -1) return -1;
  if (pipe(ctop) == -1) return -1;
  pid_t pid = fork();
  if (pid == -1) return -1;
  if (pid == 0) {
    close(ctop[0]);
    close(ptoc[1]);
    close(0);
    close(1);
    dup2(ptoc[0], 0);
    dup2(ctop[1], 1);
    exec_child(prog, args, env);
  }
  close(ptoc[0]);
  close(ctop[1]);
  *rd = ctop[0];
  *wr = ptoc[1];
  return pid;
}

/* PROC execve child pipe = (STRING, [] STRING, [] STRING) PIPE (genie_exec_sub_pipeline) */
void os_execve_child_pipe(const char* prog, char** args, char** env, int32_t r[3]) {
  r[0] = r[1] = r[2] = -1;
  int rd = -1, wr = -1;
  pid_t pid = piped_child(prog, args, env, &rd, &wr);
  if (pid != -1) { r[0] = rd; r[1] = wr; r[2] = (int32_t) pid; }
}

/* PROC execve output = (STRING, [] STRING, [] STRING, REF STRING) INT (genie_exec_sub_output) */
int32_t os_execve_output(const char* prog, char** args, char** env, int* collected, os_bytes* out) {
  *collected = 0;
  out->p = NULL; out->n = 0;
  int rd = -1, wr = -1;
  pid_t pid = piped_child(prog, args, env, &rd, &wr);
  if (pid == -1) return -1;
  size_t cap = 4096, len = 0;
  uint8_t* buf = (uint8_t*) xm(cap);
  for (;;) {
    uint8_t chunk[4096];
    ssize_t n = read(rd, chunk, sizeof chunk);
    if (n == -1 && errno == EINTR) continue;
    if (n <= 0) break;
    while (len + (size_t) n > cap) { cap *= 2; buf = (uint8_t*) realloc(buf, cap); if (!buf) exit(1); }
    memcpy(buf + len, chunk, (size_t) n);
    len += (size_t) n;
  }
  int status = 0, ret;
  do { ret = waitpid(pid, &status, 0); } while (ret == -1 && errno == EINTR);
  int32_t code = -1;
  if (ret == pid) { code = WIFEXITED(status) ? WEXITSTATUS(status) : -1; *collected = 1; }
  close(wr);
  close(rd);
  if (*collected) { out->p = buf; out->n = len; } else free(buf);
  return code;
}

/* PROC wait pid = (INT) INT (genie_waitpid) */
int32_t os_waitpid(int32_t pid) {
  int status = 0, ret;
  do { ret = waitpid((pid_t) pid, &status, 0); } while (ret == -1 && errno == EINTR);
  if (ret == (int) pid) return WIFEXITED(status) ? (int32_t) WEXITSTATUS(status) : -1;
  return -1;
}

os_bytes os_read_fd(int fd) {
  uint8_t buf[4096];
  ssize_t n;
  do { n = read(fd, buf, sizeof buf); } while (n == -1 && errno == EINTR);
  os_bytes b;
  b.n = n > 0 ? (size_t) n : 0;
  b.p = (uint8_t*) xm(b.n + 1);
  if (b.n) memcpy(b.p, buf, b.n);
  return b;
}

int os_write_fd(int fd, const uint8_t* p, size_t n) {
  while (n > 0) {
    ssize_t w = write(fd, p, n);
    if (w == -1) { if (errno == EINTR) continue; return 1; }
    p += w;
    n -= (size_t) w;
  }
  return 0;
}

int os_close_fd(int fd) { return close(fd); }

/* PROC utc time, local time = [] INT (genie_utctime, genie_localtime) */
int os_time(int utc, int32_t v[8]) {
  time_t dt;
  if (time(&dt) == (time_t) -1) return 0;
  struct tm* t = utc ? gmtime(&dt) : localtime(&dt);
  v[0] = t->tm_year + 1900; v[1] = t->tm_mon + 1; v[2] = t->tm_mday; v[3] = t->tm_hour;
  v[4] = t->tm_min; v[5] = t->tm_sec; v[6] = t->tm_wday + 1; v[7] = t->tm_isdst;
  return 1;
}

double os_walltime(void) {
  struct timeval tv;
  gettimeofday(&tv, NULL);
  return (double) tv.tv_sec + (double) tv.tv_usec * 1e-6;
}

/* PROC get directory = (STRING) [] STRING (genie_directory) */
char** os_readdir(const char* path, size_t* n) {
  *n = 0;
  DIR* d = opendir(path);
  if (d == NULL) return NULL;
  size_t cap = 16;
  char** v = (char**) xm(cap * sizeof(char*));
  struct dirent* e;
  while ((e = readdir(d)) != NULL) {
    if (*n == cap) { cap *= 2; v = (char**) realloc(v, cap * sizeof(char*)); if (!v) exit(1); }
    v[(*n)++] = strdup(e->d_name);
  }
  closedir(d);
  return v;
}

/* The st_mode of a file, or 0 when stat fails (genie_file_is_directory and friends). */
uint32_t os_stat_mode(const char* path) {
  struct stat st;
  return stat(path, &st) == 0 ? (uint32_t) st.st_mode : 0;
}

/* What a68g's open and append return: 0 for a regular file, ENOENT for anything else that
   exists, and the error number of stat otherwise. */
uint32_t os_open_status(const char* path) {
  struct stat st;
  errno = 0;
  int r = stat(path, &st);
  int e = errno;
  errno = 0;
  if (r == 0) return S_ISREG(st.st_mode) ? 0 : ENOENT;
  return (uint32_t) e;
}

/* PROC grep in string, grep in substring (genie_grep_in_string) */
int32_t os_regex(const char* pat, const char* str, int notbol, int32_t* so, int32_t* eo) {
  *so = *eo = 0;
  regex_t re;
  int ret = regcomp(&re, pat, REG_NEWLINE | REG_EXTENDED);
  if (ret == 0) {
    size_t nmatch = re.re_nsub == 0 ? 1 : re.re_nsub;
    regmatch_t* m = (regmatch_t*) xm(nmatch * sizeof(regmatch_t));
    ret = regexec(&re, str, nmatch, m, notbol ? REG_NOTBOL : 0);
    if (ret == 0) {
      int widest = 0;
      size_t k0 = 0;
      for (size_t k = 0; k < nmatch; k++) {
        int dif = (int) m[k].rm_eo - (int) m[k].rm_so;
        if (dif > widest) { widest = dif; k0 = k; }
      }
      *so = (int32_t) m[k0].rm_so;
      *eo = (int32_t) m[k0].rm_eo;
    }
    free(m);
    regfree(&re);
  }
  return ret == 0 ? 0 : ret == REG_NOMATCH ? 1 : ret == REG_ESPACE ? 3 : 2;
}

const char* os_strerror(int e) { return strerror(e); }
int os_errno(void) { return errno; }
void os_set_errno(int e) { errno = e; }

char* os_getcwd(void) {
  char buf[PATH_MAX + 1];
  if (getcwd(buf, sizeof buf) == NULL) return strdup("");
  return strdup(buf);
}

int os_chdir(const char* path) { return chdir(path); }

char* os_realpath(const char* path) {
  char* o = realpath(path, NULL);
  return o ? o : strdup("");
}

uint32_t os_sleep(uint32_t secs) {
  unsigned w = secs;
  while (w > 0) w = sleep(w);
  return w;
}

const char* os_getenv(const char* name) {
  const char* v = getenv(name);
  return v ? v : "";
}

void os_sleep_ms(uint32_t ms) {
  struct timespec ts = { (time_t) (ms / 1000), (long) (ms % 1000) * 1000000L };
  while (nanosleep(&ts, &ts) == -1 && errno == EINTR) {}
}

int os_write_file(const char* path, const uint8_t* p, size_t n) {
  FILE* f = fopen(path, "wb");
  if (!f) return 1;
  int bad = n > 0 && fwrite(p, 1, n, f) != n;
  if (fclose(f) != 0) bad = 1;
  return bad;
}

int os_read_file(const char* path, os_bytes* out) {
  out->p = NULL; out->n = 0;
  FILE* f = fopen(path, "rb");
  if (!f) return 1;
  size_t cap = 4096, len = 0;
  uint8_t* buf = (uint8_t*) xm(cap);
  for (;;) {
    if (len == cap) { cap *= 2; buf = (uint8_t*) realloc(buf, cap); if (!buf) exit(1); }
    size_t n = fread(buf + len, 1, cap - len, f);
    if (n == 0) break;
    len += n;
  }
  fclose(f);
  out->p = buf; out->n = len;
  return 0;
}

int os_remove_file(const char* path) { return remove(path); }

/* COMPLEX arithmetic and functions as a68g computes them (single.c, single-math.c).  The
   expressions are a68g's own, compiled by a C compiler that, like the one a68g was built
   with, fuses a multiplication and an addition within one expression into a single
   operation, so the last figures of a result agree with a68g's and not only the first
   fifteen.  Part 0 of a result is its real part, part 1 its imaginary part. */
#include <complex.h>
#include <math.h>

#define A68_ABS(x) ((x) >= 0 ? (x) : -(x))

/* genie_mul_complex (which 0) and genie_div_complex (which 1) */
double a68_compl_op(uint8_t which, uint8_t part, double re_x, double im_x, double re_y, double im_y) {
  double re = 0.0, im = 0.0;
  if (which == 0) {
    re = re_x * re_y - im_x * im_y;
    im = im_x * re_y + re_x * im_y;
  } else if (A68_ABS (re_y) >= A68_ABS (im_y)) {
    double r = im_y / re_y, den = re_y + r * im_y;
    re = (re_x + r * im_x) / den;
    im = (im_x - r * re_x) / den;
  } else {
    double r = re_y / im_y, den = im_y + r * re_y;
    re = (re_x * r + im_x) / den;
    im = (im_x * r - re_x) / den;
  }
  return part == 0 ? re : im;
}

/* genie_pow_complex_int for a non-negative exponent; a negative one divides 1 by this */
double a68_compl_pow(uint8_t part, double re_x, double im_x, uint64_t j) {
  double re_z = 1.0, im_z = 0.0;
  double re_y = re_x, im_y = im_x;
  uint64_t expo = 1;
  while (expo <= j) {
    double rea;
    if (expo & j) {
      rea = re_z * re_y - im_z * im_y;
      im_z = re_z * im_y + im_z * re_y;
      re_z = rea;
    }
    rea = re_y * re_y - im_y * im_y;
    im_y = im_y * re_y + re_y * im_y;
    re_y = rea;
    expo <<= 1;
  }
  return part == 0 ? re_z : im_z;
}

/* a68g_hypot_real, which OP ABS on COMPLEX uses */
double a68_compl_abs(double x, double y) {
  double xabs = A68_ABS (x), yabs = A68_ABS (y), min, max;
  if (xabs < yabs) {
    min = xabs;
    max = yabs;
  } else {
    min = yabs;
    max = xabs;
  }
  if (min == 0) {
    return max;
  } else {
    double u = min / max;
    return max * sqrt (1 + u * u);
  }
}

/* the C_C_FUNCTION routines: the C library's complex functions */
double a68_compl_fn(uint8_t which, uint8_t part, double re, double im) {
  double complex z = re + im * _Complex_I;
  switch (which) {
    case 0: z = csqrt (z); break;
    case 1: z = cexp (z); break;
    case 2: z = clog (z); break;
    case 3: z = csin (z); break;
    case 4: z = ccos (z); break;
    case 5: z = ctan (z); break;
    case 6: z = casin (z); break;
    case 7: z = cacos (z); break;
    case 8: z = catan (z); break;
    case 9: z = csinh (z); break;
    case 10: z = ccosh (z); break;
    case 11: z = ctanh (z); break;
    case 12: z = casinh (z); break;
    case 13: z = cacosh (z); break;
    default: z = catanh (z); break;
  }
  return part == 0 ? creal (z) : cimag (z);
}
