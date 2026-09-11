/* Operating-system services of the a68g standard environment: processes and pipes,
   directories and file status, time, regular expressions and error texts.

   The evaluator declares these with `@[extern]` (A68/Interp.lean), so `a68lean run` and a
   compiled program, which links this library, reach the same code.  Algol 68 strings
   cross as byte arrays, since an Algol 68 character is a byte.  Each routine follows the
   a68g routine named in its comment (genie-unix.c, genie-regex.c, genie-misc.c). */
#include <lean/lean.h>
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

/* A NUL-terminated copy of a byte array; the caller frees it. */
static char *a68_cstr(b_lean_obj_arg b) {
  size_t n = lean_sarray_size(b);
  char *s = (char *) malloc(n + 1);
  if (n > 0) memcpy(s, lean_sarray_cptr(b), n);
  s[n] = 0;
  return s;
}

static lean_obj_res a68_bytes(const char *s, size_t n) {
  lean_object *o = lean_alloc_sarray(1, n, n);
  if (n > 0) memcpy(lean_sarray_cptr(o), s, n);
  return o;
}

static lean_obj_res a68_ints(const int32_t *v, size_t n) {
  return a68_bytes((const char *) v, n * sizeof(int32_t));
}

/* The non-empty strings of a row as a NULL-terminated vector (convert_string_vector). */
static char **a68_cvec(b_lean_obj_arg arr) {
  size_t n = lean_array_size(arr);
  char **v = (char **) malloc((n + 1) * sizeof(char *));
  size_t k = 0;
  for (size_t i = 0; i < n; i++) {
    char *s = a68_cstr(lean_array_get_core(arr, i));
    if (s[0] != 0) v[k++] = s; else free(s);
  }
  v[k] = NULL;
  return v;
}

static void a68_free_cvec(char **v) {
  for (size_t k = 0; v[k] != NULL; k++) free(v[k]);
  free(v);
}

/* PROC fork = INT (genie_fork) */
uint32_t a68_sys_fork(lean_object *u) {
  (void) u;
  return (uint32_t) fork();
}

/* PROC system = (STRING) INT (genie_system): the status system () returns. */
uint32_t a68_sys_system(b_lean_obj_arg cmd) {
  char *c = a68_cstr(cmd);
  int r = system(c);
  free(c);
  return (uint32_t) r;
}

/* PROC execve = (STRING, [] STRING, [] STRING) INT (genie_exec): returns only on failure. */
uint32_t a68_sys_execve(b_lean_obj_arg prog, b_lean_obj_arg args, b_lean_obj_arg env) {
  char *p = a68_cstr(prog);
  char **a = a68_cvec(args), **e = a68_cvec(env);
  int r = execve(p, a, e);
  a68_free_cvec(a);
  a68_free_cvec(e);
  free(p);
  return (uint32_t) r;
}

static void a68_exec_child(b_lean_obj_arg prog, b_lean_obj_arg args, b_lean_obj_arg env) {
  char *p = a68_cstr(prog);
  char **a = a68_cvec(args), **e = a68_cvec(env);
  (void) execve(p, a, e);
  _exit(EXIT_FAILURE);
}

/* PROC execve child = (STRING, [] STRING, [] STRING) INT (genie_exec_sub) */
uint32_t a68_sys_execve_child(b_lean_obj_arg prog, b_lean_obj_arg args, b_lean_obj_arg env) {
  pid_t pid = fork();
  if (pid == 0) a68_exec_child(prog, args, env);
  return (uint32_t) pid;
}

/* Fork a child whose standard input and output are two pipes; the child runs the program. */
static pid_t a68_piped_child(b_lean_obj_arg prog, b_lean_obj_arg args, b_lean_obj_arg env,
                             int *rd, int *wr) {
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
    a68_exec_child(prog, args, env);
  }
  close(ptoc[0]);
  close(ctop[1]);
  *rd = ctop[0];
  *wr = ptoc[1];
  return pid;
}

/* PROC execve child pipe = (STRING, [] STRING, [] STRING) PIPE (genie_exec_sub_pipeline):
   the parent's read descriptor, write descriptor and the process id, all -1 on failure. */
lean_obj_res a68_sys_execve_child_pipe(b_lean_obj_arg prog, b_lean_obj_arg args, b_lean_obj_arg env) {
  int32_t r[3] = {-1, -1, -1};
  int rd = -1, wr = -1;
  pid_t pid = a68_piped_child(prog, args, env, &rd, &wr);
  if (pid != -1) {
    r[0] = rd;
    r[1] = wr;
    r[2] = pid;
  }
  return a68_ints(r, 3);
}

/* PROC execve output = (STRING, [] STRING, [] STRING, REF STRING) INT (genie_exec_sub_output):
   the exit status (-1 on failure), whether the output was collected, then the output. */
lean_obj_res a68_sys_execve_output(b_lean_obj_arg prog, b_lean_obj_arg args, b_lean_obj_arg env) {
  int32_t head[2] = {-1, 0};
  int rd = -1, wr = -1;
  pid_t pid = a68_piped_child(prog, args, env, &rd, &wr);
  if (pid == -1) return a68_ints(head, 2);
  size_t cap = 4096, len = sizeof head;
  char *buf = (char *) malloc(cap);
  for (;;) {
    char chunk[4096];
    ssize_t n = read(rd, chunk, sizeof chunk);
    if (n == -1 && errno == EINTR) continue;
    if (n <= 0) break;
    while (len + (size_t) n > cap) {
      cap *= 2;
      buf = (char *) realloc(buf, cap);
    }
    memcpy(buf + len, chunk, (size_t) n);
    len += (size_t) n;
  }
  int status = 0, ret;
  do {
    ret = waitpid(pid, &status, 0);
  } while (ret == -1 && errno == EINTR);
  if (ret == pid) {
    head[0] = WIFEXITED(status) ? WEXITSTATUS(status) : -1;
    head[1] = 1;
  }
  close(wr);
  close(rd);
  memcpy(buf, head, sizeof head);
  lean_obj_res o = a68_bytes(buf, head[1] ? len : sizeof head);
  free(buf);
  return o;
}

/* PROC wait pid = (INT) INT (genie_waitpid) */
uint32_t a68_sys_waitpid(uint32_t pid) {
  int status = 0, ret;
  do {
    ret = waitpid((pid_t) (int32_t) pid, &status, 0);
  } while (ret == -1 && errno == EINTR);
  if (ret == (int) (int32_t) pid) return WIFEXITED(status) ? (uint32_t) WEXITSTATUS(status) : (uint32_t) -1;
  return (uint32_t) -1;
}

/* What one read of a descriptor gives; empty at end of file or on an error. */
lean_obj_res a68_sys_read_fd(uint32_t fd) {
  char buf[4096];
  ssize_t n;
  do {
    n = read((int) fd, buf, sizeof buf);
  } while (n == -1 && errno == EINTR);
  return a68_bytes(buf, n > 0 ? (size_t) n : 0);
}

uint32_t a68_sys_write_fd(uint32_t fd, b_lean_obj_arg b) {
  const char *p = (const char *) lean_sarray_cptr(b);
  size_t n = lean_sarray_size(b);
  while (n > 0) {
    ssize_t w = write((int) fd, p, n);
    if (w == -1) {
      if (errno == EINTR) continue;
      return 1;
    }
    p += w;
    n -= (size_t) w;
  }
  return 0;
}

uint32_t a68_sys_close_fd(uint32_t fd) {
  return (uint32_t) close((int) fd);
}

/* PROC utc time, local time = [] INT (genie_utctime, genie_localtime): year, month, day,
   hours, minutes, seconds, day of the week and daylight saving flag. */
lean_obj_res a68_sys_time(uint8_t utc) {
  time_t dt;
  if (time(&dt) == (time_t) -1) return a68_bytes("", 0);
  struct tm *t = utc ? gmtime(&dt) : localtime(&dt);
  int32_t v[8] = {t->tm_year + 1900, t->tm_mon + 1, t->tm_mday, t->tm_hour,
                  t->tm_min, t->tm_sec, t->tm_wday + 1, t->tm_isdst};
  return a68_ints(v, 8);
}

double a68_sys_walltime(lean_object *u) {
  (void) u;
  struct timeval tv;
  gettimeofday(&tv, NULL);
  return (double) tv.tv_sec + (double) tv.tv_usec * 1e-6;
}

/* PROC get directory = (STRING) [] STRING (genie_directory): a marker entry "1" followed by
   the names in the order readdir gives them, or no entries at all when the directory
   cannot be read. */
lean_obj_res a68_sys_readdir(b_lean_obj_arg path) {
  lean_object *arr = lean_mk_empty_array();
  char *p = a68_cstr(path);
  DIR *d = opendir(p);
  free(p);
  if (d == NULL) return arr;
  arr = lean_array_push(arr, a68_bytes("1", 1));
  struct dirent *e;
  while ((e = readdir(d)) != NULL) arr = lean_array_push(arr, a68_bytes(e->d_name, strlen(e->d_name)));
  closedir(d);
  return arr;
}

/* The st_mode of a file, or 0 when stat fails (genie_file_is_directory and friends). */
uint32_t a68_sys_stat_mode(b_lean_obj_arg path) {
  struct stat st;
  char *p = a68_cstr(path);
  int r = stat(p, &st);
  free(p);
  return r == 0 ? (uint32_t) st.st_mode : 0;
}

/* What a68g's open and append return: 0 for a regular file, ENOENT for anything else that
   exists, and the error number of stat otherwise. */
uint32_t a68_sys_open_status(b_lean_obj_arg path) {
  struct stat st;
  char *p = a68_cstr(path);
  errno = 0;
  int r = stat(p, &st);
  int e = errno;
  free(p);
  errno = 0;
  if (r == 0) return S_ISREG(st.st_mode) ? 0 : ENOENT;
  return (uint32_t) e;
}

/* PROC grep in string, grep in substring (genie_grep_in_string): the result code (0 match,
   1 no match, 2 another error, 3 out of memory) and the start and end offsets of the
   widest of the first re_nsub matches, as a68g takes them. */
lean_obj_res a68_sys_regex(b_lean_obj_arg pat, b_lean_obj_arg str, uint8_t notbol) {
  int32_t r[3] = {2, 0, 0};
  char *p = a68_cstr(pat), *s = a68_cstr(str);
  regex_t re;
  int ret = regcomp(&re, p, REG_NEWLINE | REG_EXTENDED);
  if (ret == 0) {
    size_t nmatch = re.re_nsub == 0 ? 1 : re.re_nsub;
    regmatch_t *m = (regmatch_t *) malloc(nmatch * sizeof(regmatch_t));
    ret = regexec(&re, s, nmatch, m, notbol ? REG_NOTBOL : 0);
    if (ret == 0) {
      int widest = 0;
      size_t k0 = 0;
      for (size_t k = 0; k < nmatch; k++) {
        int dif = (int) m[k].rm_eo - (int) m[k].rm_so;
        if (dif > widest) {
          widest = dif;
          k0 = k;
        }
      }
      r[1] = (int32_t) m[k0].rm_so;
      r[2] = (int32_t) m[k0].rm_eo;
    }
    free(m);
    regfree(&re);
  }
  r[0] = ret == 0 ? 0 : ret == REG_NOMATCH ? 1 : ret == REG_ESPACE ? 3 : 2;
  free(p);
  free(s);
  return a68_ints(r, 3);
}

lean_obj_res a68_sys_strerror(uint32_t e) {
  const char *s = strerror((int) e);
  return a68_bytes(s, strlen(s));
}

uint32_t a68_sys_errno(lean_object *u) {
  (void) u;
  return (uint32_t) errno;
}

uint32_t a68_sys_set_errno(uint32_t e) {
  errno = (int) e;
  return e;
}

lean_obj_res a68_sys_getcwd(lean_object *u) {
  (void) u;
  char buf[PATH_MAX + 1];
  if (getcwd(buf, sizeof buf) == NULL) return a68_bytes("", 0);
  return a68_bytes(buf, strlen(buf));
}

uint32_t a68_sys_chdir(b_lean_obj_arg path) {
  char *p = a68_cstr(path);
  int r = chdir(p);
  free(p);
  return (uint32_t) r;
}

lean_obj_res a68_sys_realpath(b_lean_obj_arg path) {
  char *p = a68_cstr(path);
  char *o = realpath(p, NULL);
  free(p);
  if (o == NULL) return a68_bytes("", 0);
  lean_obj_res r = a68_bytes(o, strlen(o));
  free(o);
  return r;
}

uint32_t a68_sys_sleep(uint32_t secs) {
  unsigned w = secs;
  while (w > 0) w = sleep(w);
  return w;
}

lean_obj_res a68_sys_getenv(b_lean_obj_arg name) {
  char *n = a68_cstr(name);
  const char *v = getenv(n);
  free(n);
  return v != NULL ? a68_bytes(v, strlen(v)) : a68_bytes("", 0);
}

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
