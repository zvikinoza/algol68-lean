/* Operating-system services of the standard environment, in plain C (os.c): the
   evaluator's wrappers in sys.c and the runtime of compiled programs both call these. */
#ifndef A68_OS_H
#define A68_OS_H
#include <stdint.h>
#include <stddef.h>

/* A byte string with its length; `p` is malloc'ed by the routines that return one. */
typedef struct { uint8_t* p; size_t n; } os_bytes;

int32_t os_fork(void);
int32_t os_system(const char* cmd);
/* `args` and `env` are NULL-terminated vectors */
int32_t os_execve(const char* prog, char** args, char** env);
int32_t os_execve_child(const char* prog, char** args, char** env);
/* the parent's read descriptor, write descriptor and the process id; all -1 on failure */
void os_execve_child_pipe(const char* prog, char** args, char** env, int32_t r[3]);
/* the exit status (-1 on failure); `*collected` says whether `*out` holds the output */
int32_t os_execve_output(const char* prog, char** args, char** env, int* collected, os_bytes* out);
int32_t os_waitpid(int32_t pid);
os_bytes os_read_fd(int fd);          /* what one read gives; empty at the end */
int os_write_fd(int fd, const uint8_t* p, size_t n);
int os_close_fd(int fd);
int os_time(int utc, int32_t v[8]);   /* 0 when the time is unavailable */
double os_walltime(void);
/* the names of a directory, NULL when it cannot be read; the caller frees the strings and the vector */
char** os_readdir(const char* path, size_t* n);
uint32_t os_stat_mode(const char* path);
uint32_t os_open_status(const char* path);
/* the result code (0 match, 1 no match, 2 error, 3 out of memory) with the match's offsets */
int32_t os_regex(const char* pat, const char* str, int notbol, int32_t* so, int32_t* eo);
const char* os_strerror(int e);
int os_errno(void);
void os_set_errno(int e);
char* os_getcwd(void);                /* malloc'ed, "" when unavailable */
int os_chdir(const char* path);
char* os_realpath(const char* path);  /* malloc'ed, "" when unavailable */
uint32_t os_sleep(uint32_t secs);
const char* os_getenv(const char* name);   /* "" when unset */
void os_sleep_ms(uint32_t ms);
int os_write_file(const char* path, const uint8_t* p, size_t n);   /* 0 on success */
int os_read_file(const char* path, os_bytes* out);                /* 0 on success */
int os_remove_file(const char* path);

/* COMPLEX arithmetic as a68g computes it */
double a68_compl_op(uint8_t which, uint8_t part, double re_x, double im_x, double re_y, double im_y);
double a68_compl_pow(uint8_t part, double re_x, double im_x, uint64_t j);
double a68_compl_abs(double x, double y);
double a68_compl_fn(uint8_t which, uint8_t part, double re, double im);

#endif
