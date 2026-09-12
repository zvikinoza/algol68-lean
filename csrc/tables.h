/* The tables a compiled program carries (A68/Serial.lean): modes, format texts, strings
   and the program's mode declarations, parsed from the blob at start-up. */
#ifndef A68_TABLES_H
#define A68_TABLES_H
#include <stdint.h>
#include <stddef.h>

typedef enum {
  M_INT, M_REAL, M_BOOL, M_CHAR, M_VOID, M_BITS, M_BYTES, M_COMPL, M_REF, M_ROW, M_PROC,
  M_STRUCT, M_UNION, M_NAMED, M_FORMAT, M_FILE, M_CHANNEL, M_SEMA, M_SIMPLOUT, M_SIMPLIN,
  M_NUMBER, M_BAD
} a68_mkind;

typedef struct {
  a68_mkind k;
  int64_t len;        /* INT/REAL/BITS/BYTES/COMPL: the length (0 = plain) */
  uint32_t sub;       /* REF: the mode referred to; ROW: the element mode; PROC: the result; NAMED: the name */
  uint32_t dims;      /* ROW */
  int flex;           /* ROW */
  uint32_t n;         /* STRUCT: fields; UNION: members; PROC: parameters */
  uint32_t* strs;     /* STRUCT: field names (string indices) */
  uint32_t* modes;    /* STRUCT: field modes; UNION: members; PROC: parameters */
} a68_mode;

typedef enum {
  F_LIT, F_NL, F_NP, F_SP, F_BS, F_REP, F_DIG, F_SIGN, F_POINT, F_EXP, F_GEN, F_BOOL,
  F_CHOICE, F_CHAR, F_STRINGS, F_GROUP, F_INCL, F_SEP, F_COL, F_RADIX, F_HMARK, F_CPAT,
  F_CWIDTH, F_CAFTER, F_BAD
} a68_fkind;

typedef struct {
  a68_fkind k;
  uint32_t str;       /* LIT: the text; CPAT: the flags; BOOL: the flip text */
  uint32_t str2;      /* BOOL: the flop text */
  int flag;           /* DIG: zero-suppressing; SIGN: plus; BOOL: has texts */
  int64_t rep;        /* REP: the static replicator */
  uint32_t dyn;       /* REP: core index + 1 of the dynamic replicator, 0 for none; INCL: core index + 1 */
  uint32_t item;      /* REP: the item */
  uint32_t n;         /* GEN: arguments; CHOICE: alternatives; GROUP: items */
  uint32_t* list;     /* GEN: core indices; CHOICE: string indices; GROUP: item indices */
} a68_fmt;

typedef struct { int is_hole; uint32_t fn, idx; int64_t lit; } a68_core;
typedef struct { uint32_t n; uint32_t* items; } a68_fmtlist;
typedef struct { uint32_t name; uint32_t mode; } a68_decl;

extern a68_mode* modes; extern size_t nmodes;
extern a68_fmt* fmts;
extern a68_core* cores;
extern a68_fmtlist* fmtlists;
extern a68_decl* decls; extern size_t ndecls;

void tables_parse(const char* blob, char*** strtab_out, size_t** strlen_out, size_t* nstr_out);

/* `Mode.resolve`: a named mode unfolded to its structure (an index) */
uint32_t mode_resolve(uint32_t m);
/* `Mode.eqv` */
int mode_eqv(uint32_t a, uint32_t b);
/* `Mode.toString`: malloc'ed */
char* mode_string(uint32_t m);
/* the index of a simple mode, added to the table when absent */
uint32_t mode_simple(a68_mkind k, int64_t len);
uint32_t mode_ref(uint32_t sub);
uint32_t mode_row(uint32_t dims, int flex, uint32_t sub);
uint32_t mode_empty_union(void);
/* the mode a value of `INT`/`REAL`/… with a length tag */
const a68_mode* mode_at(uint32_t m);

#endif
