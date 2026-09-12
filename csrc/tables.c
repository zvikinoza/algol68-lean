/* The tables of a compiled program, parsed from the blob `A68.Serial.Writer.render`
   produces: one entry of every table per line, each line referring only to earlier
   ones.  The line grammar is `A68.Serial.putMode`, `putFmt`, `putFmtCore`, `putFmtList`
   and the `n` lines `CodeGen.program` adds for the mode declarations. */
#include "tables.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

a68_mode* modes = NULL; size_t nmodes = 0;
static size_t modes_cap = 0;
a68_fmt* fmts = NULL;
a68_core* cores = NULL;
a68_fmtlist* fmtlists = NULL;
a68_decl* decls = NULL; size_t ndecls = 0;

static char** tstr = NULL;
static size_t* tstrlen = NULL;
static size_t tnstr = 0;
size_t strtab_cap = 0;

static void* xm(size_t n) {
  void* p = calloc(1, n ? n : 1);
  if (!p) { fprintf(stderr, "a68lean: out of memory\n"); exit(1); }
  return p;
}

static int hexval(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return 10 + c - 'a';
  return 0;
}

/* the fields of a line, split on blanks */
typedef struct { const char* f[600]; size_t len[600]; size_t n; } fields;

static void split(const char* p, size_t n, fields* out) {
  out->n = 0;
  size_t i = 0;
  while (i < n) {
    while (i < n && p[i] == ' ') i++;
    if (i >= n) break;
    size_t j = i;
    while (j < n && p[j] != ' ') j++;
    if (out->n < 600) { out->f[out->n] = p + i; out->len[out->n] = j - i; out->n++; }
    i = j;
  }
}

static int64_t fld(const fields* fs, size_t i) {
  if (i >= fs->n) return 0;
  char buf[32];
  size_t n = fs->len[i] < 31 ? fs->len[i] : 31;
  memcpy(buf, fs->f[i], n); buf[n] = 0;
  return strtoll(buf, NULL, 10);
}

static int is(const fields* fs, size_t i, const char* s) {
  return i < fs->n && strlen(s) == fs->len[i] && memcmp(fs->f[i], s, fs->len[i]) == 0;
}

static uint32_t* ulist(const fields* fs, size_t from, uint32_t n) {
  uint32_t* l = (uint32_t*) xm((n ? n : 1) * sizeof(uint32_t));
  for (uint32_t k = 0; k < n; k++) l[k] = (uint32_t) fld(fs, from + k);
  return l;
}

static a68_mkind mkind_of(const fields* fs) {
  if (is(fs, 1, "int")) return M_INT;
  if (is(fs, 1, "real")) return M_REAL;
  if (is(fs, 1, "bool")) return M_BOOL;
  if (is(fs, 1, "char")) return M_CHAR;
  if (is(fs, 1, "void")) return M_VOID;
  if (is(fs, 1, "bits")) return M_BITS;
  if (is(fs, 1, "bytes")) return M_BYTES;
  if (is(fs, 1, "compl")) return M_COMPL;
  if (is(fs, 1, "ref")) return M_REF;
  if (is(fs, 1, "row")) return M_ROW;
  if (is(fs, 1, "proc")) return M_PROC;
  if (is(fs, 1, "struct")) return M_STRUCT;
  if (is(fs, 1, "union")) return M_UNION;
  if (is(fs, 1, "named")) return M_NAMED;
  if (is(fs, 1, "format")) return M_FORMAT;
  if (is(fs, 1, "file")) return M_FILE;
  if (is(fs, 1, "channel")) return M_CHANNEL;
  if (is(fs, 1, "sema")) return M_SEMA;
  if (is(fs, 1, "simplout")) return M_SIMPLOUT;
  if (is(fs, 1, "simplin")) return M_SIMPLIN;
  if (is(fs, 1, "number")) return M_NUMBER;
  return M_BAD;
}

static a68_fkind fkind_of(const fields* fs) {
  static const struct { const char* s; a68_fkind k; } tab[] = {
    {"lit", F_LIT}, {"nl", F_NL}, {"np", F_NP}, {"sp", F_SP}, {"bs", F_BS}, {"rep", F_REP},
    {"dig", F_DIG}, {"sign", F_SIGN}, {"point", F_POINT}, {"exp", F_EXP}, {"gen", F_GEN},
    {"bool", F_BOOL}, {"choice", F_CHOICE}, {"char", F_CHAR}, {"strings", F_STRINGS},
    {"group", F_GROUP}, {"incl", F_INCL}, {"sep", F_SEP}, {"col", F_COL}, {"radix", F_RADIX},
    {"hmark", F_HMARK}, {"cpat", F_CPAT}, {"cwidth", F_CWIDTH}, {"cafter", F_CAFTER} };
  for (size_t i = 0; i < sizeof tab / sizeof tab[0]; i++) if (is(fs, 1, tab[i].s)) return tab[i].k;
  return F_BAD;
}

void tables_parse(const char* blob, char*** strtab_out, size_t** strlen_out, size_t* nstr_out) {
  size_t lines = 1;
  for (const char* p = blob; *p; p++) if (*p == '\n') lines++;
  modes_cap = lines + 64;
  modes = (a68_mode*) xm(modes_cap * sizeof(a68_mode));
  fmts = (a68_fmt*) xm(lines * sizeof(a68_fmt));
  cores = (a68_core*) xm(lines * sizeof(a68_core));
  fmtlists = (a68_fmtlist*) xm(lines * sizeof(a68_fmtlist));
  decls = (a68_decl*) xm(lines * sizeof(a68_decl));
  strtab_cap = lines + 1024;   /* room for the names the Lean side adds while it is still linked */
  tstr = (char**) xm(strtab_cap * sizeof(char*));
  tstrlen = (size_t*) xm(strtab_cap * sizeof(size_t));
  const char* p = blob;
  size_t i = 0;
  fields fs;
  while (1) {
    const char* e = strchr(p, '\n');
    size_t n = e ? (size_t) (e - p) : strlen(p);
    tstr[i] = (char*) xm(1); tstrlen[i] = 0;
    modes[i].k = M_VOID;
    fmts[i].k = F_SEP;
    split(p, n, &fs);
    if (fs.n >= 1) {
      if (is(&fs, 0, "s")) {
        size_t hn = fs.n >= 2 ? fs.len[1] : 0;
        char* s = (char*) xm(hn / 2 + 1);
        for (size_t k = 0; k + 1 < hn; k += 2) s[k / 2] = (char) (hexval(fs.f[1][k]) * 16 + hexval(fs.f[1][k + 1]));
        free(tstr[i]);
        tstr[i] = s; tstrlen[i] = hn / 2;
      } else if (is(&fs, 0, "m")) {
        a68_mode* m = &modes[i];
        m->k = mkind_of(&fs);
        switch (m->k) {
          case M_INT: case M_REAL: case M_BITS: case M_BYTES: case M_COMPL: m->len = fld(&fs, 2); break;
          case M_REF: m->sub = (uint32_t) fld(&fs, 2); break;
          case M_ROW: m->dims = (uint32_t) fld(&fs, 2); m->flex = fld(&fs, 3) == 1; m->sub = (uint32_t) fld(&fs, 4); break;
          case M_PROC: m->sub = (uint32_t) fld(&fs, 2); m->n = (uint32_t) fld(&fs, 3); m->modes = ulist(&fs, 4, m->n); break;
          case M_STRUCT:
            m->n = (uint32_t) fld(&fs, 2);
            m->strs = (uint32_t*) xm((m->n ? m->n : 1) * sizeof(uint32_t));
            m->modes = (uint32_t*) xm((m->n ? m->n : 1) * sizeof(uint32_t));
            for (uint32_t k = 0; k < m->n; k++) { m->strs[k] = (uint32_t) fld(&fs, 3 + 2 * k); m->modes[k] = (uint32_t) fld(&fs, 4 + 2 * k); }
            break;
          case M_UNION: m->n = (uint32_t) fld(&fs, 2); m->modes = ulist(&fs, 3, m->n); break;
          case M_NAMED: m->sub = (uint32_t) fld(&fs, 2); break;
          default: break;
        }
      } else if (is(&fs, 0, "c")) {
        if (is(&fs, 1, "hole")) { cores[i].is_hole = 1; cores[i].fn = (uint32_t) fld(&fs, 2); cores[i].idx = (uint32_t) fld(&fs, 3); }
        else if (is(&fs, 1, "int")) { cores[i].is_hole = 0; cores[i].lit = fld(&fs, 2); }
      } else if (is(&fs, 0, "f")) {
        a68_fmt* f = &fmts[i];
        f->k = fkind_of(&fs);
        switch (f->k) {
          case F_LIT: case F_CPAT: f->str = (uint32_t) fld(&fs, 2); break;
          case F_REP: f->rep = fld(&fs, 2); f->dyn = (uint32_t) fld(&fs, 3); f->item = (uint32_t) fld(&fs, 4); break;
          case F_DIG: case F_SIGN: f->flag = fld(&fs, 2) == 1; break;
          case F_GEN: case F_CHOICE: case F_GROUP: f->n = (uint32_t) fld(&fs, 2); f->list = ulist(&fs, 3, f->n); break;
          case F_BOOL: f->flag = fld(&fs, 2) == 1; if (f->flag) { f->str = (uint32_t) fld(&fs, 3); f->str2 = (uint32_t) fld(&fs, 4); } break;
          case F_INCL: f->dyn = (uint32_t) fld(&fs, 2) + 1; break;
          default: break;
        }
      } else if (is(&fs, 0, "k")) {
        fmtlists[i].n = (uint32_t) fld(&fs, 1);
        fmtlists[i].items = ulist(&fs, 2, fmtlists[i].n);
      } else if (is(&fs, 0, "n")) {
        decls[ndecls].name = (uint32_t) fld(&fs, 1);
        decls[ndecls].mode = (uint32_t) fld(&fs, 2);
        ndecls++;
      }
    }
    i++;
    if (!e) break;
    p = e + 1;
  }
  nmodes = i;
  tnstr = i;
  *strtab_out = tstr; *strlen_out = tstrlen; *nstr_out = tnstr;
}

const a68_mode* mode_at(uint32_t m) {
  static a68_mode bad = { M_BAD, 0, 0, 0, 0, 0, NULL, NULL };
  return m < nmodes ? &modes[m] : &bad;
}

static int name_eq(uint32_t si, uint32_t sj) {
  return tstrlen[si] == tstrlen[sj] && memcmp(tstr[si], tstr[sj], tstrlen[si]) == 0;
}

/* the declaration of a named mode, or nmodes when there is none */
static uint32_t decl_of(uint32_t name) {
  for (size_t i = 0; i < ndecls; i++) if (name_eq(decls[i].name, name)) return decls[i].mode;
  return (uint32_t) nmodes;
}

/* `Mode.resolve`, with its fuel of 32 */
uint32_t mode_resolve(uint32_t m) {
  for (int fuel = 32; fuel > 0; fuel--) {
    const a68_mode* mm = mode_at(m);
    if (mm->k != M_NAMED) return m;
    uint32_t d = decl_of(mm->sub);
    if (d >= nmodes) return m;
    m = d;
  }
  return m;
}

/* `Mode.eqv`, with its fuel of 64 */
static int eqv(uint32_t a, uint32_t b, int fuel) {
  if (fuel == 0) return 0;
  const a68_mode* x = mode_at(a);
  const a68_mode* y = mode_at(b);
  if (x->k == M_NAMED && y->k == M_NAMED) {
    if (name_eq(x->sub, y->sub)) return 1;
    uint32_t da = decl_of(x->sub), db = decl_of(y->sub);
    if (da >= nmodes || db >= nmodes) return 0;
    return eqv(da, db, fuel - 1);
  }
  if (x->k == M_NAMED) { uint32_t d = decl_of(x->sub); return d < nmodes && eqv(d, b, fuel - 1); }
  if (y->k == M_NAMED) { uint32_t d = decl_of(y->sub); return d < nmodes && eqv(a, d, fuel - 1); }
  if (x->k != y->k) return 0;
  switch (x->k) {
    case M_INT: case M_REAL: case M_BITS: case M_BYTES: case M_COMPL: return x->len == y->len;
    case M_BOOL: case M_CHAR: case M_VOID: case M_FORMAT: case M_FILE: case M_CHANNEL: case M_SEMA:
    case M_SIMPLOUT: case M_SIMPLIN: case M_NUMBER: return 1;
    case M_REF: return eqv(x->sub, y->sub, fuel - 1);
    case M_ROW: return x->dims == y->dims && eqv(x->sub, y->sub, fuel - 1);
    case M_PROC:
      if (x->n != y->n) return 0;
      for (uint32_t k = 0; k < x->n; k++) if (!eqv(x->modes[k], y->modes[k], fuel - 1)) return 0;
      return eqv(x->sub, y->sub, fuel - 1);
    case M_STRUCT:
      if (x->n != y->n) return 0;
      for (uint32_t k = 0; k < x->n; k++) if (!name_eq(x->strs[k], y->strs[k]) || !eqv(x->modes[k], y->modes[k], fuel - 1)) return 0;
      return 1;
    case M_UNION:
      if (x->n != y->n) return 0;
      for (uint32_t k = 0; k < x->n; k++) {
        int found = 0;
        for (uint32_t j = 0; j < y->n && !found; j++) if (eqv(x->modes[k], y->modes[j], fuel - 1)) found = 1;
        if (!found) return 0;
      }
      return 1;
    default: return 0;
  }
}

int mode_eqv(uint32_t a, uint32_t b) { return eqv(a, b, 64); }

/* ---------------------------------------------------------------- Mode.toString */

typedef struct { char* p; size_t n, cap; } sb;
static void sb_add(sb* b, const char* s, size_t n) {
  if (b->n + n + 1 > b->cap) { b->cap = (b->n + n + 1) * 2 + 32; b->p = (char*) realloc(b->p, b->cap); if (!b->p) exit(1); }
  memcpy(b->p + b->n, s, n); b->n += n; b->p[b->n] = 0;
}
static void sb_str(sb* b, const char* s) { sb_add(b, s, strlen(s)); }

static void long_prefix(sb* b, int64_t n) {
  for (int64_t k = 0; k < n; k++) sb_str(b, "LONG ");
  for (int64_t k = 0; k < -n; k++) sb_str(b, "SHORT ");
}

static void mode_to(sb* b, uint32_t m, int fuel) {
  const a68_mode* x = mode_at(m);
  if (fuel == 0) { sb_str(b, "..."); return; }
  switch (x->k) {
    case M_INT: long_prefix(b, x->len); sb_str(b, "INT"); break;
    case M_REAL: long_prefix(b, x->len); sb_str(b, "REAL"); break;
    case M_BOOL: sb_str(b, "BOOL"); break;
    case M_CHAR: sb_str(b, "CHAR"); break;
    case M_VOID: sb_str(b, "VOID"); break;
    case M_BITS: long_prefix(b, x->len); sb_str(b, "BITS"); break;
    case M_BYTES: long_prefix(b, x->len); sb_str(b, "BYTES"); break;
    case M_COMPL: long_prefix(b, x->len); sb_str(b, "COMPL"); break;
    case M_REF: sb_str(b, "REF "); mode_to(b, x->sub, fuel - 1); break;
    case M_ROW:
      if (x->flex) sb_str(b, "FLEX ");
      sb_str(b, "[");
      for (uint32_t k = 1; k < x->dims; k++) sb_str(b, ",");
      sb_str(b, "] ");
      mode_to(b, x->sub, fuel - 1);
      break;
    case M_PROC:
      sb_str(b, "PROC ");
      if (x->n) {
        sb_str(b, "(");
        for (uint32_t k = 0; k < x->n; k++) { if (k) sb_str(b, ", "); mode_to(b, x->modes[k], fuel - 1); }
        sb_str(b, ") ");
      }
      mode_to(b, x->sub, fuel - 1);
      break;
    case M_STRUCT:
      sb_str(b, "STRUCT (");
      for (uint32_t k = 0; k < x->n; k++) {
        if (k) sb_str(b, ", ");
        mode_to(b, x->modes[k], fuel - 1);
        sb_str(b, " ");
        sb_add(b, tstr[x->strs[k]], tstrlen[x->strs[k]]);
      }
      sb_str(b, ")");
      break;
    case M_UNION:
      sb_str(b, "UNION (");
      for (uint32_t k = 0; k < x->n; k++) { if (k) sb_str(b, ", "); mode_to(b, x->modes[k], fuel - 1); }
      sb_str(b, ")");
      break;
    case M_NAMED: sb_add(b, tstr[x->sub], tstrlen[x->sub]); break;
    case M_FORMAT: sb_str(b, "FORMAT"); break;
    case M_FILE: sb_str(b, "FILE"); break;
    case M_CHANNEL: sb_str(b, "CHANNEL"); break;
    case M_SEMA: sb_str(b, "SEMA"); break;
    case M_SIMPLOUT: sb_str(b, "SIMPLOUT"); break;
    case M_SIMPLIN: sb_str(b, "SIMPLIN"); break;
    case M_NUMBER: sb_str(b, "NUMBER"); break;
    default: sb_str(b, "?"); break;
  }
}

char* mode_string(uint32_t m) {
  sb b = {0};
  sb_str(&b, "");
  mode_to(&b, m, 40);
  return b.p;
}

/* ---------------------------------------------------------------- modes made at run time */

static uint32_t mode_push(a68_mode m) {
  if (nmodes == modes_cap) {
    modes_cap = modes_cap * 2 + 64;
    modes = (a68_mode*) realloc(modes, modes_cap * sizeof(a68_mode));
    if (!modes) exit(1);
  }
  modes[nmodes] = m;
  return (uint32_t) nmodes++;
}

uint32_t mode_simple(a68_mkind k, int64_t len) {
  for (size_t i = 0; i < nmodes; i++) if (modes[i].k == k && modes[i].len == len) return (uint32_t) i;
  a68_mode m; memset(&m, 0, sizeof m); m.k = k; m.len = len;
  return mode_push(m);
}

uint32_t mode_ref(uint32_t sub) {
  for (size_t i = 0; i < nmodes; i++) if (modes[i].k == M_REF && modes[i].sub == sub) return (uint32_t) i;
  a68_mode m; memset(&m, 0, sizeof m); m.k = M_REF; m.sub = sub;
  return mode_push(m);
}

uint32_t mode_row(uint32_t dims, int flex, uint32_t sub) {
  for (size_t i = 0; i < nmodes; i++)
    if (modes[i].k == M_ROW && modes[i].dims == dims && modes[i].flex == flex && modes[i].sub == sub) return (uint32_t) i;
  a68_mode m; memset(&m, 0, sizeof m); m.k = M_ROW; m.dims = dims; m.flex = flex; m.sub = sub;
  return mode_push(m);
}

/* the mode of `Value.emptyUnion`: a union of no modes */
uint32_t mode_empty_union(void) {
  for (size_t i = 0; i < nmodes; i++) if (modes[i].k == M_UNION && modes[i].n == 0) return (uint32_t) i;
  a68_mode m; memset(&m, 0, sizeof m); m.k = M_UNION; m.n = 0; m.modes = (uint32_t*) xm(sizeof(uint32_t));
  return mode_push(m);
}
