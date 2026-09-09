#!/usr/bin/env python3
"""Grammar-based random Algol 68 program generator for differential fuzzing.

Programs are generated so that Algol 68 Genie runs them without runtime errors:
integers stay far from overflow, divisors are never zero, subscripts stay in
bounds, every variable is initialised before use.  Every statement prints
something so that the byte-for-byte comparison of the two implementations is
sensitive to every value computed.

Usage: gen.py SEED OUTFILE
"""
import random, sys

rnd = random.Random(int(sys.argv[1]))
out = []

INT_VARS, REAL_VARS, BOOL_VARS, STR_VARS, CHAR_VARS, ARR_VARS = [], [], [], [], [], []
LOOP_VARS = []    # loop counters: readable but never assigned
PROCS = []        # (name, [param types], return type)
OPS = []          # (name, type)
DEPTH = 3

def pick(xs): return rnd.choice(xs)
def maybe(p=0.5): return rnd.random() < p
def ident(prefix):
    ident.n += 1
    return f"{prefix}{ident.n}"
ident.n = 0

def int_expr(d=0):
    r = rnd.random()
    if d >= DEPTH or r < 0.25:
        if INT_VARS and maybe(0.6): return pick(INT_VARS)
        return str(rnd.randint(-99, 99)) if maybe(0.7) else str(rnd.randint(0, 9999))
    if r < 0.45:
        return f"({int_expr(d+1)} {pick(['+', '-'])} {int_expr(d+1)})"
    if r < 0.55:
        return f"({small_int(d+1)} * {small_int(d+1)})"
    if r < 0.65:
        return f"({int_expr(d+1)} {pick(['OVER', 'MOD', '%', '%*'])} ({small_int(d+1)} MOD 7 + 1))"
    if r < 0.7:
        return f"ABS {int_expr(d+1)}"
    if r < 0.75:
        return f"SIGN {int_expr(d+1)}"
    if r < 0.8:
        return f"ENTIER {real_expr(d+1)}"
    if r < 0.84:
        return f"ROUND {real_expr(d+1)}"
    if r < 0.88 and ARR_VARS:
        a, n = pick(ARR_VARS)
        return f"{a}[ABS {int_expr(d+1)} MOD {n} + 1]"
    if r < 0.92 and STR_VARS:
        return f"UPB {pick(STR_VARS)}"
    if r < 0.95 and CHAR_VARS:
        return f"ABS {pick(CHAR_VARS)}"
    if r < 0.97 and [p for p in PROCS if p[2] == 'INT']:
        return call([p for p in PROCS if p[2] == 'INT'], d)
    return f"(IF {bool_expr(d+1)} THEN {int_expr(d+1)} ELSE {int_expr(d+1)} FI)"

def small_int(d=0):
    # values whose product stays safely inside 32 bits
    return f"({int_expr(d)} MOD 1000)"

def real_expr(d=0):
    r = rnd.random()
    if d >= DEPTH or r < 0.25:
        if REAL_VARS and maybe(0.6): return pick(REAL_VARS)
        v = rnd.choice([rnd.uniform(-100, 100), rnd.uniform(-1, 1), rnd.uniform(-1e6, 1e6), float(rnd.randint(-50, 50))])
        s = repr(v)
        if 'e' in s and '.' not in s.split('e')[0]: s = s.replace('e', '.0e')
        if '.' not in s: s += '.0'
        return s if v >= 0 else f"({s})"
    if r < 0.5:
        return f"({real_expr(d+1)} {pick(['+', '-', '*'])} {real_expr(d+1)})"
    if r < 0.6:
        return f"({real_expr(d+1)} / ({real_expr(d+1)} * {real_expr(d+1)} + 1.5))"
    if r < 0.65:
        return f"({int_expr(d+1)} / ({small_int(d+1)} MOD 9 + 2))"
    if r < 0.7:
        return f"sqrt(ABS {real_expr(d+1)})"
    if r < 0.75:
        return f"(sin({real_expr(d+1)}) ** {rnd.randint(0, 4)})"
    if r < 0.8:
        return f"{pick(['sin', 'cos', 'arctan', 'exp'])}({real_expr(d+1)} / 1000.0)"
    if r < 0.85:
        return f"ABS {real_expr(d+1)}"
    if r < 0.9:
        return f"({int_expr(d+1)} + {real_expr(d+1)})"
    if r < 0.93:
        return f"ln(ABS {real_expr(d+1)} + 1.0)"
    return f"(IF {bool_expr(d+1)} THEN {real_expr(d+1)} ELSE {real_expr(d+1)} FI)"

def bool_expr(d=0):
    r = rnd.random()
    if d >= DEPTH or r < 0.2:
        if BOOL_VARS and maybe(0.5): return pick(BOOL_VARS)
        return pick(['TRUE', 'FALSE'])
    if r < 0.5:
        return f"({int_expr(d+1)} {pick(['<', '<=', '>', '>=', '=', '/='])} {int_expr(d+1)})"
    if r < 0.65:
        return f"({real_expr(d+1)} {pick(['<', '<=', '>', '>='])} {real_expr(d+1)})"
    if r < 0.75:
        return f"({bool_expr(d+1)} {pick(['AND', 'OR'])} {bool_expr(d+1)})"
    if r < 0.8:
        return f"NOT {bool_expr(d+1)}"
    if r < 0.87:
        return f"ODD {int_expr(d+1)}"
    if r < 0.93 and STR_VARS:
        return f"({pick(STR_VARS)} {pick(['<', '=', '/=', '>='])} {str_expr(d+1)})"
    if r < 0.97 and CHAR_VARS:
        return f"({pick(CHAR_VARS)} {pick(['<', '=', '/='])} {char_expr(d+1)})"
    return f"({bool_expr(d+1)} XOR {bool_expr(d+1)})"

def char_expr(d=0):
    r = rnd.random()
    if d >= DEPTH or r < 0.4:
        if CHAR_VARS and maybe(0.5): return pick(CHAR_VARS)
        return '"' + pick('abcxyzAQZ09 ') + '"'
    if r < 0.7:
        return f"REPR (ABS {int_expr(d+1)} MOD 26 + 65)"
    if STR_VARS and maybe():
        s = pick(STR_VARS)
        return f"(UPB {s} > 0 | {s}[ABS {int_expr(d+1)} MOD UPB {s} + 1] | \"-\")"
    return f"(IF {bool_expr(d+1)} THEN {char_expr(d+1)} ELSE {char_expr(d+1)} FI)"

def str_lit():
    return '"' + ''.join(pick('abcdefgh xyz,.-:') for _ in range(rnd.randint(0, 8))).replace('"', '') + '"'

def str_expr(d=0):
    r = rnd.random()
    if d >= DEPTH or r < 0.25:
        if STR_VARS and maybe(0.6): return pick(STR_VARS)
        return str_lit()
    if r < 0.45:
        return f"({str_expr(d+1)} + {str_expr(d+1)})"
    if r < 0.55:
        return f"({str_expr(d+1)} + {char_expr(d+1)})"
    if r < 0.65:
        return f"(ABS {int_expr(d+1)} MOD 4 * {str_expr(d+1)})"
    if r < 0.75:
        return f"whole({int_expr(d+1)}, {rnd.randint(-8, 8)})"
    if r < 0.85:
        return f"fixed({real_expr(d+1)}, {rnd.randint(0, 14)}, {rnd.randint(0, 6)})"
    if r < 0.92:
        return f"float({real_expr(d+1)}, {rnd.randint(8, 22)}, {rnd.randint(1, 8)}, {rnd.randint(2, 4)})"
    if STR_VARS and maybe():
        s = pick(STR_VARS)
        return f"{s}[ABS {int_expr(d+1)} MOD (UPB {s} + 1) + 1 : UPB {s}]"
    return f"(IF {bool_expr(d+1)} THEN {str_expr(d+1)} ELSE {str_expr(d+1)} FI)"

def call(procs, d):
    name, params, _ = pick(procs)
    args = ", ".join(expr_of(t, d + 1) for t in params)
    return f"{name}({args})" if params else name

def expr_of(t, d=0):
    return {'INT': int_expr, 'REAL': real_expr, 'BOOL': bool_expr, 'STRING': str_expr, 'CHAR': char_expr}[t](d)

def emit(s): out.append(s)

def print_stmt():
    r = rnd.random()
    if r < 0.3:
        emit(f"print(({int_expr()}, newline));")
    elif r < 0.5:
        emit(f"print(({real_expr()}, newline));")
    elif r < 0.6:
        emit(f"print(({bool_expr()}, newline));")
    elif r < 0.7:
        emit(f"print(({str_expr()}, newline));")
    elif r < 0.8:
        emit(f"print(({char_expr()}, newline));")
    elif r < 0.9:
        fmt = pick(['$g(0)l$', '$5dl$', '$zzzdl$', '$-4dl$', '$+5dl$', '$g(-8)l$', '$"v="g(0)"."l$'])
        emit(f"printf(({fmt}, {int_expr()} MOD 10000));")
    else:
        fmt = pick(['$g(0,3)l$', '$g(-12,4)l$', '$-d.3dl$', '$zd.2dl$', '$g(14,5,2)l$', '$+3d.2de+2dl$', '$gl$'])
        emit(f"printf(({fmt}, sin({real_expr()}) * 9.0));")

def decl_stmt():
    r = rnd.random()
    if r < 0.25:
        v = ident("i"); e = int_expr(); INT_VARS.append(v); emit(f"INT {v} := {e};")
    elif r < 0.45:
        v = ident("r"); e = real_expr(); REAL_VARS.append(v); emit(f"REAL {v} := {e};")
    elif r < 0.55:
        v = ident("b"); e = bool_expr(); BOOL_VARS.append(v); emit(f"BOOL {v} := {e};")
    elif r < 0.7:
        v = ident("s"); e = str_expr(); STR_VARS.append(v); emit(f"STRING {v} := {e};")
    elif r < 0.8:
        v = ident("c"); e = char_expr(); CHAR_VARS.append(v); emit(f"CHAR {v} := {e};")
    elif r < 0.9:
        v = ident("a"); n = rnd.randint(1, 6)
        init = ', '.join(int_expr() for _ in range(n))
        ARR_VARS.append((v, n))
        emit(f"[{n}]INT {v} := ({init});")
    else:
        v = ident("k"); e = int_expr(); INT_VARS.append(v); emit(f"INT {v} = {e};")

def assign_stmt():
    r = rnd.random()
    if r < 0.3 and [v for v in INT_VARS if v not in LOOP_VARS and not v.startswith('k')]:
        v = pick([v for v in INT_VARS if v not in LOOP_VARS and not v.startswith('k')])
        if maybe(0.3): emit(f"{v} {pick(['+:=', '-:='])} {int_expr()};")
        else: emit(f"{v} := {int_expr()};")
    elif r < 0.5 and REAL_VARS:
        v = pick(REAL_VARS)
        if maybe(0.3): emit(f"{v} {pick(['+:=', '-:=', '*:='])} {real_expr()};")
        else: emit(f"{v} := {real_expr()};")
    elif r < 0.65 and STR_VARS:
        v = pick(STR_VARS)
        if maybe(0.4): emit(f"{v} +:= {str_expr()};")
        else: emit(f"{v} := {str_expr()};")
    elif r < 0.8 and ARR_VARS:
        a, n = pick(ARR_VARS)
        emit(f"{a}[{rnd.randint(1, n)}] := {int_expr()};")
    elif BOOL_VARS:
        emit(f"{pick(BOOL_VARS)} := {bool_expr()};")
    else:
        print_stmt()

def block(depth, n=None):
    n = n or rnd.randint(1, 4)
    body = []
    saved = out[:]
    scope = (INT_VARS[:], REAL_VARS[:], BOOL_VARS[:], STR_VARS[:], CHAR_VARS[:], ARR_VARS[:], PROCS[:])
    del out[:]
    for _ in range(n):
        stmt(depth + 1)
    print_stmt()   # a clause must not end with a declaration
    body = out[:]
    del out[:]
    out.extend(saved)
    # declarations inside the clause are not visible after it
    INT_VARS[:], REAL_VARS[:], BOOL_VARS[:], STR_VARS[:], CHAR_VARS[:], ARR_VARS[:], PROCS[:] = scope
    return body

def stmt(depth=0):
    r = rnd.random()
    if depth > 2 or r < 0.3:
        print_stmt(); return
    if r < 0.45:
        decl_stmt(); return
    if r < 0.6:
        assign_stmt(); return
    if r < 0.72:
        cond = bool_expr()
        b1 = block(depth); b2 = block(depth)
        emit(f"IF {cond} THEN")
        out.extend(b1)
        if out[-1].endswith(';'): out[-1] = out[-1][:-1]
        if maybe():
            emit("ELSE"); out.extend(b2)
            if out[-1].endswith(';'): out[-1] = out[-1][:-1]
        emit("FI;")
        return
    if r < 0.84:
        v = ident("j"); INT_VARS.append(v); LOOP_VARS.append(v)
        b = block(depth)
        INT_VARS.remove(v)
        emit(f"FOR {v} FROM {rnd.randint(-3, 3)} BY {pick([1, 2, -1, 3])} TO {rnd.randint(-3, 6)} DO")
        out.extend(b)
        if out[-1].endswith(';'): out[-1] = out[-1][:-1]
        emit("OD;")
        return
    if r < 0.9:
        v = ident("w"); INT_VARS.append(v); LOOP_VARS.append(v)
        emit(f"INT {v} := 0;")
        b = block(depth)
        emit(f"WHILE {v} < {rnd.randint(1, 4)} DO {v} +:= 1;")
        out.extend(b)
        if out[-1].endswith(';'): out[-1] = out[-1][:-1]
        emit("OD;")
        return
    if r < 0.95:
        emit(f"CASE ABS {int_expr()} MOD 3 + 1 IN")
        alts = []
        for _ in range(3):
            alts.append(f"print(({pick([int_expr(), str_expr()])}, newline))")
        emit(",\n".join(alts))
        emit(f"OUT print((\"out\", newline)) ESAC;")
        return
    # procedure declaration and call
    rt = pick(['INT', 'REAL', 'BOOL', 'STRING'])
    params = [pick(['INT', 'REAL', 'STRING']) for _ in range(rnd.randint(0, 2))]
    name = ident("p")
    pnames = [ident("x") for _ in params]
    saved = {'i': INT_VARS[:], 'r': REAL_VARS[:], 's': STR_VARS[:]}
    for t, pn in zip(params, pnames):
        {'INT': INT_VARS, 'REAL': REAL_VARS, 'STRING': STR_VARS}[t].append(pn)
    body = expr_of(rt)
    INT_VARS[:] = saved['i']; REAL_VARS[:] = saved['r']; STR_VARS[:] = saved['s']
    hdr = "(" + ", ".join(f"{t} {pn}" for t, pn in zip(params, pnames)) + ")" if params else ""
    emit(f"PROC {name} = {hdr}{rt}: {body};")
    PROCS.append((name, params, rt))
    emit(f"print(({call([(name, params, rt)], 0)}, newline));")

emit("BEGIN")
for _ in range(rnd.randint(4, 14)):
    stmt()
emit("print((\"end\", newline))")
emit("END")
open(sys.argv[2], "w").write("\n".join(out) + "\n")
