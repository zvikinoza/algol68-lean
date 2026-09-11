#!/usr/bin/env python3
"""Generate a differential test for csrc/mp.c: random LONG / LONG LONG operations.

Usage: mp_gen.py SEED N PROG.a68 [PRECISION] > ops.txt

Writes the operations file (read by mp_test) to stdout and the equivalent Algol 68
program, which prints the same values with the evaluator, to PROG.a68.  With a
PRECISION the program starts with `PR precision PRECISION PR` and mp_test must be run
with the matching digit count (2 + ceil (PRECISION / 7)).  Operations are emitted in
the order both sides perform them, since a68g's π and ln caches depend on history."""
import random, sys

seed = int(sys.argv[1]); N = int(sys.argv[2]); prog = sys.argv[3]
prec = int(sys.argv[4]) if len(sys.argv) > 4 else None
random.seed(seed)
ll = 2 + (prec + 6) // 7 if prec else 12

MODES = ["L", "LL"]
def kw(m): return "LONG" if m == "L" else "LONG LONG"
def fn(m): return "long" if m == "L" else "long long"

def mant(nd):
    """A random mantissa of nd significant digits, as `d.ddd`."""
    s = str(random.randint(1, 9)) + "".join(random.choice("0123456789") for _ in range(nd - 1))
    return s[0] + "." + s[1:] if nd > 1 else s + ".0"

def rreal(lo=-30, hi=30, m="L", neg=True, nonzero=False):
    """A random LONG REAL denotation text (with a leading '-' for a negative one)."""
    k = random.random()
    maxd = 42 if m == "L" else (ll - 2) * 7
    if k < 0.15: nd = random.randint(1, 3)
    elif k < 0.6: nd = random.randint(4, 16)
    else: nd = random.randint(17, maxd + 3)
    e = random.randint(lo, hi)
    s = mant(nd)
    r = random.random()
    if r < 0.3 and -5 <= e <= 5:
        # a plain decimal without exponent
        digs = s.replace(".", "")
        if e >= 0: s = digs[:e + 1].ljust(e + 1, "0") + "." + (digs[e + 1:] or "0")
        else: s = "0." + "0" * (-e - 1) + digs
    else:
        s = s + "e" + str(e)
    if neg and random.random() < 0.4: s = "-" + s
    return s

def rsmall(lo, hi, m="L", neg=True, nonzero=False):
    """A random value with |x| between 10^lo and 10^hi."""
    return rreal(lo, hi, m, neg)

def a68(m, s):
    """The Algol 68 text of a denotation with its sign."""
    if s.startswith("-"): return "(-%s %s)" % (kw(m), s[1:])
    return "%s %s" % (kw(m), s)

ops = []   # (ops line, a68 unit)
def emit(line, unit): ops.append((line, unit))

def rint(nd):
    return str(random.randint(1, 9)) + "".join(random.choice("0123456789") for _ in range(nd - 1))

def gen_one():
    m = random.choice(MODES)
    kind = random.choices(
        ["bin", "cmp", "mon", "fn", "fmt", "int", "cbin", "cfn", "conv", "misc"],
        [22, 6, 8, 20, 14, 8, 8, 6, 5, 3])[0]
    if kind == "bin":
        op = random.choice(["+", "-", "*", "/", "**", "+", "-", "*", "/"])
        if op == "**":
            a = rreal(-3, 3, m, neg=False); b = rreal(-2, 1, m)
        elif op == "/":
            a = rreal(-40, 40, m); b = rreal(-40, 40, m)
            if b.lstrip("-").startswith("0"): b = "1.5"
        else:
            a = rreal(-40, 40, m); b = rreal(-40, 40, m)
            if random.random() < 0.15:   # nearly aligned operands exercise the cancellation paths
                b = a[:-1] + random.choice("0123456789") if len(a) > 3 else a
        emit("bin %s %s %s %s" % (m, op, a, b), "%s %s %s" % (a68(m, a), op, a68(m, b)))
    elif kind == "cmp":
        op = random.choice(["=", "/=", "<", "<=", ">", ">="])
        a = rreal(-10, 10, m); b = a if random.random() < 0.3 else rreal(-10, 10, m)
        emit("cmp %s %s %s %s" % (m, op, a, b), "%s %s %s" % (a68(m, a), op, a68(m, b)))
    elif kind == "mon":
        op = random.choice(["-", "ABS", "SIGN", "ENTIER", "ROUND", "ENTIER", "ROUND"])
        a = rreal(-8, 40 if op in ("ENTIER", "ROUND") else 40, m)
        if op in ("ENTIER", "ROUND") and random.random() < 0.3:
            a = random.choice(["2.5", "-2.5", "0.5", "-0.5", "3.0", "-3.0", "0.0", "1e-30", "-1e-30", "12345678.5", "-12345678.5"])
        emit("mon %s %s %s" % (m, op, a), "%s %s" % (op, a68(m, a)))
    elif kind == "fn":
        name = random.choice(["sqrt", "curt", "exp", "ln", "log", "sin", "cos", "tan", "cot", "arcsin", "arccos",
                              "arctan", "sinh", "cosh", "tanh", "arcsinh", "arccosh", "arctanh", "csc", "sec",
                              "arccsc", "arcsec", "arccot", "sindg", "cosdg", "tandg", "cotdg", "cscdg", "secdg",
                              "arcsindg", "arccosdg", "arctandg", "arccotdg", "arccscdg", "arcsecdg", "cas",
                              "sqrt", "exp", "ln", "sin", "cos", "arctan"])
        if name == "sqrt": a = rreal(-60, 60, m, neg=False)
        elif name == "curt": a = rreal(-60, 60, m)
        elif name in ("exp", "sinh", "cosh", "tanh"): a = rreal(-30, 2, m)
        elif name in ("ln", "log"): a = rreal(-60, 60, m, neg=False)
        elif name in ("sin", "cos", "tan", "cot", "csc", "sec", "cas"): a = rreal(-10, 4, m)
        elif name in ("arcsin", "arccos", "arctanh", "arcsindg", "arccosdg"): a = rreal(-20, -1, m)
        elif name in ("arccosh", "arccsc", "arcsec", "arccscdg", "arcsecdg"): a = rreal(0, 20, m, neg=name != "arccosh")
        elif name in ("sindg", "cosdg", "tandg", "cotdg", "cscdg", "secdg"): a = rreal(-3, 5, m)
        elif name == "arcsinh": a = rreal(-30, 8, m)   # sqrt (x² + 1) + x cancels to 0 for large negative x
        else: a = rreal(-30, 30, m)
        if name in ("arccosh",) and random.random() < 0.2: a = "1.0"
        emit("fn %s %s %s" % (m, name, a), "%s %s(%s)" % (fn(m), name, a68(m, a)))
    elif kind == "fmt":
        a = rreal(-25, 25, m)
        k = random.choice(["whole", "fixed", "float", "float2"])
        if k == "whole":
            w = random.randint(-60, 60)
            emit("fmt %s whole %s %d" % (m, a, w), "whole(%s, %d)" % (a68(m, a), w))
        elif k == "fixed":
            w = random.randint(-70, 70); af = random.randint(0, 50)
            emit("fmt %s fixed %s %d %d" % (m, a, w, af), "fixed(%s, %d, %d)" % (a68(m, a), w, af))
        elif k == "float":
            w = random.randint(0, 90); af = random.randint(0, 50); e = random.randint(-6, 6)
            emit("fmt %s float %s %d %d %d" % (m, a, w, af, e), "float(%s, %d, %d, %d)" % (a68(m, a), w, af, e))
        else:
            w = random.randint(0, 90); af = random.randint(0, 50); e = random.randint(1, 6); f = random.randint(-3, 3)
            emit("fmt %s float2 %s %d %d %d %d" % (m, a, w, af, e, f), "real(%s, %d, %d, %d, %d)" % (a68(m, a), w, af, e, f))
    elif kind == "int":
        maxd = 49 if m == "L" else ll * 7
        op = random.choice(["+", "-", "*", "%", "%*", "/", "**"])
        if op == "**":
            a = rint(random.randint(1, 4)); b = str(random.randint(0, 8))
            if len(a) * int(b) > maxd - 2: b = "2"
            a = ("-" if random.random() < 0.3 else "") + a
            emit("int %s ** %s %s" % (m, a, b), "%s ** %s" % (a68(m, a), b))
            return
        if op == "*":
            na = random.randint(1, maxd // 2 - 1); nb = random.randint(1, maxd - na - 2)
        else:
            na = random.randint(1, maxd - 2); nb = random.randint(1, maxd - 2)
        a = rint(na); b = rint(nb)
        if random.random() < 0.3 and op not in ("%*",): a = "-" + a
        if random.random() < 0.3 and op not in ("%*",): b = "-" + b
        if random.random() < 0.2 and op in ("%", "%*"): b = str(random.randint(1, 3000))
        unit = "%s %s %s" % (a68(m, a), op, a68(m, b))
        emit("int %s %s %s %s" % (m, op, a, b), unit)
    elif kind == "cbin":
        op = random.choice(["+", "-", "*", "/", "=", "/=", "**"])
        a, b, c, d = (rreal(-10, 10, m) for _ in range(4))
        if op == "**":
            k = random.randint(-6, 8)
            emit("cpow %s %s %s %d" % (m, a, b, k), "(%s I %s) ** %d" % (a68(m, a), a68(m, b), k))
        elif op in ("=", "/=") and random.random() < 0.3:
            emit("cbin %s %s %s %s %s %s" % (m, op, a, b, a, b), "(%s I %s) %s (%s I %s)" % (a68(m, a), a68(m, b), op, a68(m, a), a68(m, b)))
        else:
            emit("cbin %s %s %s %s %s %s" % (m, op, a, b, c, d), "(%s I %s) %s (%s I %s)" % (a68(m, a), a68(m, b), op, a68(m, c), a68(m, d)))
    elif kind == "cfn":
        if random.random() < 0.3:
            op = random.choice(["-", "CONJ", "RE", "IM", "ABS", "ARG"])
            a, b = rreal(-10, 10, m), rreal(-10, 10, m)
            emit("cmon %s %s %s %s" % (m, op, a, b), "%s (%s I %s)" % (op, a68(m, a), a68(m, b)))
        else:
            name = random.choice(["sqrt", "exp", "ln", "sin", "cos", "tan", "arcsin", "arccos", "arctan",
                                  "sinh", "cosh", "tanh", "arcsinh", "arccosh", "arctanh"])
            a, b = rreal(-4, 1, m), rreal(-4, 1, m)
            emit("cfn %s %s %s %s" % (m, name, a, b), "%s complex %s(%s I %s)" % (fn(m), name, a68(m, a), a68(m, b)))
    elif kind == "conv":
        k = random.choice(["shorten", "leng", "real", "roundtrip"])
        if k == "shorten":
            a = rreal(-30, 30, "LL")
            emit("shorten %s" % a, "SHORTEN %s" % a68("LL", a))
        elif k == "leng":
            a = rreal(-30, 30, "L")
            emit("leng %s" % a, "LENG %s" % a68("L", a))
        elif k == "real":
            a = rreal(-30, 30, "L"); mm = random.choice(MODES)
            unit = "BEGIN REAL r := %s; print((%s r, newline)) END" % (a, "LENG" if mm == "L" else "LENG LENG")
            ops.append(("real %s %s" % (mm, a), None)); ops[-1] = ("real %s %s" % (mm, a), ("raw", unit))
        else:
            a = rreal(-30, 30, "L")
            emit("roundtrip %s" % a, "LENG SHORTEN %s" % a68("L", a))
    else:
        k = random.choice(["pi", "atan2", "atan2dg", "powi"])
        if k == "pi":
            emit("pi %s" % m, "%s pi" % fn(m))
        elif k == "powi":
            a = rreal(-3, 3, m); e = random.randint(-30, 30)
            emit("powi %s %s %d" % (m, a, e), "%s ** %d" % (a68(m, a), e))
        else:
            a, b = rreal(-5, 5, m), rreal(-5, 5, m)
            if random.random() < 0.15: a = "0.0"
            emit("%s %s %s %s" % (k, m, a, b), "%s %s(%s, %s)" % (fn(m), "arctan2" if k == "atan2" else "arctan2dg", a68(m, a), a68(m, b)))

for _ in range(N): gen_one()

with open(prog, "w") as f:
    if prec: f.write("PR precision %d PR\n" % prec)
    f.write("BEGIN\n")
    for line, unit in ops:
        if isinstance(unit, tuple): f.write(unit[1] + ";\n")
        else: f.write("print((%s, newline));\n" % unit)
        sys.stdout.write(line + "\n")
    f.write("SKIP\nEND\n")
