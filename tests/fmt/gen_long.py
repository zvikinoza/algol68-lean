#!/usr/bin/env python3
"""Generate extended number-formatting cases (LONG widths, printBits, fixedLongInt, the
frmt argument of float) for csrc/fmt_test.c and tests/fmt/fmtlong.lean.

    python3 tests/fmt/gen_long.py SEED COUNT > cases_long.txt
"""
import random, sys, struct
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
N = int(sys.argv[2]) if len(sys.argv) > 2 else 300

def rbig(digits):
    n = random.randint(0, 10 ** random.randint(1, digits) - 1)
    return -n if random.random() < 0.4 else n

def rreal():
    k = random.random()
    if k < 0.3: return repr(random.uniform(-1000, 1000))
    if k < 0.5: return repr(random.uniform(-1, 1))
    if k < 0.7: return repr(random.uniform(-1e10, 1e10))
    if k < 0.85: return "%.17g" % (random.random() * 10 ** random.randint(-30, 30))
    return "%.17g" % struct.unpack('d', struct.pack('Q', random.getrandbits(62)))[0]

lines = []
edge_ints = [0, 1, -1, 10 ** 49 - 1, -(10 ** 49 - 1), 10 ** 84 - 1, 10 ** 30, 2 ** 64, 2 ** 63 - 1, -2 ** 63,
             2 ** 63, 2 ** 64 - 1, 123456789012345678901234567890]
for n in edge_ints:
    for (l, ll) in [(0, 12), (1, 12), (2, 12), (2, 17), (2, 2)]:
        lines.append(("pin", n, l, ll))
    for (w, a) in [(0, 0), (0, 3), (30, 2), (-30, 5), (60, 10), (5, 1), (100, 30), (0, 80)]:
        lines.append(("fil", n, w, a))
    for (w, a, e, f) in [(30, 20, 4, 1), (30, 20, 4, 3), (40, 30, 3, -2), (20, 10, 2, 0), (0, 5, 2, 3), (60, 45, 4, 3)]:
        # floatDec with frmt <= 0 does not terminate on zero (in the Lean as in the C)
        if n != 0 or f > 0:
            lines.append(("flif", n, w, a, e, f))
    lines.append(("pb", abs(n), 32))
    lines.append(("pb", abs(n), 162))
    lines.append(("pb", abs(n), 279))
for _ in range(N):
    n = rbig(random.choice([9, 20, 49, 84, 100]))
    lines.append(("pin", n, random.choice([0, 1, 2]), random.choice([12, 12, 17, 6])))
    lines.append(("fil", n, random.randint(-60, 60), random.randint(0, 40)))
    f = random.choice([1, 2, 3, 0, -1, -3]) if n != 0 else random.choice([1, 2, 3])
    lines.append(("flif", n, random.randint(0, 60), random.randint(0, 30), random.randint(-4, 4), f))
    lines.append(("pb", random.getrandbits(random.choice([8, 32, 64, 162, 279])), random.choice([32, 162, 279, 1, 7])))
    x = rreal()
    lines.append(("prn", x, random.choice([0, 1, 2]), random.choice([12, 17, 2, 3])))
    lines.append(("flf", x, random.randint(0, 60), random.randint(0, 30), random.randint(-4, 4), random.choice([1, 2, 3, 0, -1, -3])))
for (l, ll) in [(0, 12), (1, 12), (2, 12), (2, 17), (2, 2), (2, 3), (-1, 12), (3, 30)]:
    lines.append(("widths", l, ll))
for n in [0, 1, 6, 7, 8, 28, 70, 84, 85, 100, 1000]:
    lines.append(("llp", n))
# subnormal and extreme reals: a68g's ten_up overflows and the digit loop extracts inf
for x in ["4.9406564584124654e-324", "2.2250738585072011e-308", "1e-310", "-3.5e-315", "1.7976931348623157e308",
          "1e-300", "9.9e-324", "2.2250738585072014e-308", "1e-320"]:
    lines.append(("pr", x))
    lines.append(("prn", x, 1, 12))
    lines.append(("fr", x, 40, 20))
    lines.append(("fl", x, 40, 20, 4))
    lines.append(("wr", x, 0))
for _ in range(N):
    x = rreal()
    lines.append(("sf", x, random.randint(0, 80), random.randint(-3, 40)))
    lines.append(("st", x, random.randint(-2, 40), random.randint(0, 40), random.randint(-5, 5)))
for l in lines:
    print(" ".join(str(v) for v in l))
