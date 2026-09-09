#!/usr/bin/env python3
"""Generate matching a68g / a68lean inputs for number-formatting differential tests."""
import random, sys, struct
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
N = int(sys.argv[2]) if len(sys.argv) > 2 else 400
ints = [0, 1, -1, 7, -7, 42, 123, 999, 1000, 12345, -12345, 2147483647, -2147483647, 1000000, 9999999, 10000000, 65536]
reals = ["0.0","1.0","-1.0","0.5","-0.5","0.125","2.675","9.996","0.1","0.2","0.3","1e-10","1e22","123456789012345678.0","3.14159","2.718281828459045","1e100","1.7976931348623157e308","2.2204460492503131e-16","0.005","123.456","0.999999","99.5","0.05","1.5e-5","12345.678","100000.0","1e7","9999999.0","10000001.0","0.000123","1e-5","1e-7","1e15","1e16","1e17","123456.7"]
def rreal():
    k = random.random()
    if k < 0.3: return repr(random.uniform(-1000, 1000))
    if k < 0.5: return repr(random.uniform(-1, 1))
    if k < 0.7: return repr(random.uniform(-1e10, 1e10))
    if k < 0.85: return "%.17g" % (random.random() * 10 ** random.randint(-30, 30))
    return "%.17g" % struct.unpack('d', struct.pack('Q', random.getrandbits(62)))[0]
lines = []
for n in ints:
    for w in [0, 1, 2, 5, 11, -5, -11, 20]:
        lines.append(("w", n, w))
    lines.append(("pi", n))
for _ in range(N):
    n = random.randint(-2147483647, 2147483647)
    lines.append(("w", n, random.choice([0, 3, 5, 8, 11, 12, -6, -11])))
    lines.append(("pi", n))
    lines.append(("fi", n, random.randint(-20, 20), random.randint(0, 5)))
    lines.append(("fli", n, random.randint(0, 25), random.randint(0, 6), random.randint(-3, 4)))
for x in reals:
    lines.append(("pr", x))
    for (w, a) in [(0,2),(0,0),(5,2),(10,3),(-10,3),(8,0),(3,2),(20,10),(0,6),(0,20),(30,25)]:
        lines.append(("fr", x, w, a))
    for (w, a, e) in [(22,14,4),(10,3,2),(12,4,3),(8,2,1),(0,3,2),(5,0,2),(6,1,1),(9,2,2),(15,6,-3),(30,20,5),(22,14,-4)]:
        lines.append(("fl", x, w, a, e))
    lines.append(("wr", x, random.choice([0, 5, 10, -10])))
for _ in range(N):
    x = rreal()
    lines.append(("pr", x))
    lines.append(("fr", x, random.randint(-25, 25), random.randint(0, 12)))
    lines.append(("fl", x, random.randint(0, 30), random.randint(0, 12), random.randint(-6, 6)))
    lines.append(("wr", x, random.randint(-15, 15)))
with open("cases.txt", "w") as f:
    for l in lines: f.write(" ".join(str(v) for v in l) + "\n")
def a68real(x):
    # ensure a68g parses it as a REAL: needs digit before '.', exponent form ok
    s = x
    if s.startswith("-"): s = s[1:]; neg = True
    else: neg = False
    if "e" in s and "." not in s.split("e")[0]: s = s.replace("e", ".0e")
    if "." not in s: s = s + ".0"
    if s.startswith("."): s = "0" + s
    return ("-" + s) if neg else s
with open("cases.a68", "w") as f:
    f.write("BEGIN\n")
    for l in lines:
        k = l[0]
        if k == "w": f.write(f'print((whole({l[1]}, {l[2]}), newline));\n')
        elif k == "pi": f.write(f'print(({l[1]}, newline));\n')
        elif k == "fi": f.write(f'print((fixed({l[1]}, {l[2]}, {l[3]}), newline));\n')
        elif k == "fli": f.write(f'print((float({l[1]}, {l[2]}, {l[3]}, {l[4]}), newline));\n')
        elif k == "pr": f.write(f'print(({a68real(l[1])}, newline));\n')
        elif k == "fr": f.write(f'print((fixed({a68real(l[1])}, {l[2]}, {l[3]}), newline));\n')
        elif k == "fl": f.write(f'print((float({a68real(l[1])}, {l[2]}, {l[3]}, {l[4]}), newline));\n')
        elif k == "wr": f.write(f'print((whole({a68real(l[1])}, {l[2]}), newline));\n')
    f.write("SKIP\nEND\n")
