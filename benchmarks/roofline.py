#!/usr/bin/env python3
"""Roofline analysis of a68lean's emitted code.

The classical roofline bounds achieved performance by machine peaks. For a
compiler the interesting ceiling is not the silicon but the *same algorithm
written by hand in C*: that is what the emitted code could in principle reach,
since it runs on the same machine with the same memory traffic. So for each
benchmark we take

    ceiling = the hand-written C program in native/
    floor   = what each implementation achieves

and report, per Algol 68 operation:

    ns/op            wall time divided by the declared operation count
    slowdown         ns/op relative to native C
    overhead ns/op   ns/op minus native ns/op — the cost the implementation adds
                     per operation, which is what an optimisation has to remove

The machine peaks are measured too (scalar integer throughput and memory
bandwidth), so it is visible whether a benchmark is compute- or memory-bound and
therefore which ceiling applies.

Usage: roofline.py [results/bench.csv]
"""
import csv, subprocess, sys, os, tempfile, textwrap

HERE = os.path.dirname(os.path.abspath(__file__))

PEAK_SRC = r"""
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
int main(void){
  /* scalar integer add throughput (dependent chain: one add per cycle at best) */
  volatile long long sink=0; long long n=2000000000LL, s=0; double t0=now();
  for(long long i=0;i<n;i++) s+=i;
  double t1=now(); sink=s;
  /* memory streaming bandwidth */
  size_t m=64u*1024*1024; char*b=malloc(m); for(size_t i=0;i<m;i++) b[i]=(char)i;
  double t2=now(); long long acc=0;
  for(int r=0;r<4;r++) for(size_t i=0;i<m;i+=64) acc+=b[i];
  double t3=now(); sink=acc;
  printf("%.4f %.4f\n", n/(t1-t0)/1e9, (4.0*m)/(t3-t2)/1e9);
  free(b); return (int)(sink&0);
}
"""

def machine_peaks():
    d = tempfile.mkdtemp()
    c = os.path.join(d, "peak.c"); x = os.path.join(d, "peak")
    open(c, "w").write(PEAK_SRC)
    if subprocess.run(["cc", "-O2", "-w", c, "-o", x]).returncode != 0:
        return None, None
    out = subprocess.run([x], capture_output=True, text=True).stdout.split()
    return float(out[0]), float(out[1])   # Gadds/s, GB/s

def main():
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "results", "bench.csv")
    rows = list(csv.DictReader(open(path)))
    by_prog = {}
    for r in rows:
        by_prog.setdefault(r["program"], {})[r["variant"]] = r

    gadds, gbs = machine_peaks()
    print("# Roofline analysis\n")
    if gadds:
        print(f"Machine: scalar integer add chain {gadds:.2f} G/s "
              f"({1/gadds:.3f} ns per dependent add), streaming read {gbs:.1f} GB/s.\n")

    order = ["native", "a68gO", "a68g", "interp", "comp0", "comp1", "comp2"]
    label = {"native": "hand-written C", "a68g": "a68g interpreted", "a68gO": "a68g --compile",
             "interp": "a68lean evaluator", "comp0": "a68lean -O0", "comp1": "a68lean -O1",
             "comp2": "a68lean -O2"}
    for prog, vs in sorted(by_prog.items()):
        base = vs.get("native")
        bns = float(base["ns_per_op"]) if base and base["ns_per_op"] != "NA" else None
        print(f"## {prog}  (ops = {int(float(base['ops'])) if base else '?'})\n")
        print("| variant | ns/op | slowdown vs C | overhead ns/op | status |")
        print("|---|---:|---:|---:|---|")
        for v in order:
            r = vs.get(v)
            if not r:
                continue
            if r["ns_per_op"] == "NA":
                print(f"| {label[v]} | – | – | – | {r['status']} |")
                continue
            ns = float(r["ns_per_op"])
            sl = f"{ns/bns:.1f}x" if bns else "–"
            ov = f"{ns-bns:.1f}" if bns else "–"
            print(f"| {label[v]} | {ns:.2f} | {sl} | {ov} | {r['status']} |")
        print()

    # the headline number an optimisation has to move
    print("## Where the gap is\n")
    for prog, vs in sorted(by_prog.items()):
        n, c2 = vs.get("native"), vs.get("comp2")
        if not (n and c2) or "NA" in (n["ns_per_op"], c2["ns_per_op"]):
            continue
        ov = float(c2["ns_per_op"]) - float(n["ns_per_op"])
        print(f"* **{prog}**: {ov:.1f} ns of overhead per operation "
              f"({float(c2['ns_per_op'])/float(n['ns_per_op']):.0f}x native). ")

if __name__ == "__main__":
    main()
