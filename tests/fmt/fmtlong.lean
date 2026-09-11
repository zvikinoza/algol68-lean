import A68.Numfmt
/-!
Lean oracle for the extended number-formatting cases of `csrc/fmt_test.c`: the case
kinds of `a68lean fmttest` plus LONG widths, `printBits`, `fixedLongInt` and the
`frmt` argument of `float`.  Runs against the built oleans without rebuilding:

    LEAN_PATH=.lake/build/lib/lean lean --run tests/fmt/fmtlong.lean cases.txt
-/
open A68

def pf (x : String) : Float :=
  if x.startsWith "-" then -(Numfmt.parseFloat (String.ofList (x.toList.drop 1))) else Numfmt.parseFloat x

def fmtLine (line : String) : String :=
  match line.splitOn " " |>.filter (· ≠ "") with
  | ["w", n, w] => Numfmt.whole n.toInt! w.toInt!
  | ["fr", x, w, a] => Numfmt.fixedReal (pf x) w.toInt! a.toInt!
  | ["fi", n, w, a] => Numfmt.fixedInt n.toInt! w.toInt! a.toInt!
  | ["fl", x, w, a, e] => Numfmt.floatReal (pf x) w.toInt! a.toInt! e.toInt!
  | ["fli", n, w, a, e] => Numfmt.floatInt n.toInt! w.toInt! a.toInt! e.toInt!
  | ["pi", n] => Numfmt.printInt n.toInt! 0
  | ["pr", x] => Numfmt.printReal (pf x) 0
  | ["wr", x, w] => Numfmt.wholeReal (pf x) w.toInt!
  | ["pin", n, l, ll] => Numfmt.printInt n.toInt! l.toInt! ll.toNat!
  | ["prn", x, l, ll] => Numfmt.printReal (pf x) l.toInt! ll.toNat!
  | ["fil", n, w, a] => Numfmt.fixedLongInt n.toInt! w.toInt! a.toInt!
  | ["pb", v, w] => Numfmt.printBits v.toNat! w.toNat!
  | ["flf", x, w, a, e, f] => Numfmt.floatReal (pf x) w.toInt! a.toInt! e.toInt! f.toInt!
  | ["flif", n, w, a, e, f] => Numfmt.floatInt n.toInt! w.toInt! a.toInt! e.toInt! f.toInt!
  | ["sf", x, w, a] => Numfmt.subFixed (Numfmt.realToDec (pf x)).2 w.toInt! a.toInt!
  | ["st", x, b, a, q] =>
    let before := b.toInt!
    let after := a.toInt!
    let (z, q') := Numfmt.standardize (Numfmt.realToDec (pf x)).2 before after q.toInt!
    Numfmt.subFixed z (max before 0 + max after 0 + 2) after ++ " " ++ toString q'
  | ["widths", l, ll] =>
    let l := l.toInt!
    let ll := ll.toNat!
    s!"{Numfmt.intWidthOf l ll} {Numfmt.realWidthOf l ll} {Numfmt.expWidthOf l} {Numfmt.bitsWidthOfLen l ll} {Numfmt.maxIntOf l ll}"
  | ["llp", n] => toString (Numfmt.llDigitsOfPrecision n.toNat!)
  | _ => "?"

def main (args : List String) : IO Unit := do
  let src ← IO.FS.readFile args.head!
  for line in src.splitOn "\n" do
    if line ≠ "" then IO.println (fmtLine line)
