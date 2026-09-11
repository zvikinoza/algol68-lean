/-!
# A68.MP — Algol 68 Genie's multi-precision arithmetic, digit for digit

Algol 68 Genie 3.13.3 as built here (clang, "level 2", no 128-bit types, no MPFR)
represents `LONG REAL`, `LONG LONG REAL` — and, through them, `LONG INT` and
`LONG LONG INT` — with its own multi-precision library (`mp.c`, `mp-math.c`):

* a number is a status word, an exponent `e` and digits `d₁ … dₙ` in radix
  `R = 10⁷`, denoting `Σ dₖ · R^(e - k + 1)`; only `d₁` carries the sign;
* `LONG` modes have `n = 7` digits, `LONG LONG` modes `n = 12` (or `2 + ⌈p/7⌉`
  after `PR precision p PR`);
* digits are C `double`s holding integers, and every operation works on an
  over-long scratch number, normalises carries, and rounds back to `n` digits
  with a68g's peculiar "Gaussian" rounding.

This module re-implements those routines step by step, so that every digit a68g
computes is computed here too.  The model keeps what is observable in C:

* a number is an array longer than the precision an operation is asked to use;
  an operation on `digs` digits writes exactly the status, exponent and first
  `digs` digits of its destination and leaves the rest alone (a68g's functions
  rely on stale guard digits, e.g. `sqrt_mp` rounds with guard digits that an
  earlier `rec_mp` did not overwrite);
* digits are exact integers: a68g's scratch values stay below 2⁵³ by design, so
  its double arithmetic on them is exact.  The one place where a68g relies on
  rounding is the quotient-digit estimate of the division routines, which the
  compiler fused into `fmadd` instructions; `dblOfInt`, `fma` and `truncDiv`
  reproduce that rounding in exact integer arithmetic;
* a68g's run-time errors (a NaN operand under strict maths, an exponent out of
  range, a truncation out of bounds) are `Except` failures.

Proofs about the digit representation are in `A68.Verified.MP`.
-/
namespace A68.MP

/-- The radix of a digit, `MP_RADIX`. -/
def R : Int := 10000000
/-- Decimal digits per MP digit, `LOG_MP_RADIX`. -/
def logR : Nat := 7
/-- `A68G_MP_GUARDS`. -/
def guards : Nat := 2
/-- Digits of a `LONG` number, `LONG_MP_DIGITS`. -/
def longDigits : Nat := 7
/-- Default digits of a `LONG LONG` number, `width_to_mp_digits (4 * 15 + 15 / 2)`. -/
def longLongDigits : Nat := 12
/-- `MAX_MP_EXPONENT`. -/
def maxExpo : Int := 142857
/-- `MAX_REPR_INT`, 2⁵³. -/
def maxRepr : Int := 9007199254740992

/-- `width_to_mp_digits`: digits for `PR precision n PR`. -/
def widthToDigits (n : Nat) : Nat := guards + (n + logR - 1) / logR

/-- Status bits (`a68g-masks.h`). -/
def INIT : Nat := 0x10
def PINF : Nat := 0x20
def MINF : Nat := 0x40
def NAN  : Nat := 0x80

/-- A multi-precision number.  `d[k]` is `MP_DIGIT (z, k)` for `k ≥ 1`; `d[0]` is unused.
    The array may be longer than the precision in use. -/
structure MP where
  st : Nat
  ex : Int
  d  : Array Int
  deriving Inhabited, BEq, Repr

abbrev MPE := Except String

namespace MP

@[inline] def dig (z : MP) (k : Nat) : Int := z.d.getD k 0
def isNaN (z : MP) : Bool := z.st &&& NAN != 0
def isPInf (z : MP) : Bool := z.st &&& PINF != 0
def isMInf (z : MP) : Bool := z.st &&& MINF != 0
def isInf (z : MP) : Bool := z.isPInf || z.isMInf
/-- `A68G_FINITE_MP`. -/
def isFinite (z : MP) : Bool := if z.isNaN then false else !z.isInf
def isZero (z : MP) : Bool := z.dig 1 == 0
def isPlus (z : MP) : Bool := z.dig 1 > 0
def isMinus (z : MP) : Bool := z.dig 1 < 0
/-- Number of digits held. -/
def size (z : MP) : Nat := z.d.size - 1

end MP

/-- Grow an array with zeros to at least `n` entries. -/
@[inline] def grow (a : Array Int) (n : Nat) : Array Int :=
  if a.size ≥ n then a else a ++ Array.replicate (n - a.size) 0

@[inline] def setAt (a : Array Int) (k : Nat) (v : Int) : Array Int :=
  (grow a (k + 1)).set! k v

namespace MP

def setDig (z : MP) (k : Nat) (v : Int) : MP := { z with d := setAt z.d k v }
def negate1 (z : MP) : MP := z.setDig 1 (-(z.dig 1))
def withInit (z : MP) : MP := { z with st := z.st ||| INIT }

end MP

/-- A fresh number of `digs` digits, `lit_mp (p, u, expo, digs)`; `nil_mp` is `lit 0 0`. -/
def lit (digs : Nat) (u : Int) (e : Int) : MP :=
  { st := INIT, ex := e, d := (Array.replicate (digs + 1) 0).set! 1 u }

def nil (digs : Nat) : MP := lit digs 0 0

/-- `set_mp (z, x, expo, digs)`: clears status, exponent and `digs` digits of `z`. -/
def setMp (z : MP) (x : Int) (e : Int) (digs : Nat) : MP := Id.run do
  let mut a := grow z.d (digs + 1)
  for k in [1:digs+1] do a := a.set! k 0
  a := a.set! 1 x
  return { st := INIT, ex := e, d := a }

def setZero (z : MP) (digs : Nat) : MP := setMp z 0 0 digs

/-- `move_mp (z, x, n)`: status, exponent and `n` digits. -/
def moveMp (z x : MP) (n : Nat) : MP := Id.run do
  let mut a := grow z.d (n + 1)
  for k in [1:n+1] do a := a.set! k (x.dig k)
  return { st := x.st, ex := x.ex, d := a }

def setNaN (z : MP) : MP := { z with st := NAN ||| INIT }
def setPInf (z : MP) : MP := { z with st := PINF ||| INIT }
def setMInf (z : MP) : MP := { z with st := MINF ||| INIT }

/-- `len_mp (p, u, digs, gdigs)`: a fresh copy of `digs` digits, zero-extended to `gdigs`. -/
def lenMp (u : MP) (digs gdigs : Nat) : MP := Id.run do
  let mut a := Array.replicate (gdigs + 1) (0 : Int)
  for k in [1:(min digs gdigs)+1] do a := a.set! k (u.dig k)
  return { st := u.st, ex := u.ex, d := a }

-- ## Rounding of C doubles, in exact integer arithmetic

/-- Integer log₂ of a positive natural. -/
def log2Nat (n : Nat) : Nat := n.log2

/-- The double nearest to the integer `n` (ties to even), as an integer.  Every
    double of magnitude ≥ 2⁵³ is an integer, so this is exact. -/
def dblOfInt (n : Int) : Int :=
  let a := n.natAbs
  if a < 2 ^ 53 then n
  else
    -- powers of two as shifts: `2^s` is `1 <<< s`, `a % 2^s` is `a &&& (2^s - 1)`
    let s := log2Nat a + 1 - 53
    let m := a >>> s
    let rem := a &&& ((1 <<< s) - 1)
    let half := 1 <<< (s - 1)
    let m' := if rem > half || (rem == half && m % 2 == 1) then m + 1 else m
    let r : Int := (m' <<< s : Nat)
    if n < 0 then -r else r

/-- `fmadd (a, b, c)` on integer-valued doubles: `a · b + c` rounded once. -/
def fma (a b c : Int) : Int := dblOfInt (a * b + c)

/-- `(int) (x / y)` for integer-valued doubles `x` and `y > 0`: the quotient is rounded
    to a double, then truncated toward zero. -/
def truncDiv (x y : Int) : Int :=
  if x == 0 || y ≤ 0 then 0
  else
    let a := x.natAbs
    let b := y.natAbs
    -- find e with 2⁵² ≤ a / b · 2^(52 - e) < 2⁵³ (powers of two as shifts)
    let e0 : Int := (log2Nat a : Int) - (log2Nat b : Int)
    let scaled (e : Int) : Nat × Nat :=
      if 52 - e ≥ 0 then (a <<< (52 - e).toNat, b) else (a, b <<< (e - 52).toNat)
    let pick : Int := Id.run do
      let mut e := e0 - 1
      for _ in [0:4] do
        let (p, q) := scaled e
        if p / q ≥ 2 ^ 53 then e := e + 1 else break
      return e
    let e := pick
    let (p, q) := scaled e
    let m := p / q
    let r := p % q
    let m' := if 2 * r > q || (2 * r == q && m % 2 == 1) then m + 1 else m
    -- value is m' · 2^(e - 52); truncate toward zero
    let t : Nat := if e - 52 ≥ 0 then m' <<< (e - 52).toNat else m' >>> (52 - e).toNat
    if x < 0 then -(t : Int) else t

/-- a68g's quotient-digit estimate `(int) (nom / den)`, where `nom` is
    `fma (fma (fma tm1 R t0) R t1) R t2` and `den` the double denominator (`denF` is a
    double close to it).  The exact computation above is exact but allocates big
    integers on every digit; this one first computes the same quotient with plain
    doubles.  Every double operation perturbs a value by at most one part in 2⁵³, so
    a68g's fused estimate and the plain one (14 roundings between them) both lie within
    2·10⁻¹⁵ of `nom / den` relatively, which for a quotient below 2²⁶ is less than
    1.4·10⁻⁷.  When the plain quotient is further than 10⁻⁶ from every integer, both
    therefore truncate to the same integer; otherwise the exact computation decides. -/
def qDigit (tm1 t0 t1 t2 den : Int) (denF : Float) : Int :=
  -- 2⁵² as a `Nat` literal: an `Int` literal this large is rebuilt from its digits on
  -- every call, while a `Nat` below 2⁶³ is an unboxed scalar
  let lim : Nat := 4503599627370496
  if tm1.natAbs < lim && t0.natAbs < lim && t1.natAbs < lim
      && t2.natAbs < lim && denF > 0.0 then
    let rF : Float := 10000000.0
    let nomF := ((Float.ofInt tm1 * rF + Float.ofInt t0) * rF + Float.ofInt t1) * rF + Float.ofInt t2
    let qF := nomF / denF
    let aq := Float.abs qF
    let fr := aq - Float.floor aq
    if aq < 67108864.0 && fr > 0.000001 && fr < 0.999999 then
      let t : Int := (Float.floor aq).toUInt64.toNat
      if qF < 0.0 then -t else t
    else truncDiv (fma (fma (fma tm1 R t0) R t1) R t2) den
  else truncDiv (fma (fma (fma tm1 R t0) R t1) R t2) den

-- ## Normalisation and rounding

/-- One carry of `norm_mp` at position `j ≥ 1`: move whole multiples of `R` out of
    digit `j` into digit `j - 1`.  The carries are those of a68g's double computation,
    which is exact for scratch values below 2⁵³. -/
def carryAt (a : Array Int) (j : Nat) : Array Int :=
  let z := a.getD j 0
  -- the neighbour is read before the first write, so the array is updated in place
  let lo := a.getD (j - 1) 0
  if z ≥ R then
    let c := z / R
    (a.setIfInBounds j (z - c * R)).setIfInBounds (j - 1) (lo + c)
  else if z < 0 then
    let c := 1 + (-z - 1) / R
    (a.setIfInBounds j (z + c * R)).setIfInBounds (j - 1) (lo - c)
  else a

/-- `norm_mp`'s loop: carries at `j, j - 1, …, k` (and never below position 1). -/
def normFrom (a : Array Int) (k : Nat) : Nat → Array Int
  | 0 => a
  | j + 1 => if j + 1 < k then a else normFrom (carryAt a (j + 1)) k j

/-- `norm_mp (w, k, digs)` on a scratch array. -/
def normDigits (w : Array Int) (k digs : Nat) : Array Int :=
  normFrom (grow w (digs + 1)) k digs

/-- `round_internal_mp (z, w, digs)` for a finite scratch number `w` (digits `wd`,
    exponent `wex`) with at least `digs + 2` digits. -/
def roundInternal (z : MP) (wd : Array Int) (wex : Int) (digs : Nat) : MP := Id.run do
  let mut w := grow wd (digs + 3)
  let last := if w[1]! == 0 then 2 + digs else 1 + digs
  -- GAUSSIAN_ROUNDING as written in mp.c
  if w[last]! > R / 2 then
    w := w.set! (last - 1) (w[last - 1]! + 1)
  else if w[last]! == R / 2 then
    if Int.tmod (w[last - 1]!) 2 == 0 then
      w := w.set! (last - 1) (w[last - 1]! + 1)
    w := w.set! (last - 1) (w[last - 1]! + 1)
  if w[last - 1]! ≥ R then
    w := normDigits w 2 last
  let mut a := grow z.d (digs + 1)
  let mut ex := z.ex
  if w[1]! == 0 then
    for k in [1:digs+1] do a := a.set! k w[k + 1]!
    ex := wex - 1
  else
    for k in [1:digs+1] do a := a.set! k w[k]!
    ex := wex
  if a[1]! == 0 then ex := 0
  return { z with ex := ex, d := a }

/-- `check_mp_exp`. -/
def checkExp (z : MP) : MPE MP :=
  let e := z.ex.natAbs
  if (e : Int) > maxExpo || ((e : Int) == maxExpo && (z.dig 1).natAbs > 1) then
    throw "multiprecision value out of bounds"
  else pure z

/-- `CATCH_NAN_MP`: strict maths turns a NaN operand into a run-time error. -/
def catchNaN (x : MP) : MPE Unit :=
  if x.isNaN then throw "LONG LONG REAL value is not a number" else pure ()

-- ## Shortening and lengthening

/-- `lengthen_mp (z, digs_z, x, digs_x)` for `digs_z > digs_x`. -/
def lengthenRaw (z x : MP) (digsZ digsX : Nat) : MP := Id.run do
  let mut a := grow z.d (digsZ + 1)
  for k in [1:digsX+1] do a := a.set! k (x.dig k)
  for k in [digsX+1:digsZ+1] do a := a.set! k 0
  return { st := x.st, ex := x.ex, d := a }

/-- `shorten_mp (z, digs, x, digs_x)`.  (a68g also leaves `x` made positive; no caller
    looks at `x` afterwards.) -/
def shortenMp (z : MP) (digs : Nat) (x : MP) (digsX : Nat) : MPE MP := do
  catchNaN x
  if x.isPInf then return setPInf z
  if x.isMInf then return setMInf z
  if digs > digsX then return lengthenRaw z x digs digsX
  if digs == digsX then return moveMp z x digs
  let neg := x.isMinus
  let mut w := Array.replicate (digs + 3) (0 : Int)
  for k in [1:digs+2] do
    let v := x.dig k
    w := w.set! (k + 1) (if k == 1 && neg then -v else v)
  let z' := roundInternal z w (x.ex + 1) digs
  let z' := if neg then z'.negate1 else z'
  return { z' with st := x.st }

/-- `lengthen_mp`. -/
def lengthenMp (z : MP) (digsZ : Nat) (x : MP) (digsX : Nat) : MPE MP :=
  if digsZ < digsX then shortenMp z digsZ x digsX
  else do
    catchNaN x
    if x.isPInf then return setPInf z
    if x.isMInf then return setMInf z
    if digsZ == digsX then return moveMp z x digsZ
    return lengthenRaw z x digsZ digsX

-- ## Addition and subtraction

/-- Digit `j` of a `digs`-digit number, zero outside `1 … digs`. -/
def digitOr0 (a : Array Int) (digs : Nat) (j : Int) : Int :=
  if j ≤ 0 || j > digs then 0 else a.getD j.toNat 0

/-- The aligned digit sums of two positive numbers into a scratch of `digs + 2` digits
    (`add_mp` and `sub_mp` differ only in the sign `s` of the second operand). -/
def alignedSum (x y : Array Int) (xex yex : Int) (digs : Nat) (s : Int) : Array Int × Int :=
  -- the three loops of add_mp / sub_mp (equal exponents, x larger, y larger) fill scratch
  -- digit `i ∈ [2, digs + 2]` with digit `i - 1` of the operand with the larger exponent
  -- and the correspondingly shifted digit of the other; digits past `digs` are zero
  let digsH := digs + 2
  let shlX : Int := if yex > xex then yex - xex else 0
  let shlY : Int := if xex > yex then xex - yex else 0
  let w := Array.ofFn (n := digsH + 1) fun i =>
    if i.val < 2 then 0
    else digitOr0 x digs ((i.val : Int) - 1 - shlX) + s * digitOr0 y digs ((i.val : Int) - 1 - shlY)
  (w, 1 + max xex yex)

mutual

/-- `add_mp (z, x, y, digs)`. -/
partial def addMp (z x y : MP) (digs : Nat) : MPE MP := do
  catchNaN x; catchNaN y
  if x.isPInf && y.isMInf then return setNaN z
  if y.isPInf && x.isMInf then return setNaN z
  if x.isPInf || y.isPInf then return setPInf z
  if x.isMInf || y.isMInf then return setMInf z
  let z := z.withInit
  if x.isZero then return moveMp z y digs
  if y.isZero then return moveMp z x digs
  let x1 := x.dig 1
  let y1 := y.dig 1
  let xa := x.setDig 1 x1.natAbs
  let ya := y.setDig 1 y1.natAbs
  if x1 ≥ 0 && y1 < 0 then subMp z xa ya digs
  else if x1 < 0 && y1 ≥ 0 then subMp z ya xa digs
  else if x1 < 0 && y1 < 0 then
    let r ← addMp z xa ya digs
    return r.negate1
  else
    let (w, wex) := alignedSum xa.d ya.d xa.ex ya.ex digs 1
    let w := normDigits w 2 (digs + 2)
    checkExp (roundInternal z w wex digs)

/-- `sub_mp (z, x, y, digs)`. -/
partial def subMp (z x y : MP) (digs : Nat) : MPE MP := do
  catchNaN x; catchNaN y
  if x.isPInf && y.isMInf then return setNaN z
  if y.isPInf && x.isMInf then return setNaN z
  if x.isPInf || y.isPInf then return setPInf z
  if x.isMInf || y.isMInf then return setMInf z
  let z := z.withInit
  if x.isZero then return (moveMp z y digs).negate1
  if y.isZero then return moveMp z x digs
  let x1 := x.dig 1
  let y1 := y.dig 1
  let xa := x.setDig 1 x1.natAbs
  let ya := y.setDig 1 y1.natAbs
  if x1 ≥ 0 && y1 < 0 then addMp z xa ya digs
  else if x1 < 0 && y1 ≥ 0 then
    let r ← addMp z ya xa digs
    return r.negate1
  else if x1 < 0 && y1 < 0 then subMp z ya xa digs
  else
    let digsH := digs + 2
    let (w0, wex0) := alignedSum xa.d ya.d xa.ex ya.ex digs (-1)
    let mut w := w0
    let mut wex := wex0
    let mut negative := false
    if w[2]! ≤ 0 then
      let mut fnz : Option Nat := none
      for j in [2:digsH+1] do
        if fnz.isNone && w[j]! != 0 then fnz := some j
      match fnz with
      | some f =>
        negative := w[f]! < 0
        if negative then
          for j in [f:digsH+1] do w := w.set! j (-w[j]!)
      | none => pure ()
    w := normDigits w 2 digsH
    let mut fnz : Option Nat := none
    for j in [1:digsH+1] do
      if fnz.isNone && w[j]! != 0 then fnz := some j
    match fnz with
    | some f =>
      if f > 1 then
        let j2 := f - 1
        for j in [1:digsH - j2 + 1] do
          w := w.set! j w[j + j2]!
          w := w.set! (j + j2) 0
        wex := wex - j2
    | none => pure ()
    let r := roundInternal z w wex digs
    checkExp (if negative then r.negate1 else r)

end

-- ## Multiplication

/-- `CATCH_MUL_INF_MP (u, v, w)` when `v` is infinite. -/
def mulInf (u v w : MP) : MP :=
  let plus := v.isPInf
  if w.isPInf then (if plus then setPInf u else setMInf u)
  else if w.isMInf then (if plus then setMInf u else setPInf u)
  else if w.isZero then setNaN u
  else if w.isPlus then (if plus then setPInf u else setMInf u)
  else (if plus then setMInf u else setPInf u)

/-- `mul_mp (z, x, y, digs)`: grammar-school multiplication with intermittent normalisation. -/
def mulMp (z x y : MP) (digs : Nat) : MPE MP := do
  catchNaN x; catchNaN y
  if x.isInf then return mulInf z x y
  if y.isInf then return mulInf z y x
  if x.isZero || y.isZero then return setZero z digs
  let digsH := 2 + digs
  let x1 := x.dig 1
  let y1 := y.dig 1
  let xa := x.setDig 1 x1.natAbs
  let ya := y.setDig 1 y1.natAbs
  let z := z.withInit
  -- oflow = floor (MAX_REPR_INT / (2 R²)) - 1
  let oflow : Nat := 44
  let mut w := Array.replicate (digsH + 1) (0 : Int)
  let mut i := digs
  while i ≥ 1 do
    let yi := ya.dig i
    if yi != 0 then
      let k := digsH - i
      let j := if k > digs then digs else k
      if (digs - i + 1) % oflow == 0 then w := normDigits w 2 digsH
      let mut jj := j
      while jj ≥ 1 do
        w := w.set! (i + jj) (w[i + jj]! + yi * xa.dig jj)
        jj := jj - 1
    i := i - 1
  w := normDigits w 2 digsH
  let r := roundInternal z w (x.ex + y.ex + 1) digs
  let z1 := r.dig 1
  checkExp (r.setDig 1 (if x1 * y1 ≥ 0 then z1 else -z1))

/-- `mul_mp_digit`, `half_mp`, `tenth_mp` share this O(n) scaling of `|x|` by `y`. -/
def scaleDigits (z x : MP) (y : Int) (wex : Int) (digs : Nat) : MP := Id.run do
  let digsH := 2 + digs
  let mut w := Array.replicate (digsH + 1) (0 : Int)
  let mut j := digs
  while j ≥ 1 do
    let v := if j == 1 then ((x.dig 1).natAbs : Int) else x.dig j
    w := w.set! (j + 1) (w[j + 1]! + y * v)
    j := j - 1
  w := normDigits w 2 digsH
  return roundInternal z w wex digs

/-- `half_mp (z, x, digs)`. -/
def halfMp (z x : MP) (digs : Nat) : MPE MP := do
  catchNaN x
  if x.isPInf then return setPInf z
  if x.isMInf then return setMInf z
  let x1 := x.dig 1
  let r := scaleDigits z.withInit x (R / 2) x.ex digs
  let z1 := r.dig 1
  checkExp (r.setDig 1 (if x1 ≥ 0 then z1 else -z1))

/-- `tenth_mp (z, x, digs)`. -/
def tenthMp (z x : MP) (digs : Nat) : MPE MP := do
  catchNaN x
  if x.isPInf then return setPInf z
  if x.isMInf then return setMInf z
  let x1 := x.dig 1
  let r := scaleDigits z.withInit x (R / 10) x.ex digs
  let z1 := r.dig 1
  checkExp (r.setDig 1 (if x1 ≥ 0 then z1 else -z1))

/-- `mul_mp_digit (z, x, y, digs)`. -/
def mulMpDigit (z x : MP) (y : Int) (digs : Nat) : MPE MP := do
  catchNaN x
  if x.isInf && y == 0 then return setNaN z
  if x.isInf then
    if x.isPInf then return (if y > 0 then setPInf z else setMInf z)
    else return (if y < 0 then setPInf z else setMInf z)
  let x1 := x.dig 1
  let xa := x.setDig 1 x1.natAbs
  let z := z.withInit
  let ya := y.natAbs
  let r ← if ya == 2 then addMp z xa xa digs
          else pure (scaleDigits z xa ya (x.ex + 1) digs)
  let z1 := r.dig 1
  checkExp (r.setDig 1 (if x1 * y ≥ 0 then z1 else -z1))

-- ## Division

/-- Whether a68g's estimate numerator `fma (fma (fma tm1 R t0) R t1) R t2` is zero.
    When every input is below 2⁵² in magnitude it is zero exactly when the exact value
    `((tm1·R + t0)·R + t1)·R + t2` is (a non-zero integer never rounds to zero, and a
    stage that had to round is too large for the later small terms to cancel), which is
    decided by divisibility by `R` on small integers.  Otherwise the chain is evaluated. -/
def nomZero (tm1 t0 t1 t2 : Int) : Bool :=
  let lim : Nat := 4503599627370496   -- 2⁵², unboxed (see `qDigit`)
  if tm1.natAbs < lim && t0.natAbs < lim && t1.natAbs < lim
      && t2.natAbs < lim then
    if t2 % R != 0 then false
    else
      let s1 := t1 + t2 / R
      if s1 % R != 0 then false
      else
        let s0 := t0 + s1 / R
        if s0 % R != 0 then false
        else tm1 + s0 / R == 0
  else fma (fma (fma tm1 R t0) R t1) R t2 == 0

/-- The quotient loop of `div_mp_digit` for `|x|` and `ya = |y| ∉ {2, 10}`, outside the
    error monad (it cannot fail). -/
def divDigitLoop (z xa : MP) (ya : Int) (digs oflow : Nat) : MP := Id.run do
  let wdigs := 4 + digs
  let mut w := Array.replicate (wdigs + 1) (0 : Int)
  for k in [1:digs+1] do w := w.set! (k + 1) (xa.dig k)
  let den := dblOfInt (dblOfInt (ya * R) * R)
  -- div_mp_digit computes its denominator with two plain multiplications, as here
  let denF := (Float.ofInt ya * 10000000.0) * 10000000.0
  for k in [1:digs+3] do
    let first := k + 2
    let t2 := if wdigs ≥ first + 2 then w[k + 3]! else 0
    let q := qDigit w[k]! w[k + 1]! w[k + 2]! t2 den denF
    let wk := w[k]!
    w := w.set! (k + 1) (w[k + 1]! + (wk * R - q * ya))
    w := w.set! k q
    if k % oflow == 0 || k == digs + 2 then w := normDigits w first wdigs
  w := normDigits w 2 digs
  return roundInternal z w xa.ex digs

/-- The quotient loop of `div_mp` for `|x|` and the digits `yd` of `|y|`. -/
def divLoop (z xa : MP) (yd : Array Int) (nzdigs digs oflow : Nat) (wex : Int) : MP := Id.run do
  let wdigs := 4 + digs
  let mut w := Array.replicate (wdigs + 1) (0 : Int)
  for k in [1:digs+1] do w := w.set! (k + 1) (xa.dig k)
  let y1 := yd.getD 1 0
  let y2 := yd.getD 2 0
  let y3 := yd.getD 3 0
  let den := fma (fma y1 R y2) R y3
  let denF := (Float.ofInt y1 * 10000000.0 + Float.ofInt y2) * 10000000.0 + Float.ofInt y3
  for k in [1:digs+3] do
    let first := k + 2
    let len := digs + 1 + k
    let t2 := if wdigs ≥ first + 2 then w[k + 3]! else 0
    let tm1 := w[k]!
    let t0 := w[k + 1]!
    let t1 := w[k + 2]!
    let nomIsZero := nomZero tm1 t0 t1 t2
    let mut q : Int := 0
    if !nomIsZero then
      q := qDigit tm1 t0 t1 t2 den denF
      let mut lim := min len wdigs
      if nzdigs + first ≤ lim + 1 then lim := first + nzdigs - 1
      for j in [first:lim+1] do
        let idx := k + 1 + (j - first)
        w := w.set! idx (w[idx]! - q * yd.getD (1 + (j - first)) 0)
    let wk := w[k]!
    w := w.set! (k + 1) (fma wk R w[k + 1]!)
    w := w.set! k q
    if k % oflow == 0 || k == digs + 2 then w := normDigits w first wdigs
  w := normDigits w 2 digs
  return roundInternal z w wex digs

/-- `div_mp_digit (z, x, y, digs)`. -/
def divMpDigit (z x : MP) (y : Int) (digs : Nat) : MPE MP := do
  catchNaN x
  if x.isPInf then return setPInf z
  if x.isMInf then return setMInf z
  if y == 0 then return setNaN z
  let oflow : Nat := 29
  let x1 := x.dig 1
  let xa := x.setDig 1 x1.natAbs
  let z := z.withInit
  let ya := y.natAbs
  let r ← if ya == 2 then halfMp z xa digs
    else if ya == 10 then tenthMp z xa digs
    else pure (divDigitLoop z xa ya digs oflow)
  let z1 := r.dig 1
  checkExp (r.setDig 1 (if x1 * y ≥ 0 then z1 else -z1))

/-- `div_mp (z, x, y, digs)`, after D. M. Smith's algorithm, with a68g's estimates. -/
def divMp (z x y : MP) (digs : Nat) : MPE MP := do
  catchNaN x; catchNaN y
  if x.isInf then return setNaN z
  if y.isInf then return setZero z digs
  if y.isZero then
    if x.isZero then return setNaN z
    else if x.isPlus then return setPInf z
    else return setMInf z
  let oflow : Nat := 29
  let x1 := x.dig 1
  let y1 := y.dig 1
  let xa := x.setDig 1 x1.natAbs
  let ya := y.setDig 1 y1.natAbs
  let z := z.withInit
  let mut nzdigs := digs
  while ya.dig nzdigs == 0 && nzdigs > 1 do nzdigs := nzdigs - 1
  if nzdigs == 1 && ya.ex == 0 then
    let r ← divMpDigit z xa (ya.dig 1) digs
    let z1 := r.dig 1
    return ← checkExp (r.setDig 1 (if x1 * y1 ≥ 0 then z1 else -z1))
  let r := divLoop z xa (grow ya.d (digs + 1)) nzdigs digs oflow (x.ex - y.ex)
  let z1 := r.dig 1
  checkExp (r.setDig 1 (if x1 * y1 ≥ 0 then z1 else -z1))

/-- `mp_one (digs)`. -/
def one (digs : Nat) : MP := lit digs 1 0

/-- `rec_mp (z, x, digs)`. -/
def recMp (z x : MP) (digs : Nat) : MPE MP :=
  if x.isZero then pure (setNaN z) else divMp z (one digs) x digs

-- ## Truncation and rounding

/-- `trunc_mp (z, x, digs)`. -/
def truncMp (z x : MP) (digs : Nat) : MPE MP := do
  catchNaN x
  if x.isPInf then return setPInf z
  if x.isMInf then return setMInf z
  if x.ex < 0 then return setZero z digs
  if x.ex ≥ digs then throw "value out of bounds"
  let mut r := moveMp z x digs
  for k in [(x.ex + 2).toNat:digs+1] do r := r.setDig k 0
  return r.withInit

/-- `over_mp (z, x, y, digs)`: truncated quotient. -/
def overMp (z x y : MP) (digs : Nat) : MPE MP := do
  catchNaN x; catchNaN y
  if x.isInf then return setNaN z
  if y.isInf then return setZero z digs
  if y.isZero then
    if x.isZero then return setNaN z
    else if x.isPlus then return setPInf z
    else return setMInf z
  let dg := digs + guards
  let zg ← divMp (nil dg) (lenMp x digs dg) (lenMp y digs dg) dg
  let zg ← truncMp zg zg dg
  let r ← shortenMp z digs zg dg
  return r.withInit

/-- `over_mp_digit (z, x, y, digs)`. -/
def overMpDigit (z x : MP) (y : Int) (digs : Nat) : MPE MP := do
  catchNaN x
  if x.isPInf then return setPInf z
  if x.isMInf then return setMInf z
  if y == 0 then return setNaN z
  let dg := digs + guards
  let zg ← divMpDigit (nil dg) (lenMp x digs dg) y dg
  let zg ← truncMp zg zg dg
  shortenMp z digs zg dg

/-- `mod_mp (z, x, y, digs)`: `x - y · trunc (x / y)`. -/
def modMp (z x y : MP) (digs : Nat) : MPE MP := do
  catchNaN x; catchNaN y
  if x.isInf || y.isInf then return setNaN z
  if y.isZero then return setNaN z
  let dg := digs + guards
  let xg := lenMp x digs dg
  let yg := lenMp y digs dg
  let zg ← overMp (nil dg) xg yg dg
  let zg ← mulMp zg yg zg dg
  let zg ← subMp zg xg zg dg
  shortenMp z digs zg dg

/-- `SET_MP_HALF`. -/
def half (digs : Nat) : MP := lit digs (R / 2) (-1)

/-- `round_mp (z, x, digs)`: add or subtract one half, then truncate. -/
def roundMp (z x : MP) (digs : Nat) : MPE MP := do
  catchNaN x
  if x.isPInf then return setPInf z
  if x.isMInf then return setMInf z
  let y := half digs
  let r ← if x.dig 1 ≥ 0 then addMp z x y digs else subMp z x y digs
  let r ← truncMp r r digs
  return r.withInit

/-- `entier_mp (z, x, digs)`; the scratch copy is taken from `z`, which a68g always
    calls with `z` equal to `x`. -/
def entierMp (z x : MP) (digs : Nat) : MPE MP := do
  catchNaN x
  if x.isPInf then return setPInf z
  if x.isMInf then return setMInf z
  if x.dig 1 ≥ 0 then return ← truncMp z x digs
  let y := moveMp (nil digs) z digs
  let z' ← truncMp z x digs
  let y ← subMp y y z' digs
  if y.dig 1 != 0 then
    let r ← subMp z' z' (one digs) digs
    return r.withInit
  return z'.withInit

/-- `minus_mp`, `abs_mp`. -/
def minusMp (x : MP) : MPE MP := do
  catchNaN x
  if x.isPInf then return setMInf x
  if x.isMInf then return setPInf x
  return x.negate1.withInit

def absMp (x : MP) : MPE MP := do
  catchNaN x
  if x.isInf then return setPInf x
  return (x.setDig 1 (x.dig 1).natAbs).withInit

/-- `x ± 1`, `1 - x`. -/
def minusOneMp (z x : MP) (digs : Nat) : MPE MP := do
  catchNaN x
  if x.isPInf then return setPInf z
  if x.isMInf then return setMInf z
  subMp z x (one digs) digs

def plusOneMp (z x : MP) (digs : Nat) : MPE MP := do
  catchNaN x
  if x.isPInf then return setPInf z
  if x.isMInf then return setMInf z
  addMp z x (one digs) digs

def oneMinusMp (z x : MP) (digs : Nat) : MPE MP := do
  catchNaN x
  if x.isPInf then return setMInf z
  if x.isMInf then return setPInf z
  subMp z (one digs) x digs

/-- `pow_mp_int (z, x, n, digs)`: square and multiply at two guard digits. -/
def powMpInt (z x : MP) (n : Int) (digs : Nat) : MPE MP := do
  catchNaN x
  if x.isInf then
    if n == 0 then return setNaN z
    else if n < 0 then return setZero z digs
    else if x.isPInf then return setPInf z
    else return (if n % 2 == 0 then setPInf z else setMInf z)
  let dg := digs + guards
  let mut xg := lenMp x digs dg
  let mut zg := lit dg 1 0
  let neg := n < 0
  let nn := n.natAbs
  let mut bit : Nat := 1
  while bit ≤ nn do
    if nn &&& bit != 0 then zg ← mulMp zg zg xg dg
    xg ← mulMp xg xg xg dg
    bit := bit <<< 1
  if neg then zg ← recMp zg zg dg
  let r ← shortenMp z digs zg dg
  checkExp r

-- ## Comparison

/-- `eq_mp`, `lt_mp`, `gt_mp` and their negations, as a68g computes them (by
    subtraction, which can itself overflow). -/
def eqMp (x y : MP) (digs : Nat) : MPE Bool := do
  if x.isNaN || y.isNaN then return false
  if x.isFinite && y.isFinite then
    let v ← subMp (nil digs) x y digs
    return v.dig 1 == 0
  return (x.isPInf && y.isPInf) || (x.isMInf && y.isMInf)

def ltMp (x y : MP) (digs : Nat) : MPE Bool := do
  if x.isNaN || y.isNaN then return false
  if x.isFinite && y.isFinite then
    let v ← subMp (nil digs) x y digs
    return v.isMinus
  return (x.isMInf && y.isPInf) || (x.isFinite && y.isPInf) || (x.isMInf && y.isFinite)

def gtMp (x y : MP) (digs : Nat) : MPE Bool := do
  if x.isNaN || y.isNaN then return false
  if x.isFinite && y.isFinite then
    let v ← subMp (nil digs) x y digs
    return v.isPlus
  return (x.isPInf && y.isMInf) || (x.isPInf && y.isFinite) || (x.isFinite && y.isMInf)

def neMp (x y : MP) (digs : Nat) : MPE Bool := do return !(← eqMp x y digs)
def leMp (x y : MP) (digs : Nat) : MPE Bool := do return !(← gtMp x y digs)
def geMp (x y : MP) (digs : Nat) : MPE Bool := do return !(← ltMp x y digs)

-- ## Conversions

/-- `align_mp (z, &expo, digs)`: shift the decimal digits of a mantissa built in radix
    10 so that the exponent becomes a multiple of `LOG_MP_RADIX`. -/
def alignMp (z : MP) (expo : Int) (digs : Nat) : MP × Int := Id.run do
  if !z.isFinite then return (z, expo)
  let (shift, e) : Int × Int :=
    if expo ≥ 0 then ((logR : Int) - Int.tmod expo logR - 1, Int.tdiv expo logR)
    else (Int.tmod (-expo - 1) logR, Int.tdiv (expo + 1) logR - 1)
  let mut a := grow z.d (digs + 1)
  for _ in [0:shift.toNat] do
    let mut carry : Int := 0
    for j in [1:digs+1] do
      let v := a[j]!
      let k := Int.tmod v 10
      a := a.set! j (Int.tdiv v 10 + carry * (R / 10))
      carry := k
  return ({ z with d := a }, e)

/-- `int_to_mp (z, k, digs)` for any integer that fits the number. -/
def intToMp (z : MP) (k : Int) (digs : Nat) : MPE MP := do
  let a := k.natAbs
  let mut m := a
  let mut n : Nat := 0
  while m / R.toNat != 0 do
    m := m / R.toNat
    n := n + 1
  let mut r := setMp z 0 n digs
  let mut kk := a
  let mut j := 1 + n
  while j ≥ 1 do
    r := r.setDig j (kk % R.toNat)
    kk := kk / R.toNat
    j := j - 1
  if k < 0 then r := r.negate1
  checkExp r

/-- A fresh `digs`-digit number holding the integer `k`. -/
def ofInt (k : Int) (digs : Nat) : MPE MP := intToMp (nil digs) k digs

/-- The integer value of a number whose exponent is below its precision (digits past
    the units position are ignored, as `mp_to_int` ignores them). -/
def toIntTrunc (z : MP) : Int := Id.run do
  if z.ex < 0 then return 0
  let e := z.ex.toNat
  let mut s : Int := 0
  for j in [1:e+2] do
    s := s * R + (if j == 1 then ((z.dig 1).natAbs : Int) else z.dig j)
  return if z.dig 1 < 0 then -s else s

/-- `check_mp_int`: is `z` a valid integer of `digs` digits? -/
def isIntOfDigits (z : MP) (digs : Nat) : Bool := z.ex ≥ 0 && z.ex < digs

/-- `mp_to_int (p, z, digs)` for 32-bit `INT` (weights wrap as C `int` does). -/
def toInt32 (z : MP) (digs : Nat) : MPE Int := do
  let maxInt : Int := 2147483647
  if z.ex ≥ digs then throw "value out of bounds"
  let neg := z.dig 1 < 0
  let e := z.ex.toNat
  let wrap (v : Int) : Int :=
    let m := v % 4294967296
    if m ≥ 2147483648 then m - 4294967296 else m
  let mut sum : Int := 0
  let mut weight : Int := 1
  let mut j := 1 + e
  while j ≥ 1 do
    let dj := if j == 1 then ((z.dig 1).natAbs : Int) else z.dig j
    if weight == 0 then throw "division by zero"
    if dj > Int.tdiv maxInt weight then throw "INT value out of bounds"
    let term := wrap (dj * weight)
    if sum > maxInt - term then throw "INT value out of bounds"
    sum := sum + term
    weight := wrap (weight * R)
    j := j - 1
  return if neg then -sum else sum

/-- `ten_up_mp (z, n, digs)`. -/
def tenUpMp (z : MP) (n : Int) (digs : Nat) : MPE MP :=
  let y : Array Int := #[1, 10, 100, 1000, 10000, 100000, 1000000]
  if n ≥ 0 then checkExp (setMp z y[(Int.tmod n logR).toNat]! (Int.tdiv n logR) digs)
  else checkExp (setMp z y[(Int.tmod ((logR : Int) + Int.tmod n logR) logR).toNat]! (Int.tdiv (n + 1) logR - 1) digs)

/-- `string_to_mp (z, s, digs)`: `none` when a68g would return NaN (bad syntax, or more
    significant digits than the number holds). -/
def stringToMp (s : String) (digs : Nat) : MPE (Option MP) := do
  let cs := s.toList.toArray
  let n := cs.size
  let mut z := nil digs
  let mut i0 := 0
  while i0 < n && (cs[i0]! == ' ' || cs[i0]! == '\t' || cs[i0]! == '\n') do i0 := i0 + 1
  let sign : Int := if i0 < n && cs[i0]! == '-' then -1 else 1
  if i0 < n && (cs[i0]! == '+' || cs[i0]! == '-') then i0 := i0 + 1
  while i0 < n && cs[i0]! == '0' do i0 := i0 + 1
  let chr (k : Nat) : Char := if i0 + k < n then cs[i0 + k]! else '\x00'
  let mut i := 0
  let mut dig := 1
  let mut sum : Int := 0
  let mut dot : Int := -1
  let mut one : Int := -1
  let mut pow : Int := 0
  let mut W : Int := R / 10
  while chr i != '\x00' && dig ≤ digs && ((chr i).isDigit || chr i == '.') do
    if chr i == '.' then dot := i
    else
      let value : Int := (chr i).toNat - '0'.toNat
      if one < 0 && value > 0 then one := pow
      sum := sum + W * value
      if one ≥ 0 then W := Int.tdiv W 10
      pow := pow + 1
      if W < 1 then
        z := z.setDig dig sum
        dig := dig + 1
        sum := 0
        W := R / 10
    i := i + 1
  if dig ≤ digs then
    z := z.setDig dig sum
    dig := dig + 1
  let mut expo : Int := 0
  let mut ok := true
  if chr i == 'e' || chr i == 'E' then
    -- strtol: optional blanks and sign, then digits; everything must be consumed
    let rest := (List.range (n - (i0 + i + 1))).map fun k => cs[i0 + i + 1 + k]!
    let rest := rest.dropWhile (· == ' ')
    let (neg, digits) := match rest with
      | '-' :: r => (true, r)
      | '+' :: r => (false, r)
      | r => (false, r)
    let ds := digits.takeWhile Char.isDigit
    let v : Int := ds.foldl (fun acc c => acc * 10 + ((c.toNat - '0'.toNat : Nat) : Int)) 0
    expo := if neg then -v else v
    -- strtol leaves `end` after the digits, or at the start when there are none
    let afterRaw := (List.range (n - (i0 + i + 1))).map fun k => cs[i0 + i + 1 + k]!
    ok := if ds.isEmpty then afterRaw.isEmpty else ds.length == digits.length
  else
    ok := chr i == '\x00'
  if dot ≥ 0 then
    if one > dot then expo := expo - (one - dot + 1)
    else expo := expo + dot - 1
  else
    expo := expo + pow - 1
  let (z', e) := alignMp z expo digs
  let z' := { z' with ex := if z'.dig 1 == 0 then 0 else e }
  let z' := z'.setDig 1 (z'.dig 1 * sign)
  let z' ← checkExp z'
  return if ok then some z' else none

/-- a68g's `ten_up`: 10^expo by binary powers in double precision, with its range check. -/
def tenUpReal (expo : Int) : MPE Float := do
  if expo.natAbs > 511 then throw "invalid REAL value"
  let table : Array Float := #[10.0, 100.0, 1.0e4, 1.0e8, 1.0e16, 1.0e32, 1.0e64, 1.0e128, 1.0e256]
  let mut e := expo.natAbs
  let mut r : Float := 1.0
  let mut i := 0
  while e != 0 do
    if e % 2 == 1 then r := r * table[i]!
    e := e / 2
    i := i + 1
  return if expo < 0 then 1.0 / r else r

/-- C truncation of a finite double toward zero. -/
def truncFloat (x : Float) : Int :=
  if x ≥ 0 then (x.toUInt64.toNat : Int) else -((-x).toUInt64.toNat : Int)

/-- `real_to_mp (z, x, digs)` of the generic build. -/
def realToMp (z : MP) (x : Float) (digs : Nat) : MPE MP := do
  if x.isNaN then return setNaN z
  if x.isInf then return (if x > 0 then setPInf z else setMInf z)
  let z := setZero z digs
  if x == 0.0 then return z
  if Float.abs x < 1.0e7 && Float.floor (Float.abs x) == Float.abs x then
    return ← intToMp z (truncFloat x) digs
  let signX : Int := if x > 0 then 1 else -1
  let mut a := Float.abs x
  let mut expo : Int := truncFloat (Float.log10 a)
  a := a / (← tenUpReal expo)
  expo := expo - 1
  if a ≥ 1.0 then
    a := a / 10.0
    expo := expo + 1
  let mut r := z
  let mut j := 1
  let mut k := 0
  while k ≤ 15 && j ≤ digs do
    let t := a * 1.0e7
    let dg := Float.floor t
    a := t - dg
    r := r.setDig j (truncFloat dg)
    j := j + 1
    k := k + logR
  let (r1, e) := alignMp r expo digs
  let r2 := { r1 with ex := e }
  checkExp (r2.setDig 1 (r2.dig 1 * signX))

/-- `a68g_neumaier_sum_real`. -/
def neumaierSum (terms : Array Float) : Float := Id.run do
  let n := terms.size
  if n == 0 then return 0.0
  let ascend := Float.abs terms[0]! < Float.abs terms[n - 1]!
  let mut sum : Float := 0.0
  let mut lost : Float := 0.0
  for k in [0:n] do
    let u := terms[if ascend then k else n - k - 1]!
    let v := sum + u
    if Float.abs sum ≥ Float.abs u then lost := lost + ((sum - v) + u)
    else lost := lost + ((u - v) + sum)
    sum := v
  return sum + lost

/-- `mp_to_real (p, z, digs)` of the generic build.  The result is checked as
    `CHECK_REAL` checks it. -/
def mpToReal (z : MP) (digs : Nat) : MPE Float := do
  if z.isNaN then return (0.0 / 0.0)
  if z.isPInf then return (1.0 / 0.0)
  if z.isMInf then return (-1.0 / 0.0)
  if z.ex * logR ≤ -307 then return 0.0
  let lim := min digs 36
  let mut terms : Array Float := #[]
  let mut weight : Float := 1.0
  for k in [0:lim] do
    terms := terms.push (Float.ofInt (z.dig (k + 1)).natAbs * weight)
    weight := weight / 1.0e7
  let sum := neumaierSum terms * (← tenUpReal (z.ex * logR))
  if sum.isNaN then throw "REAL value is not a number"
  if sum.isInf then throw "infinite REAL value"
  return if z.dig 1 ≥ 0 then sum else -sum

/-- `|d₁| d₂ … dₖ` read as an integer in radix `R`. -/
def mantOf (z : MP) : Nat → Int
  | 0 => 0
  | k + 1 => mantOf z k * R + (if k + 1 == 1 then ((z.dig 1).natAbs : Int) else z.dig (k + 1))

/-- The exact rational value `mant · 10^exp` of the first `digs` digits (for printing and
    for the proofs): `Σ dₖ R^(e-k+1)` with `R = 10⁷`. -/
def toDecParts (z : MP) (digs : Nat) : Int × Int :=
  let m := mantOf z digs
  (if z.dig 1 < 0 then -m else m, (z.ex - digs + 1) * logR)

end A68.MP
