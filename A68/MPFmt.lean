import A68.MP
import A68.Numfmt

/-!
# A68.MPFmt — `whole`, `fixed` and `float` of multi-precision values

a68g formats `LONG` and `LONG LONG` values (and `LONG INT` values given to
`fixed` or `float`, which it re-labels as `LONG REAL`) with the multi-precision
arithmetic of the value's own length (`transput-formatting.c`: `sub_fixed_mp`,
`choose_dig_mp`, `fixed`, `standardize_mp`, `real`).  Those computations round
at that precision — adding the rounding term, dividing by ten while counting
digits before the point, multiplying by ten to extract each digit — so the
digits printed are not the exact decimal expansion of the value.  The routines
below repeat them with `A68.MP`.

Digits past `A68G_LONG_LONG_REAL_WIDTH` (which depends on the `LONG LONG`
precision, not on the value's) are printed as `0`, as a68g prints them.
-/
namespace A68.MPFmt

open A68.MP
open A68.Numfmt (errorChars hasError leadingSpaces wholeInt)

/-- `choose_dig_mp`: multiply by ten and take the units digit. -/
def chooseDig (y : MP) (digits : Nat) : MPE (Char × MP) := do
  let y ← mulMpDigit y y 10 digits
  let c0 : Int := if y.ex == 0 then y.dig 1 else 0
  let c := if c0 > 9 then 9 else c0
  let y ← subMp y y (lit digits c 0) digits
  return (Char.ofNat ('0'.toNat + c.toNat), y)

/-- `sub_fixed_mp (x, digits, width, after)` for non-negative `x`; `llw` is
    `A68G_LONG_LONG_REAL_WIDTH`. -/
def subFixed (x : MP) (digits : Nat) (width after : Int) (llw : Nat) : MPE String := do
  let t ← tenUpMp (nil digits) (-after) digits
  let t ← halfMp t t digits
  let mut y ← addMp (nil digits) x t digits
  let mut before : Int := 0
  while y.ex > 1 do
    let k := y.ex - 1
    y := { y with ex := y.ex - k }
    before := before + k * logR
  let s := one digits
  let mut t := t
  repeat
    t ← subMp t y s digits
    if t.dig 1 ≥ 0 then
      before := before + 1
      y ← divMpDigit y y 10 digits
    else break
  if before + after + (if after > 0 then 1 else 0) > width then
    return errorChars width
  let mut str := ""
  let mut len := 0
  for _ in [0:before.toNat] do
    if len < llw then
      let (ch, y') ← chooseDig y digits
      y := y'
      str := str.push ch
    else str := str.push '0'
    len := len + 1
  if after > 0 then str := str.push '.'
  for _ in [0:after.toNat] do
    if len < llw then
      let (ch, y') ← chooseDig y digits
      y := y'
      str := str.push ch
    else str := str.push '0'
    len := len + 1
  if (str.length : Int) > width then return errorChars width
  return str

/-- `CHECK_LONG_REAL` under strict maths. -/
def checkFinite (x : MP) : MPE Unit := do
  if x.isNaN then throw "LONG REAL value is not a number"
  if x.isInf then throw "infinite LONG REAL value"

/-- a68g `fixed (x, width, after)` for a multi-precision value. -/
partial def fixed (x : MP) (digits : Nat) (width after : Int) (llw : Nat) : MPE String := do
  checkFinite x
  let ltz := x.dig 1 < 0
  let x := x.setDig 1 (x.dig 1).natAbs
  let mut length : Int := width.natAbs - (if ltz || width > 0 then 1 else 0)
  if after ≥ 0 && (length > after || width == 0) then
    if width == 0 then
      length := if after == 0 then 1 else 0
      let z0 ← powMpInt (setMp (nil digits) (R / 10) (-1) digits) (setMp (nil digits) (R / 10) (-1) digits) after digits
      let mut z1 ← powMpInt (setMp (nil digits) 10 0 digits) (setMp (nil digits) 10 0 digits) length digits
      repeat
        let t ← divMpDigit (nil digits) z0 2 digits
        let t ← addMp t x t digits
        let t ← subMp t t z1 digits
        if t.dig 1 > 0 then
          length := length + 1
          z1 ← mulMpDigit z1 z1 10 digits
        else break
      length := length + (if after == 0 then 0 else after + 1)
    let s ← subFixed x digits length after llw
    if !hasError s then
      let mut s := s
      if length > s.length && (s.isEmpty || s.front == '.') && (x.ex < 0 || x.dig 1 == 0) then
        s := "0" ++ s
      if ltz then s := "-" ++ s else if width > 0 then s := "+" ++ s
      if width != 0 then s := leadingSpaces s width.natAbs
      return s
    else if after > 0 then
      return ← fixed (if ltz then x.negate1 else x) digits width (after - 1) llw
    else
      return errorChars width
  else
    return errorChars width

/-- `standardize_mp (y, digits, before, after, &q)`. -/
def standardize (y : MP) (digits : Nat) (before after : Int) (q : Int) : MPE (MP × Int) := do
  let g ← tenUpMp (nil digits) before digits
  let h ← divMpDigit (nil digits) g 10 digits
  let mut y := y
  let mut q := q
  if y.ex - g.ex > 1 then
    q := q + logR * (y.ex - g.ex - 1)
    y := { y with ex := g.ex + 1 }
  repeat
    let t ← subMp (nil digits) y g digits
    if t.dig 1 ≥ 0 then
      y ← divMpDigit y y 10 digits
      q := q + 1
    else break
  if y.dig 1 != 0 then
    if y.ex - h.ex < -1 then
      q := q - logR * (h.ex - y.ex - 1)
      y := { y with ex := h.ex - 1 }
    repeat
      let t ← subMp (nil digits) y h digits
      if t.dig 1 < 0 then
        y ← mulMpDigit y y 10 digits
        q := q - 1
      else break
  let f ← tenUpMp (nil digits) (-after) digits
  let t ← divMpDigit (nil digits) f 2 digits
  let t ← addMp t y t digits
  let t ← subMp t t g digits
  if t.dig 1 ≥ 0 then
    y := moveMp y h digits
    q := q + 1
  return (y, q)

/-- a68g `real (x, width, after, expo, frmt)` — `float` is `frmt = 1`. -/
partial def float (x : MP) (digits : Nat) (width after expo frmt : Int) (llw : Nat) : MPE String := do
  checkFinite x
  let x1 := x.dig 1
  let ltz := x1 < 0
  let xa := x.setDig 1 x1.natAbs
  let before : Int := width.natAbs - expo.natAbs - (if after != 0 then after + 1 else 0) - 2
  let sgn (v : Int) : Int := if v > 0 then 1 else if v < 0 then -1 else 0
  if sgn before + sgn after > 0 then
    let mut after := after
    let (z0, q0) ← standardize (moveMp (nil digits) xa digits) digits before after 0
    let mut z := z0
    let mut q := q0
    if frmt > 0 then
      while Int.tmod q frmt != 0 do
        z ← mulMpDigit z z 10 digits
        q := q - 1
        if after > 0 then after := after - 1
    else
      let mut lim ← tenUpMp (nil digits) (-frmt - 1) digits
      let mut dif ← subMp (nil digits) z lim digits
      while dif.dig 1 < 0 do
        z ← mulMpDigit z z 10 digits
        q := q - 1
        if after > 0 then after := after - 1
        dif ← subMp dif z lim digits
      lim ← mulMpDigit lim lim 10 digits
      dif ← subMp dif z lim digits
      while dif.dig 1 > 0 do
        z ← divMpDigit z z 10 digits
        q := q + 1
        if after > 0 then after := after + 1
        dif ← subMp dif z lim digits
    let zs := if ltz then z.negate1 else z
    let mut s ← fixed zs digits (sgn width * (width.natAbs - expo.natAbs - 1)) after llw
    s := s ++ "e" ++ wholeInt q expo
    if expo == 0 || hasError s then
      return ← float x digits width (if after != 0 then after - 1 else 0)
                     (if expo > 0 then expo + 1 else expo - 1) frmt llw
    else
      return s
  else
    return errorChars width

/-- `whole` of a `LONG REAL` value is `fixed (x, width, 0)`. -/
def whole (x : MP) (digits : Nat) (width : Int) (llw : Nat) : MPE String :=
  fixed x digits width 0 llw

end A68.MPFmt
