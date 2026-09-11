/-!
# A68.Numfmt — number formatting, byte-compatible with Algol 68 Genie

Algol 68 Genie formats numbers through its multi-precision (MP) library:

* `whole (n, width)`, `fixed (x, width, after)`, `float (x, width, after, exp)`;
* `print (x)` for `INT` is `whole (x, int width + 1)`, for `REAL` it is
  `float (x, real width + exp width + 4, real width - 1, exp width + 1)`.

The MP arithmetic on the values involved here is exact, *except* for the
initial conversion of a C `double` to MP, which (in the generic build used
on this platform) extracts 21 significant decimal digits with a floating
point loop (`log10`, a division by a power of ten, then repeated
`modf (a * 10^7)`).  We reproduce that loop bit for bit with `Float` and
then continue in exact decimal arithmetic (`Dec`), so that the output is
byte-for-byte identical to a68g's.
-/
namespace A68.Numfmt

/-- Exact decimal number `mant * 10^exp`. -/
structure Dec where
  mant : Int
  exp  : Int
  deriving Repr, Inhabited

namespace Dec

def zero : Dec := ⟨0, 0⟩
def ofInt (n : Int) : Dec := ⟨n, 0⟩
def tenUp (n : Int) : Dec := ⟨1, n⟩

def pow10 (n : Nat) : Int := (10 : Int) ^ n

/-- Bring two numbers to a common exponent. -/
def align (a b : Dec) : Int × Int × Int :=
  let e := min a.exp b.exp
  (a.mant * pow10 (a.exp - e).toNat, b.mant * pow10 (b.exp - e).toNat, e)

def add (a b : Dec) : Dec :=
  let (x, y, e) := align a b
  ⟨x + y, e⟩

def sub (a b : Dec) : Dec :=
  let (x, y, e) := align a b
  ⟨x - y, e⟩

def mul10 (a : Dec) : Dec := ⟨a.mant, a.exp + 1⟩
def div10 (a : Dec) : Dec := ⟨a.mant, a.exp - 1⟩
def half (a : Dec) : Dec := ⟨a.mant * 5, a.exp - 1⟩
def neg (a : Dec) : Dec := ⟨-a.mant, a.exp⟩
def isZero (a : Dec) : Bool := a.mant == 0
def sign (a : Dec) : Int := if a.mant > 0 then 1 else if a.mant < 0 then -1 else 0

/-- Sign of `a - b`. -/
def cmp (a b : Dec) : Int := (sub a b).sign

def lt (a b : Dec) : Bool := cmp a b < 0
def ge (a b : Dec) : Bool := cmp a b ≥ 0
def gt (a b : Dec) : Bool := cmp a b > 0

/-- Integer part (floor) of a non-negative number. -/
def floorNat (a : Dec) : Nat :=
  if a.exp ≥ 0 then (a.mant * pow10 a.exp.toNat).toNat
  else (a.mant / pow10 (-a.exp).toNat).toNat

/-- Number of decimal digits of a natural number (0 has one digit). -/
def ndigits (n : Nat) : Nat := if n < 10 then 1 else 1 + ndigits (n / 10)

end Dec

/-- a68g's `ten_up`: 10^expo computed by binary exponentiation in double precision. -/
def tenUpFloat (expo : Int) : Float := Id.run do
  let table : Array Float := #[10.0, 100.0, 1.0e4, 1.0e8, 1.0e16, 1.0e32, 1.0e64, 1.0e128, 1.0e256]
  let neg := expo < 0
  let mut e := expo.natAbs
  let mut r : Float := 1.0
  let mut i := 0
  while e != 0 do
    if e % 2 == 1 then r := r * table[i]!
    e := e / 2
    i := i + 1
  return if neg then 1.0 / r else r

/-- C-style truncation of a float to an integer (toward zero). -/
def truncInt (x : Float) : Int :=
  if x ≥ 0 then (x.toUInt64.toNat : Int) else -((-x).toUInt64.toNat : Int)

/-- Reproduce a68g's `real_to_mp` (generic build): returns (isNegative, |x| as Dec). -/
def realToDec (x : Float) : Bool × Dec := Id.run do
  if x == 0.0 then return (false, Dec.zero)
  let neg := x < 0
  let a0 := Float.abs x
  -- small integers are converted exactly
  if a0 < 1.0e7 && Float.floor a0 == a0 then
    return (neg, Dec.ofInt (truncInt a0))
  let mut expo := truncInt (Float.log10 a0)
  let mut a := a0 / tenUpFloat expo
  expo := expo - 1
  if a ≥ 1.0 then
    a := a / 10.0
    expo := expo + 1
  -- three MP digits of radix 10^7 (k = 0, 7, 14 ≤ 15)
  let mut mant : Int := 0
  for _ in [0:3] do
    let t := a * 1.0e7
    let dig := Float.floor t
    a := t - dig
    mant := mant * 10000000 + truncInt dig
  -- value = 0.D1D2D3 * 10^(expo+1)
  return (neg, ⟨mant, expo + 1 - 21⟩)

def errorChar : Char := '*'

def errorChars (width : Int) : String :=
  let k := if width == 0 then 1 else width.natAbs
  String.ofList (List.replicate k errorChar)

def hasError (s : String) : Bool := s.any (· == errorChar)

def leadingSpaces (s : String) (width : Nat) : String :=
  if s.length ≥ width then s else String.ofList (List.replicate (width - s.length) ' ') ++ s

/-- Digits of a natural number, or error chars if it has more than `width` digits. -/
def subWhole (n : Nat) (width : Int) : String :=
  let s := toString n
  if (s.length : Int) > width then errorChars width else s

/-- `whole` for integral values (any length). -/
def wholeInt (n : Int) (width : Int) : String :=
  let ltz := n < 0
  let an := n.natAbs
  let length : Int := if width == 0 then Dec.ndigits an
                      else width.natAbs - (if ltz || width > 0 then 1 else 0)
  let s := subWhole an length
  if length == 0 || hasError s then errorChars width.natAbs
  else
    let s := if ltz then "-" ++ s else if width > 0 then "+" ++ s else s
    if width != 0 then leadingSpaces s width.natAbs else s

/-- Digit extraction: `y` is in `[0, 1)`; returns the next decimal digit and the remainder. -/
def chooseDig (y : Dec) : Char × Dec :=
  let y := y.mul10
  let c := min (y.floorNat) 9
  (Char.ofNat ('0'.toNat + c), y.sub (Dec.ofInt c))

/-- a68g `A68G_LONG_LONG_REAL_WIDTH` on this platform: digits beyond this are printed as 0. -/
def longLongRealWidth : Nat := 70

/-- a68g `sub_fixed_mp`. -/
def subFixed (x : Dec) (width after : Int) : String := Id.run do
  let mut y := x.add (Dec.tenUp (-after)).half
  let mut before : Int := 0
  while y.ge (Dec.ofInt 1) do
    before := before + 1
    y := y.div10
  if before + after + (if after > 0 then 1 else 0) > width then
    return errorChars width
  let mut str := ""
  let mut len := 0
  for _ in [0:before.toNat] do
    if len < longLongRealWidth then
      let (ch, y') := chooseDig y
      y := y'
      str := str.push ch
    else
      str := str.push '0'
    len := len + 1
  if after > 0 then str := str.push '.'
  for _ in [0:after.toNat] do
    if len < longLongRealWidth then
      let (ch, y') := chooseDig y
      y := y'
      str := str.push ch
    else
      str := str.push '0'
    len := len + 1
  if (str.length : Int) > width then return errorChars width
  return str

/-- a68g `fixed` on a non-negative exact decimal `x` with sign flag `ltz`. -/
partial def fixedDec (ltz : Bool) (x : Dec) (width after : Int) : String := Id.run do
  let mut length : Int := width.natAbs - (if ltz || width > 0 then 1 else 0)
  if after ≥ 0 && (length > after || width == 0) then
    if width == 0 then
      length := if after == 0 then 1 else 0
      let z0 := Dec.tenUp (-after)
      let mut z1 := Dec.tenUp length
      while (z0.half.add x).sub z1 |>.gt Dec.zero do
        length := length + 1
        z1 := z1.mul10
      length := length + (if after == 0 then 0 else after + 1)
    let s := subFixed x length after
    if !hasError s then
      let mut s := s
      if length > s.length && (s.isEmpty || s.front == '.') && x.lt (Dec.ofInt 1) then
        s := "0" ++ s
      if ltz then s := "-" ++ s else if width > 0 then s := "+" ++ s
      if width != 0 then s := leadingSpaces s width.natAbs
      return s
    else if after > 0 then
      return fixedDec ltz x width (after - 1)
    else
      return errorChars width
  else
    return errorChars width

/-- a68g `standardize_mp`: scale `y` into `[10^(before-1), 10^before)` adjusting `q`,
    then pre-empt rounding overflow. -/
def standardize (y : Dec) (before after : Int) (q : Int) : Dec × Int := Id.run do
  let g := Dec.tenUp before
  let h := g.div10
  let mut y := y
  let mut q := q
  while (y.sub g).ge Dec.zero do
    y := y.div10
    q := q + 1
  if !y.isZero then
    while (y.sub h).lt Dec.zero do
      y := y.mul10
      q := q - 1
  let f := Dec.tenUp (-after)
  let t := (f.half.add y).sub g
  if t.ge Dec.zero then
    y := h
    q := q + 1
  return (y, q)

/-- a68g `real` (the `float` routine, with `frmt` = 1 for `float`, 3 for `h` patterns). -/
partial def floatDec (ltz : Bool) (x : Dec) (width after expo frmt : Int) : String := Id.run do
  let before : Int := width.natAbs - expo.natAbs - (if after != 0 then after + 1 else 0) - 2
  let sgn (v : Int) : Int := if v > 0 then 1 else if v < 0 then -1 else 0
  if sgn before + sgn after > 0 then
    let mut after := after
    let (z0, q0) := standardize x before after 0
    let mut z := z0
    let mut q := q0
    if frmt > 0 then
      while Int.tmod q frmt != 0 do
        z := z.mul10
        q := q - 1
        if after > 0 then after := after - 1
    else
      let mut lim := Dec.tenUp (-frmt - 1)
      while (z.sub lim).lt Dec.zero do
        z := z.mul10
        q := q - 1
        if after > 0 then after := after - 1
      lim := lim.mul10
      while (z.sub lim).gt Dec.zero do
        z := z.div10
        q := q + 1
        if after > 0 then after := after + 1
    let mwidth : Int := (sgn width) * (width.natAbs - expo.natAbs - 1)
    let mut s := fixedDec ltz z mwidth after
    s := s ++ "e" ++ wholeInt q expo
    if expo == 0 || hasError s then
      return floatDec ltz x width (if after != 0 then after - 1 else 0)
                      (if expo > 0 then expo + 1 else expo - 1) frmt
    else
      return s
  else
    return errorChars width

-- ## Public entry points

/-- `whole (INT, width)`. -/
def whole (n : Int) (width : Int) : String := wholeInt n width

/-- `fixed (REAL, width, after)` for a `REAL` value (double). -/
def fixedReal (x : Float) (width after : Int) : String :=
  let (neg, d) := realToDec x
  fixedDec neg d width after

/-- `fixed (INT, width, after)`: a68g first converts the INT to a double. -/
def fixedInt (n : Int) (width after : Int) : String :=
  fixedReal (Float.ofInt n) width after

/-- `fixed` for an exact integral value (LONG INT). -/
def fixedLongInt (n : Int) (width after : Int) : String :=
  fixedDec (n < 0) (Dec.ofInt n.natAbs) width after

/-- `float (REAL, width, after, exp)`. -/
def floatReal (x : Float) (width after expo : Int) (frmt : Int := 1) : String :=
  let (neg, d) := realToDec x
  floatDec neg d width after expo frmt

/-- `float (INT, ...)`: a68g converts the INT exactly. -/
def floatInt (n : Int) (width after expo : Int) (frmt : Int := 1) : String :=
  floatDec (n < 0) (Dec.ofInt n.natAbs) width after expo frmt

/-- `whole (REAL, width)` = `fixed (x, width, 0)`. -/
def wholeReal (x : Float) (width : Int) : String := fixedReal x width 0

-- ## Standard widths (a68g on a 32-bit-INT, 64-bit-REAL build)

def intWidth : Nat := 10
def realWidth : Nat := 15
def expWidth : Nat := 3
def longIntWidth : Nat := 50
def longLongIntWidth : Nat := 85
def longRealWidth : Nat := 42
def longLongRealWidth' : Nat := 70
def longExpWidth : Nat := 3
def bitsWidth : Nat := 32

/-- Number of MP digit blocks (radix 10^7) for LONG LONG modes; `PR precision N PR` changes it
    (`2 + ⌈N/7⌉`). The default corresponds to 84 decimal digits. -/
def defaultLLDigits : Nat := 12
def llDigitsOfPrecision (n : Nat) : Nat := 2 + (n + 6) / 7

/-- a68g's `MP_BITS_WIDTH (k)`, the bits of a multi-precision BITS of `k` digits:
    `ceil (k * LOG_MP_RADIX * CONST_LOG2_10) - 1`, computed in doubles as it is there. -/
def mpBitsWidth (k : Nat) : Nat :=
  (Float.ceil (Float.ofNat (k * 7) * 3.321928094887362)).toUInt64.toNat - 1

/-- The width of BITS of a length: 32 bits, and for LONG and LONG LONG BITS the width of
    a68g's multi-precision representation (162 and, at the default precision, 279). -/
def bitsWidthOfLen (long : Int) (ll : Nat := 12) : Nat :=
  if long ≤ 0 then 32 else if long == 1 then mpBitsWidth 7 else mpBitsWidth ll

def intWidthOf (long : Int) (ll : Nat := defaultLLDigits) : Nat :=
  if long ≤ 0 then intWidth else if long == 1 then longIntWidth else ll * 7 + 1
def realWidthOf (long : Int) (ll : Nat := defaultLLDigits) : Nat :=
  if long ≤ 0 then realWidth else if long == 1 then longRealWidth else (ll - 2) * 7
def expWidthOf (long : Int) : Nat := if long ≤ 0 then expWidth else longExpWidth

/-- Default `print` of an integral value of the given length. -/
def printInt (n : Int) (long : Int) (ll : Nat := defaultLLDigits) : String :=
  whole n (if long ≤ 0 then intWidthOf long ll + 1 else intWidthOf long ll)

/-- Default `print` of a real value of the given length. -/
def printReal (x : Float) (long : Int) (ll : Nat := defaultLLDigits) : String :=
  let rw := realWidthOf long ll
  let ew := expWidthOf long
  floatReal x (rw + ew + 4) (rw - 1) (ew + 1)

/-- Default `print` of BITS: `bits width` flip/flop characters, most significant first. -/
def printBits (v : Nat) (width : Nat := bitsWidth) : String :=
  String.ofList ((List.range width).reverse.map fun i => if (v / 2^i) % 2 == 1 then 'T' else 'F')

/-- Integer limits. -/
def maxInt : Int := 2147483647
def longMaxInt : Int := (10 : Int) ^ 49 - 1
def longLongMaxInt : Int := (10 : Int) ^ 84 - 1
def maxIntOf (long : Int) (ll : Nat := defaultLLDigits) : Int :=
  if long ≤ 0 then maxInt else if long == 1 then longMaxInt else (10 : Int) ^ (ll * 7) - 1

end A68.Numfmt

namespace A68.Numfmt

/-- Parse a decimal literal (`123`, `1.5`, `.5`, `1e-5`, `1.5E+3`) into a correctly rounded
    `Float`, as C `strtod` would. -/
def parseFloat (s : String) : Float := Id.run do
  let cs := s.toList
  let mut mant : Nat := 0
  let mut exp : Int := 0
  let mut i := 0
  let arr := cs.toArray
  let n := arr.size
  while i < n && arr[i]!.isDigit do
    mant := mant * 10 + (arr[i]!.toNat - '0'.toNat); i := i + 1
  if i < n && arr[i]! == '.' then
    i := i + 1
    while i < n && arr[i]!.isDigit do
      mant := mant * 10 + (arr[i]!.toNat - '0'.toNat); exp := exp - 1; i := i + 1
  if i < n && (arr[i]! == 'e' || arr[i]! == 'E') then
    i := i + 1
    let mut neg := false
    if i < n && (arr[i]! == '+' || arr[i]! == '-') then
      neg := arr[i]! == '-'; i := i + 1
    let mut e : Nat := 0
    while i < n && arr[i]!.isDigit do
      e := e * 10 + (arr[i]!.toNat - '0'.toNat); i := i + 1
    exp := exp + (if neg then -(e : Int) else e)
  if exp ≥ 0 then Float.ofScientific mant false exp.toNat
  else Float.ofScientific mant true (-exp).toNat

end A68.Numfmt
