import A68.Core

/-!
# A68.Blob — values crossing between a compiled program and the Lean services

A compiled program keeps its Algol 68 values in C memory (`csrc/rt.c`) and calls the
Lean side only for services on copies: formatting, transput, reading, the arithmetic of
`LONG` modes.  A value crosses as a byte string in the encoding below, which the C side
writes and reads with the same rules, so neither side needs to know the other's memory
layout.  Names and closures cross as the addresses of the C objects they refer to, and
the Lean side reaches through them by calling back into C (`Value.cref`, `Value.cclos`,
`Value.cfmt`).

Every integer is little-endian.  A mode crosses as its index in the mode table that the
program's serialised blob defines and that the Lean side may extend at run time.
-/
namespace A68.Blob

/-- Tags of the encoding. -/
inductive Tag where
  | undef | int | bigint | real | bool | char | bits | bigbits | void | nil | ref
  | row | struct | union | cproc | cfmt | builtin | file | mp | lref
  deriving Repr, DecidableEq

def Tag.code : Tag → UInt8
  | .undef => 0 | .int => 1 | .bigint => 2 | .real => 3 | .bool => 4 | .char => 5
  | .bits => 6 | .bigbits => 7 | .void => 8 | .nil => 9 | .ref => 10 | .row => 11
  | .struct => 12 | .union => 13 | .cproc => 14 | .cfmt => 15 | .builtin => 16
  | .file => 17 | .mp => 18 | .lref => 19

def Tag.ofCode : UInt8 → Option Tag
  | 0 => some .undef | 1 => some .int | 2 => some .bigint | 3 => some .real | 4 => some .bool
  | 5 => some .char | 6 => some .bits | 7 => some .bigbits | 8 => some .void | 9 => some .nil
  | 10 => some .ref | 11 => some .row | 12 => some .struct | 13 => some .union
  | 14 => some .cproc | 15 => some .cfmt | 16 => some .builtin | 17 => some .file
  | 18 => some .mp | 19 => some .lref | _ => none

-- ## Writing

def putU8 (b : ByteArray) (x : UInt8) : ByteArray := b.push x

def putU32 (b : ByteArray) (x : UInt32) : ByteArray :=
  (((b.push (x.toUInt8)).push ((x >>> 8).toUInt8)).push ((x >>> 16).toUInt8)).push ((x >>> 24).toUInt8)

def putU64 (b : ByteArray) (x : UInt64) : ByteArray := Id.run do
  let mut b := b
  for k in [0:8] do
    b := b.push ((x >>> (UInt64.ofNat (8 * k))).toUInt8)
  return b

/-- An `Int` that fits in 64 bits, two's complement. -/
def putI64 (b : ByteArray) (x : Int) : ByteArray :=
  putU64 b (if x < 0 then UInt64.ofNat ((x + 2 ^ 64).toNat) else UInt64.ofNat x.toNat)

def putF64 (b : ByteArray) (x : Float) : ByteArray := putU64 b x.toBits

def putBytes (b : ByteArray) (s : ByteArray) : ByteArray :=
  (putU32 b (UInt32.ofNat s.size)) ++ s

def putStr (b : ByteArray) (s : String) : ByteArray :=
  putBytes b (ByteArray.mk (s.toList.map fun c => UInt8.ofNat (c.toNat % 256)).toArray)

def fitsI64 (x : Int) : Bool := x ≥ -(2 ^ 63) && x < 2 ^ 63

/-- Encode a value.  `indexOf` gives the table index of a mode. -/
partial def encode (indexOf : Mode → Nat) (b : ByteArray) : Value → ByteArray
  | .undef => putU8 b Tag.undef.code
  | .int v =>
    if fitsI64 v then putI64 (putU8 b Tag.int.code) v
    else putStr (putU8 b Tag.bigint.code) (toString v)
  | .real x => putF64 (putU8 b Tag.real.code) x
  | .mp x =>
    let b := putI64 (putU64 (putU8 b Tag.mp.code) (UInt64.ofNat x.st)) x.ex
    let b := putU32 b (UInt32.ofNat x.d.size)
    x.d.foldl putI64 b
  | .bool v => putU8 (putU8 b Tag.bool.code) (if v then 1 else 0)
  | .char c => putU32 (putU8 b Tag.char.code) (UInt32.ofNat c)
  | .bits v =>
    if v < 2 ^ 64 then putU64 (putU8 b Tag.bits.code) (UInt64.ofNat v)
    else putStr (putU8 b Tag.bigbits.code) (toString v)
  | .compl re im => encode indexOf b (.struct #[.real re, .real im])
  | .void => putU8 b Tag.void.code
  | .nil => putU8 b Tag.nil.code
  | .cref a o => putU32 (putU64 (putU8 b Tag.ref.code) a) o
  | .row l u es =>
    let b := putU32 (putU8 b Tag.row.code) (UInt32.ofNat l.size)
    let b := (List.range l.size).foldl (fun b k => putI64 (putI64 b l[k]!) u[k]!) b
    let b := putU32 b (UInt32.ofNat es.size)
    es.foldl (encode indexOf) b
  | .struct fs =>
    let b := putU32 (putU8 b Tag.struct.code) (UInt32.ofNat fs.size)
    fs.foldl (encode indexOf) b
  | .union m v => encode indexOf (putU32 (putU8 b Tag.union.code) (UInt32.ofNat (indexOf m))) v
  | .cclos fn np fr => putU64 (putU32 (putU32 (putU8 b Tag.cproc.code) (UInt32.ofNat fn)) (UInt32.ofNat np)) fr
  | .cfmt fr skel => putU32 (putU64 (putU8 b Tag.cfmt.code) fr) (UInt32.ofNat skel)
  | .builtin n => putStr (putU8 b Tag.builtin.code) n
  | .file id => putU32 (putU8 b Tag.file.code) (UInt32.ofNat id)
  | .ref c [] => putU32 (putU8 b Tag.lref.code) (UInt32.ofNat c)
  -- a name with a path into a Lean value has no C counterpart; it is never produced for
  -- a compiled program, whose names all live in C
  | .ref _ _ => putU8 b Tag.undef.code
  | .proc _ _ _ _ => putU8 b Tag.undef.code
  | .fmt _ _ => putU8 b Tag.undef.code
  | .cproc _ _ _ => putU8 b Tag.undef.code

-- ## Reading

structure Cur where
  b : ByteArray
  i : Nat := 0

abbrev R := StateT Cur (Except String)

def getU8 : R UInt8 := do
  let c ← get
  if h : c.i < c.b.size then
    set { c with i := c.i + 1 }
    return c.b[c.i]
  else throw "blob: unexpected end"

def getU32 : R UInt32 := do
  let a ← getU8; let b ← getU8; let c ← getU8; let d ← getU8
  return a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) ||| (d.toUInt32 <<< 24)

def getU64 : R UInt64 := do
  let mut x : UInt64 := 0
  for k in [0:8] do
    let v ← getU8
    x := x ||| (v.toUInt64 <<< (UInt64.ofNat (8 * k)))
  return x

def getI64 : R Int := do
  let x ← getU64
  return (if x.toNat ≥ 2 ^ 63 then (x.toNat : Int) - 2 ^ 64 else x.toNat)

def getF64 : R Float := do return Float.ofBits (← getU64)

def getBytes : R ByteArray := do
  let n ← getU32
  let c ← get
  if c.i + n.toNat > c.b.size then throw "blob: string past end"
  set { c with i := c.i + n.toNat }
  return c.b.extract c.i (c.i + n.toNat)

def getStr : R String := do
  let s ← getBytes
  return String.ofList (s.data.toList.map fun x => Char.ofNat x.toNat)

/-- Decode one value.  `modeOf` gives the mode of a table index. -/
partial def decode (modeOf : Nat → Mode) : R Value := do
  match Tag.ofCode (← getU8) with
  | none => throw "blob: bad tag"
  | some t =>
    match t with
    | .undef => return .undef
    | .int => return .int (← getI64)
    | .bigint =>
      let s ← getStr
      return .int (if s.startsWith "-" then -((String.ofList (s.toList.drop 1)).toNat! : Int) else (s.toNat! : Int))
    | .real => return .real (← getF64)
    | .bool => return .bool ((← getU8) != 0)
    | .char => return .char (← getU32).toNat
    | .bits => return .bits (← getU64).toNat
    | .bigbits => return .bits (← getStr).toNat!
    | .void => return .void
    | .nil => return .nil
    | .ref => let a ← getU64; let o ← getU32; return .cref a o
    | .row =>
      let nd ← getU32
      let mut l : Array Int := #[]
      let mut u : Array Int := #[]
      for _ in [0:nd.toNat] do
        l := l.push (← getI64)
        u := u.push (← getI64)
      let n ← getU32
      let mut es : Array Value := Array.mkEmpty n.toNat
      for _ in [0:n.toNat] do
        es := es.push (← decode modeOf)
      return .row l u es
    | .struct =>
      let n ← getU32
      let mut fs : Array Value := Array.mkEmpty n.toNat
      for _ in [0:n.toNat] do
        fs := fs.push (← decode modeOf)
      return .struct fs
    | .union => let m ← getU32; return .union (modeOf m.toNat) (← decode modeOf)
    | .cproc => let fn ← getU32; let np ← getU32; let fr ← getU64; return .cclos fn.toNat np.toNat fr
    | .cfmt => let fr ← getU64; let sk ← getU32; return .cfmt fr sk.toNat
    | .builtin => return .builtin (← getStr)
    | .file => return .file (← getU32).toNat
    | .mp =>
      let st ← getU64; let ex ← getI64; let n ← getU32
      let mut d : Array Int := Array.mkEmpty n.toNat
      for _ in [0:n.toNat] do d := d.push (← getI64)
      return .mp { st := st.toNat, ex := ex, d := d }
    | .lref => return .ref (← getU32).toNat []

def decodeAll (modeOf : Nat → Mode) (b : ByteArray) : Except String (Value × Nat) := do
  let (v, c) ← (decode modeOf).run { b := b }
  return (v, c.i)

/-- Decode a sequence of `n` values laid end to end. -/
def decodeMany (modeOf : Nat → Mode) (b : ByteArray) (n : Nat) : Except String (List Value) := do
  let mut cur : Cur := { b := b }
  let mut out : List Value := []
  for _ in [0:n] do
    let (v, c) ← (decode modeOf).run cur
    cur := c
    out := out ++ [v]
  return out

end A68.Blob
