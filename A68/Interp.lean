import A68.Core
import A68.Elab
import A68.Numfmt

/-!
# A68.Interp — evaluator for the elaborated `Core` representation

Runtime model:

* a heap of *cells* (`Array Value`), each holding one value; a `REF` is a cell
  number plus a path of selections (field / element / sub-row view) into it;
* an environment is a list of frames, each frame an array of cell numbers;
  frames are pushed by blocks, calls, loops and conformity alternatives —
  exactly where the elaborator opened a scope;
* values are immutable data; only cells are mutable;
* control flow that escapes expressions (jumps, `stop`, runtime errors) is
  modelled with `ExceptT`.

Numeric semantics follow Algol 68 Genie: 32-bit `INT` with overflow checks,
49/84-digit `LONG`/`LONG LONG INT`, IEEE double `REAL` with checks for
infinities and NaNs after every operation, `**` by square-and-multiply.
-/
namespace A68.Interp

inductive Ctrl where
  | error (msg : String) (pos : Pos)
  | jump (label : Nat)
  | stop
  | fileEnd (fid : Nat)   -- mended logical file end (internal)
  deriving Inhabited

/-- State of the taus113 generator (as in a68g / GSL). -/
structure Taus where
  z1 : UInt32
  z2 : UInt32
  z3 : UInt32
  z4 : UInt32
  deriving Inhabited

/-- State of an open file. Standard files: 0 = stand out, 1 = stand in, 2 = stand error, 3 = stand back. -/
structure FileSt where
  name    : String := ""
  buf     : ByteArray := ByteArray.empty     -- contents (reading) or accumulated output (writing)
  pos     : Nat := 0
  assoc   : Option Value := none             -- REF STRING for associated files
  onEnd   : Option Value := none             -- PROC (REF FILE) BOOL, on logical file end
  onValue : Option Value := none             -- PROC (REF FILE) BOOL, on value error
  onLine  : Option Value := none             -- PROC (REF FILE) BOOL, on line end
  term    : List Nat := []                   -- string terminators (make term)
  writing : Bool := false
  reading : Bool := false
  loaded  : Bool := false                    -- stand in: read lazily
  eof     : Bool := false                    -- stand in: no more input available
  dirty   : Bool := false                    -- has unflushed output for a disk file
  onDisk  : Bool := false
  deriving Inhabited

structure Rt where
  heap  : IO.Ref (Array Value)
  out   : IO.Ref ByteArray
  pos   : IO.Ref Pos
  modes : Mode.Table
  files : IO.Ref (Array FileSt)
  rng   : IO.Ref Taus
  args  : Array String
  ll    : Nat := Numfmt.defaultLLDigits
  regression : Bool := false
  col   : IO.Ref Nat                        -- characters on the current formatted-output line

abbrev M := ReaderT Rt (ExceptT Ctrl IO)

abbrev Env := List (Array Nat)

instance : Inhabited (M α) := ⟨fun _ => throw default⟩

def rtErr (msg : String) : M α := do
  let p ← (← read).pos.get
  throw (.error msg p)

def alloc (v : Value) : M Nat := do
  (← read).heap.modifyGet fun h => (h.size, h.push v)

def llDigits : M Nat := do return (← read).ll

def readCell (c : Nat) : M Value := do
  let h ← (← read).heap.get
  return h[c]!

def writeCell (c : Nat) (v : Value) : M Unit := do
  (← read).heap.modify fun h => h.set! c v

def modifyCell (c : Nat) (f : Value → Value) : M Unit := do
  (← read).heap.modify fun h => h.modify c f

def emitByte (b : UInt8) : M Unit := do
  (← read).out.modify fun o => o.push b

def emit (s : String) : M Unit := do
  (← read).out.modify fun o => s.foldl (fun acc c => acc.push c.toNat.toUInt8) o

def flushOut : M Unit := do
  let r := (← read).out
  let o ← r.get
  r.set ByteArray.empty
  let stdout ← IO.getStdout
  stdout.write o
  stdout.flush

def frameCell (env : Env) (d s : Nat) : M Nat := do
  match env[d]? with
  | some fr =>
    match fr[s]? with
    | some c => return c
    | none => rtErr s!"internal: slot {s} out of range in frame {d}"
  | none => rtErr s!"internal: frame depth {d} out of range"

-- ## Values

def resolveM (m : Mode) : M Mode := do return Mode.resolve (← read).modes m

def modeName (m : Mode) : String := Mode.toString m

/-- Check a scalar value is initialised. -/
def checkInit (v : Value) (m : Mode := .void) : M Value := do
  match v with
  | .undef => rtErr s!"attempt to use an uninitialised {if m == .void then "" else modeName m ++ " "}value"
  | _ => return v

def expectInt : Value → M Int
  | .int n => pure n
  | .undef => rtErr "attempt to use an uninitialised INT value"
  | v => rtErr s!"internal: INT expected, got {reprValue v}"
where
  reprValue : Value → String
    | .real _ => "REAL" | .bool _ => "BOOL" | .char _ => "CHAR" | .row .. => "row"
    | .ref .. => "REF" | .nil => "NIL" | .proc .. => "PROC" | .struct _ => "STRUCT"
    | .union .. => "UNION" | .void => "VOID" | .bits _ => "BITS" | .builtin n => s!"builtin {n}"
    | _ => "?"

def expectReal : Value → M Float
  | .real x => pure x
  | .int n => pure (Float.ofInt n)
  | .undef => rtErr "attempt to use an uninitialised REAL value"
  | _ => rtErr "internal: REAL expected"

def expectBool : Value → M Bool
  | .bool b => pure b
  | .undef => rtErr "attempt to use an uninitialised BOOL value"
  | _ => rtErr "internal: BOOL expected"

def expectChar : Value → M Nat
  | .char c => pure c
  | .undef => rtErr "attempt to use an uninitialised CHAR value"
  | _ => rtErr "internal: CHAR expected"

def expectBits : Value → M Nat
  | .bits b => pure b
  | .undef => rtErr "attempt to use an uninitialised BITS value"
  | _ => rtErr "internal: BITS expected"

def expectRow : Value → M (Array Int × Array Int × Array Value)
  | .row l u es => pure (l, u, es)
  | .undef => rtErr "attempt to use an uninitialised row"
  | _ => rtErr "internal: row expected"

def strOf : Value → M String
  | .row _ _ es => do
    let mut s := ""
    for e in es do
      match e with
      | .char c => s := s.push (Char.ofNat c)
      | .undef => rtErr "attempt to use an uninitialised CHAR value"
      | _ => rtErr "internal: [] CHAR expected"
    return s
  | .char c => pure (String.singleton (Char.ofNat c))
  | .undef => rtErr "attempt to use an uninitialised STRING value"
  | _ => rtErr "internal: STRING expected"

def rowSize (l u : Array Int) : Nat := Id.run do
  let mut n := 1
  for i in [0:l.size] do
    let d := u[i]! - l[i]! + 1
    if d ≤ 0 then return 0
    n := n * d.toNat
  return n

-- ## References

/-- Read the value designated by a path inside `v`. -/
def readPath (v : Value) : List Sel → M Value
  | [] => pure v
  | .field i :: rest =>
    match v with
    | .struct fs => readPath fs[i]! rest
    | .row l u es => do
      -- multiple selection: the field of every element
      let fs ← es.mapM fun e => match e with
        | .struct efs => pure efs[i]!
        | _ => rtErr "internal: field selection on non-struct element"
      readPath (.row l u fs) rest
    | _ => rtErr "internal: field selection on non-struct"
  | .elem i :: rest =>
    match v with
    | .row _ _ es =>
      match es[i]? with
      | some e => readPath e rest
      | none => rtErr "internal: element index out of range"
    | _ => rtErr "internal: element selection on non-row"
  | .sub l u offs :: rest =>
    match v with
    | .row _ _ es => readPath (.row l u (offs.map fun o => es[o]!)) rest
    | _ => rtErr "internal: sub-row of non-row"

/-- Functionally update the value at a path. -/
partial def updatePath (v : Value) (path : List Sel) (nv : Value) : M Value := do
  match path with
  | [] => return nv
  | .field i :: rest =>
    match v with
    | .struct fs =>
      let old := fs[i]!
      let fs' := fs.set! i .undef
      let nw ← updatePath old rest nv
      return .struct (fs'.set! i nw)
    | .row l u es =>
      -- multiple selection: assign the field of every element from a row of values
      match rest, nv with
      | [], .row _ _ vs =>
        if vs.size != es.size then rtErr "bounds of source and destination do not match"
        let mut es' := es
        for k in [0:es.size] do
          match es'[k]! with
          | .struct efs => es' := es'.set! k (.struct (efs.set! i vs[k]!))
          | _ => rtErr "internal: field update on non-struct element"
        return .row l u es'
      | .elem k :: rest', _ =>
        -- `(field OF row)[k] := v`  is  `field OF row[k] := v`
        updatePath v (.elem k :: .field i :: rest') nv
      | _, _ => rtErr "internal: unsupported multiple-selection update"
    | _ => rtErr "internal: field update on non-struct"
  | .elem i :: rest =>
    match v with
    | .row l u es =>
      if i ≥ es.size then rtErr "internal: element update out of range"
      let old := es[i]!
      let es' := es.set! i .undef
      let nw ← updatePath old rest nv
      return .row l u (es'.set! i nw)
    | _ => rtErr "internal: element update on non-row"
  | .sub _ _ offs :: rest =>
    match v with
    | .row l u es =>
      match rest with
      | [] =>
        match nv with
        | .row _ _ ses =>
          if ses.size != offs.size then rtErr "bounds of source and destination do not match"
          let mut es' := es
          for k in [0:offs.size] do
            es' := es'.set! (offs[k]!) (ses[k]!)
          return .row l u es'
        | _ => rtErr "internal: sub-row assignment of non-row"
      | _ => rtErr "internal: path continues after sub-row"
    | _ => rtErr "internal: sub-row update of non-row"

def readRef : Value → M Value
  | .ref c path => do readPath (← readCell c) path
  | .nil => rtErr "attempt to dereference NIL"
  | .undef => rtErr "attempt to use an uninitialised REF value"
  | _ => rtErr "internal: dereferencing a non-REF"

/-- Take the value out of a cell (leaving it undefined), so that the value is uniquely owned
    and can be updated in place. -/
def takeCell (c : Nat) : M Value := do
  (← read).heap.modifyGet fun h => (h[c]!, h.set! c .undef)

def writeRef (r : Value) (nv : Value) : M Unit := do
  match r with
  | .ref c [] => writeCell c nv
  | .ref c path =>
    let old ← takeCell c
    let nw ← updatePath old path nv
    writeCell c nw
  | .nil => rtErr "attempt to assign to NIL"
  | _ => rtErr "internal: assignment to a non-REF"

/-- Extend a ref path by an element selection, composing through a sub-row view. -/
def refElem (r : Value) (i : Nat) : M Value := do
  match r with
  | .ref c path =>
    match path.getLast? with
    | some (.sub _ _ offs) => return .ref c (path.dropLast ++ [.elem offs[i]!])
    | _ => return .ref c (path ++ [.elem i])
  | _ => rtErr "internal: refElem"

def refSub (r : Value) (l u : Array Int) (offs : Array Nat) : M Value := do
  match r with
  | .ref c path =>
    match path.getLast? with
    | some (.sub _ _ offs0) => return .ref c (path.dropLast ++ [.sub l u (offs.map fun o => offs0[o]!)])
    | _ => return .ref c (path ++ [.sub l u offs])
  | _ => rtErr "internal: refSub"

def fileOut (fid : Nat) (s : String) : M Unit := do
  let colRef := (← read).col
  for c in s.toList do
    if c == '\n' then colRef.set 0 else colRef.modify (· + 1)
  if fid == 0 then emit s
  else if fid == 2 then
    let stderr ← IO.getStderr
    stderr.putStr s
  else
    let fs ← (← read).files.get
    match fs[fid]? with
    | none => rtErr "file is not open"
    | some f0 =>
      -- an associated file whose string was reassigned starts from the string's current value
      let f ← if f0.loaded then pure f0 else do
        match f0.assoc with
        | some r =>
          let str ← strOf (← readRef r)
          pure { f0 with buf := str.foldl (fun acc c => acc.push c.toNat.toUInt8) ByteArray.empty, pos := 0, loaded := true }
        | none => pure { f0 with loaded := true }
      let f' := { f with buf := s.foldl (fun acc c => acc.push c.toNat.toUInt8) f.buf, writing := true, dirty := true }
      (← read).files.modify fun fs => fs.set! fid f'
      match f'.assoc with
      | some r => writeRef r (Value.ofString (String.ofList (f'.buf.toList.map fun b => Char.ofNat b.toNat)))
      | none => pure ()

-- ## Numbers

/-- COMPL values are represented as `STRUCT (REAL re, REAL im)` so that `re OF z` is a name. -/
def mkCompl (a b : Float) : Value := .struct #[.real a, .real b]

def checkIntRange (n : Int) (long : Int) : M Int := do
  if n.natAbs > (Numfmt.maxIntOf long (← llDigits)).natAbs then
    rtErr s!"{Mode.toString (.int long)} value overflow, result too large"
  return n

def checkReal (x : Float) : M Float := do
  if x.isNaN then rtErr "REAL value is not a number"
  if x.isInf then rtErr "infinite REAL value"
  return x

/-- a68g `a68g_x_up_n_real`: square-and-multiply in a fixed order. -/
def powRealIntPos (x : Float) (nn : Nat) : M Float := do
  if x == 0.0 && nn == 0 then return 1.0
  if x == 0.0 || x == 1.0 then return x
  if x == -1.0 then return (if nn % 2 == 0 then 1.0 else -1.0)
  let mut bit : Nat := 1
  let mut mm := x
  let mut p : Float := 1.0
  repeat
    if nn &&& bit != 0 then p := p * mm
    bit := bit <<< 1
    if bit ≤ nn then mm := mm * mm
    if !(bit ≤ nn) then break
  if p.isInf || p.isNaN then rtErr "infinite REAL value"
  return p

def powRealInt (x : Float) (n : Int) : M Float := do
  if n < 0 then
    let p ← powRealIntPos x n.natAbs
    return 1.0 / p
  else powRealIntPos x n.toNat

def powIntInt (m n : Int) (long : Int) : M Int := do
  if n < 0 then rtErr "invalid INT exponent"
  if m == 0 && n == 0 then return 1
  if m == 0 || m == 1 then return m
  if m == -1 then return (if n % 2 == 0 then 1 else -1)
  let mut bit : Nat := 1
  let mut mm := m
  let mut p : Int := 1
  let nn := n.toNat
  repeat
    if nn &&& bit != 0 then p ← checkIntRange (p * mm) long
    bit := bit <<< 1
    if bit ≤ nn then mm ← checkIntRange (mm * mm) long
    if !(bit ≤ nn) then break
  return p

/-- a68g ROUND: round half away from zero. -/
def roundReal (x : Float) : Int :=
  let ax := Float.abs x
  let r := Float.floor (ax + 0.5)
  let n : Int := r.toUInt64.toNat
  if x < 0 then -n else n

def realMod (a b : Float) : Float := a - b * Float.floor (a / b)

def bitsWidthOf (long : Int) : Nat := if long ≤ 0 then 32 else 64
def bitsMask (long : Int) : Nat := 2 ^ (bitsWidthOf long) - 1

-- ## Output of values (unformatted transput)

def fileOutByte (fid : Nat) (b : UInt8) : M Unit := do
  if fid == 0 then emitByte b
  else fileOut fid (String.singleton (Char.ofNat b.toNat))

/-- Print a value of the given mode with the standard layout. -/
partial def printValue (fid : Nat) (m : Mode) (v : Value) : M Unit := do
  let mr ← resolveM m
  match mr, v with
  | _, .union m' v' => printValue fid m' v'
  | .int n, .int i => fileOut fid (Numfmt.printInt i n (← llDigits))
  | .int _, .real x => fileOut fid (Numfmt.printReal x 0)
  | .real n, .real x => do let _ ← checkReal x; fileOut fid (Numfmt.printReal x n (← llDigits))
  | .real n, .int i => fileOut fid (Numfmt.printReal (Float.ofInt i) n (← llDigits))
  | .bool, .bool b => fileOut fid (if b then "T" else "F")
  | .char, .char c => fileOutByte fid c.toUInt8
  | .bits n, .bits b => fileOut fid (Numfmt.printBits b (bitsWidthOf n))
  | .compl n, .struct #[.real re, .real im] => do
    let _ ← checkReal re; let _ ← checkReal im
    fileOut fid (Numfmt.printReal re n (← llDigits) ++ Numfmt.printReal im n (← llDigits))
  | .row _ _ em, .row _ _ es =>
    for e in es do
      match e with
      | .undef => rtErr s!"attempt to use an uninitialised {modeName em} value"
      | _ => printValue fid em e
  | .struct fs, .struct vs =>
    for (f, x) in fs.zip vs.toList do
      match x with
      | .undef => rtErr s!"attempt to use an uninitialised {modeName f.2} value"
      | _ => printValue fid f.2 x
  | .proc [.ref .file] .void, f => callFileProc fid f
  | .format, _ => rtErr "cannot print a FORMAT value"
  | _, .undef => rtErr s!"attempt to use an uninitialised {modeName m} value"
  | _, .nil => rtErr "cannot print NIL"
  | _, _ => rtErr s!"cannot print a value of mode {modeName m}"
where
  callFileProc (fid : Nat) (f : Value) : M Unit := do
    match f with
    | .builtin "newline" => fileOut fid "\n"
    | .builtin "newpage" => fileOut fid "\x0c"
    | .builtin "space" => fileOut fid " "
    | .builtin "backspace" => fileOut fid "\x08"
    | .builtin n => rtErr s!"cannot print procedure {n}"
    | _ => rtErr "cannot print a procedure value"

def fileIdOf (f : Value) : M Nat := do
  match f with
  | .file id => return id
  | .ref _ _ =>
    match (← readRef f) with
    | .file id => return id
    | _ => rtErr "internal: file expected"
  | _ => rtErr "internal: file expected"

-- ## Formats

/-- A flattened format picture. -/
inductive Frame where
  | z | d | plus | minus | point | e | a
  | ins (s : String)          -- literal / alignment insertion inside a pattern
  deriving Repr, Inhabited, BEq

inductive Pic where
  | ins (s : String)
  | pattern (frames : List Frame)              -- numeric or string pattern
  | general (args : List Int)
  | bool_ (flip flop : Option String)
  | choice (alts : List String)
  | include (items : List CoreFmt) (env : Env)
  | col (n : Nat)
  deriving Inhabited

/-- Normalise the mode tag of a united value. -/
def resolveUnion (v : Value) : M Value := do
  match v with
  | .union m x => return .union (← resolveM m) x
  | _ => return v

/-- a68g `shift_sign`: move a leading sign right through leading `z` frames over zeros. -/
def shiftSign (frames : List Frame) (buf : List Char) : List Char := Id.run do
  let mut q := buf
  let mut pre : List Char := []
  for f in frames do
    match f, q with
    | .z, s :: z0 :: qs =>
      if (s == '+' || s == '-') && z0 == '0' then
        pre := pre ++ ['0']; q := s :: qs
    | .d, _ => return pre ++ q
    | _, _ => pure ()
  return pre ++ q

/-- Builder state for flattening a format into pictures. -/
structure FmtBuild where
  pics : List Pic := []
  pending : List Frame := []
  pendingIns : List Frame := []

def FmtBuild.flush (b : FmtBuild) : List Pic := Id.run do
  let mut ps := b.pics
  if !b.pending.isEmpty then ps := ps ++ [.pattern b.pending]
  for f in b.pendingIns do
    match f with
    | .ins s => ps := ps ++ [.ins s]
    | _ => pure ()
  return ps

def FmtBuild.addFrame (b : FmtBuild) (fr : Frame) : FmtBuild :=
  { b with pending := b.pending ++ b.pendingIns ++ [fr], pendingIns := [] }

def FmtBuild.addIns (b : FmtBuild) (s : String) : FmtBuild :=
  if b.pending.isEmpty then { b with pics := b.pics ++ [.ins s] }
  else { b with pendingIns := b.pendingIns ++ [.ins s] }

def FmtBuild.addPic (b : FmtBuild) (p : Pic) : FmtBuild :=
  { pics := b.flush ++ [p], pending := [], pendingIns := [] }

/-- One (possibly embedded) format being processed. -/
structure FmtFrame where
  pics : Array Pic
  cursor : Nat
  embedded : Bool
  deriving Inhabited

/-- Formatted transput state: a stack of format frames, innermost first. -/
structure FmtState where
  frames : List FmtFrame
  deriving Inhabited

/-- Compiled code installs these: they evaluate a hole of a format text, and apply a
    compiled procedure. In interpreted mode they are never reached. -/
@[extern "a68_dispatch_hole"]
opaque dispatchHole (fn : USize) (idx : USize) (env : @& Env) : IO Value

@[extern "a68_dispatch_proc"]
opaque dispatchProc (fn : USize) (env : @& Env) (args : @& Array Value) : IO Value

-- ## Evaluation

mutual

partial def eval (env : Env) (c : Core) : M Value := do
  match c with
  | .lit v => return v
  | .loadCell d s =>
    let v ← readCell (← frameCell env d s)
    match v with
    | .undef => rtErr "attempt to use an uninitialised value"
    | _ => return v
  | .refCell d s => return .ref (← frameCell env d s) []
  | .deref e =>
    let r ← eval env e
    let v ← readRef r
    match v with
    | .undef => rtErr "attempt to use an uninitialised value"
    | _ => return v
  | .deproc e =>
    let f ← eval env e
    callValue f []
  | .widen src dst e => widenValue src dst (← eval env e)
  | .rowOf e =>
    let v ← eval env e
    match v with
    | .ref _ _ => return v   -- REF rowing: keep the name (approximation)
    | _ => return .row #[1] #[1] #[v]
  | .unite m e => return .union m (← eval env e)
  | .voiding e => do let _ ← eval env e; return .void
  | .assign dest src flex =>
    let d ← eval env dest
    let v ← eval env src
    assignTo d v flex
    return d
  | .identRel l r isnt =>
    let a ← eval env l
    let b ← eval env r
    let same := match a, b with
      | .ref c1 p1, .ref c2 p2 => c1 == c2 && p1 == p2
      | .nil, .nil => true
      | _, _ => false
    return .bool (if isnt then !same else same)
  | .dyop op m1 m2 l r =>
    let a ← eval env l
    let b ← eval env r
    dyadic op m1 m2 a b
  | .monop op m e => monadic op m (← eval env e)
  | .call f args =>
    let fv ← eval env f
    let avs ← args.mapM (eval env)
    callValue fv avs
  | .routine n fs body => return .proc env n fs body
  | .slice arr idx viaRef => evalSlice env arr idx viaRef
  | .select i e viaRef =>
    let v ← eval env e
    if viaRef then
      match v with
      | .ref c path => return .ref c (path ++ [.field i])
      | .nil => rtErr "attempt to select from NIL"
      | _ => rtErr "internal: select via non-REF"
    else
      match v with
      | .struct fs => return fs[i]!
      | .row _ _ _ => readPath v [.field i]
      | _ => rtErr "internal: select from non-struct"
  | .newRow bounds init _ =>
    let mut ls : Array Int := #[]
    let mut us : Array Int := #[]
    for (lc, uc) in bounds do
      ls := ls.push (← expectInt (← eval env lc))
      us := us.push (← expectInt (← eval env uc))
    let iv ← eval env init
    let n := rowSize ls us
    return .row ls us (Array.replicate n iv)
  | .gen init =>
    let v ← eval env init
    return .ref (← alloc v) []
  | .block size stmts labelBase nLabels => runBlock env size stmts labelBase nLabels
  | .collateral es isStruct dims =>
    let vs ← es.mapM (eval env)
    if isStruct then return .struct vs.toArray
    else if dims ≤ 1 then return .row #[1] #[vs.length] vs.toArray
    else
      -- rows of (dims-1)-dimensional rows with equal bounds
      match vs with
      | [] => return .row (Array.replicate dims 1) (Array.replicate dims 0) #[]
      | first :: _ =>
        let (l0, u0, _) ← expectRow first
        let mut elems : Array Value := #[]
        for v in vs do
          let (l, u, es) ← expectRow v
          if l != l0 || u != u0 then rtErr "bounds of row display elements differ"
          elems := elems ++ es
        return .row (#[(1 : Int)] ++ l0) (#[(vs.length : Int)] ++ u0) elems
  | .cond c t e =>
    if (← expectBool (← eval env c)) then eval env t else eval env e
  | .caseInt sel alts out =>
    let i ← expectInt (← eval env sel)
    if i ≥ 1 && i ≤ alts.length then eval env (alts[(i - 1).toNat]!) else eval env out
  | .caseConf sel alts out =>
    let v ← eval env sel
    let (vm, inner) := match v with
      | .union m x => (m, x)
      | x => (.void, x)
    let tb := (← read).modes
    for (m, slot, body) in alts do
      let ok ← match Mode.resolve tb m with
        | .union ms => pure (ms.any fun cm => Mode.eqv tb cm vm)
        | _ => pure (Mode.eqv tb m vm)
      if ok then
        let bound := match Mode.resolve tb m with
          | .union _ => v
          | _ => inner
        let frame ← match slot with
          | some _ => do let cnum ← alloc bound; pure #[cnum]
          | none => pure #[]
        return ← eval (frame :: env) body
    eval env out
  | .loop slot f b t w body =>
    let fv ← expectInt (← eval env f)
    let bv ← expectInt (← eval env b)
    let tv ← match t with
      | some tc => some <$> expectInt (← eval env tc)
      | none => pure none
    let mut i := fv
    repeat
      match tv with
      | some tt => if (bv > 0 && i > tt) || (bv < 0 && i < tt) then break
      | none => pure ()
      let frame ← match slot with
        | some _ => do let cnum ← alloc (.int i); pure #[cnum]
        | none => pure #[]
      let env' := frame :: env
      match w with
      | some wc => if !(← expectBool (← eval env' wc)) then break
      | none => pure ()
      let _ ← eval env' body
      i := i + bv
    return .void
  | .goto id => throw (.jump id)
  | .skip m => defaultOf m
  | .andThen l r =>
    if (← expectBool (← eval env l)) then eval env r else return .bool false
  | .orElse l r =>
    if (← expectBool (← eval env l)) then return .bool true else eval env r
  | .fmt items => return .fmt env items
  | .stop => throw .stop
  | .hole fn idx => (dispatchHole (USize.ofNat fn) (USize.ofNat idx) env : IO Value)
  | .seq a b => do let _ ← eval env a; eval env b
  | .at p e =>
    (← read).pos.set p
    eval env e

/-- The value a `SKIP` of this mode denotes; also the initial value of a generated object.
    Used by both the evaluator and the runtime of compiled programs. -/
partial def defaultOf (m : Mode) : M Value := do
  match (← resolveM m) with
  | .void => return .void
  | .row d _ _ => return .row (Array.replicate d 1) (Array.replicate d 0) #[]
  | _ => return .undef

partial def evalSlice (env : Env) (arr : Core) (idx : List CoreIdx) (viaRef : Bool) : M Value := do
  let base ← eval env arr
  let mut ivs : List IdxVal := []
  for ix in idx do
    match ix with
    | .index e => ivs := ivs ++ [.index (← eval env e)]
    | .trim lo hi at_ =>
      let lo' ← lo.mapM fun e => eval env e
      let hi' ← hi.mapM fun e => eval env e
      let at' ← at_.mapM fun e => eval env e
      ivs := ivs ++ [.trim lo' hi' at']
  sliceValue base ivs viaRef

/-- Slice or trim a value with already evaluated indexers.  Both the evaluator and the
    runtime of compiled programs use this; no syntax is involved. -/
partial def sliceValue (base : Value) (idx : List IdxVal) (viaRef : Bool) : M Value := do
  let rowV ← if viaRef then readRef base else pure base
  let (l, u, es) ← expectRow rowV
  let d := l.size
  -- fast path: one-dimensional subscript
  match idx with
  | [.index iv] =>
    if d == 1 then
      let i ← expectInt iv
      let lo := l[0]!
      let hi := u[0]!
      if i < lo || i > hi then rtErr s!"index {i} out of bounds [{lo}:{hi}]"
      let o := (i - lo).toNat
      if viaRef then return ← refElem base o
      else
        match es[o]? with
        | some v => return v
        | none => rtErr "internal: element offset out of range"
  | _ => pure ()
  -- collect the indexers
  let mut ixs : Array (Option Int × Option Int × Option Int × Bool) := #[]   -- (lwb, upb, at, isIndex)
  for ix in idx do
    match ix with
    | .index iv =>
      let i ← expectInt iv
      ixs := ixs.push (some i, some i, none, true)
    | .trim lo hi at_ =>
      let lo' ← lo.mapM expectInt
      let hi' ← hi.mapM expectInt
      let at' ← at_.mapM expectInt
      ixs := ixs.push (lo', hi', at', false)
  -- strides
  let mut strides : Array Nat := Array.replicate d 1
  for k in [0:d] do
    let j := d - 1 - k
    if j + 1 < d then
      let ext := (u[j+1]! - l[j+1]! + 1)
      strides := strides.set! j (strides[j+1]! * (if ext > 0 then ext.toNat else 0))
  -- per-dimension ranges
  let mut newL : Array Int := #[]
  let mut newU : Array Int := #[]
  let mut ranges : Array (Int × Int × Nat × Int) := #[]   -- (from, to, stride, isTrim)
  for k in [0:d] do
    let (lo, hi, at_, isIndex) := ixs[k]!
    let lo := lo.getD l[k]!
    let hi := hi.getD u[k]!
    if isIndex then
      if lo < l[k]! || lo > u[k]! then rtErr s!"index {lo} out of bounds [{l[k]!}:{u[k]!}]"
    else
      if lo < l[k]! || hi > u[k]! then
        if !(hi < lo) then rtErr s!"trim [{lo}:{hi}] out of bounds [{l[k]!}:{u[k]!}]"
      let nl := at_.getD 1
      newL := newL.push nl
      newU := newU.push (nl + (hi - lo))
    ranges := ranges.push (lo, hi, strides[k]!, if isIndex then 0 else 1)
  if newL.isEmpty then
    -- plain element
    let mut off : Int := 0
    for k in [0:d] do
      let (lo, _, st, _) := ranges[k]!
      off := off + (lo - l[k]!) * st
    let o := off.toNat
    if viaRef then refElem base o
    else
      match es[o]? with
      | some v => return v
      | none => rtErr "internal: element offset out of range"
  else
    -- gather offsets in row-major order of the trimmed dimensions
    let mut offs : Array Nat := #[]
    let mut cur : Array Int := ranges.map (·.1)
    let total := rowSize newL newU
    if total > 0 then
      repeat
        let mut off : Int := 0
        for k in [0:d] do
          off := off + (cur[k]! - l[k]!) * ranges[k]!.2.2.1
        offs := offs.push off.toNat
        -- increment
        let mut k := d
        let mut carry := true
        while carry && k > 0 do
          k := k - 1
          let (lo, hi, _, isTrim) := ranges[k]!
          if isTrim == 1 then
            if cur[k]! < hi then
              cur := cur.set! k (cur[k]! + 1); carry := false
            else
              cur := cur.set! k lo
        if carry then break
    if viaRef then refSub base newL newU offs
    else return .row newL newU (offs.map fun o => es[o]!)

partial def assignTo (d : Value) (v : Value) (flex : Bool) : M Unit := do
  match d with
  | .ref _ path =>
    match v with
    | .row vl vu _ =>
      -- bounds check for non-flex rows (unless assigning through a view, checked in updatePath)
      let old ← readRef d
      match old, path.getLast? with
      | .row ol ou _, some (.sub ..) =>
        if rowSize ol ou != rowSize vl vu then rtErr "bounds of source and destination do not match"
        writeRef d v
      | .row ol ou oes, _ =>
        -- a variable whose bounds were not given (mode indicant without bounds) is still empty:
        -- accept the first assignment as establishing its bounds
        if !flex && (ol != vl || ou != vu) && !(oes.size == 0 && rowSize ol ou == 0) then
          rtErr "bounds of source and destination do not match"
        writeRef d v
      | _, _ => writeRef d v
    | .undef => rtErr "attempt to use an uninitialised value"
    | _ => writeRef d v
  | .nil => rtErr "attempt to assign to NIL"
  | _ => rtErr "internal: assignment to a non-REF"

partial def widenValue (src dst : Mode) (v : Value) : M Value := do
  let s ← resolveM src
  let d ← resolveM dst
  match s, d, v with
  | .int _, .int _, _ => return v
  | .int _, .real _, .int n => return .real (Float.ofInt n)
  | .real _, .real _, _ => return v
  | .int _, .compl _, .int n => return mkCompl (Float.ofInt n) 0.0
  | .real _, .compl _, .real x => return mkCompl x 0.0
  | .compl _, .compl _, _ => return v
  | .bits _, .bits _, _ => return v
  | .bits n, .row _ _ .bool, .bits b =>
    let w := bitsWidthOf n
    return .row #[1] #[w] ((List.range w).reverse.map fun i => Value.bool ((b / 2^i) % 2 == 1)).toArray
  | _, _, .undef => rtErr "attempt to use an uninitialised value"
  | _, _, _ => rtErr s!"internal: cannot widen {modeName src} to {modeName dst}"

partial def runBlock (env : Env) (size : Nat) (arr : Array CoreStmt) (labelBase nLabels : Nat) : M Value := do
  let mut frame : Array Nat := Array.mkEmpty size
  for _ in [0:size] do
    frame := frame.push (← alloc .undef)
  let env' := frame :: env
  let rec go (start : Nat) : M Value := do
    try
      runStmts env' frame arr start
    catch ctrl =>
      match ctrl with
      | .jump id =>
        if id ≥ labelBase && id < labelBase + nLabels then
          match arr.findIdx? (fun st => match st with | .label l => l == id | _ => false) with
          | some i => go i
          | none => throw ctrl
        else throw ctrl
      | _ => throw ctrl
  go 0

partial def runStmts (env : Env) (frame : Array Nat) (stmts : Array CoreStmt) (start : Nat) : M Value := do
  let mut v : Value := .void
  for i in [start:stmts.size] do
    match stmts[i]! with
    | .decl slot init =>
      let x ← eval env init
      writeCell frame[slot]! x
    | .unit e => v ← eval env e
    | .label _ => pure ()
    | .exit => return v
  return v

partial def callValue (f : Value) (args : List Value) : M Value := do
  match f with
  | .proc cenv n fs body =>
    let mut frame : Array Nat := Array.mkEmpty fs
    let argsArr := args.toArray
    for i in [0:fs] do
      let v := if i < n then argsArr[i]! else .undef
      frame := frame.push (← alloc v)
    eval (frame :: cenv) body
  | .cproc fn _ cenv => (dispatchProc (USize.ofNat fn) cenv args.toArray : IO Value)
  | .builtin name => callBuiltin name args
  | .nil => rtErr "attempt to call NIL"
  | .undef => rtErr "attempt to call an uninitialised procedure"
  | _ => rtErr "internal: call of a non-procedure"

-- ### Operators

partial def dyadic (op : String) (m1 m2 : Mode) (a b : Value) : M Value := do
  let tb := (← read).modes
  let m1r := Mode.resolve tb m1
  let m2r := Mode.resolve tb m2
  match m1r, m2r with
  | .ref m, _ =>
    -- assigning operators: a is a REF
    let cur ← readRef a
    let mr := Mode.resolve tb m
    let res : Value ← match mr with
      | .int n => do
        let x ← expectInt cur
        let y ← expectInt b
        let r : Int ← match op with
          | "+:=" => checkIntRange (x + y) n
          | "-:=" => checkIntRange (x - y) n
          | "*:=" => checkIntRange (x * y) n
          | "%:=" => if y == 0 then rtErr "INT division by zero" else pure (Int.tdiv x y)
          | "%*:=" => if y == 0 then rtErr "INT division by zero" else pure (Int.emod x y.natAbs)
          | "/:=" => rtErr "operator /:= not defined for INT"
          | _ => rtErr s!"internal: assigning operator {op} on INT"
        pure (Value.int r)
      | .real _ => do
        let x ← expectReal cur
        let y ← expectReal b
        let r ← match op with
          | "+:=" => pure (x + y)
          | "-:=" => pure (x - y)
          | "*:=" => pure (x * y)
          | "/:=" => if y == 0.0 then rtErr "REAL division by zero" else pure (x / y)
          | _ => rtErr s!"internal: assigning operator {op} on REAL"
        Value.real <$> checkReal r
      | .compl _ => do
        match cur, b with
        | .struct #[.real ar, .real ai], .struct #[.real br, .real bi] =>
          match op with
          | "+:=" => pure (mkCompl (ar + br) (ai + bi))
          | "-:=" => pure (mkCompl (ar - br) (ai - bi))
          | "*:=" => pure (mkCompl (ar * br - ai * bi) (ar * bi + ai * br))
          | "/:=" =>
            let den := br * br + bi * bi
            pure (mkCompl ((ar * br + ai * bi) / den) ((ai * br - ar * bi) / den))
          | _ => rtErr s!"internal: assigning operator {op} on COMPL"
        | _, _ => rtErr "internal: COMPL expected"
      | .bits n => do
        let x ← expectBits cur
        let y ← expectBits b
        match op with
        | "&:=" => pure (Value.bits (x &&& y))
        | "|:=" => pure (Value.bits ((x ||| y) &&& bitsMask n))
        | _ => rtErr s!"internal: assigning operator {op} on BITS"
      | .row 1 _ _ => do
        match op with
        | "+:=" =>
          let (_, _, xs) ← expectRow cur
          let (_, _, ys) ← expectRow b
          pure (Value.row #[1] #[xs.size + ys.size] (xs ++ ys))
        | "*:=" =>
          let (_, _, xs) ← expectRow cur
          let k ← expectInt b
          let n := if k > 0 then k.toNat else 0
          pure (Value.row #[1] #[xs.size * n] ((List.replicate n xs).foldl (· ++ ·) #[]))
        | _ => rtErr s!"internal: assigning operator {op} on STRING"
      | _ => rtErr s!"internal: assigning operator {op}"
    writeRef a res
    return a
  | .row 1 _ .char, .ref _ =>
    -- "+=:"  value PLUSTO ref
    let cur ← readRef b
    let (_, _, xs) ← expectRow a
    let (_, _, ys) ← expectRow cur
    let res := Value.row #[1] #[xs.size + ys.size] (xs ++ ys)
    writeRef b res
    return b
  | .int n, .int _ =>
    let x ← expectInt a
    let y ← expectInt b
    match op with
    | "+" => Value.int <$> checkIntRange (x + y) n
    | "-" => Value.int <$> checkIntRange (x - y) n
    | "*" => Value.int <$> checkIntRange (x * y) n
    | "%" => if y == 0 then rtErr "INT division by zero" else return .int (Int.tdiv x y)
    | "%*" => if y == 0 then rtErr "INT division by zero" else return .int (Int.emod x y.natAbs)
    | "**" => Value.int <$> powIntInt x y n
    | "=" => return .bool (x == y)
    | "/=" => return .bool (x != y)
    | "<" => return .bool (x < y)
    | "<=" => return .bool (x ≤ y)
    | ">" => return .bool (x > y)
    | ">=" => return .bool (x ≥ y)
    | _ => rtErr s!"internal: INT operator {op}"
  | .real _, .real _ =>
    let x ← expectReal a
    let y ← expectReal b
    match op with
    | "+" => Value.real <$> checkReal (x + y)
    | "-" => Value.real <$> checkReal (x - y)
    | "*" => Value.real <$> checkReal (x * y)
    | "/" => if y == 0.0 then rtErr "REAL value is not a number" else Value.real <$> checkReal (x / y)
    | "I" => return mkCompl x y
    | "**" =>
      if y == 0.0 then return .real 1.0
      if x < 0.0 then rtErr "REAL math error"
      if x == 0.0 then
        if y < 0.0 then rtErr "REAL math error" else return .real 0.0
      return .real (Float.exp (y * Float.log x))   -- a68g: exp overflow is not checked here
    | "=" => return .bool (x == y)
    | "/=" => return .bool (x != y)
    | "<" => return .bool (x < y)
    | "<=" => return .bool (x ≤ y)
    | ">" => return .bool (x > y)
    | ">=" => return .bool (x ≥ y)
    | _ => rtErr s!"internal: REAL operator {op}"
  | .real n, .int _ =>
    -- REAL ** INT
    let x ← expectReal a
    let y ← expectInt b
    match op with
    | "**" => Value.real <$> powRealInt x y
    | "I" => return mkCompl x (Float.ofInt y)
    | _ => rtErr s!"internal: REAL/INT operator {op} ({n})"
  | .compl _, .int _ =>
    match a with
    | .struct #[.real re, .real im] =>
      let y ← expectInt b
      -- square-and-multiply on complex numbers
      let mul := fun (p q : Float × Float) => (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1)
      let mut p : Float × Float := (1.0, 0.0)
      let mut mm : Float × Float := (re, im)
      let nn := y.natAbs
      let mut bit : Nat := 1
      if nn > 0 then
        repeat
          if nn &&& bit != 0 then p := mul p mm
          bit := bit <<< 1
          if bit ≤ nn then mm := mul mm mm
          if !(bit ≤ nn) then break
      if y < 0 then
        let den := p.1 * p.1 + p.2 * p.2
        p := (p.1 / den, -p.2 / den)
      return mkCompl p.1 p.2
    | _ => rtErr "internal: COMPL expected"
  | .compl _, .compl _ =>
    match a, b with
    | .struct #[.real ar, .real ai], .struct #[.real br, .real bi] =>
      match op with
      | "+" => return mkCompl (ar + br) (ai + bi)
      | "-" => return mkCompl (ar - br) (ai - bi)
      | "*" => return mkCompl (ar * br - ai * bi) (ar * bi + ai * br)
      | "/" =>
        let den := br * br + bi * bi
        if den == 0.0 then rtErr "COMPL division by zero"
        return mkCompl ((ar * br + ai * bi) / den) ((ai * br - ar * bi) / den)
      | "=" => return .bool (ar == br && ai == bi)
      | "/=" => return .bool (!(ar == br && ai == bi))
      | _ => rtErr s!"internal: COMPL operator {op}"
    | _, _ => rtErr "internal: COMPL expected"
  | .bool, .bool =>
    let x ← expectBool a
    let y ← expectBool b
    match op with
    | "AND" => return .bool (x && y)
    | "OR" => return .bool (x || y)
    | "XOR" => return .bool (x != y)
    | "=" => return .bool (x == y)
    | "/=" => return .bool (x != y)
    | _ => rtErr s!"internal: BOOL operator {op}"
  | .char, .char =>
    let x ← expectChar a
    let y ← expectChar b
    match op with
    | "=" => return .bool (x == y)
    | "/=" => return .bool (x != y)
    | "<" => return .bool (x < y)
    | "<=" => return .bool (x ≤ y)
    | ">" => return .bool (x > y)
    | ">=" => return .bool (x ≥ y)
    | _ => rtErr s!"internal: CHAR operator {op}"
  | .row 1 _ .char, .row 1 _ .char =>
    let (_, _, xs) ← expectRow a
    let (_, _, ys) ← expectRow b
    match op with
    | "+" => return .row #[1] #[xs.size + ys.size] (xs ++ ys)
    | _ =>
      let sx ← strOf a
      let sy ← strOf b
      let cmp := compareStr sx sy
      match op with
      | "=" => return .bool (cmp == 0)
      | "/=" => return .bool (cmp != 0)
      | "<" => return .bool (cmp < 0)
      | "<=" => return .bool (cmp ≤ 0)
      | ">" => return .bool (cmp > 0)
      | ">=" => return .bool (cmp ≥ 0)
      | _ => rtErr s!"internal: STRING operator {op}"
  | .int _, .row 1 _ .char =>
    let k ← expectInt a
    let (_, _, ys) ← expectRow b
    let n := if k > 0 then k.toNat else 0
    return .row #[1] #[ys.size * n] ((List.replicate n ys).foldl (· ++ ·) #[])
  | .row 1 _ .char, .int _ =>
    let k ← expectInt b
    let (_, _, xs) ← expectRow a
    let n := if k > 0 then k.toNat else 0
    return .row #[1] #[xs.size * n] ((List.replicate n xs).foldl (· ++ ·) #[])
  | .bits n, .bits _ =>
    let x ← expectBits a
    let y ← expectBits b
    match op with
    | "AND" => return .bits (x &&& y)
    | "OR" => return .bits ((x ||| y) &&& bitsMask n)
    | "XOR" => return .bits ((x ^^^ y) &&& bitsMask n)
    | "=" => return .bool (x == y)
    | "/=" => return .bool (x != y)
    | "<=" => return .bool ((x &&& y) == x)
    | ">=" => return .bool ((x &&& y) == y)
    | _ => rtErr s!"internal: BITS operator {op}"
  | .bits n, .int _ =>
    let x ← expectBits a
    let k ← expectInt b
    let w := bitsWidthOf n
    let shl (v : Nat) (s : Int) : Nat :=
      if s ≥ 0 then (v <<< s.toNat) &&& bitsMask n else v >>> (-s).toNat
    match op with
    | "SHL" => if k.natAbs > w then rtErr "shift count out of range" else return .bits (shl x k)
    | "SHR" | "DOWN" => if k.natAbs > w then rtErr "shift count out of range" else return .bits (shl x (-k))
    | _ => rtErr s!"internal: BITS/INT operator {op}"
  | .int _, .bits n =>
    let k ← expectInt a
    let x ← expectBits b
    let w := bitsWidthOf n
    match op with
    | "ELEM" =>
      if k < 1 || k > w then rtErr "ELEM index out of range"
      return .bool ((x >>> (w - k.toNat)) &&& 1 == 1)
    | _ => rtErr s!"internal: INT/BITS operator {op}"
  | .int _, .row _ _ _ =>
    let k ← expectInt a
    let (l, u, _) ← expectRow b
    if k < 1 || k > l.size then rtErr "LWB/UPB dimension out of range"
    match op with
    | "LWB" => return .int l[(k-1).toNat]!
    | "UPB" => return .int u[(k-1).toNat]!
    | _ => rtErr s!"internal: INT/row operator {op}"
  | .row _ _ _, .row _ _ _ =>
    match op with
    | "=" | "/=" =>
      let eq ← valuesEqual a b
      return .bool (if op == "=" then eq else !eq)
    | _ => rtErr s!"internal: row operator {op}"
  | _, _ => rtErr s!"internal: operator {op} on {modeName m1} and {modeName m2}"

partial def compareStr (a b : String) : Int :=
  let rec go : List Char → List Char → Int
    | [], [] => 0
    | [], _ => -1
    | _, [] => 1
    | x :: xs, y :: ys => if x.toNat < y.toNat then -1 else if x.toNat > y.toNat then 1 else go xs ys
  go a.toList b.toList

partial def valuesEqual (a b : Value) : M Bool := do
  match a, b with
  | .int x, .int y => return x == y
  | .real x, .real y => return x == y
  | .int x, .real y => return Float.ofInt x == y
  | .real x, .int y => return x == Float.ofInt y
  | .bool x, .bool y => return x == y
  | .char x, .char y => return x == y
  | .bits x, .bits y => return x == y
  | .row _ _ xs, .row _ _ ys =>
    if xs.size != ys.size then return false
    for i in [0:xs.size] do
      if !(← valuesEqual xs[i]! ys[i]!) then return false
    return true
  | .struct xs, .struct ys =>
    if xs.size != ys.size then return false
    for i in [0:xs.size] do
      if !(← valuesEqual xs[i]! ys[i]!) then return false
    return true
  | .union _ x, .union _ y => valuesEqual x y
  | _, _ => return false

partial def monadic (op : String) (m : Mode) (v : Value) : M Value := do
  let mr ← resolveM m
  match op, mr with
  | "-", .int n => do let x ← expectInt v; Value.int <$> checkIntRange (-x) n
  | "+", .int _ => do let _ ← expectInt v; return v
  | "-", .real _ => do let x ← expectReal v; return .real (-x)
  | "+", .real _ => do let _ ← expectReal v; return v
  | "-", .compl _ => match v with | .struct #[.real r, .real i] => return mkCompl (-r) (-i) | _ => rtErr "internal"
  | "+", .compl _ => return v
  | "ABS", .int _ => do let x ← expectInt v; return .int x.natAbs
  | "ABS", .real _ => do let x ← expectReal v; return .real (Float.abs x)
  | "ABS", .compl _ => match v with
    | .struct #[.real r, .real i] => return .real (Float.sqrt (r * r + i * i))
    | _ => rtErr "internal"
  | "ABS", .char => do let c ← expectChar v; return .int c
  | "ABS", .bool => do let b ← expectBool v; return .int (if b then 1 else 0)
  | "ABS", .bits _ => do let b ← expectBits v; return .int b
  | "SIGN", .int _ => do let x ← expectInt v; return .int (if x > 0 then 1 else if x < 0 then -1 else 0)
  | "SIGN", .real _ => do let x ← expectReal v; return .int (if x > 0 then 1 else if x < 0 then -1 else 0)
  | "ODD", .int _ => do let x ← expectInt v; return .bool (x % 2 != 0)
  | "ENTIER", .real n => do
    let x ← expectReal v
    let lim := Float.ofInt (Numfmt.maxIntOf n)
    if x < -lim || x > lim then rtErr "INT value out of bounds"
    let f := Float.floor x
    let r : Int := if f < 0 then -((-f).toUInt64.toNat : Int) else (f.toUInt64.toNat : Int)
    return .int r
  | "ROUND", .real n => do
    let x ← expectReal v
    let lim := Float.ofInt (Numfmt.maxIntOf n)
    if x < -lim || x > lim then rtErr "INT value out of bounds"
    return .int (roundReal x)
  | "REPR", .int _ => do
    let x ← expectInt v
    if x < 0 || x > 255 then rtErr "REPR argument out of range"
    return .char x.toNat
  | "BIN", .int n => do
    let x ← expectInt v
    if x < 0 then rtErr "BIN argument is negative"
    if x.toNat > bitsMask n then rtErr "BIN argument out of range"
    return .bits x.toNat
  | "NOT", .bool => do let b ← expectBool v; return .bool (!b)
  | "NOT", .bits n => do let b ← expectBits v; return .bits (bitsMask n ^^^ b)
  | "SHORTEN", .int n => do let x ← expectInt v; Value.int <$> checkIntRange x (n - 1)
  | "SHORTEN", .real _ => do let _ ← expectReal v; return v
  | "SHORTEN", .bits n => do let b ← expectBits v; return .bits (b &&& bitsMask (n - 1))
  | "SHORTEN", .compl _ => return v
  | "RE", .compl _ => match v with | .struct #[.real r, _] => return .real r | _ => rtErr "internal"
  | "IM", .compl _ => match v with | .struct #[_, .real i] => return .real i | _ => rtErr "internal"
  | "CONJ", .compl _ => match v with | .struct #[.real r, .real i] => return mkCompl r (-i) | _ => rtErr "internal"
  | "ARG", .compl _ => match v with
    | .struct #[.real r, .real i] => return .real (Float.atan2 i r)
    | _ => rtErr "internal"
  | "LWB", .row _ _ _ => do let (l, _, _) ← expectRow v; return .int l[0]!
  | "UPB", .row _ _ _ => do let (_, u, _) ← expectRow v; return .int u[0]!
  | "ELEMS", .row _ _ _ => do let (l, u, _) ← expectRow v; return .int (rowSize l u)
  | _, _ => rtErr s!"internal: monadic operator {op} on {modeName m}"

-- ### Standard procedures

partial def getFile (fid : Nat) : M FileSt := do
  let fs ← (← read).files.get
  match fs[fid]? with
  | some f => return f
  | none => rtErr "file is not open"

partial def setFile (fid : Nat) (f : FileSt) : M Unit := do
  (← read).files.modify fun fs => fs.set! fid f

/-- Make sure the file's contents are loaded (stand in is read lazily; associated files
    take the current value of their string). -/
partial def loadFile (fid : Nat) : M FileSt := do
  let f ← getFile fid
  if fid == 1 then
    -- standard input is read a line at a time so that interactive programs work:
    -- pending output is flushed first, and more input is fetched only when needed
    if f.pos < f.buf.size || f.eof then return f
    flushOut
    let stdin ← IO.getStdin
    let line ← stdin.getLine
    if line.isEmpty then
      let f' := { f with eof := true, loaded := true, reading := true }
      setFile fid f'
      return f'
    let f' := { f with buf := f.buf ++ line.toUTF8, loaded := true, reading := true }
    setFile fid f'
    return f'
  if f.loaded then return f
  match f.assoc with
  | some r =>
    let sv ← readRef r
    let str ← strOf sv
    let f' := { f with buf := str.foldl (fun acc c => acc.push c.toNat.toUInt8) ByteArray.empty, pos := 0, loaded := true }
    setFile fid f'
    return f'
  | none =>
    let f' := { f with loaded := true }
    setFile fid f'
    return f'

partial def readChar (fid : Nat) : M (Option Nat) := do
  let f ← loadFile fid
  if f.pos < f.buf.size then
    setFile fid { f with pos := f.pos + 1, reading := true }
    return some (f.buf[f.pos]!).toNat
  else return none

partial def peekChar (fid : Nat) : M (Option Nat) := do
  let f ← loadFile fid
  if f.pos < f.buf.size then return some (f.buf[f.pos]!).toNat else return none

partial def atEnd (fid : Nat) : M Bool := do
  let f ← loadFile fid
  return f.pos ≥ f.buf.size

/-- Signal a value error: call the mender if any (TRUE = abandon the transput call), else runtime error. -/
partial def valueError (fid : Nat) (msg : String) : M Unit := do
  let f ← getFile fid
  match f.onValue with
  | some h =>
    let r ← callValue h [.file fid]
    match r with
    | .bool true => throw (.fileEnd fid)
    | _ => rtErr msg
  | none => rtErr msg

/-- Skip one character; at the end of a line this is a line-end event: the mender (if any)
    is called and, when it returns TRUE (or when there is none), reading continues on the
    next line. -/
partial def skipChar (fid : Nat) : M Unit := do
  match (← peekChar fid) with
  | some 10 =>
    let f ← getFile fid
    match f.onLine with
    | some h =>
      let r ← callValue h [.file fid]
      match r with
      | .bool true => let _ ← readChar fid
      | _ => rtErr "end of line reached while reading"
    | none => let _ ← readChar fid
  | some _ => let _ ← readChar fid
  | none => pure ()   -- a68g: skipping a character at end of file is not an event

/-- Reload an associated file from its string if the string changed. -/
partial def refreshAssoc (fid : Nat) : M Unit := do
  let f ← getFile fid
  match f.assoc with
  | some r =>
    let str ← strOf (← readRef r)
    let bytes := str.foldl (fun acc c => acc.push c.toNat.toUInt8) ByteArray.empty
    if bytes != f.buf then setFile fid { f with buf := bytes, pos := 0, loaded := true }
  | none => pure ()

/-- Signal logical file end: call the mender if any (TRUE = continue), else runtime error. -/
partial def logicalEnd (fid : Nat) : M Unit := do
  let f ← getFile fid
  match f.onEnd with
  | some h =>
    let r ← callValue h [.file fid]
    match r with
    | .bool true => throw (.fileEnd fid)
    | _ => rtErr "logical file end"
  | none => rtErr "attempt to read past logical end of file"

partial def skipSpaces (fid : Nat) : M Unit := do
  repeat
    match (← peekChar fid) with
    | some c => if c == 32 || c == 9 || c == 10 || c == 13 then let _ ← readChar fid else break
    | none => break

partial def readToken (fid : Nat) : M String := do
  skipSpaces fid
  if (← atEnd fid) then logicalEnd fid
  let mut s := ""
  repeat
    match (← peekChar fid) with
    | some c =>
      if c == 32 || c == 9 || c == 10 || c == 13 then break
      let _ ← readChar fid
      s := s.push (Char.ofNat c)
    | none => break
  return s

/-- Read a numeral: optional sign, digits, and for reals an optional fraction and exponent. -/
partial def readNumber (fid : Nat) (real : Bool) : M String := do
  skipSpaces fid
  if (← atEnd fid) then logicalEnd fid
  let isDigit (c : Nat) := c ≥ 48 && c ≤ 57
  let peekIs (p : Nat → Bool) : M Bool := do
    match (← peekChar fid) with
    | some c => pure (p c)
    | none => pure false
  let mut s := ""
  if (← peekIs fun c => c == 43 || c == 45) then
    s := s.push (Char.ofNat (← readChar fid).get!)
  while (← peekIs isDigit) do
    s := s.push (Char.ofNat (← readChar fid).get!)
  if real then
    if (← peekIs (· == 46)) then
      s := s.push (Char.ofNat (← readChar fid).get!)
      while (← peekIs isDigit) do
        s := s.push (Char.ofNat (← readChar fid).get!)
    if (← peekIs fun c => c == 101 || c == 69) then
      s := s.push (Char.ofNat (← readChar fid).get!)
      if (← peekIs fun c => c == 43 || c == 45) then
        s := s.push (Char.ofNat (← readChar fid).get!)
      while (← peekIs isDigit) do
        s := s.push (Char.ofNat (← readChar fid).get!)
  if s.isEmpty || s == "+" || s == "-" then valueError fid "invalid numeral in input"
  return s

/-- Read a string: up to (not including) the end of line or a terminator character. -/
partial def readLineStr (fid : Nat) : M String := do
  if (← atEnd fid) then logicalEnd fid
  let f ← getFile fid
  let mut s := ""
  repeat
    match (← peekChar fid) with
    | some c =>
      if c == 10 || f.term.contains c then break
      let _ ← readChar fid
      s := s.push (Char.ofNat c)
    | none => break
  return s

/-- Skip to the beginning of the next line. -/
partial def skipLine (fid : Nat) : M Unit := do
  repeat
    match (← readChar fid) with
    | some c => if c == 10 then break
    | none => break

partial def readInto (fid : Nat) (m : Mode) (r : Value) : M Unit := do
  match (← resolveM m) with
  | .ref t =>
    match (← resolveM t) with
    | .int _ =>
      let tok ← readNumber fid false
      let tok := if tok.startsWith "+" then String.ofList (tok.toList.drop 1) else tok
      match tok.toInt? with
      | some n => writeRef r (.int n)
      | none => rtErr s!"cannot read INT from \"{tok}\""
    | .struct fs =>
      for (i, (_, fm)) in (List.range fs.length).zip fs do
        match r with
        | .ref c path => readInto fid (.ref fm) (.ref c (path ++ [.field i]))
        | _ => rtErr "internal: struct read"
    | .real _ =>
      let tok ← readNumber fid true
      let neg := tok.startsWith "-"
      let body := if neg || tok.startsWith "+" then String.ofList (tok.toList.drop 1) else tok
      let x := Numfmt.parseFloat body
      writeRef r (.real (if neg then -x else x))
    | .bool =>
      let tok ← readToken fid
      writeRef r (.bool (tok == "T" || tok == "TRUE"))
    | .char =>
      match (← readChar fid) with
      | some c => writeRef r (.char c)
      | none => logicalEnd fid
    | .row 1 true .char =>
      let line ← readLineStr fid
      writeRef r (Value.ofString line)
    | .row 1 _ em =>
      let (_, _, es) ← expectRow (← readRef r)
      for i in [0:es.size] do
        readInto fid (.ref em) (← refElem r i)
    | _ => rtErr s!"cannot read a value of mode {modeName t}"
  | .proc [.ref .file] .void =>
    match r with
    | .builtin "newline" => skipLine fid
    | .builtin "newpage" => skipLine fid
    | .builtin "space" => skipChar fid
    | _ => pure ()
  | _ => rtErr s!"cannot read into a value of mode {modeName m}"

/-- Read one value with the next input pattern (formatted transput, `getf`/`readf`). -/
partial def readFormatted (fid : Nat) (st : FmtState) (m : Mode) (r : Value) : M FmtState := do
  let tm ← match (← resolveM m) with
    | .ref t => resolveM t
    | .proc [.ref .file] .void => pure .void
    | t => pure t
  match tm with
  | .void => readInto fid m r; return st
  | .struct fs =>
    let mut st := st
    for (i, (_, fm)) in (List.range fs.length).zip fs do
      match r with
      | .ref c path => st ← readFormatted fid st (.ref fm) (.ref c (path ++ [.field i]))
      | _ => rtErr "internal: struct read"
    return st
  | .row 1 _ .char => readScalarFormatted fid st m r
  | .row 1 _ em =>
    let mut st := st
    let (_, _, es) ← expectRow (← readRef r)
    for i in [0:es.size] do
      st ← readFormatted fid st (.ref em) (← refElem r i)
    return st
  | _ => readScalarFormatted fid st m r

partial def readInsertion (fid : Nat) (s : String) : M Unit := do
  -- insertions are skipped on input, character by character
  for c in s.toList do
    if c == '\n' then skipLine fid
    else skipChar fid

partial def readScalarFormatted (fid : Nat) (st : FmtState) (m : Mode) (r : Value) : M FmtState := do
  -- pull the next pattern, consuming insertions from the input
  let mut st := st
  let mut pat? : Option Pic := none
  repeat
    match st.frames with
    | [] => break
    | fr :: rest =>
      if fr.cursor < fr.pics.size then
        match fr.pics[fr.cursor]! with
        | .ins s => readInsertion fid s; st := { frames := { fr with cursor := fr.cursor + 1 } :: rest }
        | .col _ => st := { frames := { fr with cursor := fr.cursor + 1 } :: rest }
        | .include items env =>
          let pics ← expandFormat env items
          st := { frames := { pics := pics.toArray, cursor := 0, embedded := true } :: { fr with cursor := fr.cursor + 1 } :: rest }
        | pic => pat? := some pic; st := { frames := { fr with cursor := fr.cursor + 1 } :: rest }; break
      else if fr.embedded then st := { frames := rest }
      else st := { frames := [{ fr with cursor := 0 }] }
  let some pat := pat? | rtErr "format exhausted"
  let tm ← match (← resolveM m) with
    | .ref t => resolveM t
    | t => pure t
  match pat with
  | .general _ => readInto fid m r
  | .pattern frames =>
    if frames.any (· == .a) then
      -- string pattern: read exactly as many characters as there are `a` frames
      let mut s := ""
      for f in frames do
        match f with
        | .a =>
          match (← readChar fid) with
          | some c => s := s.push (Char.ofNat c)
          | none => logicalEnd fid
        | .ins t => readInsertion fid t
        | _ => pure ()
      match tm with
      | .char => writeRef r (.char (s.toList.headD ' ').toNat)
      | _ => writeRef r (Value.ofString s)
    else
      -- numeric pattern: read the characters covered by the frames and convert
      let mut s := ""
      for f in frames do
        match f with
        | .ins t => readInsertion fid t
        | .z | .d | .plus | .minus | .point | .e =>
          match (← readChar fid) with
          | some c => s := s.push (Char.ofNat c)
          | none => logicalEnd fid
        | _ => pure ()
      let t := String.ofList (s.toList.filter (· != ' '))
      match tm with
      | .int _ =>
        match t.toInt? with
        | some n => writeRef r (.int n)
        | none => rtErr s!"cannot read INT from \"{t}\""
      | .real _ =>
        let neg := t.startsWith "-"
        let body := if neg || t.startsWith "+" then String.ofList (t.toList.drop 1) else t
        let x := Numfmt.parseFloat body
        writeRef r (.real (if neg then -x else x))
      | _ => rtErr "numeric pattern on non-numeric value"
  | .bool_ f g =>
    let tok ← readToken fid
    match f, g with
    | some t, some e => writeRef r (.bool (if tok == t then true else if tok == e then false else tok == "T"))
    | _, _ => writeRef r (.bool (tok == "T"))
  | .choice alts =>
    -- match the longest alternative at the current position
    let fs ← loadFile fid
    let rest := String.ofList ((fs.buf.toList.drop fs.pos).map fun b => Char.ofNat b.toNat)
    let mut best : Option (Nat × Nat) := none   -- (index, length)
    for (i, a) in (List.range alts.length).zip alts do
      if rest.startsWith a then
        match best with
        | some (_, l) => if a.length > l then best := some (i, a.length)
        | none => best := some (i, a.length)
    match best with
    | some (i, l) =>
      setFile fid { fs with pos := fs.pos + l }
      writeRef r (.int (i + 1))
    | none => valueError fid "no alternative of the choice pattern matches the input"
  | .ins _ | .col _ | .include _ _ => rtErr "internal: pattern expected"
  return st

/-- Consume the insertions that follow the last pattern used (a68g's purge on input). -/
partial def purgeRead (fid : Nat) (st : FmtState) : M Unit := do
  let mut st := st
  repeat
    match st.frames with
    | [] => break
    | fr :: rest =>
      if fr.cursor < fr.pics.size then
        match fr.pics[fr.cursor]! with
        | .ins s => readInsertion fid s; st := { frames := { fr with cursor := fr.cursor + 1 } :: rest }
        | .col _ => st := { frames := { fr with cursor := fr.cursor + 1 } :: rest }
        | _ => break
      else if fr.embedded then st := { frames := rest }
      else break

partial def getfItems (fid : Nat) (es : Array Value) : M Unit := do
  refreshAssoc fid
  let mut st : Option FmtState := none
  try
    for e in es do
      match e with
      | .union .format (.fmt env fitems) =>
        match st with
        | some s => purgeRead fid s
        | none => pure ()
        let pics ← expandFormat env fitems
        st := some { frames := [{ pics := pics.toArray, cursor := 0, embedded := false }] }
      | .union m v =>
        match st with
        | some s => st := some (← readFormatted fid s m v)
        | none => readInto fid m v
      | _ => rtErr "internal: read argument"
    match st with
    | some s => purgeRead fid s
    | none => pure ()
  catch c =>
    match c with
    | .fileEnd _ => pure ()
    | _ => throw c

/-- `get`: read a list of items; a mended logical-file-end abandons the rest of the call. -/
partial def getItems (fid : Nat) (es : Array Value) : M Unit := do
  refreshAssoc fid
  try
    for e in es do
      match e with
      | .union m v => readInto fid m v
      | _ => rtErr "internal: read argument"
  catch c =>
    match c with
    | .fileEnd _ => pure ()
    | _ => throw c

/-- Allocate a file slot and store it in the REF FILE `fv`. -/
partial def newFile (fv : Value) (f : FileSt) : M Nat := do
  match fv with
  | .file id =>
    -- re-opening a standard file (`open (stand in, name, stand in channel)`)
    setFile id f
    return id
  | _ =>
    let fid ← (← read).files.modifyGet fun fs => (fs.size, fs.push f)
    writeRef fv (.file fid)
    return fid

partial def flushFile (fid : Nat) : M Unit := do
  let f ← getFile fid
  if f.onDisk && f.dirty && f.writing then
    IO.FS.writeBinFile f.name f.buf
    setFile fid { f with dirty := false }
  match f.assoc with
  | some r => if f.writing then
      let s := String.ofList (f.buf.toList.map fun b => Char.ofNat b.toNat)
      writeRef r (Value.ofString s)
  | none => pure ()

partial def mathFn (name : String) (x : Float) : M Float := do
  let r ← match name with
    | "sqrt" | "longsqrt" | "longlongsqrt" => if x < 0 then rtErr "REAL value is not a number" else pure (Float.sqrt x)
    | "exp" | "longexp" | "longlongexp" => return Float.exp x   -- a68g: overflow yields infinity silently
    | "ln" | "longln" | "longlongln" => if x < 0 then rtErr "REAL value is not a number" else pure (Float.log x)
    | "log" | "longlog" | "log10" => if x < 0 then rtErr "REAL value is not a number" else pure (Float.log10 x)
    | "log2" => pure (Float.log2 x)
    | "exp2" => return Float.exp2 x
    | "sin" | "longsin" | "longlongsin" => pure (Float.sin x)
    | "cos" | "longcos" | "longlongcos" => pure (Float.cos x)
    | "tan" | "longtan" | "longlongtan" => pure (Float.tan x)
    | "arcsin" | "asin" | "longarcsin" | "longlongarcsin" => if x < -1 || x > 1 then rtErr "REAL value is not a number" else pure (Float.asin x)
    | "arccos" | "acos" | "longarccos" | "longlongarccos" => if x < -1 || x > 1 then rtErr "REAL value is not a number" else pure (Float.acos x)
    | "arctan" | "atan" | "longarctan" | "longlongarctan" => pure (Float.atan x)
    | "sinh" => pure (Float.sinh x) | "cosh" => pure (Float.cosh x) | "tanh" => pure (Float.tanh x)
    | "arcsinh" => pure (Float.asinh x) | "arccosh" => pure (Float.acosh x) | "arctanh" => pure (Float.atanh x)
    | "cbrt" | "curt" => pure (Float.cbrt x)
    | _ => rtErr s!"unknown math function {name}"
  checkReal r

partial def tausGet (s : Taus) : UInt32 × Taus :=
  let b1 := (((s.z1 <<< 6) ^^^ s.z1) >>> 13)
  let z1 := (((s.z1 &&& 4294967294) <<< 18) ^^^ b1)
  let b2 := (((s.z2 <<< 2) ^^^ s.z2) >>> 27)
  let z2 := (((s.z2 &&& 4294967288) <<< 2) ^^^ b2)
  let b3 := (((s.z3 <<< 13) ^^^ s.z3) >>> 21)
  let z3 := (((s.z3 &&& 4294967280) <<< 7) ^^^ b3)
  let b4 := (((s.z4 <<< 3) ^^^ s.z4) >>> 12)
  let z4 := (((s.z4 &&& 4294967168) <<< 13) ^^^ b4)
  (z1 ^^^ z2 ^^^ z3 ^^^ z4, { z1 := z1, z2 := z2, z3 := z3, z4 := z4 })

partial def tausSet (seed : UInt32) : Taus := Id.run do
  let lcg (n : UInt32) : UInt32 := 69069 * n
  let s := if seed == 0 then 1 else seed
  let mut z1 := lcg s
  if z1 < 2 then z1 := z1 + 2
  let mut z2 := lcg z1
  if z2 < 8 then z2 := z2 + 8
  let mut z3 := lcg z2
  if z3 < 16 then z3 := z3 + 16
  let mut z4 := lcg z3
  if z4 < 128 then z4 := z4 + 128
  let mut st : Taus := { z1 := z1, z2 := z2, z3 := z3, z4 := z4 }
  for _ in [0:10] do
    st := (tausGet st).2
  return st

partial def nextRandom : M Float := do
  let r := (← read).rng
  let s ← r.get
  let (v, s') := tausGet s
  r.set s'
  return (Float.ofNat v.toNat) / 4294967296.0

partial def callBuiltin (name : String) (args : List Value) : M Value := do
  match name, args with
  | "print", [row] | "write", [row] =>
    let (_, _, es) ← expectRow row
    for e in es do
      match e with
      | .union m v => printValue 0 m v
      | _ => rtErr "internal: print argument"
    return .void
  | "put", [f, row] =>
    let fid ← fileIdOf f
    let (_, _, es) ← expectRow row
    for e in es do
      match e with
      | .union m v => printValue fid m v
      | _ => rtErr "internal: put argument"
    return .void
  | "printf", [row] | "writef", [row] =>
    let (_, _, es) ← expectRow row
    printf 0 es.toList
    return .void
  | "putf", [f, row] =>
    let fid ← fileIdOf f
    let (_, _, es) ← expectRow row
    printf fid es.toList
    return .void
  | "read", [row] =>
    let (_, _, es) ← expectRow row
    getItems 1 es
    return .void
  | "readf", [row] =>
    let (_, _, es) ← expectRow row
    getfItems 1 es
    return .void
  | "get", [f, row] =>
    let fid ← fileIdOf f
    let (_, _, es) ← expectRow row
    getItems fid es
    return .void
  | "getf", [f, row] =>
    let fid ← fileIdOf f
    let (_, _, es) ← expectRow row
    getfItems fid es
    return .void
  | "newline", [f] | "newpage", [f] | "space", [f] | "backspace", [f] =>
    let fid ← fileIdOf f
    let fs ← getFile fid
    if fid == 1 || (fs.reading && !fs.writing) then
      match name with
      | "newline" | "newpage" => skipLine fid
      | _ => let _ ← readChar fid
    else
      fileOut fid (match name with | "newline" => "\n" | "newpage" => "\x0c" | "space" => " " | _ => "\x08")
    return .void
  | "open", [fv, nm, _] =>
    let path ← strOf nm
    let ex ← System.FilePath.pathExists path
    if ex then
      let bytes ← IO.FS.readBinFile path
      let _ ← newFile fv { name := path, buf := bytes, loaded := true, onDisk := true }
      return .int 0
    else
      return .int 1
  | "establish", [fv, nm, _, _, _, _] =>
    let path ← strOf nm
    let _ ← newFile fv { name := path, loaded := true, onDisk := true, writing := true }
    return .int 0
  | "create", [fv, _] =>
    let _ ← newFile fv { name := "", loaded := true }
    return .int 0
  | "associate", [fv, sv] =>
    let _ ← newFile fv { assoc := some sv }
    return .void
  | "close", [f] | "lock", [f] | "scratch", [f] =>
    let fid ← fileIdOf f
    flushFile fid
    return .void
  | "reset", [f] =>
    let fid ← fileIdOf f
    flushFile fid
    let fs ← getFile fid
    setFile fid { fs with pos := 0, reading := false, writing := false, loaded := fs.assoc.isNone && fid != 1 }
    return .void
  | "maketerm", [f, t] =>
    let fid ← fileIdOf f
    let ts ← strOf t
    let fs ← getFile fid
    setFile fid { fs with term := ts.toList.map (·.toNat) }
    return .void
  | "onlogicalfileend", [f, h] | "onfileend", [f, h] | "onphysicalfileend", [f, h] =>
    let fid ← fileIdOf f
    let fs ← getFile fid
    setFile fid { fs with onEnd := some h }
    return .void
  | "onvalueerror", [f, h] =>
    let fid ← fileIdOf f
    let fs ← getFile fid
    setFile fid { fs with onValue := some h }
    return .void
  | "onlineend", [f, h] =>
    let fid ← fileIdOf f
    let fs ← getFile fid
    setFile fid { fs with onLine := some h }
    return .void
  | "whole", [x, w] =>
    let width ← expectInt w
    let x ← resolveUnion x
    match x with
    | .union (.int n) (.int i) => return Value.ofString (Numfmt.whole i width) |> fun s => (let _ := n; s)
    | .union (.real _) (.real r) => do let _ ← checkReal r; return Value.ofString (Numfmt.wholeReal r width)
    | .union _ .undef => rtErr "attempt to use an uninitialised value"
    | _ => rtErr "internal: whole argument"
  | "fixed", [x, w, a] =>
    let width ← expectInt w
    let after ← expectInt a
    let x ← resolveUnion x
    match x with
    | .union (.int n) (.int i) =>
      return Value.ofString (if n ≤ 0 then Numfmt.fixedInt i width after else Numfmt.fixedLongInt i width after)
    | .union (.real _) (.real r) => do let _ ← checkReal r; return Value.ofString (Numfmt.fixedReal r width after)
    | .union _ .undef => rtErr "attempt to use an uninitialised value"
    | _ => rtErr "internal: fixed argument"
  | "float", [x, w, a, e] =>
    let width ← expectInt w
    let after ← expectInt a
    let expo ← expectInt e
    let x ← resolveUnion x
    match x with
    | .union (.int _) (.int i) => return Value.ofString (Numfmt.floatInt i width after expo)
    | .union (.real _) (.real r) => do let _ ← checkReal r; return Value.ofString (Numfmt.floatReal r width after expo)
    | .union _ .undef => rtErr "attempt to use an uninitialised value"
    | _ => rtErr "internal: float argument"
  | "real", [x, w, a, e, f] =>
    let width ← expectInt w
    let after ← expectInt a
    let expo ← expectInt e
    let frmt ← expectInt f
    let x ← resolveUnion x
    match x with
    | .union (.int _) (.int i) => return Value.ofString (Numfmt.floatInt i width after expo frmt)
    | .union (.real _) (.real r) => do let _ ← checkReal r; return Value.ofString (Numfmt.floatReal r width after expo frmt)
    | _ => rtErr "internal: real argument"
  | "charinstring", [c, i, s] =>
    let ch ← expectChar c
    let (l, _, es) ← expectRow s
    let mut k := 0
    for e in es do
      if (← expectChar e) == ch then
        match i with
        | .nil => pure ()
        | _ => writeRef i (.int (l[0]! + k))
        return .bool true
      k := k + 1
    return .bool false
  | "lastcharinstring", [c, i, s] =>
    let ch ← expectChar c
    let (l, _, es) ← expectRow s
    let mut found : Option Nat := none
    let mut k := 0
    for e in es do
      if (← expectChar e) == ch then found := some k
      k := k + 1
    match found with
    | some kk => (match i with | .nil => pure () | _ => writeRef i (.int (l[0]! + kk))); return .bool true
    | none => return .bool false
  | "stringinstring", [pat, i, s] =>
    let p ← strOf pat
    let (l, _, _) ← expectRow s
    let t ← strOf s
    let pl := p.toList
    let tl := t.toList
    let n := tl.length
    let m := pl.length
    for k in [0:n+1] do
      if k + m ≤ n && (tl.drop k).take m == pl then
        match i with
        | .nil => pure ()
        | _ => writeRef i (.int (l[0]! + k))
        return .bool true
    return .bool false
  | "toupper", [c] => do let ch ← expectChar c; return .char (if ch ≥ 97 && ch ≤ 122 then ch - 32 else ch)
  | "tolower", [c] => do let ch ← expectChar c; return .char (if ch ≥ 65 && ch ≤ 90 then ch + 32 else ch)
  | "isupper", [c] => do let ch ← expectChar c; return .bool (ch ≥ 65 && ch ≤ 90)
  | "islower", [c] => do let ch ← expectChar c; return .bool (ch ≥ 97 && ch ≤ 122)
  | "isdigit", [c] => do let ch ← expectChar c; return .bool (ch ≥ 48 && ch ≤ 57)
  | "isalpha", [c] => do let ch ← expectChar c; return .bool ((ch ≥ 65 && ch ≤ 90) || (ch ≥ 97 && ch ≤ 122))
  | "isalnum", [c] => do let ch ← expectChar c; return .bool ((ch ≥ 65 && ch ≤ 90) || (ch ≥ 97 && ch ≤ 122) || (ch ≥ 48 && ch ≤ 57))
  | "isspace", [c] => do let ch ← expectChar c; return .bool (ch == 32 || (ch ≥ 9 && ch ≤ 13))
  | "ispunct", [c] => do let ch ← expectChar c; return .bool (ch > 32 && ch < 127 && !((ch ≥ 65 && ch ≤ 90) || (ch ≥ 97 && ch ≤ 122) || (ch ≥ 48 && ch ≤ 57)))
  | "isprint", [c] => do let ch ← expectChar c; return .bool (ch ≥ 32 && ch < 127)
  | "isgraph", [c] => do let ch ← expectChar c; return .bool (ch > 32 && ch < 127)
  | "iscntrl", [c] => do let ch ← expectChar c; return .bool (ch < 32 || ch == 127)
  | "isxdigit", [c] => do let ch ← expectChar c; return .bool ((ch ≥ 48 && ch ≤ 57) || (ch ≥ 65 && ch ≤ 70) || (ch ≥ 97 && ch ≤ 102))
  | "odd", [x] => do let n ← expectInt x; return .bool (n % 2 != 0)
  | "abs", [x] => do let n ← expectInt x; return .int n.natAbs
  | "stop", [] => throw .stop
  | "random", [] | "longrandom", [] | "nextrandom", [] => Value.real <$> nextRandom
  | "firstrandom", [n] => do
    let k ← expectInt n
    (← read).rng.set (tausSet (UInt32.ofNat (k.toNat % 4294967296)))
    return .void
  | "randomint", [n] => do
    let k ← expectInt n
    let r ← nextRandom
    return .int (1 + Int.ofNat ((r * Float.ofInt k).toUInt64.toNat))
  | "clock", [] | "seconds", [] | "cputime", [] => do
    let t ← IO.monoMsNow
    return .real (Float.ofNat t / 1000.0)
  | "complexsqrt", [z] | "csqrt", [z] | "complexexp", [z] | "cexp", [z] | "complexln", [z] | "cln", [z]
  | "complexsin", [z] | "csin", [z] | "complexcos", [z] | "ccos", [z] | "complexarctan", [z] =>
    match z with
    | .struct #[.real re, .real im] =>
      match name with
      | "complexsqrt" | "csqrt" =>
        let r := Float.sqrt (re * re + im * im)
        let a := Float.sqrt ((r + re) / 2)
        let b := Float.sqrt ((r - re) / 2)
        return mkCompl a (if im < 0 then -b else b)
      | "complexexp" | "cexp" =>
        let e := Float.exp re
        return mkCompl (e * Float.cos im) (e * Float.sin im)
      | "complexln" | "cln" => return mkCompl (Float.log (Float.sqrt (re * re + im * im))) (Float.atan2 im re)
      | "complexsin" | "csin" => return mkCompl (Float.sin re * Float.cosh im) (Float.cos re * Float.sinh im)
      | "complexcos" | "ccos" => return mkCompl (Float.cos re * Float.cosh im) (-(Float.sin re * Float.sinh im))
      | _ => rtErr s!"unsupported complex function {name}"
    | _ => rtErr "COMPL expected"
  | "arctan2", [y, x] | "atan2", [y, x] | "longarctan2", [y, x] => do
    let a ← expectReal y
    let b ← expectReal x
    Value.real <$> checkReal (Float.atan2 a b)
  | "readint", [] => do let t ← readToken 1; match t.toInt? with | some n => return .int n | none => rtErr "cannot read INT"
  | "readreal", [] => do
    let t ← readToken 1
    let neg := t.startsWith "-"
    let x := Numfmt.parseFloat (if neg then String.ofList (t.toList.drop 1) else t)
    return .real (if neg then -x else x)
  | "readstring", [] => do let s ← readLineStr 1; skipLine 1; return Value.ofString s
  | "readchar", [] => do match (← readChar 1) with | some c => return .char c | none => rtErr "end of file"
  | "readbool", [] => do let t ← readToken 1; return .bool (t == "T" || t == "TRUE")
  | "printint", [x] => do let n ← expectInt x; emit (Numfmt.printInt n 0); return .void
  | "printreal", [x] => do let r ← expectReal x; emit (Numfmt.printReal r 0); return .void
  | "printstring", [x] => do emit (← strOf x); return .void
  | "printchar", [x] => do emitByte (← expectChar x).toUInt8; return .void
  | "printbool", [x] => do emit (if (← expectBool x) then "T" else "F"); return .void
  | "setexitcode", [_] | "setexit", [_] => return .void
  | "argc", [] => return .int (← read).args.size
  | "argv", [i] => do
    let k ← expectInt i
    let a := (← read).args
    if k < 1 || k > a.size then return Value.ofString ""
    return Value.ofString a[(k - 1).toNat]!
  | "onpageend", [_, _]
  | "onformatend", [_, _] | "onformaterror", [_, _] | "ontransputerror", [_, _] =>
    return .void
  | "makeconv", [_] => return .void
  | "bitspack", [row] => do
    let (_, _, es) ← expectRow row
    let mut v := 0
    for e in es do
      v := v * 2 + (if (← expectBool e) then 1 else 0)
    return .bits v
  | "system", [_] => rtErr "system is not supported"
  | fn, [x] =>
    if ["sqrt","exp","ln","log","log10","log2","exp2","sin","cos","tan","arcsin","arccos","arctan",
        "asin","acos","atan","sinh","cosh","tanh","arcsinh","arccosh","arctanh","cbrt","curt",
        "longsqrt","longexp","longln","longlog","longsin","longcos","longtan","longarcsin","longarccos",
        "longarctan","longlongsqrt","longlongexp","longlongln","longlongsin","longlongcos","longlongtan",
        "longlongarctan","longlongarcsin","longlongarccos"].contains fn then
      Value.real <$> mathFn fn (← expectReal x)
    else rtErr s!"unsupported standard procedure {fn}/1"
  | _, _ => rtErr s!"unsupported standard procedure {name}/{args.length}"

-- ### Formatted output

/-- Evaluate an expression embedded in a format text.  In a compiled program these are
    `hole` nodes that call straight into the compiled code, so no syntax is walked. -/
partial def evalFmtExpr (env : Env) (e : Core) : M Value := do
  match e with
  | .hole fn idx => (dispatchHole (USize.ofNat fn) (USize.ofNat idx) env : IO Value)
  | _ => eval env e

/-- Expand the format items of a format value into a flat picture list. -/
partial def expandFormat (env : Env) (items : List CoreFmt) : M (List Pic) := do
  let b ← walkFormat env items {}
  return b.flush

partial def walkFormat (env : Env) (items : List CoreFmt) (b0 : FmtBuild) : M FmtBuild := do
  let mut b := b0
  for it in items do
    match it with
    | .literal s => b := b.addIns s
    | .newline => b := { pics := b.flush ++ [.ins "\n"] }
    | .newpage => b := { pics := b.flush ++ [.ins "\x0c"] }
    | .space | .backspace => b := b.addIns " "
    | .digit z => b := b.addFrame (if z then .z else .d)
    | .sign p => b := b.addFrame (if p then .plus else .minus)
    | .point => b := b.addFrame .point
    | .exp => b := b.addFrame .e
    | .char_ => b := b.addFrame .a
    | .rep n dyn .col =>
      let k ← match dyn with
        | some e => do pure (← expectInt (← eval env e)).toNat
        | none => pure n
      b := { pics := b.flush ++ [.col k] }
    | .col => b := { pics := b.flush ++ [.col 1] }
    | .rep n dyn inner =>
      let k ← match dyn with
        | some e => do pure (← expectInt (← evalFmtExpr env e)).toNat
        | none => pure n
      b ← walkFormat env (List.replicate k inner) b
    | .group inner =>
      -- a collection is a picture boundary: frames inside it never merge with frames outside
      b := { pics := b.flush }
      b ← walkFormat env inner b
      b := { pics := b.flush }
    | .general args =>
      let vs ← args.mapM fun a => do expectInt (← evalFmtExpr env a)
      b := b.addPic (.general vs)
    | .bool_ f g => b := b.addPic (.bool_ f g)
    | .choice alts => b := b.addPic (.choice alts)
    | .strings => b := { pics := b.flush }
    | .sep => b := { pics := b.flush }
    | .include f =>
      match (← evalFmtExpr env f) with
      | .fmt fenv fitems => b := b.addPic (.include fitems fenv)
      | _ => rtErr "format expected in f(...)"
  return b

/-- Get the next pattern, writing insertions passed on the way. Embedded formats (`f(...)`) are
    entered as new frames and popped when exhausted; the outermost format restarts at its end
    when a pattern is wanted (a68g's default "on format end" action). -/
partial def nextPattern (fid : Nat) (st : FmtState) (want : Bool) (restarts : Nat := 0) : M (Option Pic × FmtState) := do
  match st.frames with
  | [] => return (none, st)
  | fr :: rest =>
    let mut i := fr.cursor
    while i < fr.pics.size do
      match fr.pics[i]! with
      | .ins s => fileOut fid s; i := i + 1
      | .col k =>
        let pos ← (← read).col.get
        if k > pos + 1 then fileOut fid (String.ofList (List.replicate (k - pos - 1) ' '))
        i := i + 1
      | .include items env =>
        let pics ← expandFormat env items
        let st' : FmtState := { frames := { pics := pics.toArray, cursor := 0, embedded := true } :: { fr with cursor := i + 1 } :: rest }
        return ← nextPattern fid st' want restarts
      | pic => return (some pic, { frames := { fr with cursor := i + 1 } :: rest })
    if fr.embedded then
      return ← nextPattern fid { frames := rest } want restarts
    if want then
      if restarts > 0 || fr.pics.isEmpty then rtErr "format exhausted"
      nextPattern fid { frames := [{ fr with cursor := 0 }] } want (restarts + 1)
    else
      return (none, { frames := [{ fr with cursor := i }] })

/-- Write an integral value with a mould. -/
partial def writeIntegralPattern (fid : Nat) (frames : List Frame) (n : Int) : M Unit := do
  let hasSign := frames.any fun f => f == .plus || f == .minus
  let width := frames.foldl (fun acc f => if f == .z || f == .d then acc + 1 else acc) 0
  let digits := toString n.natAbs
  if digits.length > width then rtErr "error transputting INT value"
  if n < 0 && !hasSign then rtErr "error transputting INT value: negative value without sign frame"
  -- edit buffer: sign, zeros, digits
  let signChar : Option Char := if hasSign then
      some (if frames.any (· == .plus) then (if n ≥ 0 then '+' else '-') else (if n ≥ 0 then ' ' else '-'))
    else none
  let mut buf : List Char := (match signChar with | some c => [c] | none => [])
    ++ List.replicate (width - digits.length) '0' ++ digits.toList
  -- shift sign through the sign mould only (the z frames before the sign frame)
  if hasSign then
    let signMould := frames.takeWhile fun f => !(f == .plus || f == .minus)
    buf := shiftSign signMould buf
  writeMould fid frames buf false

/-- Write digits through a mould (the a68g `write_mould`). `normalMood` starts without zero suppression. -/
partial def writeMould (fid : Nat) (frames : List Frame) (buf : List Char) (normalMood : Bool) : M Unit := do
  let mut q := buf
  let mut digitBlank := !normalMood
  let mut insBlank := false
  let putSign : List Char → M (List Char) := fun q => do
    match q with
    | c :: rest => if c == '+' || c == '-' || c == ' ' then do fileOutByte fid c.toNat.toUInt8; pure rest else pure q
    | [] => pure q
  for f in frames do
    match f with
    | .ins s =>
      if insBlank then fileOut fid (String.ofList (List.replicate s.length ' ')) else fileOut fid s
    | .z =>
      q ← putSign q
      match q with
      | '0' :: rest =>
        if digitBlank then
          fileOut fid " "; insBlank := true; q := rest
        else
          fileOut fid "0"; q := rest
      | c :: rest => fileOut fid (String.singleton c); q := rest; digitBlank := false; insBlank := false
      | [] => pure ()
    | .d =>
      q ← putSign q
      match q with
      | c :: rest => fileOut fid (String.singleton c); q := rest
      | [] => pure ()
      digitBlank := false; insBlank := false
    | .plus | .minus => pure ()
    | _ => pure ()

partial def countZD (fs : List Frame) : Nat := fs.foldl (fun acc f => if f == .z || f == .d then acc + 1 else acc) 0

/-- Write a real (or integral) value with a real pattern. -/
partial def writeRealPattern (fid : Nat) (frames : List Frame) (neg : Bool) (x : Numfmt.Dec) : M Unit := do
  -- dissect: sign mould, stag mould, point, frac mould, exponent
  let (beforeE, afterE) := match frames.findIdx? (· == .e) with
    | some i => (frames.take i, frames.drop (i + 1))
    | none => (frames, [])
  let (mant, point, frac) := match beforeE.findIdx? (· == .point) with
    | some i => (beforeE.take i, true, beforeE.drop (i + 1))
    | none => (beforeE, false, [])
  let hasSign := mant.any fun f => f == .plus || f == .minus
  let stagDigits := countZD mant
  let fracDigits := countZD frac
  let mantLength := if point then 1 + stagDigits + fracDigits else stagDigits
  let mut z := x
  let mut expValue : Int := 0
  if !afterE.isEmpty then
    let (z', q) := Numfmt.standardize x stagDigits fracDigits 0
    z := z'; expValue := q
  let str := Numfmt.subFixed z mantLength fracDigits
  if Numfmt.hasError str then rtErr "error transputting REAL value"
  let (stagStr, fracStr) := match str.toList.findIdx? (· == '.') with
    | some i => (str.toList.take i, str.toList.drop (i + 1))
    | none => (str.toList, [])
  if neg && !hasSign then rtErr "error transputting REAL value: negative value without sign frame"
  let signChar : List Char := if hasSign then
      [if mant.any (· == .plus) then (if neg then '-' else '+') else (if neg then '-' else ' ')]
    else []
  let mut buf := signChar ++ List.replicate (stagDigits - stagStr.length) '0' ++ stagStr
  if hasSign then buf := shiftSign mant buf
  writeMould fid mant buf false
  if point then fileOut fid "."
  if !frac.isEmpty then writeMould fid frac fracStr true
  if !afterE.isEmpty then
    fileOut fid "e"
    writeIntegralPattern fid afterE expValue

partial def writeStringPattern (fid : Nat) (frames : List Frame) (s : String) : M Unit := do
  let mut cs := s.toList
  for f in frames do
    match f with
    | .a =>
      match cs with
      | c :: rest => fileOutByte fid c.toNat.toUInt8; cs := rest
      | [] => rtErr "error transputting STRING value"
    | .ins t => fileOut fid t
    | _ => pure ()
  if !cs.isEmpty then rtErr "error transputting STRING value"

/-- Convert a value to the exact decimal used by patterns. -/
partial def toDec (m : Mode) (v : Value) : M (Bool × Numfmt.Dec) := do
  match (← resolveM m), v with
  | .int _, .int n => return (n < 0, Numfmt.Dec.ofInt n.natAbs)
  | .real _, .real x => do let _ ← checkReal x; return Numfmt.realToDec x
  | _, .undef => rtErr "attempt to use an uninitialised value"
  | _, _ => rtErr "cannot transput this value with a numeric pattern"

/-- Write one value (already straightened to a scalar) with the next pattern. -/
partial def writeFormatted (fid : Nat) (st : FmtState) (m : Mode) (v : Value) : M FmtState := do
  let mr ← resolveM m
  match mr, v with
  | _, .union m' v' => writeFormatted fid st m' v'
  | .row 1 _ .char, .row _ _ _ => writeScalarFormatted fid st m v
  | .row _ _ em, .row _ _ es =>
    let mut st := st
    for e in es do
      match e with
      | .undef => rtErr s!"attempt to use an uninitialised {modeName em} value"
      | _ => st ← writeFormatted fid st em e
    return st
  | .struct fs, .struct vs =>
    let mut st := st
    for (f, x) in fs.zip vs.toList do
      st ← writeFormatted fid st f.2 x
    return st
  | _, .undef => rtErr s!"attempt to use an uninitialised {modeName m} value"
  | _, _ => writeScalarFormatted fid st m v

partial def writeScalarFormatted (fid : Nat) (st : FmtState) (m : Mode) (v : Value) : M FmtState := do
  let mr ← resolveM m
  match mr, v with
  | _, _ =>
    let (pat?, st') ← nextPattern fid st true
    let some pat := pat? | rtErr "format exhausted"
    match pat with
    | .include _ _ => rtErr "internal: include as pattern"
    | .general args =>
      match mr, v, args with
      | .int n, .int i, [] => fileOut fid (Numfmt.printInt i n (← llDigits))
      | .int _, .int i, [w] => fileOut fid (Numfmt.whole i w)
      | .int n, .int i, [w, a] => fileOut fid (if n ≤ 0 then Numfmt.fixedInt i w a else Numfmt.fixedLongInt i w a)
      | .int _, .int i, [w, a, e] => fileOut fid (Numfmt.floatInt i w a e)
      | .real n, .real x, [] => do let _ ← checkReal x; fileOut fid (Numfmt.printReal x n (← llDigits))
      | .real _, .real x, [w] => do let _ ← checkReal x; fileOut fid (Numfmt.wholeReal x w)
      | .real _, .real x, [w, a] => do let _ ← checkReal x; fileOut fid (Numfmt.fixedReal x w a)
      | .real _, .real x, [w, a, e] => do let _ ← checkReal x; fileOut fid (Numfmt.floatReal x w a e)
      | .compl n, .struct #[.real re, .real im], [] => fileOut fid (Numfmt.printReal re n (← llDigits) ++ Numfmt.printReal im n (← llDigits))
      | .compl _, .struct #[.real re, .real im], [w] => fileOut fid (Numfmt.wholeReal re w ++ Numfmt.wholeReal im w)
      | .compl _, .struct #[.real re, .real im], [w, a] => fileOut fid (Numfmt.fixedReal re w a ++ Numfmt.fixedReal im w a)
      | .compl _, .struct #[.real re, .real im], [w, a, e] => fileOut fid (Numfmt.floatReal re w a e ++ Numfmt.floatReal im w a e)
      | .bool, .bool b, [] => fileOut fid (if b then "T" else "F")
      | .char, .char c, [] => fileOutByte fid c.toUInt8
      | .bits n, .bits b, [] => fileOut fid (Numfmt.printBits b (bitsWidthOf n))
      | .row 1 _ .char, .row _ _ _, [] => fileOut fid (← strOf v)
      | .proc [.ref .file] .void, f, [] => printValue fid mr f
      | _, _, [] => rtErr s!"cannot transput {modeName m} value with a general pattern"
      | _, _, _ => rtErr s!"cannot transput {modeName m} value with a general pattern with arguments"
      return st'
    | .pattern frames =>
      let isString := frames.any (· == .a)
      let isReal := frames.any fun f => f == .point || f == .e
      if isString then
        match mr, v with
        | .char, .char c => writeStringPattern fid frames (String.singleton (Char.ofNat c))
        | .row 1 _ .char, _ => writeStringPattern fid frames (← strOf v)
        | _, _ => rtErr s!"cannot transput {modeName m} value with a string pattern"
      else if isReal then
        let (neg, d) ← toDec m v
        writeRealPattern fid frames neg d
      else
        match mr, v with
        | .int _, .int i => writeIntegralPattern fid frames i
        | .real _, _ => rtErr "cannot transput REAL value with an integral pattern"
        | _, _ => rtErr s!"cannot transput {modeName m} value with an integral pattern"
      return st'
    | .bool_ f g =>
      match v with
      | .bool b =>
        match f, g with
        | some t, some e => fileOut fid (if b then t else e)
        | _, _ => fileOut fid (if b then "T" else "F")
      | _ => rtErr s!"cannot transput {modeName m} value with a boolean pattern"
      return st'
    | .choice alts =>
      match v with
      | .int k =>
        if k ≥ 1 && k ≤ alts.length then fileOut fid alts[(k - 1).toNat]!
      | _ => rtErr s!"cannot transput {modeName m} value with a choice pattern"
      return st'
    | .ins _ => rtErr "internal: insertion as pattern"
    | .col _ => rtErr "internal: column alignment as pattern"

partial def printf (fid : Nat) (items : List Value) : M Unit := do
  (← read).col.set 0
  let mut st : Option FmtState := none
  for it in items do
    match it with
    | .union .format (.fmt env fitems) =>
      -- purge the previous format
      match st with
      | some s => let _ ← nextPattern fid s false
      | none => pure ()
      let pics ← expandFormat env fitems
      st := some { frames := [{ pics := pics.toArray, cursor := 0, embedded := false }] }
    | .union m v =>
      match st with
      | some s => st := some (← writeFormatted fid s m v)
      | none => rtErr "no format active in printf"
    | _ => rtErr "internal: printf argument"
  match st with
  | some s =>
    let (leftover, _) ← nextPattern fid s false
    if leftover.isSome then rtErr "format has unused patterns"
  | none => pure ()

end

/-- Run a program. Returns the process exit code. -/
def run (core : Core) (modes : Mode.Table) (args : Array String) (ll : Nat := Numfmt.defaultLLDigits)
    (regression : Bool := false) : IO UInt32 := do
  let rt : Rt := {
    heap := ← IO.mkRef #[], out := ← IO.mkRef ByteArray.empty, pos := ← IO.mkRef {},
    modes := modes, files := ← IO.mkRef #[{}, {}, {}, {}], rng := ← IO.mkRef (tausSet 1), args := args, ll := ll,
    regression := regression, col := ← IO.mkRef 0 }
  let res ← (eval [#[]] core).run rt |>.run
  -- flush files written by the program
  let files ← rt.files.get
  for f in files do
    if f.onDisk && f.dirty && f.writing then
      try IO.FS.writeBinFile f.name f.buf catch _ => pure ()
  let flush : IO Unit := do
    let mut o ← rt.out.get
    -- in regression mode a68g terminates an unfinished last line
    if regression && o.size > 0 && o[o.size - 1]! != 10 then o := o.push 10
    let stdout ← IO.getStdout
    stdout.write o
    stdout.flush
  match res with
  | .ok _ => flush; return 0
  | .error .stop => flush; return 0
  | .error (.jump l) => flush; IO.eprintln s!"a68lean: runtime error: jump to unknown label {l}"; return 1
  | .error (.fileEnd _) => flush; return 0
  | .error (.error msg p) =>
    flush
    IO.eprintln s!"a68lean: runtime error: {p.line}: {msg}."
    return 1

end A68.Interp
