import A68.Core
import A68.Elab
import A68.Numfmt
import A68.Parser

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
  fd      : Int := -1                        -- an operating-system descriptor: an end of a pipe
  channel : Nat := 3                         -- 0 stand out, 1 stand in, 2 stand error, 3 stand back, 4 associate
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

/-- The line a compiled program last reached; zero while the evaluator is running. -/
@[extern "a68_get_line"]
opaque compiledLine (u : Unit) : BaseIO UInt32

/-- Where to say an error happened: the line the compiled program recorded, when there is
    one, and otherwise the position the evaluator is holding. -/
def errPos : M Pos := do
  let p ← (← read).pos.get
  let cl ← compiledLine ()
  return if cl == 0 then p else { p with line := cl.toNat, col := 0 }

def rtErr (msg : String) : M α := do
  throw (.error msg (← errPos))

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

/-- `s +:= t` where `s` is a whole cell holding a row whose bounds start at 1.  Taking the
    value out of the cell leaves the element array uniquely owned, so the elements are
    appended in place and building a string a piece at a time costs time linear in its
    length rather than quadratic.  Any other shape gives `none` and takes the general
    path, which is what reports its errors. -/
def appendInPlace (a b : Value) : M (Option Value) := do
  match a, b with
  | .ref c [], .row _ _ ys =>
    match (← takeCell c) with
    | .row l u xs =>
      if l.size == 1 && u.size == 1 && l[0]! == 1 && u[0]! == (xs.size : Int) then do
        let n := xs.size + ys.size
        writeCell c (.row l (u.set! 0 (n : Int)) (ys.foldl Array.push xs))
        return some a
      else do
        writeCell c (.row l u xs)
        return none
    | old => do writeCell c old; return none
  | _, _ => return none

/-- The same for a single element, which is what `s +:= c` appends.  Returns whether it
    applied; it does not, and the general path takes over, unless the cell holds a
    one-dimensional row whose lower bound is 1. -/
def appendOne (c : Nat) (v : Value) : M Bool := do
  match (← takeCell c) with
  | .row l u xs =>
    if l.size == 1 && u.size == 1 && l[0]! == 1 && u[0]! == (xs.size : Int) then do
      let n := xs.size + 1
      writeCell c (.row l (u.set! 0 (n : Int)) (xs.push v))
      return true
    else do
      writeCell c (.row l u xs)
      return false
  | old => do writeCell c old; return false

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

-- ## Operating-system services (`csrc/sys.c`)

@[extern "a68_sys_fork"] opaque sysFork (u : Unit) : BaseIO UInt32
@[extern "a68_sys_system"] opaque sysSystem (cmd : @& ByteArray) : BaseIO UInt32
@[extern "a68_sys_execve"] opaque sysExecve (prog : @& ByteArray) (args env : @& Array ByteArray) : BaseIO UInt32
@[extern "a68_sys_execve_child"] opaque sysExecveChild (prog : @& ByteArray) (args env : @& Array ByteArray) : BaseIO UInt32
@[extern "a68_sys_execve_child_pipe"] opaque sysExecveChildPipe (prog : @& ByteArray) (args env : @& Array ByteArray) : BaseIO ByteArray
@[extern "a68_sys_execve_output"] opaque sysExecveOutput (prog : @& ByteArray) (args env : @& Array ByteArray) : BaseIO ByteArray
@[extern "a68_sys_waitpid"] opaque sysWaitpid (pid : UInt32) : BaseIO UInt32
@[extern "a68_sys_read_fd"] opaque sysReadFd (fd : UInt32) : BaseIO ByteArray
@[extern "a68_sys_write_fd"] opaque sysWriteFd (fd : UInt32) (b : @& ByteArray) : BaseIO UInt32
@[extern "a68_sys_close_fd"] opaque sysCloseFd (fd : UInt32) : BaseIO UInt32
@[extern "a68_sys_time"] opaque sysTime (utc : UInt8) : BaseIO ByteArray
@[extern "a68_sys_walltime"] opaque sysWalltime (u : Unit) : BaseIO Float
@[extern "a68_sys_readdir"] opaque sysReaddir (path : @& ByteArray) : BaseIO (Array ByteArray)
@[extern "a68_sys_stat_mode"] opaque sysStatMode (path : @& ByteArray) : BaseIO UInt32
@[extern "a68_sys_open_status"] opaque sysOpenStatus (path : @& ByteArray) : BaseIO UInt32
@[extern "a68_sys_regex"] opaque sysRegex (pat str : @& ByteArray) (notbol : UInt8) : BaseIO ByteArray
@[extern "a68_sys_strerror"] opaque sysStrerror (e : UInt32) : BaseIO ByteArray
@[extern "a68_sys_errno"] opaque sysErrno (u : Unit) : BaseIO UInt32
@[extern "a68_sys_set_errno"] opaque sysSetErrno (e : UInt32) : BaseIO UInt32
@[extern "a68_sys_getcwd"] opaque sysGetcwd (u : Unit) : BaseIO ByteArray
@[extern "a68_sys_chdir"] opaque sysChdir (path : @& ByteArray) : BaseIO UInt32
@[extern "a68_sys_realpath"] opaque sysRealpath (path : @& ByteArray) : BaseIO ByteArray
@[extern "a68_sys_sleep"] opaque sysSleep (secs : UInt32) : BaseIO UInt32
@[extern "a68_sys_getenv"] opaque sysGetenv (name : @& ByteArray) : BaseIO ByteArray
-- a68g computes these with the C library
@[extern "tgamma"] opaque cTgamma (x : Float) : Float
@[extern "lgamma"] opaque cLgamma (x : Float) : Float
@[extern "erf"] opaque cErf (x : Float) : Float
@[extern "erfc"] opaque cErfc (x : Float) : Float
@[extern "log1p"] opaque cLog1p (x : Float) : Float
def piOver180 : Float := 0.0174532925199432957692369076848861271344287188854172545609719144
def d180OverPi : Float := 57.2957795130823208767981548141051703324054724665643215491602438

/-- The bytes of a string: an Algol 68 character is a byte. -/
def strBytes (s : String) : ByteArray := s.foldl (fun acc c => acc.push c.toNat.toUInt8) ByteArray.empty
def bytesStr (b : ByteArray) : String := String.ofList (b.toList.map fun x => Char.ofNat x.toNat)
def uint32At (b : ByteArray) (i : Nat) : Nat :=
  (b.get! i).toNat + (b.get! (i+1)).toNat * 256 + (b.get! (i+2)).toNat * 65536 + (b.get! (i+3)).toNat * 16777216
def int32At (b : ByteArray) (i : Nat) : Int :=
  let u := uint32At b i
  if u ≥ 2147483648 then (u : Int) - 4294967296 else u
def signed32 (u : UInt32) : Int := if u.toNat ≥ 2147483648 then (u.toNat : Int) - 4294967296 else u.toNat
def u32 (k : Int) : UInt32 := UInt32.ofNat (k % 4294967296).toNat
/-- Little-endian bytes of the low `n` bytes of a number, as a C object is laid out. -/
def leBytes (v : Nat) (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  let mut x := v
  for _ in [0:n] do
    b := b.push (x % 256).toUInt8
    x := x / 256
  return b

/-- The program, arguments and environment of an `execve` call; a68g refuses an argument
    row whose strings are all empty. -/
def execArgs (p as en : Value) : M (ByteArray × Array ByteArray × Array ByteArray) := do
  let prog ← strOf p
  let (_, _, aes) ← expectRow as
  let (_, _, ees) ← expectRow en
  let av ← aes.mapM fun e => do pure (strBytes (← strOf e))
  let ev ← ees.mapM fun e => do pure (strBytes (← strOf e))
  if !av.any (·.size > 0) then rtErr "empty argument row"
  return (strBytes prog, av, ev)

/-- a68g collects transput in C strings, so a NUL character ends the text that reaches the
    file until the buffer is next purged: after each item of `print`, at a new line or page
    of `printf`, and at the end of a formatted call.  While this is set, standard output
    and standard error take nothing. -/
initialize nulCut : IO.Ref Bool ← IO.mkRef false

def fileOut (fid : Nat) (s : String) : M Unit := do
  let colRef := (← read).col
  for c in s.toList do
    if c == '\n' then colRef.set 0 else colRef.modify (· + 1)
  if fid == 0 || fid == 2 then
    if !(← nulCut.get) then
      let s ← if s.any (· == '\x00') then do
          nulCut.set true
          pure (String.ofList (s.toList.takeWhile (· != '\x00')))
        else pure s
      if fid == 0 then emit s
      else
        let stderr ← IO.getStderr
        stderr.putStr s
  else
    let fs ← (← read).files.get
    match fs[fid]? with
    | none => rtErr "file is not open"
    | some f0 =>
      if f0.fd ≥ 0 then
        let _ ← sysWriteFd f0.fd.toNat.toUInt32 (strBytes s)
        (← read).files.modify fun fs => fs.set! fid { f0 with writing := true }
        return
      match f0.assoc with
      | some r =>
        -- a68g empties the string when an associated file turns to writing
        -- (`open_physical_file`), and each write appends to what the string then holds
        if !f0.writing then
          writeRef r (Value.ofString "")
          (← read).files.modify fun fs => fs.set! fid { f0 with writing := true, reading := false }
        match (← appendInPlace r (Value.ofString s)) with
        | some _ => pure ()
        | none => writeRef r (Value.ofString ((← strOf (← readRef r)) ++ s))
      | none =>
        let f' := { f0 with buf := s.foldl (fun acc c => acc.push c.toNat.toUInt8) f0.buf,
                            writing := true, dirty := true, loaded := true }
        (← read).files.modify fun fs => fs.set! fid f'

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
  if fid == 0 then
    if !(← nulCut.get) then
      if b == 0 then nulCut.set true else emitByte b
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
  | .bytes _, .row _ _ es => for e in es do fileOutByte fid (← expectChar e).toUInt8
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
  | radix (r : Nat)           -- the radix frame `r` that makes a mould a bits pattern
  deriving Repr, Inhabited, BEq

inductive Pic where
  | ins (s : String)
  | pattern (frames : List Frame)              -- numeric, bits or string pattern
  | general (args : List Int)
  | bool_ (flip flop : Option String)
  | choice (alts : List String)
  | include (items : List CoreFmt) (env : Env)
  | col (n : Nat)
  | cpat (flags : String) (width after : Option Int)   -- a68g C-style pattern, `%-8.2f`
  | hgen (args : List Int)                            -- a68g `h` pattern
  deriving Inhabited

/-- a68g `convert_radix`: the digits of `v` in base `radix`, most significant first, padded
    to `width` digits (as many as it takes when `width` is 0); `none` if `v` does not fit. -/
def convertRadix (v radix width : Nat) : Option String := Id.run do
  let digit (k : Nat) : Char := "0123456789abcdef".toList[k]!
  let mut z := v
  let mut s : List Char := []
  if width == 0 then
    repeat
      s := digit (z % radix) :: s
      z := z / radix
      if z == 0 then break
    return some (String.ofList s)
  for _ in [0:width] do
    s := digit (z % radix) :: s
    z := z / radix
  return if z == 0 then some (String.ofList s) else none

/-- The exponent C `strtol` reads after the `e` of a `float` string (0 when there is none). -/
def exponentOf (s : String) : Int :=
  match s.splitOn "e" with
  | _ :: rest :: _ =>
    let cs := rest.toList.dropWhile (· == ' ')
    let (neg, cs) := match cs with
      | '-' :: t => (true, t) | '+' :: t => (false, t) | t => (false, t)
    let n : Int := (cs.takeWhile Char.isDigit).foldl (fun acc c => acc * 10 + (c.toNat - 48 : Nat)) 0
    if neg then -n else n
  | _ => 0

/-- What a68g's `strtol` accepts when it converts the characters a C-style pattern read:
    blanks, a sign and digits, with nothing after them. -/
def parseIntText (s : String) : Option Int :=
  let cs := s.toList.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n')
  let (neg, cs) := match cs with | '-' :: t => (true, t) | '+' :: t => (false, t) | t => (false, t)
  if cs.isEmpty || !cs.all Char.isDigit then none
  else
    let n : Int := cs.foldl (fun acc c => acc * 10 + (c.toNat - 48 : Nat)) 0
    some (if neg then -n else n)

/-- The same for a REAL: blanks, a sign, digits with an optional point and exponent. -/
def parseRealText (s : String) : Option Float :=
  let cs := s.toList.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n')
  let (neg, cs) := match cs with | '-' :: t => (true, t) | '+' :: t => (false, t) | t => (false, t)
  let intPart := cs.takeWhile Char.isDigit
  let rest := cs.drop intPart.length
  let (fracPart, rest) := match rest with
    | '.' :: t => (t.takeWhile Char.isDigit, t.drop (t.takeWhile Char.isDigit).length)
    | t => ([], t)
  let expOk := match rest with
    | [] => true
    | c :: t =>
      (c == 'e' || c == 'E') &&
        (match t with | '+' :: u | '-' :: u => !u.isEmpty && u.all Char.isDigit | u => !u.isEmpty && u.all Char.isDigit)
  if (intPart.isEmpty && fracPart.isEmpty) || !expOk then none
  else
    let x := Numfmt.parseFloat (String.ofList cs)
    some (if neg then -x else x)

/-- The value of the digits a bits pattern or C-style pattern read, in base `radix`; a digit
    outside the radix, or a value too wide for the mode, is an error (a68g `bits_to_int`). -/
def radixValue (s : String) (radix : Nat) (long : Int) : M Nat := do
  let mut v := 0
  -- `strtoul` passes over leading white space
  for c in s.toList.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n') do
    let d := if c.isDigit then c.toNat - 48
      else if c ≥ 'a' && c ≤ 'f' then c.toNat - 87
      else if c ≥ 'A' && c ≤ 'F' then c.toNat - 55 else 99
    if d ≥ radix then rtErr s!"error in {Mode.toString (.bits long)} denotation"
    v := v * radix + d
  if v > bitsMask long then rtErr s!"{Mode.toString (.bits long)} value out of range"
  return v

/-- The string an a68g C-style pattern `%[-][+][w][.a]letter` makes of a value, with the width
    it is aligned to (`write_c_pattern`). -/
def cPatternText (flags : String) (w a : Option Int) (mr : Mode) (v : Value) (ll : Nat) : M (Int × String) := do
  let letter := flags.back
  let signed (width : Int) : Int := if flags.contains '+' then width else -width
  match letter, mr, v with
  | 'd', .int _, .int i | 'i', .int _, .int i =>
    let width := w.getD 0
    return (width, Numfmt.whole i (signed width))
  | 'f', .int long, _ | 'e', .int long, _ | 'g', .int long, _
  | 'f', .real long, _ | 'e', .real long, _ | 'g', .real long, _ =>
    let rw : Int := Numfmt.realWidthOf long ll
    let ew : Int := Numfmt.expWidthOf long
    let floatS (width after expo : Int) : M String := match v with
      | .int i => pure (Numfmt.floatInt i width after expo)
      | .real x => do let _ ← checkReal x; pure (Numfmt.floatReal x width after expo)
      | _ => rtErr "internal: C-style pattern"
    let fixedS (width after : Int) : M String := match mr, v with
      | .int n, .int i => pure (if n ≤ 0 then Numfmt.fixedInt i width after else Numfmt.fixedLongInt i width after)
      | _, .real x => do let _ ← checkReal x; pure (Numfmt.fixedReal x width after)
      | _, _ => rtErr "internal: C-style pattern"
    let digits := w.getD 0
    let after := a.getD (rw - 1)
    let mut res : Int × String := (0, "")
    let mut useFixed := letter == 'f'
    if letter != 'f' then
      let expo := ew + 1
      let width := if digits == 0 && after > 0 then after + expo + 4
        else if digits > 0 then digits else rw + ew + 4
      let s ← floatS (signed width) after expo
      res := (width, s)
      if letter == 'g' then
        let ev := exponentOf s
        useFixed := ev > -4 && ev ≤ after
    if useFixed then
      let width := if digits == 0 then 0 else digits + after + 2
      res := (width, ← fixedS (signed width) after)
    return res
  | 'b', .bits n, .bits b | 'o', .bits n, .bits b | 'x', .bits n, .bits b =>
    let (radix, nibble) : Nat × Nat := match letter with | 'b' => (2, 1) | 'o' => (8, 3) | _ => (16, 4)
    let dflt := (bitsWidthOf n + nibble - 1) / nibble
    let width : Nat := match w with
      | some k => if k > 0 then k.toNat else dflt
      | none => dflt
    match convertRadix b radix width with
    | some s => return (width, s)
    | none => rtErr s!"error transputting {Mode.toString mr} value"
  | 's', .char, .char c => return (w.getD 1, String.singleton (Char.ofNat c))
  | 's', .row 1 _ .char, _ => let s ← strOf v; return (w.getD s.length, s)
  | _, _, _ => rtErr s!"cannot transput {Mode.toString mr} value with a C-style pattern"

/-- Write a value with a C-style pattern: blanks the conversion put in front are dropped, and
    the rest is aligned right, or left when the pattern says `-`. -/
def writeCPattern (fid : Nat) (flags : String) (w a : Option Int) (mr : Mode) (v : Value) : M Unit := do
  let (width, str) ← cPatternText flags w a mr v (← llDigits)
  if flags.back != 's' && Numfmt.hasError str then rtErr s!"error transputting {Mode.toString mr} value"
  if width == 0 then fileOut fid str
  else
    let s := String.ofList (str.toList.dropWhile (· == ' '))
    let blanks := width - s.length
    if blanks < 0 then rtErr s!"error transputting {Mode.toString mr} value"
    let pad := String.ofList (List.replicate blanks.toNat ' ')
    fileOut fid (if flags.contains '-' then s ++ pad else pad ++ s)

/-- The `real` arguments of an `h` pattern: width, after, exponent and exponent multiple
    (a68g `write_number_generic` and `genie_value_to_string`). -/
def hArguments (long : Int) (args : List Int) (ll : Nat) : M (Int × Int × Int × Int) := do
  let rw : Int := Numfmt.realWidthOf long ll
  let ew : Int := Numfmt.expWidthOf long
  let de := ew + 1
  match args with
  | [] => return (rw + ew + 4, rw - 1, de, 3)
  | [a] => return (a + de + 4, a, de, 3)
  | [a, m] => return (a + de + 4, a, de, m)
  | [w, a, m] => return (w, a, de, m)
  | [w, a, e, m] => return (w, a, e, m)
  | _ => rtErr "INT arguments required for a general pattern"

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

/-- The pending-jump flag compiled code keeps in a C variable (`csrc/stubs.c`).  A routine
    compiled to C leaves by a jump by setting the flag and returning, so what it returns is
    a dummy; after every call into compiled code the flag has to be turned back into the
    jump the evaluator itself would have raised, before anything looks at that value. -/
@[extern "a68_get_jump"]
opaque getJumpFlag (u : Unit) : BaseIO UInt32

@[extern "a68_set_jump"]
opaque setJumpFlag (v : UInt32) : BaseIO UInt32

/-- Call into compiled code, and raise the jump it left pending, if it left one.  This is
    what lets an event routine such as an `on logical file end` handler leave with a
    `GO TO`: the jump unwinds through the transput that called it, exactly as it does
    when the routine is evaluated rather than compiled. -/
def fromCompiled (act : IO Value) : ReaderT Rt (ExceptT Ctrl IO) Value := do
  let v ← (act : IO Value)
  let j ← ((getJumpFlag () : BaseIO UInt32) : IO UInt32)
  if j != 0 then
    let _ ← ((setJumpFlag 0 : BaseIO UInt32) : IO UInt32)
    throw (.jump (j.toNat - 1))
  return v

/-- The mode and value inside a united value.  A value united to a union that is itself a
    member of another union is looked through, since a68g flattens unions: a `BASIC`
    holding an `INT`, united to `UNION (VOID, BASIC)`, conforms to `INT` and to `BASIC`. -/
def unionContent : Value → Mode × Value
  | .union _ (.union m x) => unionContent (.union m x)
  | .union m x => (m, x)
  | x => (.void, x)

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
    let (vm, inner) := unionContent v
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
  | .hole fn idx => fromCompiled (dispatchHole (USize.ofNat fn) (USize.ofNat idx) env)
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
        -- `es[o]?` would allocate an `Option` for every element read
        if h : o < es.size then return es[o]
        else rtErr "internal: element offset out of range"
  -- fast path: a one-dimensional trim of a one-dimensional row is contiguous, so the
  -- elements can be copied in one go and the offsets, where they are still needed, run
  -- consecutively.  Trimming the whole dimension only renames the bounds.
  | [.trim lo hi at_] =>
    if d == 1 && es.size == rowSize l u then
      let l0 := l[0]!
      let u0 := u[0]!
      let lo' ← match lo with | some v => expectInt v | none => pure l0
      let hi' ← match hi with | some v => expectInt v | none => pure u0
      let at' ← match at_ with | some v => expectInt v | none => pure 1
      if lo' < l0 || hi' > u0 then
        if !(hi' < lo') then rtErr s!"trim [{lo'}:{hi'}] out of bounds [{l0}:{u0}]"
      let newL := #[at']
      let newU := #[at' + (hi' - lo')]
      let n := if hi' ≥ lo' then (hi' - lo' + 1).toNat else 0
      let start := if n == 0 then 0 else (lo' - l0).toNat
      if !viaRef then
        if n != 0 && lo' == l0 && hi' == u0 then return .row newL newU es
        return .row newL newU (es.extract start (start + n))
      -- through a reference: compose with any view the reference already denotes
      match base with
      | .ref c path =>
        match path.getLast?, n != 0 && lo' == l0 && hi' == u0 with
        | some (.sub _ _ offs0), true => return .ref c (path.dropLast ++ [.sub newL newU offs0])
        | some (.sub _ _ offs0), false =>
          return .ref c (path.dropLast ++ [.sub newL newU (Array.ofFn (n := n) fun k => offs0[start + k.val]!)])
        | _, _ => return .ref c (path ++ [.sub newL newU (Array.ofFn (n := n) fun k => start + k.val)])
      | _ => rtErr "internal: sub-row of a non-REF"
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
  -- a BYTES value is its row of characters, NUL padded to `bytes width`
  | .bytes _, .row _ _ .char, _ => return v
  | .bytes _, .bytes n, .row _ _ es =>
    let w : Nat := if n ≥ 1 then 256 else 32
    return .row #[1] #[(w : Int)] (es ++ Array.replicate (w - es.size) (.char 0))
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
    | .decl slot _ init =>
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
  | .cproc fn _ cenv => fromCompiled (dispatchProc (USize.ofNat fn) cenv args.toArray)
  | .builtin name => callBuiltin name args
  | .nil => rtErr "attempt to call NIL"
  | .undef => rtErr "attempt to call an uninitialised procedure"
  | _ => rtErr "internal: call of a non-procedure"

-- ### Operators

partial def dyadic (op : String) (m1 m2 : Mode) (a b : Value) : M Value := do
  let tb := (← read).modes
  let m1r := Mode.resolve tb m1
  let m2r := Mode.resolve tb m2
  -- appending to a row variable is the one assigning operator worth a special case: done
  -- the general way it rebuilds the whole row every time
  if op == "+:=" then
    match m1r with
    | .ref (.row 1 _ _) =>
      match (← appendInPlace a b) with
      | some r => return r
      | none => pure ()
    | _ => pure ()
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
          | "/:=" => if y == 0.0 then rtErr "REAL value is not a number" else pure (x / y)
          | _ => rtErr s!"internal: assigning operator {op} on REAL"
        -- as for `/`, the quotient of `/:=` is not checked
        if op == "/:=" then pure (Value.real r) else Value.real <$> checkReal r
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
    -- a68g checks the divisor but not the quotient: an infinite or NaN result is only
    -- reported by a later operation that checks, as `*` and printing do
    | "/" => if y == 0.0 then rtErr "REAL value is not a number" else return .real (x / y)
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
      let cmp ← compareChars xs ys
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
  | .int _, .bytes _ =>
    let k ← expectInt a
    let (_, _, es) ← expectRow b
    if k < 1 || k > es.size then rtErr s!"index {k} out of bounds [1:{es.size}]"
    return es[(k - 1).toNat]!
  | .bytes _, .bytes _ =>
    let (_, _, xs) ← expectRow a
    let (_, _, ys) ← expectRow b
    let cmp ← compareChars xs ys
    match op with
    | "=" => return .bool (cmp == 0)
    | "/=" => return .bool (cmp != 0)
    | "<" => return .bool (cmp < 0)
    | "<=" => return .bool (cmp ≤ 0)
    | ">" => return .bool (cmp > 0)
    | ">=" => return .bool (cmp ≥ 0)
    | _ => rtErr s!"internal: BYTES operator {op}"
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

/-- Every element of a row of CHAR, checked exactly as `strOf` checks it. -/
private partial def checkChars (es : Array Value) : M Unit := do
  for e in es do
    match e with
    | .char _ => pure ()
    | .undef => rtErr "attempt to use an uninitialised CHAR value"
    | _ => rtErr "internal: [] CHAR expected"

/-- Compare two rows of CHAR the way `compareStr` compares the strings they denote, but
    without building those strings.  Both rows are checked first, and in the same order,
    so that an uninitialised character is still reported where it was. -/
partial def compareChars (xs ys : Array Value) : M Int := do
  checkChars xs
  checkChars ys
  let n := min xs.size ys.size
  for i in [0:n] do
    let x := match xs[i]! with | .char c => c | _ => 0
    let y := match ys[i]! with | .char c => c | _ => 0
    if x < y then return -1
    if x > y then return 1
  if xs.size < ys.size then return -1
  if xs.size > ys.size then return 1
  return 0

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
  | "ABS", .bits n => do
    let b ← expectBits v
    -- a68g reads the 32 bits of a BITS as a C int: ABS NOT BIN 3 is -4
    return .int (if n ≤ 0 && b ≥ 2147483648 then (b : Int) - 4294967296 else b)
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
  if f.fd ≥ 0 then
    -- the end of a pipe: take what one read gives when the characters so far are used up
    if f.pos < f.buf.size || f.eof then return f
    flushOut
    let chunk ← sysReadFd f.fd.toNat.toUInt32
    let f' := if chunk.isEmpty then { f with eof := true, loaded := true, reading := true }
      else { f with buf := f.buf ++ chunk, loaded := true, reading := true }
    setFile fid f'
    return f'
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
    -- a68g reads the string's current value at the position reached so far
    if bytes != f.buf then setFile fid { f with buf := bytes, loaded := true }
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
    | .compl n =>
      match r with
      | .ref c path =>
        match (← readRef r) with
        | .struct _ => pure ()
        | _ => writeRef r (mkCompl 0.0 0.0 |> fun _ => .struct #[.undef, .undef])
        readInto fid (.ref (.real n)) (.ref c (path ++ [.field 0]))
        readInto fid (.ref (.real n)) (.ref c (path ++ [.field 1]))
      | _ => rtErr "internal: COMPL read"
    | .union _ =>
      -- a68g reads a value of the mode the united value currently has
      match (← readRef r) with
      | .union um uv =>
        let tmp ← alloc uv
        readInto fid (.ref um) (.ref tmp [])
        writeRef r (.union um (← readCell tmp))
      | _ => rtErr s!"attempt to use an uninitialised {modeName t} value"
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
  | .compl n =>
    match r with
    | .ref c path =>
      match (← readRef r) with
      | .struct _ => pure ()
      | _ => writeRef r (.struct #[.undef, .undef])
      let st ← readFormatted fid st (.ref (.real n)) (.ref c (path ++ [.field 0]))
      readFormatted fid st (.ref (.real n)) (.ref c (path ++ [.field 1]))
    | _ => rtErr "internal: COMPL read"
  | .union _ =>
    match (← readRef r) with
    | .union um uv =>
      let tmp ← alloc uv
      let st ← readFormatted fid st (.ref um) (.ref tmp [])
      writeRef r (.union um (← readCell tmp))
      return st
    | _ => rtErr s!"attempt to use an uninitialised {modeName tm} value"
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
  | .general _ | .hgen _ => readInto fid m r
  | .cpat flags w _ =>
    -- a68g `read_c_pattern`: without a width the value is read as `get` reads it, with one
    -- exactly that many characters are taken and converted
    let letter := flags.back
    let width := w.getD 0
    let readN (k : Int) : M String := do
      let mut s := ""
      for _ in [0:k.toNat] do
        match (← readChar fid) with
        | some c => s := s.push (Char.ofNat c)
        | none => logicalEnd fid
      return s
    match tm, letter with
    | .char, 'c' =>
      if width == 0 then readInto fid m r
      else
        let s ← readN width
        let s := if width > 1 && !flags.contains '-' then String.ofList (s.toList.drop (width.toNat - 1)) else s
        writeRef r (.char (s.toList.headD ' ').toNat)
    | .row 1 _ .char, 's' =>
      if width == 0 then readInto fid m r else writeRef r (Value.ofString (← readN width))
    | .int n, 'd' | .int n, 'i' =>
      if width == 0 then readInto fid m r
      else
        let s ← readN (if flags.contains '+' then width + 1 else width)
        match parseIntText s with
        | some k =>
          if k.natAbs > (Numfmt.maxIntOf n (← llDigits)).natAbs then valueError fid s!"cannot read {modeName tm} from \"{s}\""
          writeRef r (.int k)
        | none => valueError fid s!"cannot read {modeName tm} from \"{s}\""
    | .real _, 'f' | .real _, 'e' | .real _, 'g' =>
      if width == 0 then readInto fid m r
      else
        let s ← readN (if flags.contains '+' then width + 1 else width)
        match parseRealText s with
        | some x => writeRef r (.real x)
        | none => valueError fid s!"cannot read {modeName tm} from \"{s}\""
    | .bits n, 'b' | .bits n, 'o' | .bits n, 'x' =>
      let radix := match letter with | 'b' => 2 | 'o' => 8 | _ => 16
      let digits ← if width == 0 then do
          skipSpaces fid
          let mut s := ""
          repeat
            match (← peekChar fid) with
            | some c =>
              let ch := Char.ofNat c
              if ch.isDigit || (ch ≥ 'a' && ch ≤ 'f') || (ch ≥ 'A' && ch ≤ 'F') then
                let _ ← readChar fid
                s := s.push ch
              else break
            | none => break
          pure s
        else readN width
      writeRef r (.bits (← radixValue digits radix n))
    | _, _ => rtErr s!"cannot transput {modeName tm} value with a C-style pattern"
  | .pattern frames =>
    if let some rdx := frames.findSome? (fun f => match f with | .radix k => some k | _ => none) then
      -- a bits pattern: digits of the radix, a `z` frame also taking a blank for a zero
      match tm with
      | .bits n =>
        if rdx < 2 || rdx > 16 then rtErr s!"invalid radix {rdx}"
        let mut s := ""
        for f in frames do
          match f with
          | .ins t => readInsertion fid t
          | .z | .d =>
            match (← readChar fid) with
            | some c =>
              let ch := Char.ofNat c
              if f == .z && ch == ' ' then s := s.push '0'
              else if ch.isDigit || (ch ≥ 'a' && ch ≤ 'f') || (ch ≥ 'A' && ch ≤ 'F') then s := s.push ch
              else
                valueError fid s!"cannot read {modeName tm} from \"{s.push ch}\""
                s := s.push '0'
            | none => logicalEnd fid
          | _ => pure ()
        writeRef r (.bits (← radixValue s rdx n))
      | _ => rtErr s!"cannot transput {modeName tm} value with a bits pattern"
    else if frames.any (· == .a) then
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
    | "gamma" => pure (cTgamma x)
    | "lngamma" => pure (cLgamma x)
    | "erf" => pure (cErf x)
    | "erfc" => pure (cErfc x)
    | "ln1p" => pure (cLog1p x)
    -- a68g single-math.c, with its constants for pi / 180 and 180 / pi
    | "sindg" => pure (Float.sin (x * piOver180))
    | "cosdg" => pure (Float.cos (x * piOver180))
    | "tandg" => pure (Float.tan (x * piOver180))
    | "arcsindg" | "asindg" => pure (Float.asin x * d180OverPi)
    | "arccosdg" | "acosdg" => pure (Float.acos x * d180OverPi)
    | "arctandg" | "atandg" => pure (Float.atan x * d180OverPi)
    | "cot" => do let z := Float.sin x; if z == 0.0 then rtErr "math exception" else pure (Float.cos x / z)
    | "sec" => do let z := Float.cos x; if z == 0.0 then rtErr "math exception" else pure (1.0 / z)
    | "csc" => do let z := Float.sin x; if z == 0.0 then rtErr "math exception" else pure (1.0 / z)
    | "cotdg" => do
      let z := Float.sin (x * piOver180)
      if z == 0.0 then rtErr "math exception" else pure (Float.cos (x * piOver180) / z)
    | "secdg" => do let z := Float.cos (x * piOver180); if z == 0.0 then rtErr "math exception" else pure (1.0 / z)
    | "cscdg" => do let z := Float.sin (x * piOver180); if z == 0.0 then rtErr "math exception" else pure (1.0 / z)
    | "cas" => pure (Float.cos x + Float.sin x)
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
      | .union m v => printValue 0 m v; nulCut.set false
      | _ => rtErr "internal: print argument"
    return .void
  | "put", [f, row] =>
    let fid ← fileIdOf f
    let (_, _, es) ← expectRow row
    for e in es do
      match e with
      | .union m v => printValue fid m v; nulCut.set false
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
  | "open", [fv, nm, ch] | "append", [fv, nm, ch] =>
    -- a68g opens the file when it is first used; the result says whether it is a regular
    -- file (0), and otherwise gives the error number
    let path ← strOf nm
    let chan := match ch with | .int k => k.toNat | _ => 3
    let status ← sysOpenStatus (strBytes path)
    if status == 0 then
      let bytes ← IO.FS.readBinFile path
      let _ ← newFile fv { name := path, buf := bytes, loaded := true, onDisk := true, channel := chan }
    else
      let _ ← newFile fv { name := path, loaded := true, onDisk := true, channel := chan }
    return .int (signed32 status)
  | "establish", [fv, nm, ch, _, _, _] =>
    let path ← strOf nm
    let chan := match ch with | .int k => k.toNat | _ => 3
    let _ ← newFile fv { name := path, loaded := true, onDisk := true, writing := true, channel := chan }
    return .int 0
  | "create", [fv, ch] =>
    let chan := match ch with | .int k => k.toNat | _ => 3
    let _ ← newFile fv { name := "", loaded := true, channel := chan }
    return .int 0
  | "associate", [fv, sv] =>
    let _ ← newFile fv { assoc := some sv, channel := 4 }
    return .void
  | "close", [f] | "lock", [f] =>
    let fid ← fileIdOf f
    let fs ← getFile fid
    if fs.fd ≥ 0 then
      let _ ← sysCloseFd fs.fd.toNat.toUInt32
      setFile fid { fs with fd := -1, eof := true }
    flushFile fid
    return .void
  | "scratch", [f] | "erase", [f] =>
    -- a68g `genie_erase`: a file that has been used is removed
    let fid ← fileIdOf f
    flushFile fid
    let fs ← getFile fid
    if fs.onDisk && !fs.name.isEmpty && (fs.reading || fs.writing) then
      match (← (IO.FS.removeFile fs.name).toBaseIO) with
      | .ok _ => setFile fid { fs with onDisk := false, dirty := false }
      | .error _ => rtErr "cannot scratch the file"
    return .void
  | "rewind", [f] => callBuiltin "reset" [f]
  | "reset", [f] =>
    let fid ← fileIdOf f
    if !([3, 4].contains (← fileChannel f)) then rtErr "the channel does not allow resetting the file"
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
  | "bytespack", [s] | "longbytespack", [s] =>
    let str ← strOf s
    let w := if name == "bytespack" then 32 else 256
    if str.length > w then rtErr s!"the string is longer than {w} characters"
    return .row #[1] #[w] ((str.toList.map fun c => Value.char c.toNat) ++ List.replicate (w - str.length) (Value.char 0)).toArray
  | "evaluate", [code, .fmt env items] => evaluateCall (← strOf code) env items
  | "evaluate", [code] => evaluateCall (← strOf code) [] []
  | "system", [cmd] =>
    let c ← strOf cmd
    flushOut
    return .int (signed32 (← sysSystem (strBytes c)))
  | "fork", [] =>
    flushOut
    return .int (signed32 (← sysFork ()))
  | "getenv", [n] => return Value.ofString (bytesStr (← sysGetenv (strBytes (← strOf n))))
  | "execve", [p, as, en] | "exec", [p, as, en] =>
    let (prog, av, ev) ← execArgs p as en
    flushOut
    return .int (signed32 (← sysExecve prog av ev))
  | "execvechild", [p, as, en] | "execsub", [p, as, en] =>
    let (prog, av, ev) ← execArgs p as en
    flushOut
    return .int (signed32 (← sysExecveChild prog av ev))
  | "execvechildpipe", [p, as, en] | "execsubpipeline", [p, as, en] =>
    let (prog, av, ev) ← execArgs p as en
    flushOut
    let r ← sysExecveChildPipe prog av ev
    let fr ← (← read).files.modifyGet fun fs => (fs.size, fs.push { fd := int32At r 0, channel := 1, reading := true })
    let fw ← (← read).files.modifyGet fun fs => (fs.size, fs.push { fd := int32At r 4, channel := 0, writing := true })
    return .struct #[.ref (← alloc (.file fr)) [], .ref (← alloc (.file fw)) [], .int (int32At r 8)]
  | "execveoutput", [p, as, en, dest] | "execsuboutput", [p, as, en, dest] =>
    let (prog, av, ev) ← execArgs p as en
    flushOut
    let r ← sysExecveOutput prog av ev
    if int32At r 4 == 1 then
      match dest with
      | .nil => pure ()
      | _ => writeRef dest (Value.ofString (bytesStr (r.extract 8 r.size)))
    return .int (int32At r 0)
  | "createpipe", [] => return .struct #[.file 1, .file 0, .int (-1)]
  | "waitpid", [pid] => return .int (signed32 (← sysWaitpid (u32 (← expectInt pid))))
  | "utctime", [] | "localtime", [] =>
    let r ← sysTime (if name == "utctime" then 1 else 0)
    return Value.rowOfList ((List.range (r.size / 4)).map fun i => Value.int (int32At r (4 * i)))
  | "getdirectory", [d] =>
    let arr ← sysReaddir (strBytes (← strOf d))
    if arr.isEmpty then rtErr "cannot read the directory"
    return Value.rowOfList ((arr.toList.drop 1).map fun b => Value.ofString (bytesStr b))
  | "fileisdirectory", [s] | "fileisregular", [s] | "fileisblockdevice", [s] | "fileischardevice", [s]
  | "fileisfifo", [s] | "fileislink", [s] =>
    let mode := (← sysStatMode (strBytes (← strOf s))).toNat
    let kind : Nat := match name with
      | "fileisdirectory" => 0o040000 | "fileisregular" => 0o100000 | "fileisblockdevice" => 0o060000
      | "fileischardevice" => 0o020000 | "fileisfifo" => 0o010000 | _ => 0o120000
    return .bool (mode != 0 && (mode &&& 0o170000) == kind)
  | "filemode", [s] => return .bits (← sysStatMode (strBytes (← strOf s))).toNat
  | "grepinstring", [pat, str, b, e] | "grepinsubstring", [pat, str, b, e] =>
    let p ← strOf pat
    let (l, _, _) ← expectRow str
    let s ← strOf str
    let r ← sysRegex (strBytes p) (strBytes s) (if name == "grepinsubstring" then 1 else 0)
    let ret := int32At r 0
    if ret == 0 then
      match b with
      | .nil => pure ()
      | _ => writeRef b (.int (int32At r 4 + l[0]!))
      match e with
      | .nil => pure ()
      | _ => writeRef e (.int (int32At r 8 + l[0]! - 1))
    return .int ret
  | "subinstring", [pat, rep, rs] =>
    match rs with
    | .nil => return .int 3
    | _ =>
      let s ← strOf (← readRef rs)
      let r ← sysRegex (strBytes (← strOf pat)) (strBytes s) 0
      let ret := int32At r 0
      if ret != 0 then return .int ret
      let so := (int32At r 4).toNat
      let eo := (int32At r 8).toNat
      let t ← strOf rep
      writeRef rs (Value.ofString (String.ofList (s.toList.take so) ++ t ++ String.ofList (s.toList.drop eo)))
      return .int 0
  | "strerror", [e] => return Value.ofString (bytesStr (← sysStrerror (u32 (← expectInt e))))
  | "errno", [] => return .int (signed32 (← sysErrno ()))
  | "reseterrno", [] => let _ ← sysSetErrno 0; return .void
  | "getpwd", [] => return Value.ofString (bytesStr (← sysGetcwd ()))
  | "setpwd", [s] =>
    if (← sysChdir (strBytes (← strOf s))) == 0 then return .int 0
    else rtErr "cannot change to the directory"
  | "realpath", [s] => return Value.ofString (bytesStr (← sysRealpath (strBytes (← strOf s))))
  | "sleep", [x] =>
    match (← resolveUnion x) with
    | .union (.int _) (.int k) => return .int (signed32 (← sysSleep (u32 k.natAbs)))
    | .union (.real _) (.real r) =>
      IO.sleep (Float.abs r * 1000.0).toUInt32
      return .int 0
    | _ => return .int (-1)
  | "rows", [] => return .int 24     -- a68g's defaults when standard output is not a terminal
  | "columns", [] => return .int 500
  | "a68gargc", [] => return .int (← read).args.size
  | "a68gargv", [i] => callBuiltin "argv" [i]
  | "wallclock", [] | "wallseconds", [] | "walltime", [] => return .real (← sysWalltime ())
  | "nan", [] => return .real (0.0 / 0.0)
  | "inf", [] | "infinity", [] | "plusinf", [] | "plusinfinity", [] => return .real (1.0 / 0.0)
  | "minusinf", [] | "minusinfinity", [] => return .real (-1.0 / 0.0)
  | "isfinite", [x] => do let r ← expectReal x; return .bool (!r.isNaN && !r.isInf)
  | "isinf", [x] | "isinfinite", [x] => do let r ← expectReal x; return .bool r.isInf
  | "isplusinf", [x] => do let r ← expectReal x; return .bool (r.isInf && r > 0)
  | "isminusinf", [x] => do let r ← expectReal x; return .bool (r.isInf && r < 0)
  | "isnan", [x] => do let r ← expectReal x; return .bool r.isNaN
  | "resetpossible", [f] | "rewindpossible", [f] | "setpossible", [f] | "binpossible", [f] =>
    return .bool ([3, 4].contains (← fileChannel f))
  | "getpossible", [f] => return .bool ([1, 3, 4].contains (← fileChannel f))
  | "putpossible", [f] => return .bool ([0, 2, 3, 4].contains (← fileChannel f))
  | "reidfpossible", [_] | "drawpossible", [_] => return .bool false
  | "compressible", [_] => return .bool true
  | "idf", [f] =>
    let fs ← getFile (← fileIdOf f)
    if fs.name.isEmpty then rtErr "attempt to use NIL" else return Value.ofString fs.name
  | "term", [f] =>
    let fs ← getFile (← fileIdOf f)
    return Value.ofString (String.ofList (fs.term.map Char.ofNat))
  | "eof", [f] | "endoffile", [f] | "eoln", [f] | "endofline", [f] =>
    let fid ← fileIdOf f
    let fs ← getFile fid
    if fs.writing && fid != 1 then rtErr "the file is in write mood"
    if !(fs.reading || fid == 1 || fs.fd ≥ 0) then rtErr "the file is in undetermined mood"
    if name == "eof" || name == "endoffile" then return .bool (← atEnd fid)
    if (← atEnd fid) then logicalEnd fid
    return .bool ((← peekChar fid) == some 10)
  | "set", [f, n] | "seek", [f, n] =>
    -- a68g `genie_set` moves relative to the current position
    let fid ← fileIdOf f
    if !([3, 4].contains (← fileChannel f)) then rtErr "the channel does not allow setting the file"
    let k ← expectInt n
    let fs ← loadFile fid
    let np : Int := fs.pos + k
    if fs.buf.size == 0 || np < 0 || np ≥ fs.buf.size then
      match fs.onEnd with
      | some h =>
        match (← callValue h [.file fid]) with
        | .bool true => return .int np
        | _ => rtErr "the file has ended"
      | none => rtErr "the file has ended"
    setFile fid { fs with pos := np.toNat }
    return .int np
  | "puts", [s, row] | "string", [s, row] | "putsf", [s, row] | "stringf", [s, row] =>
    let (_, _, es) ← expectRow row
    if es.size > 0 then
      let text ← withStringFile fun fid => do
        if name == "puts" || name == "string" then
          for e in es do
            match e with
            | .union m v => printValue fid m v
            | _ => rtErr "internal: put argument"
        else printf fid es.toList
      writeRef s (Value.ofString text)
    return (if name == "string" || name == "stringf" then s else .void)
  | "gets", [s, row] | "getsf", [s, row] =>
    let (_, _, es) ← expectRow row
    let fid ← (← read).files.modifyGet fun fs => (fs.size, fs.push { assoc := some s, channel := 4 })
    if name == "gets" then getItems fid es else getfItems fid es
    (← read).files.modify fun fs => if fs.size == fid + 1 then fs.pop else fs
    return .void
  | "readline", [] => do let s ← readLineStr 1; skipLine 1; return Value.ofString s
  | "getbin", [f, row] | "putbin", [f, row] =>
    let fid ← fileIdOf f
    let (_, _, es) ← expectRow row
    for e in es do
      match e with
      | .union m v => if name == "getbin" then readBin fid m v else writeBin fid m v
      | _ => rtErr "internal: binary transput argument"
    return .void
  | "readbin", [row] => callBuiltin "getbin" [.file 3, row]
  | "printbin", [row] | "writebin", [row] => callBuiltin "putbin" [.file 3, row]
  | "onopenerror", [_, _] => return .void
  | fn, [x] =>
    if ["sqrt","exp","ln","log","log10","log2","exp2","sin","cos","tan","arcsin","arccos","arctan",
        "asin","acos","atan","sinh","cosh","tanh","arcsinh","arccosh","arctanh","cbrt","curt",
        "longsqrt","longexp","longln","longlog","longsin","longcos","longtan","longarcsin","longarccos",
        "longarctan","longlongsqrt","longlongexp","longlongln","longlongsin","longlongcos","longlongtan",
        "longlongarctan","longlongarcsin","longlongarccos","gamma","lngamma","erf","erfc","ln1p",
        "sindg","cosdg","tandg","arcsindg","asindg","arccosdg","acosdg","arctandg","atandg",
        "cot","sec","csc","cotdg","secdg","cscdg","cas"].contains fn then
      Value.real <$> mathFn fn (← expectReal x)
    else rtErr s!"unsupported standard procedure {fn}/1"
  | _, _ => rtErr s!"unsupported standard procedure {name}/{args.length}"

/-- The channel of a file (0 stand out, 1 stand in, 2 stand error, 3 stand back, 4 associate). -/
partial def fileChannel (f : Value) : M Nat := do
  let fid ← fileIdOf f
  let fs ← getFile fid
  return if fid ≤ 2 then fid else fs.channel

/-- Run some transput on a fresh string file and give what it wrote (a68g's `puts` and
    `string`); the column of the current formatted line is left as it was. -/
partial def withStringFile (act : Nat → M Unit) : M String := do
  let col ← (← read).col.get
  let cut ← nulCut.get
  nulCut.set false
  let fid ← (← read).files.modifyGet fun fs => (fs.size, fs.push { loaded := true, channel := 4 })
  act fid
  let f ← getFile fid
  (← read).files.modify fun fs => if fs.size == fid + 1 then fs.pop else fs
  (← read).col.set col
  nulCut.set cut
  return bytesStr f.buf

/-- `n` bytes of a file for binary transput. -/
partial def readBinBytes (fid : Nat) (n : Nat) : M ByteArray := do
  let mut b := ByteArray.empty
  for _ in [0:n] do
    match (← readChar fid) with
    | some c => b := b.push c.toUInt8
    | none => logicalEnd fid
  return b

/-- `get bin`: a value laid out as a68g's C object is (INT, BOOL, CHAR and BITS in four bytes,
    REAL in eight, a STRING as its length and its characters). -/
partial def readBin (fid : Nat) (m : Mode) (r : Value) : M Unit := do
  match (← resolveM m) with
  | .ref t =>
    match (← resolveM t), r with
    | .int 0, _ => writeRef r (.int (int32At (← readBinBytes fid 4) 0))
    | .bits 0, _ => writeRef r (.bits (uint32At (← readBinBytes fid 4) 0))
    | .bool, _ => writeRef r (.bool (uint32At (← readBinBytes fid 4) 0 != 0))
    | .char, _ => writeRef r (.char ((← readBinBytes fid 4).get! 0).toNat)
    | .real 0, _ =>
      let b ← readBinBytes fid 8
      writeRef r (.real (Float.ofBits (b.toList.foldr (fun x acc => acc * 256 + x.toUInt64) 0)))
    | .row 1 _ .char, _ =>
      let n := int32At (← readBinBytes fid 4) 0
      writeRef r (Value.ofString (bytesStr (← readBinBytes fid n.toNat)))
    | .struct fs, .ref c path =>
      for i in [0:fs.length] do
        readBin fid (.ref (fs[i]!).2) (.ref c (path ++ [.field i]))
    | .row 1 _ em, _ =>
      let (_, _, es) ← expectRow (← readRef r)
      for i in [0:es.size] do
        readBin fid (.ref em) (← refElem r i)
    | tt, _ => rtErr s!"cannot read a value of mode {modeName tt} in binary"
  | .proc [.ref .file] .void => readInto fid m r
  | _ => rtErr s!"cannot read into a value of mode {modeName m}"

/-- `put bin`, the converse of `readBin`. -/
partial def writeBin (fid : Nat) (m : Mode) (v : Value) : M Unit := do
  match (← resolveM m), v with
  | _, .union m' v' => writeBin fid m' v'
  | .int 0, .int i => fileOut fid (bytesStr (leBytes (i % 4294967296).toNat 4))
  | .bits 0, .bits b => fileOut fid (bytesStr (leBytes b 4))
  | .bool, .bool b => fileOut fid (bytesStr (leBytes (if b then 1 else 0) 4))
  | .char, .char c => fileOut fid (bytesStr (leBytes c 4))
  | .real 0, .real x => fileOut fid (bytesStr (leBytes x.toBits.toNat 8))
  | .row 1 _ .char, .row _ _ _ =>
    let s ← strOf v
    fileOut fid (bytesStr (leBytes s.length 4) ++ s)
  | .struct fs, .struct vs =>
    for (f, x) in fs.zip vs.toList do writeBin fid f.2 x
  | .row _ _ em, .row _ _ es =>
    for e in es do writeBin fid em e
  | .proc [.ref .file] .void, f => printValue fid (.proc [.ref .file] .void) f
  | _, .undef => rtErr s!"attempt to use an uninitialised {modeName m} value"
  | mm, _ => rtErr s!"cannot write a value of mode {modeName mm} in binary"

/-- `evaluate`: parse and elaborate the text in the environment of the call, whose names
    arrive as a format text (`Elab.evaluateScope`), run it, and give its value as `print`
    would write it.  A text that does not parse or elaborate gets a68g's monitor error on
    standard output, and is itself the result. -/
partial def evaluateCall (src : String) (env : Env) (items : List CoreFmt) : M Value := do
  let mut names : List (String × Binding) := []
  let mut ops : List OpBinding := []
  let mut frame : Array Nat := #[]
  let mut tag : String := ""
  for it in items do
    match it with
    | .literal s => tag := s
    | .general [e] =>
      match (← evalFmtExpr env e) with
      | .union m (.ref c []) =>
        let slot := frame.size
        frame := frame.push c
        let n := String.ofList (tag.toList.drop 1)
        let inner := match m with | .ref x => x | x => x
        match tag.toList.head? with
        | some 'o' => ops := ops ++ [{ name := n, mode := inner, depth := 1, slot := slot }]
        | some 'v' => names := names ++ [(n, { mode := m, depth := 1, slot := slot, kind := .var })]
        | _ => names := names ++ [(n, { mode := inner, depth := 1, slot := slot, kind := .ident })]
      | _ => pure ()
    | _ => pure ()
  let failed (msg : String) : M Value := do
    fileOut 0 s!"\na68g: monitor error: {msg}."
    return Value.ofString src
  match A68.parse src with
  | .error e => failed e.msg
  | .ok s =>
    match Elab.elabEvaluate s names ops (← read).modes (← llDigits) with
    | .error e => failed e.msg
    | .ok (core, mode) =>
      let v ← eval [frame, #[]] core
      if (← resolveM mode) == .void then return Value.ofString ""
      return Value.ofString (← withStringFile fun fid => printValue fid mode v)

-- ### Formatted output

/-- Evaluate an expression embedded in a format text.  In a compiled program these are
    `hole` nodes that call straight into the compiled code, so no syntax is walked. -/
partial def evalFmtExpr (env : Env) (e : Core) : M Value := do
  match e with
  | .hole fn idx => fromCompiled (dispatchHole (USize.ofNat fn) (USize.ofNat idx) env)
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
    | .rep n dyn .radix =>
      let k ← match dyn with
        | some e => do pure (← expectInt (← evalFmtExpr env e)).toNat
        | none => pure n
      b := b.addFrame (.radix k)
    | .radix => rtErr "radix frame without a radix"
    | .col => b := { pics := b.flush ++ [.col 1] }
    | .rep n dyn inner =>
      let k ← match dyn with
        | some e => do pure (← expectInt (← evalFmtExpr env e)).toNat
        | none => pure n
      b ← walkFormat env (List.replicate k inner) b
    | .group (.hmark :: rest) =>
      let args ← match rest with
        | [.general as] => as.mapM fun a => do expectInt (← evalFmtExpr env a)
        | _ => pure []
      b := b.addPic (.hgen args)
    | .group (.cpat flags :: rest) =>
      let mut w : Option Int := none
      let mut a : Option Int := none
      for it in rest do
        match it with
        | .rep n dyn marker =>
          let k : Int ← match dyn with
            | some e => do pure (max 0 (← expectInt (← evalFmtExpr env e)))
            | none => pure n
          match marker with
          | .cwidth => w := some k
          | _ => a := some k
        | _ => pure ()
      b := b.addPic (.cpat flags w a)
    | .hmark | .cpat _ | .cwidth | .cafter => pure ()
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
      | .ins s =>
        fileOut fid s
        -- a new line or page purges a68g's buffer (see `nulCut`)
        if s.any (fun c => c == '\n' || c == '\x0c') then nulCut.set false
        i := i + 1
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
  | .compl n, .struct #[re, im] =>
    -- a68g writes a COMPL as two REAL values, each with a pattern of its own
    let st ← writeFormatted fid st (.real n) re
    writeFormatted fid st (.real n) im
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
      if let some rdx := frames.findSome? (fun f => match f with | .radix k => some k | _ => none) then
        match mr, v with
        | .bits _, .bits b =>
          if rdx < 2 || rdx > 16 then rtErr s!"invalid radix {rdx}"
          match convertRadix b rdx (countZD frames) with
          | some s => writeMould fid frames s.toList false
          | none => rtErr s!"error transputting {modeName m} value"
        | _, _ => rtErr s!"cannot transput {modeName m} value with a bits pattern"
        return st'
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
    | .cpat flags w a => writeCPattern fid flags w a mr v; return st'
    | .hgen args =>
      match mr, v with
      | .int n, .int i =>
        let (w, a, e, mult) ← hArguments n args (← llDigits)
        fileOut fid (Numfmt.floatInt i w a e mult)
      | .real n, .real x =>
        let _ ← checkReal x
        let (w, a, e, mult) ← hArguments n args (← llDigits)
        fileOut fid (Numfmt.floatReal x w a e mult)
      -- without arguments `h` writes other values as `g` does
      | .bool, .bool b => if args.isEmpty then fileOut fid (if b then "T" else "F") else rtErr s!"cannot transput {modeName m} value with a general pattern"
      | .char, .char c => if args.isEmpty then fileOutByte fid c.toUInt8 else rtErr s!"cannot transput {modeName m} value with a general pattern"
      | .bits n, .bits b => if args.isEmpty then fileOut fid (Numfmt.printBits b (bitsWidthOf n)) else rtErr s!"cannot transput {modeName m} value with a general pattern"
      | .row 1 _ .char, .row _ _ _ => if args.isEmpty then fileOut fid (← strOf v) else rtErr s!"cannot transput {modeName m} value with a general pattern"
      | _, _ => rtErr s!"cannot transput {modeName m} value with a general pattern"
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
  nulCut.set false

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


/-- One element of the row in cell `c`, as a reference, using the general machinery.
    The compiled runtime falls back to this when the cell does not hold a plain row of
    the expected rank. -/
def sliceGeneral (c : Nat) (rank : UInt32) (i j : Int64) : M Value := do
  let ivs : List IdxVal :=
    if rank == 1 then [.index (.int i.toInt)]
    else [.index (.int i.toInt), .index (.int j.toInt)]
  -- A cell reached this way holds either the row itself, as a variable does, or a name of
  -- one, as a `REF []INT` parameter does; in the second case the subscript applies to the
  -- row the name refers to, which is the only reading that is well typed.
  match (← readCell c) with
  | r@(.ref _ _) => sliceValue r ivs true
  | _ => sliceValue (.ref c []) ivs true

end A68.Interp
