import A68.Interp
import A68.Serial

/-!
# A68.Runtime — the runtime library of compiled programs

`a68lean compile` emits C whose *structure* is compiled — blocks, loops,
conditionals, jumps and one C function per routine text — and whose values are
handled by this library.  It is a library, not an interpreter: nothing here
walks a syntax tree.  The evaluator (`A68.Interp`) shares it, which is why a
compiled program and an interpreted one produce the same bytes: `print`,
`printf`, the operators and the number formatting are one implementation
reached two ways.

The interface is integer-only, so the generated C never touches a Lean object:

* an **environment stack** of frames of cells with a current frame pointer
  (`a68rt_enter` / `a68rt_leave`), as in a68g's frame stack;
* an **operand stack** of values (`a68rt_push_*`, `a68rt_dyop`, …), the
  discipline `A68.Verified.StackMachine` proves the compilation strategy against;
* tables of modes, strings and format texts rebuilt at start-up from a blob the
  compiler embeds in the program (`A68.Serial`).

Two decisions keep the per-operation cost down.  The state lives in separate
references, so an operation touches only what it changes rather than rebuilding
one record; and the entry points are exported as plain functions rather than
`IO` actions, since an `IO` export allocates a result object on every call —
more work than most of the operations themselves.  Errors therefore do not
travel back to C: the runtime reports and exits, as a68g's `exit_genie` does.
-/
namespace A68.RT

open A68.Interp

/-- The whole runtime state.  It is created by `a68rt_boot` at *run time* and held by
    the generated program in a C variable: state kept in a Lean global would be marked
    shared between threads, and every push onto a shared array copies it. -/
structure Sta where
  rt    : Rt
  tab   : Serial.Reader
  stack : IO.Ref (Array Value)
  envs  : IO.Ref (Array (Array Nat))
  saved : IO.Ref (Array (Array (Array Nat)))
  jump  : IO.Ref UInt32

/-- The state, fetched from the C variable the program stores it in.  `Option` keeps the
    declaration trivially non-empty; the C side always supplies `some`. -/
@[extern "a68_get_state"]
opaque getState (u : Unit) : BaseIO (Option Sta)

@[inline] private def state : IO Sta := do
  match (← getState ()) with
  | some s => pure s
  | none => throw (IO.userError "a68 runtime not initialised")

@[inline] private def getRt : IO Rt := do return (← state).rt

/-- Flush pending output, adding the final newline in regression mode. -/
private def flushOut : IO Unit := do
  let rt ← getRt
  let mut o ← rt.out.get
  if rt.regression && o.size > 0 && o[o.size - 1]! != 10 then o := o.push 10
  rt.out.set ByteArray.empty
  let stdout ← IO.getStdout
  stdout.write o
  stdout.flush

private def die (msg : String) : IO α := do
  let rt ← getRt
  flushOut
  let cl ← Interp.compiledLine ()
  let evalLine := (← rt.pos.get).line
  let line := if cl == 0 then evalLine else cl.toNat
  IO.eprintln s!"a68lean: runtime error: {line}: {msg}."
  IO.Process.exit 1

/-- Run a runtime action.  `stop` and errors leave the process; a jump is recorded
    for the generated code, which checks for one after every call. -/
@[inline] private def run (act : M α) (dflt : α) : IO α := do
  let rt ← getRt
  match (← (act.run rt).run) with
  | .ok v => pure v
  | .error (.error msg p) => do
    flushOut
    IO.eprintln s!"a68lean: runtime error: {p.line}: {msg}."
    IO.Process.exit 1
  | .error .stop => do flushOut; IO.Process.exit 0
  | .error (.jump l) => do (← state).jump.set (UInt32.ofNat (l + 1)); pure dflt
  | .error (.fileEnd _) => pure dflt

@[inline] private def go (act : IO Unit) : IO Unit := act

@[inline] private def val (act : IO α) (_dflt : α) : IO α := act

@[inline] private def push (v : Value) : IO Unit := do (← state).stack.modify (·.push v)

@[inline] private def pop : IO Value := do
  let st ← (← state).stack.modifyGet fun s => (s, #[])
  match st.back? with
  | some v => (← state).stack.set st.pop; pure v
  | none => throw (IO.userError "operand stack underflow")

private def popN (n : Nat) : IO (Array Value) := do
  let st ← (← state).stack.modifyGet fun s => (s, #[])
  let k := st.size - n
  let vs := st.extract k st.size
  (← state).stack.set (st.shrink k)
  return vs

@[inline] private def mode (i : UInt32) : IO Mode := do
  return (← state).tab.modes[i.toNat]!

@[inline] private def str (i : UInt32) : IO String := do
  return (← state).tab.strs[i.toNat]!

@[inline] private def curEnv : IO Env := do
  return (← (← state).envs.get).toList.reverse

@[inline] private def cellOf (depth slot : UInt32) : IO Nat := do
  let es ← (← state).envs.get
  let fr := es[es.size - 1 - depth.toNat]!
  return fr[slot.toNat]!

-- ## Start-up and shutdown

@[export a68rt_boot]
def boot (blob : String) (ll : UInt32) (regression : UInt8) (args : Array String) : IO Sta := do
  let rt : Rt := {
    heap := ← IO.mkRef #[], out := ← IO.mkRef ByteArray.empty, pos := ← IO.mkRef {},
    modes := {}, files := ← IO.mkRef #[{}, {}, {}, {}], rng := ← IO.mkRef (Interp.tausSet 1),
    args := args, ll := ll.toNat, regression := regression != 0, col := ← IO.mkRef 0 }
  return { rt := rt, tab := Serial.parse blob, stack := ← IO.mkRef #[], envs := ← IO.mkRef #[],
           saved := ← IO.mkRef #[], jump := ← IO.mkRef 0 }

/-- Flush output and write out any files the program left open. -/
@[export a68rt_finish]
def finish : IO UInt32 :=
  val (do
    flushOut
    let rt ← getRt
    for f in (← rt.files.get) do
      if f.onDisk && f.dirty && f.writing then
        try IO.FS.writeBinFile f.name f.buf catch _ => pure ()
    return (0 : UInt32)) 0

@[export a68rt_line]
def setLine (l : UInt32) : IO Unit := go do
  (← getRt).pos.set { line := l.toNat, col := 0 }

@[export a68rt_stop]
def doStop : IO Unit := go do
  flushOut
  IO.Process.exit 0

-- ## Jumps

@[export a68rt_jump_pending]
def jumpPending : IO UInt32 := val (do (← state).jump.get) 0

@[export a68rt_jump_clear]
def jumpClear : IO Unit := go do ((← state).jump.set 0)

@[export a68rt_raise_jump]
def raiseJump (l : UInt32) : IO Unit := go do ((← state).jump.set (l + 1))

-- ## Environments

@[export a68rt_enter]
def enter (size : UInt32) : IO Unit := go do
  let rt ← getRt
  let mut frame : Array Nat := Array.mkEmpty size.toNat
  let mut heap ← rt.heap.modifyGet fun h => (h, #[])
  for _ in [0:size.toNat] do
    frame := frame.push heap.size
    heap := heap.push .undef
  rt.heap.set heap
  (← state).envs.modify (·.push frame)

/-- Enter a frame whose first `nargs` cells come from the operand stack. -/
@[export a68rt_enter_args]
def enterArgs (size nargs : UInt32) : IO Unit := go do
  let args ← popN nargs.toNat
  let rt ← getRt
  let mut frame : Array Nat := Array.mkEmpty size.toNat
  let mut heap ← rt.heap.modifyGet fun h => (h, #[])
  for i in [0:size.toNat] do
    frame := frame.push heap.size
    heap := heap.push (if i < nargs.toNat then args[i]! else .undef)
  rt.heap.set heap
  (← state).envs.modify (·.push frame)

@[export a68rt_leave]
def leave : IO Unit := go do ((← state).envs.modify (·.pop))

@[export a68rt_env_depth]
def envDepth : IO UInt32 := val (do return UInt32.ofNat (← (← state).envs.get).size) 0

@[export a68rt_env_truncate]
def envTruncate (d : UInt32) : IO Unit := go do ((← state).envs.modify (·.shrink d.toNat))

/-- Enter the environment captured by a compiled procedure, saving the current one. -/
@[export a68rt_env_set]
def envSet (env : Env) : IO Unit := go do
  (← state).saved.modify (·.push (← (← state).envs.get))
  (← state).envs.set env.reverse.toArray

@[export a68rt_env_restore]
def envRestore : IO Unit := go do
  let sv ← (← state).saved.modifyGet fun s => (s, #[])
  match sv.back? with
  | some e => (← state).envs.set e; (← state).saved.set sv.pop
  | none => throw (IO.userError "environment stack underflow")

-- ## Operand stack

@[export a68rt_stack_depth]
def stackDepth : IO UInt32 := val (do return UInt32.ofNat (← (← state).stack.get).size) 0

@[export a68rt_stack_truncate]
def stackTruncate (d : UInt32) : IO Unit := go do ((← state).stack.modify (·.shrink d.toNat))

@[export a68rt_push_int]
def pushInt (v : Int64) : IO Unit := go (push (.int v.toInt))

@[export a68rt_push_bigint]
def pushBigInt (i : UInt32) : IO Unit := go do
  let s ← str i
  push (.int (if s.startsWith "-" then -((String.ofList (s.toList.drop 1)).toNat! : Int)
              else (s.toNat! : Int)))

@[export a68rt_push_real]
def pushReal (v : Float) : IO Unit := go (push (.real v))

@[export a68rt_push_bool]
def pushBool (v : UInt8) : IO Unit := go (push (.bool (v != 0)))

@[export a68rt_push_char]
def pushChar (v : UInt32) : IO Unit := go (push (.char v.toNat))

@[export a68rt_push_bits]
def pushBits (v : UInt64) : IO Unit := go (push (.bits v.toNat))

@[export a68rt_push_str]
def pushStr (i : UInt32) : IO Unit := go do push (Value.ofString (← str i))

@[export a68rt_push_undef]
def pushUndef : IO Unit := go (push .undef)

@[export a68rt_push_nil]
def pushNil : IO Unit := go (push .nil)

@[export a68rt_push_void]
def pushVoid : IO Unit := go (push .void)

@[export a68rt_push_builtin]
def pushBuiltin (i : UInt32) : IO Unit := go do push (.builtin (← str i))

@[export a68rt_push_file]
def pushFile (i : UInt32) : IO Unit := go (push (.file i.toNat))

/-- The value a `SKIP` of this mode denotes. -/
@[export a68rt_push_skip]
def pushSkip (m : UInt32) : IO Unit := go do
  push (← run (Interp.defaultOf (← mode m)) .undef)

@[export a68rt_pop]
def popOne : IO Unit := go do let _ ← pop

@[export a68rt_dup]
def dup : IO Unit := go do
  let s ← (← state).stack.get
  match s.back? with
  | some v => push v
  | none => throw (IO.userError "operand stack underflow")

/-- Drop the value below the top of the stack (this is how a block keeps its result). -/
@[export a68rt_nip]
def nip : IO Unit := go do
  let s ← (← state).stack.modifyGet fun s => (s, #[])
  let n := s.size
  if n < 2 then throw (IO.userError "nip on a short stack")
  let top := s[n-1]!
  (← state).stack.set ((s.shrink (n-2)).push top)

@[export a68rt_push_cell]
def pushCell (depth slot : UInt32) : IO Unit := go do
  let c ← cellOf depth slot
  let v ← run (Interp.readCell c) .undef
  match v with
  | .undef => die "attempt to use an uninitialised value"
  | _ => push v

@[export a68rt_push_ref]
def pushRef (depth slot : UInt32) : IO Unit := go do
  push (.ref (← cellOf depth slot) [])

@[export a68rt_store]
def store (depth slot : UInt32) : IO Unit := go do
  let v ← pop
  let c ← cellOf depth slot
  run (Interp.writeCell c v) ()

@[export a68rt_bind_cell]
def bindCell (depth slot : UInt32) : IO Unit := go do
  let v ← pop
  let c ← cellOf depth slot
  run (Interp.writeCell c v) ()

@[export a68rt_set_int]
def setInt (depth slot : UInt32) (v : Int64) : IO Unit := go do
  let c ← cellOf depth slot
  run (Interp.writeCell c (.int v.toInt)) ()

/-- Take the top of the stack as the result of a compiled procedure. -/
@[export a68rt_take_top]
def takeTop : IO Value := do
  let st ← (← state).stack.modifyGet fun s => (s, #[])
  match st.back? with
  | some v => (← state).stack.set st.pop; pure v
  | none => throw (IO.userError "operand stack underflow")

@[export a68rt_push_array]
def pushArray (a : Array Value) : IO Unit := go do
  for v in a do push v

-- ## Native scalar access
--
-- These are the entry points the compiled code uses for values of primitive mode: they
-- read and write a cell in a native C type, so an expression like `s + i * 3` becomes C
-- arithmetic with nothing boxed and nothing pushed on the operand stack.

@[export a68rt_cell_int]
def cellInt (depth slot : UInt32) : IO Int64 := do
  match (← run (Interp.readCell (← cellOf depth slot)) .undef) with
  | .int n => return Int64.ofInt n
  | .undef => die "attempt to use an uninitialised INT value"
  | _ => throw (IO.userError "INT expected")

@[export a68rt_cell_real]
def cellReal (depth slot : UInt32) : IO Float := do
  match (← run (Interp.readCell (← cellOf depth slot)) .undef) with
  | .real x => return x
  | .int n => return Float.ofInt n
  | .undef => die "attempt to use an uninitialised REAL value"
  | _ => throw (IO.userError "REAL expected")

@[export a68rt_cell_bool]
def cellBool (depth slot : UInt32) : IO UInt8 := do
  match (← run (Interp.readCell (← cellOf depth slot)) .undef) with
  | .bool b => return (if b then 1 else 0)
  | .undef => die "attempt to use an uninitialised BOOL value"
  | _ => throw (IO.userError "BOOL expected")

@[export a68rt_cell_char]
def cellChar (depth slot : UInt32) : IO UInt32 := do
  match (← run (Interp.readCell (← cellOf depth slot)) .undef) with
  | .char c => return UInt32.ofNat c
  | .undef => die "attempt to use an uninitialised CHAR value"
  | _ => throw (IO.userError "CHAR expected")

@[export a68rt_cell_bits]
def cellBits (depth slot : UInt32) : IO UInt64 := do
  match (← run (Interp.readCell (← cellOf depth slot)) .undef) with
  | .bits b => return UInt64.ofNat b
  | .undef => die "attempt to use an uninitialised BITS value"
  | _ => throw (IO.userError "BITS expected")

@[export a68rt_set_cell_int]
def setCellInt (depth slot : UInt32) (v : Int64) : IO Unit := do
  run (Interp.writeCell (← cellOf depth slot) (.int v.toInt)) ()

@[export a68rt_set_cell_real]
def setCellReal (depth slot : UInt32) (v : Float) : IO Unit := do
  run (Interp.writeCell (← cellOf depth slot) (.real v)) ()

@[export a68rt_set_cell_bool]
def setCellBool (depth slot : UInt32) (v : UInt8) : IO Unit := do
  run (Interp.writeCell (← cellOf depth slot) (.bool (v != 0))) ()

@[export a68rt_set_cell_char]
def setCellChar (depth slot : UInt32) (v : UInt32) : IO Unit := do
  run (Interp.writeCell (← cellOf depth slot) (.char v.toNat)) ()

@[export a68rt_set_cell_bits]
def setCellBits (depth slot : UInt32) (v : UInt64) : IO Unit := do
  run (Interp.writeCell (← cellOf depth slot) (.bits v.toNat)) ()

@[export a68rt_pop_real]
def popReal : IO Float :=
  val (do
    match (← pop) with
    | .real x => return x
    | .int n => return Float.ofInt n
    | .undef => die "attempt to use an uninitialised REAL value"
    | _ => throw (IO.userError "REAL expected")) 0.0

@[export a68rt_pop_char]
def popChar : IO UInt32 :=
  val (do
    match (← pop) with
    | .char c => return UInt32.ofNat c
    | .undef => die "attempt to use an uninitialised CHAR value"
    | _ => throw (IO.userError "CHAR expected")) 0

@[export a68rt_pop_bits]
def popBits : IO UInt64 :=
  val (do
    match (← pop) with
    | .bits b => return UInt64.ofNat b
    | .undef => die "attempt to use an uninitialised BITS value"
    | _ => throw (IO.userError "BITS expected")) 0

-- ## Row elements
--
-- `a[i]` in a loop is the other shape that has to be cheap.  A declared row lives
-- directly in its cell, so the element can be reached without building a reference and
-- without going through the general slicing machinery; anything else falls back to it.

@[inline] private def elemOffset (l u : Array Int) (rank : UInt32) (i j : Int64)
    : Interp.M Nat := do
  let lo := l[0]!
  let hi := u[0]!
  let a : Int := i.toInt
  if a < lo || a > hi then Interp.rtErr s!"index {a} out of bounds [{lo}:{hi}]"
  if rank == 1 then return (a - lo).toNat
  let lo1 := l[1]!
  let hi1 := u[1]!
  let b : Int := j.toInt
  if b < lo1 || b > hi1 then Interp.rtErr s!"index {b} out of bounds [{lo1}:{hi1}]"
  return ((a - lo) * (hi1 - lo1 + 1) + (b - lo1)).toNat

private def elemOf (c : Nat) (rank : UInt32) (i j : Int64) : Interp.M Value := do
  match (← Interp.readCell c) with
  | .row l u es =>
    if l.size == rank.toNat then
      let o ← elemOffset l u rank i j
      -- the index was checked against the bounds; `es[o]?` would allocate an `Option`
      -- on every element read, which in a loop is more work than the read itself
      if h : o < es.size then return es[o]
      else Interp.rtErr "internal: element offset out of range"
    else Interp.sliceGeneral c rank i j >>= Interp.readRef
  | _ => Interp.sliceGeneral c rank i j >>= Interp.readRef

private def setElemOf (c : Nat) (rank : UInt32) (i j : Int64) (nv : Value) : Interp.M Unit := do
  match (← Interp.takeCell c) with
  | .row l u es =>
    if l.size == rank.toNat then
      -- the cell was emptied, so the element array is uniquely owned and updates in place
      let o ← try elemOffset l u rank i j
              catch e => do Interp.writeCell c (.row l u es); throw e
      Interp.writeCell c (.row l u (es.set! o nv))
    else
      Interp.writeCell c (.row l u es)
      (← Interp.sliceGeneral c rank i j) |> (Interp.writeRef · nv)
  | old =>
    Interp.writeCell c old
    (← Interp.sliceGeneral c rank i j) |> (Interp.writeRef · nv)

@[inline] private def rowCell (depth slot : UInt32) : IO Nat := cellOf depth slot

@[export a68rt_row_int]
def rowInt (depth slot rank : UInt32) (i j : Int64) : IO Int64 := do
  let c ← rowCell depth slot
  match (← run (elemOf c rank i j) .undef) with
  | .int n => return Int64.ofInt n
  | .undef => die "attempt to use an uninitialised INT value"
  | _ => throw (IO.userError "INT expected")

@[export a68rt_row_real]
def rowReal (depth slot rank : UInt32) (i j : Int64) : IO Float := do
  let c ← rowCell depth slot
  match (← run (elemOf c rank i j) .undef) with
  | .real x => return x
  | .int n => return Float.ofInt n
  | .undef => die "attempt to use an uninitialised REAL value"
  | _ => throw (IO.userError "REAL expected")

@[export a68rt_row_bool]
def rowBool (depth slot rank : UInt32) (i j : Int64) : IO UInt8 := do
  let c ← rowCell depth slot
  match (← run (elemOf c rank i j) .undef) with
  | .bool b => return (if b then 1 else 0)
  | .undef => die "attempt to use an uninitialised BOOL value"
  | _ => throw (IO.userError "BOOL expected")

@[export a68rt_row_char]
def rowChar (depth slot rank : UInt32) (i j : Int64) : IO UInt32 := do
  let c ← rowCell depth slot
  match (← run (elemOf c rank i j) .undef) with
  | .char ch => return UInt32.ofNat ch
  | .undef => die "attempt to use an uninitialised CHAR value"
  | _ => throw (IO.userError "CHAR expected")

@[export a68rt_row_bits]
def rowBits (depth slot rank : UInt32) (i j : Int64) : IO UInt64 := do
  let c ← rowCell depth slot
  match (← run (elemOf c rank i j) .undef) with
  | .bits b => return UInt64.ofNat b
  | .undef => die "attempt to use an uninitialised BITS value"
  | _ => throw (IO.userError "BITS expected")

@[export a68rt_set_row_int]
def setRowInt (depth slot rank : UInt32) (i j : Int64) (v : Int64) : IO Unit := do
  let c ← rowCell depth slot
  run (setElemOf c rank i j (.int v.toInt)) ()

@[export a68rt_set_row_real]
def setRowReal (depth slot rank : UInt32) (i j : Int64) (v : Float) : IO Unit := do
  let c ← rowCell depth slot
  run (setElemOf c rank i j (.real v)) ()

@[export a68rt_set_row_bool]
def setRowBool (depth slot rank : UInt32) (i j : Int64) (v : UInt8) : IO Unit := do
  let c ← rowCell depth slot
  run (setElemOf c rank i j (.bool (v != 0))) ()

@[export a68rt_set_row_char]
def setRowChar (depth slot rank : UInt32) (i j : Int64) (v : UInt32) : IO Unit := do
  let c ← rowCell depth slot
  run (setElemOf c rank i j (.char v.toNat)) ()

@[export a68rt_set_row_bits]
def setRowBits (depth slot rank : UInt32) (i j : Int64) (v : UInt64) : IO Unit := do
  let c ← rowCell depth slot
  run (setElemOf c rank i j (.bits v.toNat)) ()

-- ## Structure fields
--
-- `f OF s`, `f OF a[i]` and `f OF p` (`p` a `REF`) all reach one field of a structure
-- that a cell holds, or that is an element of a row a cell holds, or that a cell points
-- at.  Compiled step by step these build a reference on the operand stack one selector
-- at a time and then dereference it; here the whole chain is one call, which yields the
-- field's value directly — in a native C type where the field's mode is primitive.
--
-- `spec` describes the chain: bits 0-1 the rank of the subscript (0 = none), bit 2
-- whether the cell holds the structure itself or a `REF` to it, bits 8-11 how many
-- fields follow.  `fields` packs the field indices, one byte each, innermost first.
-- Anything the shape does not fit — a row of the wrong rank, a view, a multiple
-- selection — falls back to the general machinery, which is what reports its errors.

@[inline] private def specRank (spec : UInt32) : UInt32 := spec &&& 3
@[inline] private def specViaRef (spec : UInt32) : Bool := spec &&& 4 != 0
@[inline] private def specNF (spec : UInt32) : Nat := ((spec >>> 8) &&& 15).toNat
@[inline] private def specField (fields : UInt32) (k : Nat) : Nat :=
  ((fields >>> (UInt32.ofNat (8 * k))) &&& 255).toNat

@[inline] private def selIdx (rank : UInt32) (i j : Int64) : List IdxVal :=
  if rank == 1 then [.index (.int i.toInt)]
  else [.index (.int i.toInt), .index (.int j.toInt)]

/-- The value the chain designates.  The steps match, one for one, what pushing the cell
    or its reference, slicing and selecting would have done, so the errors are the same. -/
private def selRead (c : Nat) (spec : UInt32) (i j : Int64) (fields : UInt32)
    : Interp.M Value := do
  let mut v ← Interp.readCell c
  if specViaRef spec then
    v ← (match v with
      | .undef => Interp.rtErr "attempt to use an uninitialised value"
      | .nil => Interp.rtErr "attempt to select from NIL"
      | r => Interp.readRef r)
  let rank := specRank spec
  if rank != 0 then
    v ← (match v with
      | .row l u es =>
        if l.size == rank.toNat then do
          let o ← elemOffset l u rank i j
          if h : o < es.size then pure es[o]
          else Interp.rtErr "internal: element offset out of range"
        else Interp.sliceValue (.row l u es) (selIdx rank i j) false
      | other => Interp.sliceValue other (selIdx rank i j) false)
  for k in [0:specNF spec] do
    let f := specField fields k
    v ← (match v with
      | .struct fs =>
        if h : f < fs.size then pure fs[f]
        else Interp.rtErr "internal: field index out of range"
      | other => Interp.readPath other [.field f])
  return v

/-- The reference the chain designates, for an assignment. -/
private def selRef (c : Nat) (spec : UInt32) (i j : Int64) (fields : UInt32)
    : Interp.M Value := do
  let mut r : Value ←
    if specViaRef spec then
      match (← Interp.readCell c) with
      | .undef => Interp.rtErr "attempt to use an uninitialised value"
      | .nil => Interp.rtErr "attempt to select from NIL"
      | v => pure v
    else pure (.ref c [])
  let rank := specRank spec
  if rank != 0 then
    -- the common shape: a plain row of the expected rank held directly in the cell.  The
    -- row value is dropped again before the assignment, so the element array stays
    -- uniquely owned and the update below is in place.
    let off : Option Nat ← (match r with
      | .ref bc [] => do
        match (← Interp.readCell bc) with
        | .row l u _ => if l.size == rank.toNat then some <$> elemOffset l u rank i j else pure none
        | _ => pure none
      | _ => pure none)
    match off, r with
    | some o, .ref bc _ => r := .ref bc [.elem o]
    | _, _ => r ← Interp.sliceValue r (selIdx rank i j) true
  for k in [0:specNF spec] do
    let f := specField fields k
    r ← (match r with
      | .ref bc p => pure (.ref bc (p ++ [.field f]))
      | .nil => Interp.rtErr "attempt to select from NIL"
      | _ => Interp.rtErr "internal: select via non-REF")
  return r

@[inline] private def selWrite (c : Nat) (spec : UInt32) (i j : Int64) (fields : UInt32)
    (nv : Value) : Interp.M Unit := do
  Interp.writeRef (← selRef c spec i j fields) nv

@[export a68rt_sel_push]
def selPush (depth slot spec : UInt32) (i j : Int64) (fields : UInt32) : IO Unit := go do
  let c ← cellOf depth slot
  match (← run (selRead c spec i j fields) .undef) with
  | .undef => die "attempt to use an uninitialised value"
  | v => push v

@[export a68rt_sel_int]
def selInt (depth slot spec : UInt32) (i j : Int64) (fields : UInt32) : IO Int64 := do
  let c ← cellOf depth slot
  match (← run (selRead c spec i j fields) .undef) with
  | .int n => return Int64.ofInt n
  | .undef => die "attempt to use an uninitialised INT value"
  | _ => throw (IO.userError "INT expected")

@[export a68rt_sel_real]
def selReal (depth slot spec : UInt32) (i j : Int64) (fields : UInt32) : IO Float := do
  let c ← cellOf depth slot
  match (← run (selRead c spec i j fields) .undef) with
  | .real x => return x
  | .int n => return Float.ofInt n
  | .undef => die "attempt to use an uninitialised REAL value"
  | _ => throw (IO.userError "REAL expected")

@[export a68rt_sel_bool]
def selBool (depth slot spec : UInt32) (i j : Int64) (fields : UInt32) : IO UInt8 := do
  let c ← cellOf depth slot
  match (← run (selRead c spec i j fields) .undef) with
  | .bool b => return (if b then 1 else 0)
  | .undef => die "attempt to use an uninitialised BOOL value"
  | _ => throw (IO.userError "BOOL expected")

@[export a68rt_sel_char]
def selChar (depth slot spec : UInt32) (i j : Int64) (fields : UInt32) : IO UInt32 := do
  let c ← cellOf depth slot
  match (← run (selRead c spec i j fields) .undef) with
  | .char ch => return UInt32.ofNat ch
  | .undef => die "attempt to use an uninitialised CHAR value"
  | _ => throw (IO.userError "CHAR expected")

@[export a68rt_sel_bits]
def selBits (depth slot spec : UInt32) (i j : Int64) (fields : UInt32) : IO UInt64 := do
  let c ← cellOf depth slot
  match (← run (selRead c spec i j fields) .undef) with
  | .bits b => return UInt64.ofNat b
  | .undef => die "attempt to use an uninitialised BITS value"
  | _ => throw (IO.userError "BITS expected")

@[export a68rt_set_sel_int]
def setSelInt (depth slot spec : UInt32) (i j : Int64) (fields : UInt32) (v : Int64) : IO Unit := do
  let c ← cellOf depth slot
  run (selWrite c spec i j fields (.int v.toInt)) ()

@[export a68rt_set_sel_real]
def setSelReal (depth slot spec : UInt32) (i j : Int64) (fields : UInt32) (v : Float) : IO Unit := do
  let c ← cellOf depth slot
  run (selWrite c spec i j fields (.real v)) ()

@[export a68rt_set_sel_bool]
def setSelBool (depth slot spec : UInt32) (i j : Int64) (fields : UInt32) (v : UInt8) : IO Unit := do
  let c ← cellOf depth slot
  run (selWrite c spec i j fields (.bool (v != 0))) ()

@[export a68rt_set_sel_char]
def setSelChar (depth slot spec : UInt32) (i j : Int64) (fields : UInt32) (v : UInt32) : IO Unit := do
  let c ← cellOf depth slot
  run (selWrite c spec i j fields (.char v.toNat)) ()

@[export a68rt_set_sel_bits]
def setSelBits (depth slot spec : UInt32) (i j : Int64) (fields : UInt32) (v : UInt64) : IO Unit := do
  let c ← cellOf depth slot
  run (selWrite c spec i j fields (.bits v.toNat)) ()

-- ## Appending to a row variable
--
-- `s +:= c` is how a string is built up.  Reached the general way it pushes a reference,
-- boxes the character, rows it, and rebuilds the whole string; here it is one call that
-- appends to the element array in place.  A cell that does not hold a one-dimensional row
-- starting at 1 falls back to the operator itself, which is what reports the error.

@[inline] private def appendFallback (c : Nat) (v : Value) : Interp.M Unit := do
  let _ ← Interp.dyadic "+:=" (.ref Mode.string) Mode.string (.ref c []) v
  pure ()

@[export a68rt_append_char]
def appendChar (depth slot ch : UInt32) : IO Unit := go do
  let c ← cellOf depth slot
  run (do
    if !(← Interp.appendOne c (.char ch.toNat)) then
      appendFallback c (.row #[1] #[1] #[.char ch.toNat])) ()

/-- `s +:= t`, with the row to append on the operand stack. -/
@[export a68rt_append]
def appendTop (depth slot : UInt32) : IO Unit := go do
  let v ← pop
  let c ← cellOf depth slot
  run (do
    match (← Interp.appendInPlace (.ref c []) v) with
    | some _ => pure ()
    | none => appendFallback c v) ()

/-- A promoted C variable read before it was assigned. -/
@[export a68rt_undef_error]
def undefError (kind : UInt32) : IO Unit := do
  die (match kind with
       | 0 => "attempt to use an uninitialised INT value"
       | 1 => "attempt to use an uninitialised REAL value"
       | 2 => "attempt to use an uninitialised BOOL value"
       | 3 => "attempt to use an uninitialised CHAR value"
       | _ => "attempt to use an uninitialised BITS value")

/-- Report a failure detected by native arithmetic in compiled code. -/
@[export a68rt_arith_error]
def arithError (kind : UInt32) : IO Unit := do
  die (match kind with
       | 0 => "INT value overflow, result too large"
       | 1 => "INT division by zero"
       | 2 => "infinite REAL value"
       | 3 => "REAL value is not a number"
       | 4 => "INT value out of bounds"
       | _ => "REPR argument out of range")

-- ## Reading scalars back into C

@[export a68rt_pop_int]
def popInt : IO Int64 :=
  val (do
    match (← pop) with
    | .int n => return Int64.ofInt n
    | .undef => die "attempt to use an uninitialised INT value"
    | _ => throw (IO.userError "INT expected")) 0

@[export a68rt_pop_bool]
def popBool : IO UInt8 :=
  val (do
    match (← pop) with
    | .bool b => return (if b then (1 : UInt8) else 0)
    | .undef => die "attempt to use an uninitialised BOOL value"
    | _ => throw (IO.userError "BOOL expected")) 0

-- ## Operations

@[export a68rt_deref]
def deref : IO Unit := go do
  let r ← pop
  let v ← run (Interp.readRef r) .undef
  match v with
  | .undef => die "attempt to use an uninitialised value"
  | _ => push v

@[export a68rt_deproc]
def deproc : IO Unit := go do
  let f ← pop
  push (← run (Interp.callValue f []) .undef)

@[export a68rt_widen]
def widen (src dst : UInt32) : IO Unit := go do
  let v ← pop
  push (← run (Interp.widenValue (← mode src) (← mode dst) v) .undef)

@[export a68rt_row_of]
def rowOf : IO Unit := go do
  let v ← pop
  match v with
  | .ref _ _ => push v
  | _ => push (.row #[1] #[1] #[v])

@[export a68rt_unite]
def unite (m : UInt32) : IO Unit := go do
  let v ← pop
  push (.union (← mode m) v)

@[export a68rt_voiding]
def voiding : IO Unit := go do
  let _ ← pop
  push .void

@[export a68rt_assign]
def assign (flex : UInt8) : IO Unit := go do
  let v ← pop
  let d ← pop
  run (Interp.assignTo d v (flex != 0)) ()
  push d

@[export a68rt_ident_rel]
def identRel (isnt : UInt8) : IO Unit := go do
  let b ← pop
  let a ← pop
  let same := match a, b with
    | .ref c1 p1, .ref c2 p2 => c1 == c2 && p1 == p2
    | .nil, .nil => true
    | _, _ => false
  push (.bool (if isnt != 0 then !same else same))

@[export a68rt_dyop]
def dyop (op m1 m2 : UInt32) : IO Unit := go do
  let r ← pop
  let l ← pop
  push (← run (Interp.dyadic (← str op) (← mode m1) (← mode m2) l r) .undef)

@[export a68rt_monop]
def monop (op m : UInt32) : IO Unit := go do
  let v ← pop
  push (← run (Interp.monadic (← str op) (← mode m) v) .undef)

@[export a68rt_call]
def call (nargs : UInt32) : IO Unit := go do
  let args ← popN nargs.toNat
  let f ← pop
  push (← run (Interp.callValue f args.toList) .undef)

@[export a68rt_select]
def select (idx : UInt32) (viaRef : UInt8) : IO Unit := go do
  let v ← pop
  if viaRef != 0 then
    match v with
    | .ref c path => push (.ref c (path ++ [.field idx.toNat]))
    | .nil => die "attempt to select from NIL"
    | _ => throw (IO.userError "select via non-REF")
  else
    match v with
    | .struct fs => push fs[idx.toNat]!
    | .row _ _ _ => push (← run (Interp.readPath v [.field idx.toNat]) .undef)
    | _ => throw (IO.userError "select from non-struct")

/-- Slice.  The indexer values were pushed in order; `kinds` holds four bits per
    indexer: bit 0 = it is a trim, bit 1 = a lower bound was given, bit 2 = an upper
    bound was given, bit 3 = an `AT` was given. -/
@[export a68rt_slice]
def slice (nidx : UInt32) (kinds : UInt64) (viaRef : UInt8) : IO Unit := go do
  let nvals := Id.run do
    let mut c := 0
    for i in [0:nidx.toNat] do
      let k := (kinds >>> (UInt64.ofNat (4 * i))) &&& 15
      if k &&& 1 == 0 then c := c + 1
      else
        if k &&& 2 != 0 then c := c + 1
        if k &&& 4 != 0 then c := c + 1
        if k &&& 8 != 0 then c := c + 1
    return c
  let vals ← popN nvals
  let base ← pop
  let mut idx : List IdxVal := []
  let mut k := 0
  for i in [0:nidx.toNat] do
    let kind := (kinds >>> (UInt64.ofNat (4 * i))) &&& 15
    if kind &&& 1 == 0 then
      idx := idx ++ [.index vals[k]!]
      k := k + 1
    else
      let lo := if kind &&& 2 != 0 then some vals[k]! else none
      if kind &&& 2 != 0 then k := k + 1
      let hi := if kind &&& 4 != 0 then some vals[k]! else none
      if kind &&& 4 != 0 then k := k + 1
      let at_ := if kind &&& 8 != 0 then some vals[k]! else none
      if kind &&& 8 != 0 then k := k + 1
      idx := idx ++ [.trim lo hi at_]
  push (← run (Interp.sliceValue base idx (viaRef != 0)) .undef)

@[export a68rt_new_row]
def newRow (ndims : UInt32) (flex : UInt8) : IO Unit := go do
  let _ := flex
  let bounds ← popN (2 * ndims.toNat)
  let init ← pop
  let mut ls : Array Int := #[]
  let mut us : Array Int := #[]
  for i in [0:ndims.toNat] do
    match bounds[2*i]!, bounds[2*i+1]! with
    | .int l, .int u => ls := ls.push l; us := us.push u
    | _, _ => throw (IO.userError "row bounds must be INT")
  push (.row ls us (Array.replicate (Interp.rowSize ls us) init))

@[export a68rt_gen]
def gen : IO Unit := go do
  let v ← pop
  push (.ref (← run (Interp.alloc v) 0) [])

@[export a68rt_collateral]
def collateral (n : UInt32) (isStruct : UInt8) (dims : UInt32) : IO Unit := go do
  let vs ← popN n.toNat
  if isStruct != 0 then push (.struct vs)
  else if dims.toNat ≤ 1 then push (.row #[1] #[vs.size] vs)
  else
    match vs[0]? with
    | none => push (.row (Array.replicate dims.toNat 1) (Array.replicate dims.toNat 0) #[])
    | some first =>
      match first with
      | .row l0 u0 _ =>
        let mut elems : Array Value := #[]
        for v in vs do
          match v with
          | .row l u es =>
            if l != l0 || u != u0 then die "bounds of row display elements differ"
            elems := elems ++ es
          | _ => throw (IO.userError "row display")
        push (.row (#[(1 : Int)] ++ l0) (#[(vs.size : Int)] ++ u0) elems)
      | _ => throw (IO.userError "row display")

/-- Push a compiled procedure capturing the current environment. -/
@[export a68rt_push_proc]
def pushProc (fn nparams : UInt32) : IO Unit := go do
  push (.cproc fn.toNat nparams.toNat (← curEnv))

/-- Push a format text capturing the current environment. -/
@[export a68rt_push_format]
def pushFormat (skel : UInt32) : IO Unit := go do
  push (.fmt (← curEnv) (← state).tab.lists[skel.toNat]!)

/-- Case selector: pop an INT and return the alternative to take (0 = out). -/
@[export a68rt_case_index]
def caseIndex (n : UInt32) : IO UInt32 :=
  val (do
    match (← pop) with
    | .int i => return (if i ≥ 1 && i ≤ n.toNat then UInt32.ofNat i.toNat else 0)
    | .undef => die "attempt to use an uninitialised INT value"
    | _ => throw (IO.userError "INT expected in CASE")) 0

/-- Conformity: does the value on top of the stack conform to mode `m`?  If it does and
    `bind` is set, the constituent value is pushed for the alternative's frame. -/
@[export a68rt_conform]
def conform (m : UInt32) (bind : UInt8) : IO UInt8 :=
  val (do
    let s ← (← state).stack.get
    let v := s.back!
    let mm ← mode m
    let (vm, inner) := match v with
      | .union um x => (um, x)
      | x => (Mode.void, x)
    let tb := (← getRt).modes
    let ok := match Mode.resolve tb mm with
      | .union ms => ms.any fun cm => Mode.eqv tb cm vm
      | _ => Mode.eqv tb mm vm
    if ok && bind != 0 then
      push (match Mode.resolve tb mm with
        | .union _ => v
        | _ => inner)
    return (if ok then (1 : UInt8) else 0)) 0

end A68.RT
