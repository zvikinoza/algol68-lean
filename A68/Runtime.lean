import A68.Interp
import A68.Serial

/-!
# A68.Runtime — the C-callable runtime of compiled programs

`a68lean compile` emits a C program whose *structure* is compiled (blocks,
loops, conditionals, procedure calls and jumps are C control flow) and whose
*values* are handled by this runtime, which is the very code the interpreter
uses.  That is how a compiled program and an interpreted one produce the same
bytes: `print`, `printf`, the operators and the number formatting are one
implementation, reached two ways.

The interface is deliberately integer-only, so the generated C never touches a
Lean object:

* an **environment stack** of frames of cells, with a current frame pointer
  (`a68rt_enter` / `a68rt_leave`), exactly like the interpreter's `Env`;
* an **operand stack** of values (`a68rt_push_*`, `a68rt_dyop`, …), the same
  discipline the verified stack machine in `A68.Verified.StackMachine` models;
* tables of modes, strings and format texts rebuilt at start-up from a blob
  the compiler embeds in the program (`A68.Serial`).

Control that leaves an expression is mapped to C: a run-time error prints and
exits, `stop` exits, and a jump sets a pending label that the generated code
turns into a `goto` or a `longjmp`.
-/
namespace A68.RT

open A68.Interp

structure St where
  rt      : Rt
  stack   : Array Value := #[]
  envs    : Array (Array Nat) := #[]      -- environment stack, innermost last
  tables  : Serial.Reader := {}
  saved   : Array (Array (Array Nat)) := #[]   -- environment stacks saved across calls
  jump    : Option Nat := none            -- pending jump label

builtin_initialize stRef : IO.Ref (Option St) ← IO.mkRef none

private def getSt : IO St := do
  match (← stRef.get) with
  | some s => pure s
  | none => throw (IO.userError "a68 runtime not initialised")

private def modSt (f : St → St) : IO Unit := do
  let s ← getSt
  stRef.set (some (f s))

private def curLine : IO Nat := do
  let s ← getSt
  return (← s.rt.pos.get).line

/-- Report a run-time error the way the interpreter's driver does, then exit. -/
private def die (msg : String) (line : Nat) : IO α := do
  let s ← getSt
  let o ← s.rt.out.get
  let stdout ← IO.getStdout
  stdout.write o
  stdout.flush
  IO.eprintln s!"a68lean: runtime error: {line}: {msg}."
  IO.Process.exit 1

/-- Run an interpreter action in the global state. `stop` and errors leave the
    process; a jump is recorded for the generated code to act on. -/
private def run (act : M α) (dflt : α) : IO α := do
  let s ← getSt
  match (← (act.run s.rt).run) with
  | .ok v => pure v
  | .error (.error msg p) => die msg p.line
  | .error .stop => do
    let o ← s.rt.out.get
    let stdout ← IO.getStdout
    stdout.write o
    stdout.flush
    if s.rt.regression then pure () else pure ()
    IO.Process.exit 0
  | .error (.jump l) => do modSt (fun s => { s with jump := some l }); pure dflt
  | .error (.fileEnd _) => pure dflt

private def push (v : Value) : IO Unit := modSt fun s => { s with stack := s.stack.push v }

private def pop : IO Value := do
  let s ← getSt
  match s.stack.back? with
  | some v => stRef.set (some { s with stack := s.stack.pop }); pure v
  | none => throw (IO.userError "a68 runtime: operand stack underflow")

private def popN (n : Nat) : IO (Array Value) := do
  let s ← getSt
  let k := s.stack.size - n
  let vs := s.stack.extract k s.stack.size
  stRef.set (some { s with stack := s.stack.shrink k })
  return vs

private def mode (i : UInt32) : IO Mode := do
  let s ← getSt
  return s.tables.modes[i.toNat]!

private def str (i : UInt32) : IO String := do
  let s ← getSt
  return s.tables.strs[i.toNat]!

private def curEnv : IO Env := do
  let s ← getSt
  return s.envs.toList.reverse

-- ## Start-up and shutdown

@[export a68rt_boot]
def boot (blob : String) (ll : UInt32) (regression : UInt8) (args : Array String) : IO Unit := do
  let tables := Serial.parse blob
  let rt : Rt := {
    heap := ← IO.mkRef #[], out := ← IO.mkRef ByteArray.empty, pos := ← IO.mkRef {},
    modes := {}, files := ← IO.mkRef #[{}, {}, {}, {}], rng := ← IO.mkRef (Interp.tausSet 1),
    args := args, ll := ll.toNat, regression := regression != 0, col := ← IO.mkRef 0 }
  stRef.set (some { rt := rt, tables := tables })

/-- Flush output (adding the final newline in regression mode) and return the exit code. -/
@[export a68rt_finish]
def finish : IO UInt32 := do
  let s ← getSt
  let mut o ← s.rt.out.get
  if s.rt.regression && o.size > 0 && o[o.size - 1]! != 10 then o := o.push 10
  let stdout ← IO.getStdout
  stdout.write o
  stdout.flush
  -- write out any files the program left open
  let files ← s.rt.files.get
  for f in files do
    if f.onDisk && f.dirty && f.writing then
      try IO.FS.writeBinFile f.name f.buf catch _ => pure ()
  return 0

/-- Record the source position for diagnostics. -/
@[export a68rt_line]
def setLine (l : UInt32) : IO Unit := do
  let s ← getSt
  s.rt.pos.set { line := l.toNat, col := 0 }

/-- The label of a pending jump plus one, or 0. -/
@[export a68rt_jump_pending]
def jumpPending : IO UInt32 := do
  let s ← getSt
  return match s.jump with | some l => UInt32.ofNat (l + 1) | none => 0

@[export a68rt_jump_clear]
def jumpClear : IO Unit := modSt fun s => { s with jump := none }

@[export a68rt_raise_jump]
def raiseJump (l : UInt32) : IO Unit := modSt fun s => { s with jump := some l.toNat }

@[export a68rt_stop]
def doStop : IO Unit := do
  let _ ← finish
  IO.Process.exit 0

-- ## Environments

@[export a68rt_enter]
def enter (size : UInt32) : IO Unit := do
  let s ← getSt
  let mut frame : Array Nat := Array.mkEmpty size.toNat
  let mut heap ← s.rt.heap.get
  for _ in [0:size.toNat] do
    frame := frame.push heap.size
    heap := heap.push .undef
  s.rt.heap.set heap
  stRef.set (some { s with envs := s.envs.push frame })

@[export a68rt_leave]
def leave : IO Unit := modSt fun s => { s with envs := s.envs.pop }

@[export a68rt_env_depth]
def envDepth : IO UInt32 := do return UInt32.ofNat (← getSt).envs.size

@[export a68rt_env_truncate]
def envTruncate (d : UInt32) : IO Unit := modSt fun s => { s with envs := s.envs.shrink d.toNat }

/-- Enter the environment captured by a compiled procedure: the current environment
    stack is saved and replaced by the closure's. -/
@[export a68rt_env_set]
def envSet (env : Env) : IO Unit := do
  let s ← getSt
  stRef.set (some { s with saved := s.saved.push s.envs, envs := env.reverse.toArray })

/-- Restore the environment stack saved by `a68rt_env_set`. -/
@[export a68rt_env_restore]
def envRestore : IO Unit := do
  let s ← getSt
  match s.saved.back? with
  | some e => stRef.set (some { s with envs := e, saved := s.saved.pop })
  | none => throw (IO.userError "a68 runtime: environment stack underflow")

private def cellOf (depth slot : UInt32) : IO Nat := do
  let s ← getSt
  let fr := s.envs[s.envs.size - 1 - depth.toNat]!
  return fr[slot.toNat]!

-- ## Operand stack

@[export a68rt_push_int]
def pushInt (v : Int64) : IO Unit := push (.int v.toInt)

@[export a68rt_push_bigint]
def pushBigInt (i : UInt32) : IO Unit := do
  let s ← str i
  push (.int (if s.startsWith "-" then -((String.ofList (s.toList.drop 1)).toNat! : Int) else (s.toNat! : Int)))

@[export a68rt_push_real]
def pushReal (v : Float) : IO Unit := push (.real v)

@[export a68rt_push_bool]
def pushBool (v : UInt8) : IO Unit := push (.bool (v != 0))

@[export a68rt_push_char]
def pushChar (v : UInt32) : IO Unit := push (.char v.toNat)

@[export a68rt_push_bits]
def pushBits (v : UInt64) : IO Unit := push (.bits v.toNat)

@[export a68rt_push_str]
def pushStr (i : UInt32) : IO Unit := do push (Value.ofString (← str i))

@[export a68rt_push_undef]
def pushUndef : IO Unit := push .undef

@[export a68rt_push_nil]
def pushNil : IO Unit := push .nil

@[export a68rt_push_void]
def pushVoid : IO Unit := push .void

@[export a68rt_push_builtin]
def pushBuiltin (i : UInt32) : IO Unit := do push (.builtin (← str i))

@[export a68rt_push_file]
def pushFile (i : UInt32) : IO Unit := push (.file i.toNat)

@[export a68rt_push_skip]
def pushSkip (m : UInt32) : IO Unit := do
  let mm ← mode m
  push (← run (Interp.eval [] (.skip mm)) .undef)

@[export a68rt_pop]
def popOne : IO Unit := do let _ ← pop

@[export a68rt_nip]
def nip : IO Unit := do
  let s ← getSt
  let n := s.stack.size
  if n < 2 then throw (IO.userError "a68 runtime: nip on a short stack")
  let top := s.stack[n-1]!
  stRef.set (some { s with stack := (s.stack.shrink (n-2)).push top })

@[export a68rt_stack_depth]
def stackDepth : IO UInt32 := do return UInt32.ofNat (← getSt).stack.size

@[export a68rt_stack_truncate]
def stackTruncate (d : UInt32) : IO Unit := modSt fun s => { s with stack := s.stack.shrink d.toNat }

@[export a68rt_take_top]
def takeTop : IO Value := pop

@[export a68rt_push_array]
def pushArray (a : Array Value) : IO Unit := do
  for v in a do push v

/-- Enter a frame of `size` cells whose first `nargs` slots come from the operand stack. -/
@[export a68rt_enter_args]
def enterArgs (size nargs : UInt32) : IO Unit := do
  let args ← popN nargs.toNat
  enter size
  for i in [0:nargs.toNat] do
    let c ← cellOf 0 (UInt32.ofNat i)
    run (Interp.writeCell c args[i]!) ()

@[export a68rt_dup]
def dup : IO Unit := do
  let s ← getSt
  match s.stack.back? with
  | some v => push v
  | none => throw (IO.userError "a68 runtime: operand stack underflow")

@[export a68rt_push_cell]
def pushCell (depth slot : UInt32) : IO Unit := do
  let c ← cellOf depth slot
  let v ← run (Interp.readCell c) .undef
  match v with
  | .undef => die "attempt to use an uninitialised value" (← curLine)
  | _ => push v

@[export a68rt_push_ref]
def pushRef (depth slot : UInt32) : IO Unit := do
  push (.ref (← cellOf depth slot) [])

/-- Pop a value into a cell of the current environment (an identity declaration). -/
@[export a68rt_store]
def store (depth slot : UInt32) : IO Unit := do
  let v ← pop
  let c ← cellOf depth slot
  run (Interp.writeCell c v) ()

-- ## Reading scalars back into C

@[export a68rt_pop_int]
def popInt : IO Int64 := do
  let v ← pop
  match v with
  | .int n => return Int64.ofInt n
  | .undef => die "attempt to use an uninitialised INT value" (← curLine)
  | _ => throw (IO.userError "a68 runtime: INT expected")

@[export a68rt_pop_bool]
def popBool : IO UInt8 := do
  let v ← pop
  match v with
  | .bool b => return if b then 1 else 0
  | .undef => die "attempt to use an uninitialised BOOL value" (← curLine)
  | _ => throw (IO.userError "a68 runtime: BOOL expected")

-- ## Operations

@[export a68rt_deref]
def deref : IO Unit := do
  let r ← pop
  let v ← run (Interp.readRef r) .undef
  match v with
  | .undef => die "attempt to use an uninitialised value" (← curLine)
  | _ => push v

@[export a68rt_deproc]
def deproc : IO Unit := do
  let f ← pop
  push (← run (Interp.callValue f []) .undef)

@[export a68rt_widen]
def widen (src dst : UInt32) : IO Unit := do
  let v ← pop
  push (← run (Interp.widenValue (← mode src) (← mode dst) v) .undef)

@[export a68rt_row_of]
def rowOf : IO Unit := do
  let v ← pop
  match v with
  | .ref _ _ => push v
  | _ => push (.row #[1] #[1] #[v])

@[export a68rt_unite]
def unite (m : UInt32) : IO Unit := do
  let v ← pop
  push (.union (← mode m) v)

@[export a68rt_voiding]
def voiding : IO Unit := do
  let _ ← pop
  push .void

@[export a68rt_assign]
def assign (flex : UInt8) : IO Unit := do
  let v ← pop
  let d ← pop
  run (Interp.assignTo d v (flex != 0)) ()
  push d

@[export a68rt_ident_rel]
def identRel (isnt : UInt8) : IO Unit := do
  let b ← pop
  let a ← pop
  let same := match a, b with
    | .ref c1 p1, .ref c2 p2 => c1 == c2 && p1 == p2
    | .nil, .nil => true
    | _, _ => false
  push (.bool (if isnt != 0 then !same else same))

@[export a68rt_dyop]
def dyop (op m1 m2 : UInt32) : IO Unit := do
  let r ← pop
  let l ← pop
  push (← run (Interp.dyadic (← str op) (← mode m1) (← mode m2) l r) .undef)

@[export a68rt_monop]
def monop (op m : UInt32) : IO Unit := do
  let v ← pop
  push (← run (Interp.monadic (← str op) (← mode m) v) .undef)

@[export a68rt_call]
def call (nargs : UInt32) : IO Unit := do
  let args ← popN nargs.toNat
  let f ← pop
  push (← run (Interp.callValue f args.toList) .undef)

@[export a68rt_select]
def select (idx : UInt32) (viaRef : UInt8) : IO Unit := do
  let v ← pop
  if viaRef != 0 then
    match v with
    | .ref c path => push (.ref c (path ++ [.field idx.toNat]))
    | .nil => die "attempt to select from NIL" (← curLine)
    | _ => throw (IO.userError "a68 runtime: select via non-REF")
  else
    match v with
    | .struct fs => push fs[idx.toNat]!
    | .row _ _ _ => push (← run (Interp.readPath v [.field idx.toNat]) .undef)
    | _ => throw (IO.userError "a68 runtime: select from non-struct")

/-- Slice.  The indexer values were pushed in order; `kinds` holds four bits per
    indexer: bit 0 = it is a trim, bit 1 = a lower bound was given, bit 2 = an upper
    bound was given, bit 3 = an `AT` was given. -/
@[export a68rt_slice]
def slice (nidx : UInt32) (kinds : UInt64) (viaRef : UInt8) : IO Unit := do
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
  let mut idx : List CoreIdx := []
  let mut k := 0
  for i in [0:nidx.toNat] do
    let kind := (kinds >>> (UInt64.ofNat (4 * i))) &&& 15
    if kind &&& 1 == 0 then
      idx := idx ++ [.index (.lit vals[k]!)]
      k := k + 1
    else
      let lo := if kind &&& 2 != 0 then some (Core.lit vals[k]!) else none
      if kind &&& 2 != 0 then k := k + 1
      let hi := if kind &&& 4 != 0 then some (Core.lit vals[k]!) else none
      if kind &&& 4 != 0 then k := k + 1
      let at_ := if kind &&& 8 != 0 then some (Core.lit vals[k]!) else none
      if kind &&& 8 != 0 then k := k + 1
      idx := idx ++ [.trim lo hi at_]
  push (← run (Interp.evalSlice [] (.lit base) idx (viaRef != 0)) .undef)

@[export a68rt_new_row]
def newRow (ndims : UInt32) (flex : UInt8) : IO Unit := do
  let bounds ← popN (2 * ndims.toNat)
  let init ← pop
  let mut ls : Array Int := #[]
  let mut us : Array Int := #[]
  for i in [0:ndims.toNat] do
    match bounds[2*i]!, bounds[2*i+1]! with
    | .int l, .int u => ls := ls.push l; us := us.push u
    | _, _ => throw (IO.userError "a68 runtime: row bounds must be INT")
  push (.row ls us (Array.replicate (Interp.rowSize ls us) init))

@[export a68rt_gen]
def gen : IO Unit := do
  let v ← pop
  push (.ref (← run (Interp.alloc v) 0) [])

@[export a68rt_collateral]
def collateral (n : UInt32) (isStruct : UInt8) (dims : UInt32) : IO Unit := do
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
            if l != l0 || u != u0 then die "bounds of row display elements differ" (← curLine)
            elems := elems ++ es
          | _ => throw (IO.userError "a68 runtime: row display")
        push (.row (#[(1 : Int)] ++ l0) (#[(vs.size : Int)] ++ u0) elems)
      | _ => throw (IO.userError "a68 runtime: row display")

/-- Push a compiled procedure capturing the current environment. -/
@[export a68rt_push_proc]
def pushProc (fn nparams : UInt32) : IO Unit := do
  push (.cproc fn.toNat nparams.toNat (← curEnv))

/-- Push a format text capturing the current environment. -/
@[export a68rt_push_format]
def pushFormat (skel : UInt32) : IO Unit := do
  let s ← getSt
  push (.fmt (← curEnv) s.tables.lists[skel.toNat]!)

/-- Case selector: pop an INT and return the alternative to take (0 = out). -/
@[export a68rt_case_index]
def caseIndex (n : UInt32) : IO UInt32 := do
  let v ← pop
  match v with
  | .int i => return if i ≥ 1 && i ≤ n.toNat then UInt32.ofNat i.toNat else 0
  | .undef => die "attempt to use an uninitialised INT value" (← curLine)
  | _ => throw (IO.userError "a68 runtime: INT expected in CASE")

/-- Conformity: does the value on top of the stack conform to mode `m`?  If it does and
    `bind` is set, the constituent value is pushed for the alternative's frame. -/
@[export a68rt_conform]
def conform (m : UInt32) (bind : UInt8) : IO UInt8 := do
  let s ← getSt
  let v := s.stack.back!
  let mm ← mode m
  let (vm, inner) := match v with
    | .union um x => (um, x)
    | x => (Mode.void, x)
  let tb := s.rt.modes
  let ok := match Mode.resolve tb mm with
    | .union ms => ms.any fun cm => Mode.eqv tb cm vm
    | _ => Mode.eqv tb mm vm
  if ok && bind != 0 then
    let bound := match Mode.resolve tb mm with
      | .union _ => v
      | _ => inner
    push bound
  return if ok then 1 else 0

/-- Push the value in a cell without the uninitialised check (for conformity binding). -/
@[export a68rt_bind_cell]
def bindCell (depth slot : UInt32) : IO Unit := do
  let v ← pop
  let c ← cellOf depth slot
  run (Interp.writeCell c v) ()

/-- Set an INT cell directly (loop counters). -/
@[export a68rt_set_int]
def setInt (depth slot : UInt32) (v : Int64) : IO Unit := do
  let c ← cellOf depth slot
  run (Interp.writeCell c (.int v.toInt)) ()

end A68.RT
