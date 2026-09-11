import A68.Interp
import A68.Serial
import A68.Blob

/-!
# A68.Runtime — the Lean services of a compiled program

A program compiled to C keeps its Algol 68 values in C memory and runs its structure —
frames, the operand stack, names, rows, structures, unions, closures — in the C runtime
`csrc/rt.c`.  What it cannot do there it asks of the evaluator's code through the entry
points below: the standard prelude (transput above all), the operators and widenings of
the modes that are Lean values (`LONG` arithmetic, `COMPL`, `BYTES`), the default value
of a mode, conformity, and error reporting.  Values cross as `A68.Blob` byte strings;
names, closures and format texts cross as C addresses that the evaluator reaches back
through (`Interp.cLoad` and its relatives).

The state a service needs — the evaluator's `Rt` and the program's tables — is created
by `a68l_boot` and held in a C variable (`csrc/stubs.c`), so no Lean global is involved.
-/
namespace A68.RT

open A68.Interp (M Rt Ctrl)

structure Sta where
  rt  : Rt
  tab : Serial.Reader

@[extern "a68_get_state"]
opaque getState (u : Unit) : BaseIO (Option Sta)

@[extern "a68_set_jump"]
opaque setJump (v : UInt32) : BaseIO UInt32

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

/-- Run a service.  `stop` and errors leave the process; a jump raised by a callback into
    compiled code is recorded in the flag the generated code tests after every call. -/
@[inline] private def run (act : M α) (dflt : α) : IO α := do
  let rt ← getRt
  match (← (act.run rt).run) with
  | .ok v => pure v
  | .error (.error msg p) => do
    flushOut
    let cl ← Interp.compiledLine ()
    let line := if cl == 0 then p.line else cl.toNat
    IO.eprintln s!"a68lean: runtime error: {line}: {msg}."
    IO.Process.exit 1
  | .error .stop => do flushOut; IO.Process.exit 0
  | .error (.jump l) => do let _ ← setJump (UInt32.ofNat (l + 1)); pure dflt
  | .error (.fileEnd _) => pure dflt

@[inline] private def mode (i : UInt32) : IO Mode := do
  return ((← (← getRt).mtab.get)[i.toNat]?).getD .void

private def strOf (b : ByteArray) : String :=
  String.ofList (b.data.toList.map fun x => Char.ofNat x.toNat)

-- ## Start-up and shutdown

@[export a68l_boot]
def boot (blob : String) (ll : UInt32) (regression : UInt8) (args : Array String) : IO Sta := do
  let tab0 := Serial.parse blob
  let _ ← setJump 0
  let rt : Rt := {
    heap := ← IO.mkRef #[], out := ← IO.mkRef ByteArray.empty, pos := ← IO.mkRef {},
    modes := tab0.decls.foldl (fun t (n, m) => t.insert n m) {},
    files := ← IO.mkRef #[{}, {}, {}, {}], rng := ← IO.mkRef (Interp.tausSet 1),
    args := args, ll := ll.toNat, regression := regression != 0, col := ← IO.mkRef 0,
    mtab := ← IO.mkRef tab0.modes, fmts := ← IO.mkRef tab0.lists }
  return { rt := rt, tab := tab0 }

/-- Flush output and write out any files the program left open. -/
@[export a68l_finish]
def finish : IO UInt32 := do
  flushOut
  let rt ← getRt
  for f in (← rt.files.get) do
    if f.onDisk && f.dirty && f.writing then
      try IO.FS.writeBinFile f.name f.buf catch _ => pure ()
  return 0

@[export a68l_stop]
def doStop : IO Unit := do
  flushOut
  IO.Process.exit 0

/-- A run-time error detected by the C runtime, in the evaluator's words. -/
@[export a68l_die]
def dieWith (msg : String) : IO Unit := die msg

@[export a68l_flush]
def flush : IO Unit := flushOut

-- ## Values crossing

private def encode (v : Value) : IO ByteArray := run (Interp.encodeValue v) ByteArray.empty
private def decode (b : ByteArray) : IO Value := run (Interp.decodeValue b) .undef
private def decodeN (b : ByteArray) (n : Nat) : IO (List Value) := run (Interp.decodeValues b n) []

/-- Call a procedure of the standard prelude.  A jump raised by an event routine or a
    format hole the call reached leaves `.undef` behind, which the caller never looks at. -/
@[export a68l_call]
def callBuiltin (name : String) (args : ByteArray) (nargs : UInt32) : IO ByteArray := do
  let vs ← decodeN args nargs.toNat
  let r ← run (Interp.callBuiltin name vs) .undef
  encode r

/-- A dyadic operator the C runtime leaves to the evaluator. -/
@[export a68l_dyop]
def dyop (op : String) (m1 m2 : UInt32) (args : ByteArray) : IO ByteArray := do
  let vs ← decodeN args 2
  match vs with
  | [l, r] => encode (← run (Interp.dyadic op (← mode m1) (← mode m2) l r) .undef)
  | _ => die "internal: dyadic operands"

@[export a68l_monop]
def monop (op : String) (m : UInt32) (arg : ByteArray) : IO ByteArray := do
  encode (← run (Interp.monadic op (← mode m) (← decode arg)) .undef)

@[export a68l_widen]
def widen (src dst : UInt32) (arg : ByteArray) : IO ByteArray := do
  encode (← run (Interp.widenValue (← mode src) (← mode dst) (← decode arg)) .undef)

/-- The value a `SKIP` of this mode denotes. -/
@[export a68l_skip]
def skip (m : UInt32) : IO ByteArray := do
  encode (← run (Interp.defaultOf (← mode m)) .undef)

/-- Does a value whose united mode has index `vm` (`0xffffffff` for a value that is not a
    union) conform to mode `m`? -/
@[export a68l_conform]
def conform (m vm : UInt32) : IO UInt8 := do
  let mm ← mode m
  let vmm ← if vm == 0xffffffff then pure Mode.void else mode vm
  let tb := (← getRt).modes
  let ok := match Mode.resolve tb mm with
    | .union ms => ms.any fun cm => Mode.eqv tb cm vmm
    | _ => Mode.eqv tb mm vmm
  return (if ok then 1 else 0)

/-- Is the mode a union, once resolved?  Conformity binds the whole united value for a
    union alternative and the constituent for any other. -/
@[export a68l_mode_is_union]
def modeIsUnion (m : UInt32) : IO UInt8 := do
  let tb := (← getRt).modes
  return (match Mode.resolve tb (← mode m) with | .union _ => 1 | _ => 0)

/-- The value in a cell of the evaluator's heap, for a name the Lean side made. -/
@[export a68l_lcell]
def lcell (c : UInt32) : IO ByteArray := do
  encode (← run (Interp.readCell c.toNat) .undef)

@[export a68l_lstore]
def lstore (c : UInt32) (b : ByteArray) : IO Unit := do
  run (Interp.writeCell c.toNat (← decode b)) ()

/-- Whether standard output ends without a newline, for `PR regression PR`. -/
@[export a68l_line]
def setLine (l : UInt32) : IO Unit := do
  (← getRt).pos.set { line := l.toNat, col := 0 }

end A68.RT
