import A68.MIR

/-!
# A68.LLVM — MIR printed as LLVM IR

Each MIR variable becomes an `alloca` in the function's entry block and every read and
write a `load` or `store`; LLVM's `mem2reg` turns that into SSA form, as it does for
the locals of C.  The checked scalar operations expand into the compare-and-branch
they need, trapping through `a68rt_arith_error`.  Runtime entry points are declared
from `A68.MIR.rtSigs`; a compiled routine is `define void @a68_fn<n>()`.
-/
namespace A68.LLVM
open A68.MIR

def tyName : Ty → String
  | .i64 => "i64" | .f64 => "double" | .i1 => "i1" | .i32 => "i32"

/-- The C type of a runtime argument or result of a MIR type. -/
def cTyName : Ty → String
  | .i64 => "i64" | .f64 => "double" | .i1 => "i8" | .i32 => "i32"

def retName : RtRet → String
  | .none => "void" | .i64 => "i64" | .f64 => "double" | .u8 => "i8" | .u32 => "i32"

/-- A double as LLVM writes it: the IEEE bits in hexadecimal, exact for every value. -/
def hexDouble (x : Float) : String :=
  let b := x.toBits
  let d := "0123456789ABCDEF"
  let digits := (List.range 16).reverse.map fun i => d.get ⟨((b >>> (4 * i.toUInt64)) &&& 15).toNat⟩
  "0x" ++ String.ofList digits

def constText (ty : Ty) (c : Const) : String :=
  match ty, c with
  | .f64, .f x => hexDouble x
  | .f64, .i n => hexDouble (Float.ofInt n)
  | .i1, .i n => if n == 0 then "false" else "true"
  | _, .i n => toString n
  | _, .f x => toString x

/-- A byte string as an LLVM `c"…"` literal. -/
def cstr (s : String) : String := Id.run do
  let mut out := "c\""
  let d := "0123456789ABCDEF"
  for ch in s.toList do
    let n := ch.toNat % 256
    if n ≥ 32 && n < 127 && ch != '"' && ch != '\\' then out := out.push ch
    else out := out ++ "\\" ++ String.singleton (d.get ⟨n / 16⟩) ++ String.singleton (d.get ⟨n % 16⟩)
  return out ++ "\""

structure P where
  out  : Array String := #[]
  tmp  : Nat := 0
  used : List String := []      -- runtime and native functions referenced
  deriving Inhabited

abbrev M := StateM P

def line (s : String) : M Unit := modify fun p => { p with out := p.out.push s }
def fresh : M String := do
  let p ← get
  set { p with tmp := p.tmp + 1 }
  return s!"%t{p.tmp}"
def use (n : String) : M Unit := modify fun p => if p.used.contains n then p else { p with used := n :: p.used }

/-- Read an operand into an SSA value of its MIR type. -/
def opnd (o : Opnd) : M String := do
  match o with
  | .k ty c => return constText ty c
  | .v x =>
    let t ← fresh
    line s!"  {t} = load {tyName x.ty}, ptr %v{x.id}"
    return t

def store (x : Var) (val : String) : M Unit :=
  line s!"  store {tyName x.ty} {val}, ptr %v{x.id}"

/-- Branch to a trap on `cond`, continuing in a fresh block otherwise. -/
def trapIf (cond : String) (kind : Nat) : M Unit := do
  let n ← fresh
  let tb := "trap" ++ n.drop 2
  let cb := "cont" ++ n.drop 2
  line s!"  br i1 {cond}, label %{tb}, label %{cb}"
  line s!"{tb}:"
  use "a68rt_arith_error"
  line s!"  call void @a68rt_arith_error(i32 {kind}, i32 0)"
  line "  unreachable"
  line s!"{cb}:"

/-- The INT range check of `a68_rng`. -/
def rangeCheck (r : String) : M Unit := do
  let a ← fresh; line s!"  {a} = icmp sgt i64 {r}, 2147483647"
  let b ← fresh; line s!"  {b} = icmp slt i64 {r}, -2147483647"
  let c ← fresh; line s!"  {c} = or i1 {a}, {b}"
  trapIf c 0

/-- The REAL result check of `a68_chk_r`. -/
def realCheck (r : String) : M Unit := do
  let nan ← fresh; line s!"  {nan} = fcmp uno double {r}, {r}"
  trapIf nan 3
  let a ← fresh; line s!"  {a} = fcmp ogt double {r}, 0x7FEFFFFFFFFFFFFF"
  let b ← fresh; line s!"  {b} = fcmp olt double {r}, 0xFFEFFFFFFFFFFFFF"
  let c ← fresh; line s!"  {c} = or i1 {a}, {b}"
  trapIf c 2

def cmpPred (op : BinOp) (ty : Ty) : String :=
  match ty, op with
  | .f64, .eq => "fcmp oeq" | .f64, .ne => "fcmp une" | .f64, .lt => "fcmp olt"
  | .f64, .le => "fcmp ole" | .f64, .gt => "fcmp ogt" | .f64, .ge => "fcmp oge"
  | .i32, .lt => "icmp ult" | .i32, .le => "icmp ule" | .i32, .gt => "icmp ugt" | .i32, .ge => "icmp uge"
  | _, .eq => "icmp eq" | _, .ne => "icmp ne" | _, .lt => "icmp slt"
  | _, .le => "icmp sle" | _, .gt => "icmp sgt" | _, .ge => "icmp sge"
  | _, _ => "icmp eq"

def isCmp : BinOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

/-- Coerce an SSA value of MIR type `from` to the C parameter type `to`. -/
def coerce (v : String) (from_ to : Ty) : M String := do
  if from_ == to then return v
  let t ← fresh
  match from_, to with
  | .i1, .i32 | .i1, .i64 => line s!"  {t} = zext i1 {v} to {tyName to}"
  | .i32, .i64 => line s!"  {t} = zext i32 {v} to i64"
  | .i64, .i32 => line s!"  {t} = trunc i64 {v} to i32"
  | .i64, .i1 | .i32, .i1 => line s!"  {t} = icmp ne {tyName from_} {v}, 0"
  | _, _ => line s!"  {t} = bitcast {tyName from_} {v} to {tyName to}"
  return t

/-- A call; the C `uint8_t` arguments and results are `i8`. -/
def call (f : Callee) (args : Array Opnd) (dst : Option Var) : M Unit := do
  match f with
  | .fn i => line s!"  call void @a68_fn{i}()"
  | .hole i => line s!"  call void @a68_hole{i}()"
  | .rt name | .nat name =>
    use name
    let isRt := match f with | .rt _ => true | _ => false
    let sg? : Option RtSig := if isRt then (rtSigs.find? (·.1 == name)).map (·.2) else (natSigs.find? (·.1 == name)).map (·.2)
    let some (sg : RtSig) := sg? | line s!"  ; unknown runtime function {name}"
    let mut as : Array String := #[]
    for i in [0:args.size] do
      let a := args[i]!
      let pty : Ty := sg.args[i]?.getD a.ty
      let v ← opnd a
      let v ← coerce v a.ty pty
      let v ← if pty == Ty.i1 then do let t ← fresh; line s!"  {t} = zext i1 {v} to i8"; pure t else pure v
      as := as.push s!"{cTyName pty} {v}"
    if isRt then as := as.push "i32 0"
    let argText := ", ".intercalate as.toList
    let ret : RtRet := sg.ret
    match dst with
    | none =>
      if ret == RtRet.none then line s!"  call void @{name}({argText})"
      else do let t ← fresh; line s!"  {t} = call {retName ret} @{name}({argText})"
    | some d =>
      let t ← fresh
      line s!"  {t} = call {retName ret} @{name}({argText})"
      match ret with
      | RtRet.u8 => let b ← fresh; line s!"  {b} = icmp ne i8 {t}, 0"; store d b
      | RtRet.u32 =>
        if d.ty == Ty.i32 then store d t
        else do let z ← fresh; line s!"  {z} = zext i32 {t} to i64"; store d z
      | _ => store d t

def bin (d : Var) (op : BinOp) (a b : Opnd) : M Unit := do
  let x ← opnd a
  let y ← opnd b
  let ty := a.ty
  if isCmp op then
    let t ← fresh
    line s!"  {t} = {cmpPred op ty} {tyName ty} {x}, {y}"
    store d t
    return
  let t ← fresh
  match op with
  | .addI => line s!"  {t} = add {tyName ty} {x}, {y}"; if ty == Ty.i64 then rangeCheck t
  | .subI => line s!"  {t} = sub {tyName ty} {x}, {y}"; if ty == Ty.i64 then rangeCheck t
  | .mulI => line s!"  {t} = mul {tyName ty} {x}, {y}"; if ty == Ty.i64 then rangeCheck t
  | .overI =>
    let z ← fresh; line s!"  {z} = icmp eq i64 {y}, 0"; trapIf z 1
    line s!"  {t} = sdiv i64 {x}, {y}"
  | .modI =>
    let z ← fresh; line s!"  {z} = icmp eq i64 {y}, 0"; trapIf z 1
    let neg ← fresh; line s!"  {neg} = icmp slt i64 {y}, 0"
    let ny ← fresh; line s!"  {ny} = sub i64 0, {y}"
    let m ← fresh; line s!"  {m} = select i1 {neg}, i64 {ny}, i64 {y}"
    let r ← fresh; line s!"  {r} = srem i64 {x}, {m}"
    let rn ← fresh; line s!"  {rn} = icmp slt i64 {r}, 0"
    let r2 ← fresh; line s!"  {r2} = add i64 {r}, {m}"
    line s!"  {t} = select i1 {rn}, i64 {r2}, i64 {r}"
  | .powI => use "a68n_pow_i"; line s!"  {t} = call i64 @a68n_pow_i(i64 {x}, i64 {y})"
  | .addF => line s!"  {t} = fadd double {x}, {y}"; realCheck t
  | .subF => line s!"  {t} = fsub double {x}, {y}"; realCheck t
  | .mulF => line s!"  {t} = fmul double {x}, {y}"; realCheck t
  | .divF =>
    let z ← fresh; line s!"  {z} = fcmp oeq double {y}, 0.0"; trapIf z 3
    line s!"  {t} = fdiv double {x}, {y}"
  | .powFI => use "a68n_pow_ri"; line s!"  {t} = call double @a68n_pow_ri(double {x}, i64 {y})"
  | .powFF => use "a68n_pow_rr"; line s!"  {t} = call double @a68n_pow_rr(double {x}, double {y})"
  | .andB => line s!"  {t} = and i1 {x}, {y}"
  | .orB => line s!"  {t} = or i1 {x}, {y}"
  | .xorB => line s!"  {t} = xor i1 {x}, {y}"
  | .andU => line s!"  {t} = and i64 {x}, {y}"
  | .orU => let u ← fresh; line s!"  {u} = or i64 {x}, {y}"; line s!"  {t} = and i64 {u}, 4294967295"
  | .xorU => let u ← fresh; line s!"  {u} = xor i64 {x}, {y}"; line s!"  {t} = and i64 {u}, 4294967295"
  | _ => line s!"  {t} = add i64 {x}, {y}"
  store d t

def un (d : Var) (op : UnOp) (a : Opnd) : M Unit := do
  let x ← opnd a
  let t ← fresh
  match op with
  | .negI => line s!"  {t} = sub i64 0, {x}"; rangeCheck t
  | .absI =>
    let n ← fresh; line s!"  {n} = icmp slt i64 {x}, 0"
    let nx ← fresh; line s!"  {nx} = sub i64 0, {x}"
    line s!"  {t} = select i1 {n}, i64 {nx}, i64 {x}"
  | .signI =>
    let p ← fresh; line s!"  {p} = icmp sgt i64 {x}, 0"
    let n ← fresh; line s!"  {n} = icmp slt i64 {x}, 0"
    let s ← fresh; line s!"  {s} = select i1 {n}, i64 -1, i64 0"
    line s!"  {t} = select i1 {p}, i64 1, i64 {s}"
  | .oddI =>
    let r ← fresh; line s!"  {r} = srem i64 {x}, 2"
    line s!"  {t} = icmp ne i64 {r}, 0"
  | .reprI =>
    let a1 ← fresh; line s!"  {a1} = icmp slt i64 {x}, 0"
    let a2 ← fresh; line s!"  {a2} = icmp sgt i64 {x}, 255"
    let c ← fresh; line s!"  {c} = or i1 {a1}, {a2}"
    trapIf c 6
    line s!"  {t} = trunc i64 {x} to i32"
  | .negF => line s!"  {t} = fneg double {x}"
  | .absF =>
    let n ← fresh; line s!"  {n} = fcmp olt double {x}, 0.0"
    let nx ← fresh; line s!"  {nx} = fneg double {x}"
    line s!"  {t} = select i1 {n}, double {nx}, double {x}"
  | .signF =>
    let p ← fresh; line s!"  {p} = fcmp ogt double {x}, 0.0"
    let n ← fresh; line s!"  {n} = fcmp olt double {x}, 0.0"
    let s ← fresh; line s!"  {s} = select i1 {n}, i64 -1, i64 0"
    line s!"  {t} = select i1 {p}, i64 1, i64 {s}"
  | .entier => use "a68n_entier"; line s!"  {t} = call i64 @a68n_entier(double {x})"
  | .round => use "a68n_round"; line s!"  {t} = call i64 @a68n_round(double {x})"
  | .notB => line s!"  {t} = xor i1 {x}, true"
  | .absB => line s!"  {t} = zext i1 {x} to i64"
  | .absC => line s!"  {t} = zext i32 {x} to i64"
  | .i2f => line s!"  {t} = sitofp i64 {x} to double"
  | .math n => use s!"a68n_m_{n}"; line s!"  {t} = call double @a68n_m_{n}(double {x})"
  store d t

def instr (i : Instr) : M Unit := do
  match i with
  | .line n => line s!"  store i32 {n}, ptr @a68_line_no"
  | .call f args => call f args none
  | .set d rhs =>
    match rhs with
    | .opnd o => let v ← opnd o; let v ← coerce v o.ty d.ty; store d v
    | .bin op a b => bin d op a b
    | .un op a => un d op a
    | .call f args => call f args (some d)

def term (t : Term) : M Unit := do
  match t with
  | .br b => line s!"  br label %b{b}"
  | .condBr c a b =>
    let v ← opnd c
    line s!"  br i1 {v}, label %b{a}, label %b{b}"
  | .switch o cases d =>
    let v ← opnd o
    let ty := tyName o.ty
    let cs := " ".intercalate (cases.toList.map fun (k, b) => s!"{ty} {k}, label %b{b}")
    line s!"  switch {ty} {v}, label %b{d} [ {cs} ]"
  | .ret => line "  ret void"
  | .unreachable => line "  unreachable"

def func (f : Func) : M Unit := do
  modify fun p => { p with tmp := 0 }
  line ("define void @" ++ f.name ++ "() {")
  line "entry:"
  for i in [0:f.vars.size] do
    line s!"  %v{i} = alloca {tyName f.vars[i]!}"
  line "  br label %b0"
  for i in [0:f.blocks.size] do
    let b := f.blocks[i]!
    line s!"b{i}:"
    for ins in b.instrs do instr ins
    term b.term
  line "}"
  line ""

/-- The whole module. -/
def print (p : Program) : String := Id.run do
  let ((), st) := (do
      for f in p.fns do func f
      for h in p.holes do func h
      -- the dispatchers the runtime calls back through
      line "define void @a68_dispatch_proc(i64 %fn) {"
      line "entry:"
      let cs := " ".intercalate ((List.range p.fns.size).map fun i => s!"i64 {i}, label %f{i}")
      line s!"  switch i64 %fn, label %none [ {cs} ]"
      for i in [0:p.fns.size] do
        line s!"f{i}:"
        line s!"  call void @a68_fn{i}()"
        line "  ret void"
      line "none:"
      line "  ret void"
      line "}"
      line ""
      line "define void @a68_dispatch_hole(i64 %idx) {"
      line "entry:"
      let hs := " ".intercalate ((List.range p.holes.size).map fun i => s!"i64 {i}, label %h{i}")
      line s!"  switch i64 %idx, label %none [ {hs} ]"
      for i in [0:p.holes.size] do
        line s!"h{i}:"
        line s!"  call void @a68_hole{i}()"
        line "  ret void"
      line "none:"
      line "  ret void"
      line "}"
      line ""
      line "define i32 @main(i32 %argc, ptr %argv) {"
      line "entry:"
      let mut k := 0
      for _ in p.echoes do
        use "a68n_echo"
        line s!"  call void @a68n_echo(ptr @echo{k})"
        k := k + 1
      line s!"  call void @a68rt_boot(ptr @A68_BLOB, i32 {p.ll}, i8 {if p.regression then 1 else 0}, i32 %argc, ptr %argv, ptr @A68_SRC)"
      line "  call void @a68_fn0()"
      use "a68rt_finish"
      line "  %rc = call i32 @a68rt_finish(i32 0)"
      line "  ret i32 %rc"
      line "}"
    : M Unit).run {}
  let mut head : Array String := #[]
  head := head.push "; generated by a68lean compile --llvm"
  head := head.push "target triple = \"arm64-apple-macosx\""
  head := head.push ""
  head := head.push "@a68_line_no = external global i32"
  let blobBytes := p.blob.utf8ByteSize + 1
  head := head.push s!"@A68_BLOB = private constant [{blobBytes} x i8] {cstr (p.blob ++ "\x00")}"
  head := head.push s!"@A68_SRC = private constant [{p.src.utf8ByteSize + 1} x i8] {cstr (p.src ++ "\x00")}"
  let mut k := 0
  for e in p.echoes do
    head := head.push s!"@echo{k} = private constant [{e.utf8ByteSize + 2} x i8] {cstr (e ++ "\n\x00")}"
    k := k + 1
  head := head.push "declare void @a68rt_boot(ptr, i32, i8, i32, ptr, ptr)"
  for n in st.used do
    match rtSigs.find? (·.1 == n) with
    | some (_, sg) =>
      let as := (sg.args.toList.map cTyName) ++ ["i32"]
      head := head.push s!"declare {retName sg.ret} @{n}({", ".intercalate as})"
    | none =>
      match natSigs.find? (·.1 == n) with
      | some (_, sg) =>
        let as := sg.args.toList.map cTyName
        head := head.push s!"declare {retName sg.ret} @{n}({", ".intercalate as})"
      | none =>
        if n.startsWith "a68n_m_" then head := head.push s!"declare double @{n}(double)"
  head := head.push ""
  return "\n".intercalate (head ++ st.out).toList

end A68.LLVM
