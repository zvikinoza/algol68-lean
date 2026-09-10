import A68.Core
import A68.Serial

/-!
# A68.CodeGen — translation of the core representation to C

The emitted program is self-contained C: the program's *structure* becomes C
control flow (blocks, conditionals, cases, loops, jumps and one C function per
routine text), and values are handled by the runtime of `A68.Runtime`, which is
the same code the interpreter runs.  This mirrors Algol 68 Genie's optimiser,
which also compiles units to C against its own runtime, except that here the
result is a whole program rather than a plugin loaded back into an interpreter.

Two conventions govern the generated code:

* **Operand stack.** Every expression leaves exactly one value on the runtime's
  operand stack; a block leaves its result there too. This is the discipline
  proved correct for the expression core in `A68.Verified.StackMachine`.
* **Jumps.** A jump to a label of the enclosing C function is a C `goto`. A jump
  out of a routine sets a pending label and returns; every call site checks and
  either lands on its own label or returns in turn, so the C stack unwinds
  without `longjmp`.  Landing on a label restores the environment and operand
  stack to the depths recorded when the block was entered, which is what the
  interpreter does when it re-enters a block at a label.
-/
namespace A68.CodeGen

structure Fn where
  name  : String
  body  : Array String := #[]
  deriving Inhabited

structure St where
  w      : Serial.Writer := {}
  fns    : Array Fn := #[]
  holes  : Array Fn := #[]
  cur    : Array String := #[]     -- lines of the function being emitted
  labels : List Nat := []          -- labels owned by the function being emitted
  depth  : Nat := 0                -- indentation
  tmp    : Nat := 0
  deriving Inhabited

abbrev M := StateM St

def emit (line : String) : M Unit :=
  modify fun s => { s with cur := s.cur.push (String.ofList (List.replicate (2 * s.depth) ' ') ++ line) }

def indent (act : M α) : M α := do
  modify fun s => { s with depth := s.depth + 1 }
  let r ← act
  modify fun s => { s with depth := s.depth - 1 }
  return r

def fresh : M Nat := do
  let s ← get
  set { s with tmp := s.tmp + 1 }
  return s.tmp

def putMode (m : Mode) : M Nat := do
  let s ← get
  let (i, w) := Serial.putMode s.w m
  set { s with w := w }
  return i

def putStr (str : String) : M Nat := do
  let s ← get
  let (i, w) := s.w.str str
  set { s with w := w }
  return i

def putFmtList (items : List CoreFmt) : M Nat := do
  let s ← get
  let (i, w) := Serial.putFmtList s.w items
  set { s with w := w }
  return i

/-- C string literal for an arbitrary byte string. -/
def cstring (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\"
    else if c == '\n' then "\\n" else if c == '\t' then "\\t"
    else if c.toNat < 32 || c.toNat > 126 then
      let n := c.toNat % 256
      let d := "0123456789abcdef"
      "\\x" ++ String.singleton (d.get ⟨n / 16⟩) ++ String.singleton (d.get ⟨n % 16⟩)
    else String.singleton c) ++ "\""

/-- Render a `Float` as a C double literal that reads back exactly. -/
def creal (x : Float) : String :=
  if x.isNaN then "(0.0/0.0)"
  else if x.isInf then (if x > 0 then "(1.0/0.0)" else "(-1.0/0.0)")
  else
    let s := toString x
    if s.contains '.' || s.contains 'e' || s.contains 'E' then s else s ++ ".0"

/-- Labels declared directly in this function (not inside nested routine texts). -/
partial def labelsOf : Core → List Nat
  | .block _ stmts _ _ =>
    stmts.toList.flatMap fun st => match st with
      | .label id => [id]
      | .decl _ c => labelsOf c
      | .unit c => labelsOf c
      | .exit => []
  | .deref e | .deproc e | .rowOf e | .voiding e | .gen e | .at _ e => labelsOf e
  | .widen _ _ e | .unite _ e | .monop _ _ e | .select _ e _ => labelsOf e
  | .assign a b _ | .identRel a b _ | .andThen a b | .orElse a b | .seq a b => labelsOf a ++ labelsOf b
  | .dyop _ _ _ a b => labelsOf a ++ labelsOf b
  | .call f args => labelsOf f ++ args.flatMap labelsOf
  | .slice a idx _ => labelsOf a ++ idx.flatMap fun
      | .index e => labelsOf e
      | .trim l u a => (l.map labelsOf).getD [] ++ (u.map labelsOf).getD [] ++ (a.map labelsOf).getD []
  | .newRow bs i _ => bs.flatMap (fun (l, u) => labelsOf l ++ labelsOf u) ++ labelsOf i
  | .collateral es _ _ => es.flatMap labelsOf
  | .cond c t e => labelsOf c ++ labelsOf t ++ labelsOf e
  | .caseInt s alts o => labelsOf s ++ alts.flatMap labelsOf ++ labelsOf o
  | .caseConf s alts o => labelsOf s ++ alts.flatMap (fun (_, _, c) => labelsOf c) ++ labelsOf o
  | .loop _ f b t w body =>
    labelsOf f ++ labelsOf b ++ (t.map labelsOf).getD [] ++ (w.map labelsOf).getD [] ++ labelsOf body
  | _ => []

/-- After a call that may raise a jump, land on our own label or propagate. -/
def jumpCheck : M Unit := do
  let s ← get
  if s.labels.isEmpty then
    emit "if (a68_jump()) return;"
  else
    emit "if (a68_jump()) { switch (a68_jump()-1) {"
    for l in s.labels do
      emit s!"  case {l}: goto L{l};"
    emit "  default: return; } }"

mutual

/-- Emit code leaving the value of `c` on the operand stack. -/
partial def gen (c : Core) : M Unit := do
  match c with
  | .lit v => genLit v
  | .loadCell d s => emit s!"a68_v(a68rt_push_cell({d}, {s}, W));"
  | .refCell d s => emit s!"a68_v(a68rt_push_ref({d}, {s}, W));"
  | .deref e => gen e; emit "a68_v(a68rt_deref(W));"
  | .deproc e => gen e; emit "a68_v(a68rt_deproc(W));"; jumpCheck
  | .widen a b e =>
    gen e
    emit s!"a68_v(a68rt_widen({← putMode a}, {← putMode b}, W));"
  | .rowOf e => gen e; emit "a68_v(a68rt_row_of(W));"
  | .unite m e => gen e; emit s!"a68_v(a68rt_unite({← putMode m}, W));"
  | .voiding e => gen e; emit "a68_v(a68rt_voiding(W));"
  | .assign d s flex =>
    gen d; gen s
    emit s!"a68_v(a68rt_assign({if flex then 1 else 0}, W));"
  | .identRel l r isnt =>
    gen l; gen r
    emit s!"a68_v(a68rt_ident_rel({if isnt then 1 else 0}, W));"
  | .dyop op m1 m2 l r =>
    gen l; gen r
    emit s!"a68_v(a68rt_dyop({← putStr op}, {← putMode m1}, {← putMode m2}, W));"
  | .monop op m e =>
    gen e
    emit s!"a68_v(a68rt_monop({← putStr op}, {← putMode m}, W));"
  | .call f args =>
    gen f
    for a in args do gen a
    emit s!"a68_v(a68rt_call({args.length}, W));"
    jumpCheck
  | .routine nparams frameSize body =>
    let idx ← genFunction nparams frameSize body
    emit s!"a68_v(a68rt_push_proc({idx}, {nparams}, W));"
  | .slice arr idx viaRef =>
    gen arr
    let mut kinds : Nat := 0
    let mut i := 0
    for ix in idx do
      match ix with
      | .index e => gen e
      | .trim l u a =>
        let mut bits := 1
        match l with | some e => gen e; bits := bits + 2 | none => pure ()
        match u with | some e => gen e; bits := bits + 4 | none => pure ()
        match a with | some e => gen e; bits := bits + 8 | none => pure ()
        kinds := kinds + bits * 16 ^ i
      i := i + 1
    emit s!"a68_v(a68rt_slice({idx.length}, {kinds}ULL, {if viaRef then 1 else 0}, W));"
  | .select i e viaRef =>
    gen e
    emit s!"a68_v(a68rt_select({i}, {if viaRef then 1 else 0}, W));"
  | .newRow bounds init flex =>
    gen init
    for (l, u) in bounds do gen l; gen u
    emit s!"a68_v(a68rt_new_row({bounds.length}, {if flex then 1 else 0}, W));"
  | .gen init => gen init; emit "a68_v(a68rt_gen(W));"
  | .block size stmts labelBase nLabels => genBlock size stmts labelBase nLabels
  | .collateral es isStruct dims =>
    for e in es do gen e
    emit s!"a68_v(a68rt_collateral({es.length}, {if isStruct then 1 else 0}, {dims}, W));"
  | .cond c t e =>
    gen c
    emit "if (a68_bool()) {"
    indent (gen t)
    emit "} else {"
    indent (gen e)
    emit "}"
  | .caseInt sel alts out =>
    gen sel
    emit ("switch (a68_case(" ++ toString alts.length ++ ")) {")
    let mut k := 1
    for a in alts do
      emit ("case " ++ toString k ++ ": {")
      indent (gen a)
      emit "} break;"
      k := k + 1
    emit "default: {"
    indent (gen out)
    emit "} }"
  | .caseConf sel alts out => genConformity sel alts out
  | .loop slot f b t w body => genLoop slot f b t w body
  | .goto l =>
    let s ← get
    if s.labels.contains l then emit s!"goto L{l};"
    else emit s!"a68_v(a68rt_raise_jump({l}, W)); return;"
  | .skip m => emit s!"a68_v(a68rt_push_skip({← putMode m}, W));"
  | .andThen l r =>
    gen l
    emit "if (a68_bool()) {"
    indent (gen r)
    emit "} else { a68_v(a68rt_push_bool(0, W)); }"
  | .orElse l r =>
    gen l
    emit "if (a68_bool()) { a68_v(a68rt_push_bool(1, W)); } else {"
    indent (gen r)
    emit "}"
  | .fmt items =>
    let items ← items.mapM genFmtItem
    emit s!"a68_v(a68rt_push_format({← putFmtList items}, W));"
  | .stop => emit "a68_v(a68rt_stop(W));"
  | .seq a b => gen a; emit "a68_v(a68rt_pop(W));"; gen b
  | .at p e => emit s!"a68_v(a68rt_line({p.line}, W));"; gen e
  | .hole _ _ => emit "a68_v(a68rt_push_void(W));"

partial def genLit (v : Value) : M Unit := do
  match v with
  | .int n =>
    if n ≥ -2147483647 && n ≤ 2147483647 then emit s!"a68_v(a68rt_push_int({n}LL, W));"
    else emit s!"a68rt_push_bigint({← putStr (toString n)});"
  | .real x => emit s!"a68_v(a68rt_push_real({creal x}, W));"
  | .bool b => emit s!"a68_v(a68rt_push_bool({if b then 1 else 0}, W));"
  | .char c => emit s!"a68_v(a68rt_push_char({c}, W));"
  | .bits b => emit s!"a68_v(a68rt_push_bits({b}ULL, W));"
  | .void => emit "a68_v(a68rt_push_void(W));"
  | .nil => emit "a68_v(a68rt_push_nil(W));"
  | .undef => emit "a68_v(a68rt_push_undef(W));"
  | .builtin n => emit s!"a68_v(a68rt_push_builtin({← putStr n}, W));"
  | .file id => emit s!"a68_v(a68rt_push_file({id}, W));"
  | .row _ _ es =>
    if es.all (fun e => match e with | .char _ => true | _ => false) then
      let str := String.ofList (es.toList.map fun e => match e with | .char c => Char.ofNat c | _ => '?')
      emit s!"a68_v(a68rt_push_str({← putStr str}, W));"
    else
      -- a row literal of non-characters: build it element by element
      for e in es do genLit e
      emit s!"a68_v(a68rt_collateral({es.size}, 0, 1, W));"
  | _ => emit "a68_v(a68rt_push_void(W));"

partial def genBlock (size : Nat) (stmts : Array CoreStmt) (labelBase nLabels : Nat) : M Unit := do
  let _ := labelBase
  let _ := nLabels
  let n ← fresh
  emit "{"
  indent do
    emit s!"uint32_t e{n} = a68_env_depth(); uint32_t s{n} = a68_stack_depth();"
    emit s!"a68_v(a68rt_enter({size}, W));"
    emit "a68_v(a68rt_push_void(W));"
    for st in stmts do
      match st with
      | .decl slot init =>
        gen init
        emit s!"a68_v(a68rt_store(0, {slot}, W));"
      | .unit e =>
        gen e
        emit "a68_v(a68rt_nip(W));"
      | .label id =>
        emit s!"L{id}: a68_v(a68rt_env_truncate(e{n}+1, W)); a68_v(a68rt_stack_truncate(s{n}, W));"
        emit "a68_v(a68rt_push_void(W));"
      | .exit => emit s!"goto B{n};"
    emit s!"B{n}: a68_v(a68rt_leave(W));"
  emit "}"

partial def genConformity (sel : Core) (alts : List (Mode × Option Nat × Core)) (out : Core) : M Unit := do
  gen sel
  let n ← fresh
  emit s!"int done{n} = 0;"
  for (m, slot, body) in alts do
    let mi ← putMode m
    emit ("if (!done" ++ toString n ++ " && a68_conform(" ++ toString mi ++ ", " ++ (if slot.isSome then "1" else "0") ++ ")) {")
    indent do
      emit s!"done{n} = 1;"
      -- as in the evaluator: a frame per alternative, empty when nothing is bound
      if slot.isSome then
        emit "a68_v(a68rt_enter(1, W));"
        emit "a68_v(a68rt_bind_cell(0, 0, W));"
      else emit "a68_v(a68rt_enter(0, W));"
      gen body
      emit "a68_v(a68rt_nip(W));"
      emit "a68_v(a68rt_leave(W));"
    emit "}"
  emit ("if (!done" ++ toString n ++ ") {")
  indent do
    gen out
    emit "a68_v(a68rt_nip(W));"
  emit "}"

partial def genLoop (slot : Option Nat) (f b : Core) (t : Option Core) (w : Option Core) (body : Core) : M Unit := do
  let n ← fresh
  gen f
  emit s!"int64_t from{n} = a68_int();"
  gen b
  emit s!"int64_t by{n} = a68_int();"
  match t with
  | some tc => gen tc; emit s!"int64_t to{n} = a68_int(); int has{n} = 1;"
  | none => emit s!"int64_t to{n} = 0; int has{n} = 0;"
  emit ("for (int64_t i" ++ toString n ++ " = from" ++ toString n ++ "; ; i" ++ toString n ++ " += by" ++ toString n ++ ") {")
  indent do
    emit s!"if (has{n} && ((by{n} > 0 && i{n} > to{n}) || (by{n} < 0 && i{n} < to{n}))) break;"
    -- the evaluator pushes a frame for every iteration, empty when there is no counter
    match slot with
    | some sl =>
      emit "a68_v(a68rt_enter(1, W));"
      emit s!"a68_v(a68rt_set_int(0, {sl}, i{n}, W));"
    | none => emit "a68_v(a68rt_enter(0, W));"
    match w with
    | some wc =>
      gen wc
      emit "if (!a68_bool()) { a68_v(a68rt_leave(W)); break; }"
    | none => pure ()
    gen body
    emit "a68_v(a68rt_pop(W));"
    emit "a68_v(a68rt_leave(W));"
  emit "}"
  emit "a68_v(a68rt_push_void(W));"

/-- Compile a routine text into its own C function; returns its index. -/
partial def genFunction (nparams frameSize : Nat) (body : Core) : M Nat := do
  let s ← get
  let idx := s.fns.size
  -- reserve the slot so that nested routines get later indices
  set { s with fns := s.fns.push { name := s!"a68_fn{idx}" } }
  let savedCur := s.cur
  let savedLabels := s.labels
  let savedDepth := s.depth
  modify fun st => { st with cur := #[], labels := labelsOf body, depth := 1 }
  emit s!"a68_v(a68rt_enter_args({frameSize}, {nparams}, W));"
  gen body
  emit "a68_v(a68rt_leave(W));"
  let st ← get
  let lines := st.cur
  let f : Fn := { name := s!"a68_fn{idx}", body := lines }
  set { st with cur := savedCur, labels := savedLabels, depth := savedDepth, fns := st.fns.set! idx f }
  return idx

/-- Format items: the dynamic parts become holes evaluated by compiled code. -/
partial def genFmtItem (it : CoreFmt) : M CoreFmt := do
  match it with
  | .rep n dyn item =>
    let d ← match dyn with
      | some c => some <$> genHole c
      | none => pure none
    return .rep n d (← genFmtItem item)
  | .general args => return .general (← args.mapM genHole)
  | .group items => return .group (← items.mapM genFmtItem)
  | .include f => return .include (← genHole f)
  | other => return other

/-- Compile an expression embedded in a format text into a hole function. -/
partial def genHole (c : Core) : M Core := do
  let s ← get
  let idx := s.holes.size
  set { s with holes := s.holes.push { name := s!"a68_hole{idx}" } }
  let savedCur := s.cur
  let savedLabels := s.labels
  let savedDepth := s.depth
  modify fun st => { st with cur := #[], labels := [], depth := 1 }
  gen c
  let st ← get
  let lines := st.cur
  let f : Fn := { name := s!"a68_hole{idx}", body := lines }
  set { st with cur := savedCur, labels := savedLabels, depth := savedDepth, holes := st.holes.set! idx f }
  return .hole 0 idx

end

/-- The fixed part of every generated program. -/
def prelude : String := "
#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define W lean_io_mk_world()


void lean_initialize_runtime_module(void);
void lean_io_mark_end_initialization(void);
void lean_init_task_manager(void);
char** lean_setup_args(int argc, char** argv);

lean_object* a68rt_boot(lean_object* blob, uint32_t ll, uint8_t reg, lean_object* args, lean_object* w);
lean_object* a68rt_finish(lean_object* w);
lean_object* a68rt_line(uint32_t l, lean_object* w);
lean_object* a68rt_jump_pending(lean_object* w);
lean_object* a68rt_jump_clear(lean_object* w);
lean_object* a68rt_raise_jump(uint32_t l, lean_object* w);
lean_object* a68rt_stop(lean_object* w);
lean_object* a68rt_enter(uint32_t n, lean_object* w);
lean_object* a68rt_enter_args(uint32_t n, uint32_t k, lean_object* w);
lean_object* a68rt_leave(lean_object* w);
lean_object* a68rt_env_depth(lean_object* w);
lean_object* a68rt_env_truncate(uint32_t d, lean_object* w);
lean_object* a68rt_env_set(lean_object* env, lean_object* w);
lean_object* a68rt_env_restore(lean_object* w);
lean_object* a68rt_stack_depth(lean_object* w);
lean_object* a68rt_stack_truncate(uint32_t d, lean_object* w);
lean_object* a68rt_push_int(int64_t v, lean_object* w);
lean_object* a68rt_push_bigint(uint32_t i, lean_object* w);
lean_object* a68rt_push_real(double v, lean_object* w);
lean_object* a68rt_push_bool(uint8_t v, lean_object* w);
lean_object* a68rt_push_char(uint32_t v, lean_object* w);
lean_object* a68rt_push_bits(uint64_t v, lean_object* w);
lean_object* a68rt_push_str(uint32_t i, lean_object* w);
lean_object* a68rt_push_undef(lean_object* w);
lean_object* a68rt_push_nil(lean_object* w);
lean_object* a68rt_push_void(lean_object* w);
lean_object* a68rt_push_builtin(uint32_t i, lean_object* w);
lean_object* a68rt_push_file(uint32_t i, lean_object* w);
lean_object* a68rt_push_skip(uint32_t m, lean_object* w);
lean_object* a68rt_push_cell(uint32_t d, uint32_t s, lean_object* w);
lean_object* a68rt_push_ref(uint32_t d, uint32_t s, lean_object* w);
lean_object* a68rt_push_proc(uint32_t fn, uint32_t np, lean_object* w);
lean_object* a68rt_push_format(uint32_t k, lean_object* w);
lean_object* a68rt_push_array(lean_object* a, lean_object* w);
lean_object* a68rt_store(uint32_t d, uint32_t s, lean_object* w);
lean_object* a68rt_bind_cell(uint32_t d, uint32_t s, lean_object* w);
lean_object* a68rt_set_int(uint32_t d, uint32_t s, int64_t v, lean_object* w);
lean_object* a68rt_pop(lean_object* w);
lean_object* a68rt_nip(lean_object* w);
lean_object* a68rt_dup(lean_object* w);
lean_object* a68rt_pop_int(lean_object* w);
lean_object* a68rt_pop_bool(lean_object* w);
lean_object* a68rt_take_top(lean_object* w);
lean_object* a68rt_deref(lean_object* w);
lean_object* a68rt_deproc(lean_object* w);
lean_object* a68rt_widen(uint32_t a, uint32_t b, lean_object* w);
lean_object* a68rt_row_of(lean_object* w);
lean_object* a68rt_unite(uint32_t m, lean_object* w);
lean_object* a68rt_voiding(lean_object* w);
lean_object* a68rt_assign(uint8_t flex, lean_object* w);
lean_object* a68rt_ident_rel(uint8_t isnt, lean_object* w);
lean_object* a68rt_dyop(uint32_t op, uint32_t m1, uint32_t m2, lean_object* w);
lean_object* a68rt_monop(uint32_t op, uint32_t m, lean_object* w);
lean_object* a68rt_call(uint32_t n, lean_object* w);
lean_object* a68rt_select(uint32_t i, uint8_t viaRef, lean_object* w);
lean_object* a68rt_slice(uint32_t n, uint64_t kinds, uint8_t viaRef, lean_object* w);
lean_object* a68rt_new_row(uint32_t n, uint8_t flex, lean_object* w);
lean_object* a68rt_gen(lean_object* w);
lean_object* a68rt_collateral(uint32_t n, uint8_t st, uint32_t dims, lean_object* w);
lean_object* a68rt_case_index(uint32_t n, lean_object* w);
lean_object* a68rt_conform(uint32_t m, uint8_t bind, lean_object* w);
lean_object* initialize_algol68_A68_Runtime(uint8_t builtin);
void a68_set_state(lean_object* s);

static void a68_fail(lean_object* r) {
  lean_io_result_show_error(r);
  exit(1);
}
static inline lean_object* a68_take(lean_object* r) {
  if (lean_io_result_is_error(r)) a68_fail(r);
  lean_object* v = lean_io_result_take_value(r);
  return v;
}
static inline void a68_v(lean_object* r) {
  if (lean_io_result_is_error(r)) a68_fail(r);
  lean_dec_ref(r);
}
static inline uint32_t a68_u32(lean_object* r) {
  if (lean_io_result_is_error(r)) a68_fail(r);
  uint32_t v = lean_unbox_uint32(lean_io_result_get_value(r));
  lean_dec_ref(r);
  return v;
}
static inline int64_t a68_i64(lean_object* r) {
  if (lean_io_result_is_error(r)) a68_fail(r);
  int64_t v = (int64_t) lean_unbox_uint64(lean_io_result_get_value(r));
  lean_dec_ref(r);
  return v;
}
static inline uint8_t a68_u8(lean_object* r) {
  if (lean_io_result_is_error(r)) a68_fail(r);
  uint8_t v = lean_unbox(lean_io_result_get_value(r));
  lean_dec_ref(r);
  return v;
}
#define a68_jump()        a68_u32(a68rt_jump_pending(W))
#define a68_env_depth()   a68_u32(a68rt_env_depth(W))
#define a68_stack_depth() a68_u32(a68rt_stack_depth(W))
#define a68_bool()        (a68_u8(a68rt_pop_bool(W)) != 0)
#define a68_int()         a68_i64(a68rt_pop_int(W))
#define a68_case(n)       a68_u32(a68rt_case_index(n, W))
#define a68_conform(m,b)  (a68_u8(a68rt_conform(m, b, W)) != 0)
"

/-- Emit the whole program. -/
def program (core : Core) (ll : Nat) (regression : Bool) : String := Id.run do
  let (_, st) := (do
      let idx ← genFunction 0 0 core
      pure idx : M Nat).run {}
  let mut out := prelude
  out := out ++ "\nstatic const char* A68_BLOB =\n"
  -- the blob is emitted in chunks so that no C string literal grows too long
  for chunk in (st.w.render.splitOn "\n") do
    out := out ++ "  " ++ cstring (chunk ++ "\n") ++ "\n"
  out := out ++ ";\n\n"
  for f in st.fns do
    out := out ++ s!"static void {f.name}(void);\n"
  for h in st.holes do
    out := out ++ s!"static void {h.name}(void);\n"
  out := out ++ "\n"
  for f in st.fns do
    out := out ++ "static void " ++ f.name ++ "(void) {\n" ++ "\n".intercalate f.body.toList ++ "\n}\n\n"
  for h in st.holes do
    out := out ++ "static void " ++ h.name ++ "(void) {\n" ++ "\n".intercalate h.body.toList ++ "\n}\n\n"
  -- dispatchers called from the runtime
  out := out ++ "lean_object* a68_dispatch_proc(size_t fn, lean_object* env, lean_object* args, lean_object* w) {\n"
  out := out ++ "  lean_inc(env);\n  a68_v(a68rt_env_set(env, W));\n"
  out := out ++ "  lean_inc(args);\n  a68_v(a68rt_push_array(args, W));\n  switch (fn) {\n"
  for i in [0:st.fns.size] do
    out := out ++ s!"    case {i}: a68_fn{i}(); break;\n"
  out := out ++ "    default: break;\n  }\n"
  out := out ++ "  lean_object* r = a68rt_take_top(lean_io_mk_world());\n  a68_v(a68rt_env_restore(W));\n  return r;\n}\n\n"
  out := out ++ "lean_object* a68_dispatch_hole(size_t fn, size_t idx, lean_object* env, lean_object* w) {\n"
  out := out ++ "  lean_inc(env);\n  a68_v(a68rt_env_set(env, W));\n  switch (idx) {\n"
  for i in [0:st.holes.size] do
    out := out ++ s!"    case {i}: a68_hole{i}(); break;\n"
  out := out ++ "    default: break;\n  }\n"
  out := out ++ "  lean_object* r = a68rt_take_top(lean_io_mk_world());\n  a68_v(a68rt_env_restore(W));\n  return r;\n}\n\n"
  -- main
  out := out ++ "int main(int argc, char** argv) {\n"
  out := out ++ "  argv = lean_setup_args(argc, argv);\n  lean_initialize_runtime_module();\n"
  out := out ++ "  lean_object* ir = initialize_algol68_A68_Runtime(1);\n"
  out := out ++ "  if (lean_io_result_is_error(ir)) { a68_fail(ir); }\n  lean_dec_ref(ir);\n"
  out := out ++ "  lean_io_mark_end_initialization();\n  lean_init_task_manager();\n"
  out := out ++ "  lean_object* args = lean_mk_empty_array();\n"
  out := out ++ "  for (int i = 0; i < argc; i++) args = lean_array_push(args, lean_mk_string(argv[i]));\n"
  out := out ++ s!"  a68_set_state(a68_take(a68rt_boot(lean_mk_string(A68_BLOB), {ll}, {if regression then 1 else 0}, args, W)));\n"
  out := out ++ "  a68_fn0();\n"
  out := out ++ "  uint32_t rc = a68_u32(a68rt_finish(W));\n  return (int) rc;\n}\n"
  return out

end A68.CodeGen
