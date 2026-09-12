import A68.Core

/-!
# A68.MIR — the typed intermediate representation of the LLVM back end

A program is a set of functions; a function is a set of basic blocks over typed
variables (docs/LLVM-DESIGN.md §2).  A variable may be assigned more than once: the
LLVM printer gives each an `alloca` and LLVM's `mem2reg` builds the SSA form, as clang
does for C locals, which keeps the lowering and the semantics simple.

Milestone 1 has only scalar types; values of every other mode live in the runtime and
pass through the operand stack, so a function of this representation and one compiled
by the C back end are interchangeable.
-/
namespace A68.MIR

inductive Ty where
  | i64      -- INT and BITS
  | f64      -- REAL
  | i1       -- BOOL
  | i32      -- CHAR
  | ptr      -- an opaque pointer: a native entry point
  deriving Repr, BEq, Inhabited, DecidableEq

structure Var where
  id : Nat
  ty : Ty
  deriving Repr, BEq, Inhabited

inductive Const where
  | i (n : Int)         -- i64 and i32 (as a natural), i1 as 0/1
  | f (x : Float)
  deriving Repr, Inhabited

inductive Opnd where
  | v (x : Var)
  | k (ty : Ty) (c : Const)
  deriving Repr, Inhabited

def Opnd.ty : Opnd → Ty
  | .v x => x.ty
  | .k t _ => t

/-- Dyadic scalar operations, each with the check its interpreted counterpart performs
    (`Interp.dyadic`); a check that fails traps with a68g's message. -/
inductive BinOp where
  | addI | subI | mulI      -- INT, overflow past ±2147483647 traps
  | overI | modI            -- INT, zero divisor traps; MOD is non-negative
  | powI                    -- INT ** INT, square-and-multiply with the checks
  | addF | subF | mulF      -- REAL, a NaN or infinite result traps
  | divF                    -- REAL, a zero divisor traps, the quotient is not checked
  | powFI | powFF           -- REAL ** INT, REAL ** REAL
  | eq | ne | lt | le | gt | ge   -- on i64, f64, i32, i1 (BOOL = and /=)
  | andB | orB | xorB       -- BOOL (both operands evaluated)
  | andU | orU | xorU       -- BITS
  | addW | subW | mulW      -- i64, wrapping, unchecked: address arithmetic
  | shlW | shrW | andW | orW   -- i64 bit operations, unchecked: address arithmetic
  deriving Repr, BEq, Inhabited

inductive UnOp where
  | negI | absI | signI | oddI | reprI
  | negF | absF | signF | entier | round
  | notB | absB | absC
  | i2f                     -- INT widened to REAL
  | math (name : String)    -- the REAL standard functions computed natively (`a68n_m_<name>`)
  deriving Repr, BEq, Inhabited

/-- What a call reaches. -/
inductive Callee where
  | rt (name : String)      -- an entry point of the C runtime, by name
  | fn (idx : Nat)          -- a compiled routine, boxed convention (`a68_fn<idx>`)
  | hole (idx : Nat)        -- a format hole (`a68_hole<idx>`)
  | nat (name : String)     -- a native helper of the LLVM runtime support (`a68n_*`)
  | nfn (idx : Nat)         -- a compiled routine, plain convention: typed arguments and result (`a68_nf<idx>`)
  | ind (ptys : Array Ty) (rty : Option Ty)   -- a plain routine reached through a pointer: the first argument
  deriving Repr, BEq, Inhabited

inductive Rhs where
  | opnd (o : Opnd)
  | bin (op : BinOp) (a b : Opnd)
  | un (op : UnOp) (a : Opnd)
  | call (f : Callee) (args : Array Opnd)
  | natTab (i : Opnd)       -- the plain entry point of boxed routine `i - 1`, null when it has none
  deriving Repr, Inhabited

inductive Instr where
  | set (dst : Var) (rhs : Rhs)
  | call (f : Callee) (args : Array Opnd)     -- result discarded or void
  | line (n : Nat)                            -- the source line reached
  deriving Repr, Inhabited

inductive Term where
  | br (b : Nat)
  | condBr (c : Opnd) (t f : Nat)
  | switch (o : Opnd) (cases : Array (Int × Nat)) (dflt : Nat)
  | ret
  | retVal (o : Opnd)
  | unreachable
  deriving Repr, Inhabited

structure Block where
  instrs : Array Instr := #[]
  term   : Term := .ret
  deriving Repr, Inhabited

structure Func where
  name   : String
  vars   : Array Ty := #[]
  blocks : Array Block := #[]     -- block 0 is the entry
  params : Array Ty := #[]        -- a plain routine: its parameters are variables 0 .. params.size-1
  ret    : Option Ty := none
  deriving Repr, Inhabited

/-- A whole program: its routines, its format holes, the tables it carries and what
    `main` needs. -/
structure Program where
  fns     : Array Func
  holes   : Array Func
  nfns    : Array Func            -- the plain routines
  nfnTab  : Array (Option Nat)    -- per boxed routine: its plain entry point, when a call through a value may use it
  blob    : String
  src     : String
  ll      : Nat
  regression : Bool
  echoes  : List String
  deriving Inhabited

/-- The signatures of the runtime entry points the lowering calls (`csrc/rt.c`); every
    one takes the trailing dummy `int w`.  Result types: `i64`, `f64`, `i1` (a C
    `uint8_t`), `i32`, or none. -/
inductive RtRet where
  | none | i64 | f64 | u8 | u32 | ptr
  deriving Repr, BEq, Inhabited

structure RtSig where
  args : Array Ty
  ret  : RtRet
  deriving Repr, Inhabited

/-- `i32` here means a C `uint32_t` argument (a table index, a depth, a slot); `i64` a
    `int64_t`/`uint64_t`; `i1` a `uint8_t`; `f64` a `double`. -/
def rtSigs : List (String × RtSig) :=
  let u32 := Ty.i32
  [ ("a68rt_enter", ⟨#[u32], .ptr⟩), ("a68rt_enter_args", ⟨#[u32, u32], .ptr⟩), ("a68rt_leave", ⟨#[], .none⟩),
    ("a68rt_frame_cells", ⟨#[u32], .ptr⟩),
    ("a68rt_env_depth", ⟨#[], .u32⟩), ("a68rt_env_truncate", ⟨#[u32], .none⟩),
    ("a68rt_stack_depth", ⟨#[], .u32⟩), ("a68rt_stack_truncate", ⟨#[u32], .none⟩),
    ("a68rt_jump_pending", ⟨#[], .u32⟩), ("a68rt_jump_clear", ⟨#[], .none⟩), ("a68rt_raise_jump", ⟨#[u32], .none⟩),
    ("a68rt_push_int", ⟨#[.i64], .none⟩), ("a68rt_push_real", ⟨#[.f64], .none⟩), ("a68rt_push_bool", ⟨#[.i1], .none⟩),
    ("a68rt_push_char", ⟨#[u32], .none⟩), ("a68rt_push_bits", ⟨#[.i64], .none⟩),
    ("a68rt_push_undef", ⟨#[], .none⟩), ("a68rt_push_nil", ⟨#[], .none⟩), ("a68rt_push_void", ⟨#[], .none⟩),
    ("a68rt_push_builtin", ⟨#[u32], .none⟩), ("a68rt_push_file", ⟨#[u32], .none⟩),
    ("a68rt_push_bigint", ⟨#[u32], .none⟩), ("a68rt_push_bigbits", ⟨#[u32], .none⟩), ("a68rt_push_str", ⟨#[u32], .none⟩),
    ("a68rt_push_skip", ⟨#[u32], .none⟩), ("a68rt_pop", ⟨#[], .none⟩), ("a68rt_dup", ⟨#[], .none⟩), ("a68rt_nip", ⟨#[], .none⟩),
    ("a68rt_push_cell", ⟨#[u32, u32], .none⟩), ("a68rt_push_ref", ⟨#[u32, u32], .none⟩),
    ("a68rt_store", ⟨#[u32, u32], .none⟩), ("a68rt_bind_cell", ⟨#[u32, u32], .none⟩), ("a68rt_set_int", ⟨#[u32, u32, .i64], .none⟩),
    ("a68rt_cell_int", ⟨#[u32, u32], .i64⟩), ("a68rt_cell_real", ⟨#[u32, u32], .f64⟩), ("a68rt_cell_bool", ⟨#[u32, u32], .u8⟩),
    ("a68rt_cell_char", ⟨#[u32, u32], .u32⟩), ("a68rt_cell_bits", ⟨#[u32, u32], .i64⟩),
    ("a68rt_set_cell_int", ⟨#[u32, u32, .i64], .none⟩), ("a68rt_set_cell_real", ⟨#[u32, u32, .f64], .none⟩),
    ("a68rt_set_cell_bool", ⟨#[u32, u32, .i1], .none⟩), ("a68rt_set_cell_char", ⟨#[u32, u32, u32], .none⟩),
    ("a68rt_set_cell_bits", ⟨#[u32, u32, .i64], .none⟩),
    ("a68rt_pop_int", ⟨#[], .i64⟩), ("a68rt_pop_real", ⟨#[], .f64⟩), ("a68rt_pop_bool", ⟨#[], .u8⟩),
    ("a68rt_pop_char", ⟨#[], .u32⟩), ("a68rt_pop_bits", ⟨#[], .i64⟩),
    ("a68rt_cell_isnil", ⟨#[u32, u32], .u8⟩), ("a68rt_cell_cproc", ⟨#[u32, u32], .u32⟩),
    ("a68rt_row_int", ⟨#[u32, u32, u32, .i64, .i64], .i64⟩), ("a68rt_row_real", ⟨#[u32, u32, u32, .i64, .i64], .f64⟩),
    ("a68rt_row_bool", ⟨#[u32, u32, u32, .i64, .i64], .u8⟩), ("a68rt_row_char", ⟨#[u32, u32, u32, .i64, .i64], .u32⟩),
    ("a68rt_row_bits", ⟨#[u32, u32, u32, .i64, .i64], .i64⟩),
    ("a68rt_set_row_int", ⟨#[u32, u32, u32, .i64, .i64, .i64], .none⟩), ("a68rt_set_row_real", ⟨#[u32, u32, u32, .i64, .i64, .f64], .none⟩),
    ("a68rt_set_row_bool", ⟨#[u32, u32, u32, .i64, .i64, .i1], .none⟩), ("a68rt_set_row_char", ⟨#[u32, u32, u32, .i64, .i64, u32], .none⟩),
    ("a68rt_set_row_bits", ⟨#[u32, u32, u32, .i64, .i64, .i64], .none⟩),
    ("a68rt_sel_int", ⟨#[u32, u32, u32, .i64, .i64, u32], .i64⟩), ("a68rt_sel_real", ⟨#[u32, u32, u32, .i64, .i64, u32], .f64⟩),
    ("a68rt_sel_bool", ⟨#[u32, u32, u32, .i64, .i64, u32], .u8⟩), ("a68rt_sel_char", ⟨#[u32, u32, u32, .i64, .i64, u32], .u32⟩),
    ("a68rt_sel_bits", ⟨#[u32, u32, u32, .i64, .i64, u32], .i64⟩),
    ("a68rt_set_sel_int", ⟨#[u32, u32, u32, .i64, .i64, u32, .i64], .none⟩), ("a68rt_set_sel_real", ⟨#[u32, u32, u32, .i64, .i64, u32, .f64], .none⟩),
    ("a68rt_set_sel_bool", ⟨#[u32, u32, u32, .i64, .i64, u32, .i1], .none⟩), ("a68rt_set_sel_char", ⟨#[u32, u32, u32, .i64, .i64, u32, u32], .none⟩),
    ("a68rt_set_sel_bits", ⟨#[u32, u32, u32, .i64, .i64, u32, .i64], .none⟩),
    ("a68rt_sel_push", ⟨#[u32, u32, u32, .i64, .i64, u32], .none⟩), ("a68rt_sel_store", ⟨#[u32, u32, u32, u32, u32, .i64, .i64, u32], .none⟩),
    ("a68rt_append_char", ⟨#[u32, u32, u32], .none⟩), ("a68rt_append", ⟨#[u32, u32], .none⟩),
    ("a68rt_undef_error", ⟨#[u32], .none⟩), ("a68rt_index_error", ⟨#[.i64, .i64, .i64], .none⟩), ("a68rt_arith_error", ⟨#[u32], .none⟩),
    ("a68rt_deref", ⟨#[], .none⟩), ("a68rt_deproc", ⟨#[], .none⟩), ("a68rt_call", ⟨#[u32], .none⟩),
    ("a68rt_widen", ⟨#[u32, u32], .none⟩), ("a68rt_row_of", ⟨#[], .none⟩), ("a68rt_unite", ⟨#[u32], .none⟩),
    ("a68rt_voiding", ⟨#[], .none⟩), ("a68rt_assign", ⟨#[.i1], .none⟩), ("a68rt_ident_rel", ⟨#[.i1], .none⟩),
    ("a68rt_dyop", ⟨#[u32, u32, u32], .none⟩), ("a68rt_monop", ⟨#[u32, u32], .none⟩),
    ("a68rt_select", ⟨#[u32, .i1], .none⟩), ("a68rt_slice", ⟨#[u32, .i64, .i1], .none⟩),
    ("a68rt_new_row", ⟨#[u32, .i1], .none⟩), ("a68rt_new_row_of", ⟨#[u32, .i1, u32], .none⟩), ("a68rt_gen", ⟨#[], .none⟩),
    ("a68rt_collateral", ⟨#[u32, .i1, u32], .none⟩), ("a68rt_push_proc", ⟨#[u32, u32], .none⟩),
    ("a68rt_push_format", ⟨#[u32], .none⟩), ("a68rt_case_index", ⟨#[u32], .u32⟩), ("a68rt_conform", ⟨#[u32, .i1], .u8⟩),
    ("a68rt_stop", ⟨#[], .none⟩), ("a68rt_line", ⟨#[u32], .none⟩),
    ("a68rt_finish", ⟨#[], .u32⟩) ]

/-- The native helpers (`csrc/native.c`): the pieces of a68g's arithmetic that are not one
    LLVM instruction and a check. -/
def natSigs : List (String × RtSig) :=
  [ ("a68n_pow_i", ⟨#[.i64, .i64], .i64⟩), ("a68n_pow_ri", ⟨#[.f64, .i64], .f64⟩), ("a68n_pow_rr", ⟨#[.f64, .f64], .f64⟩),
    ("a68n_entier", ⟨#[.f64], .i64⟩), ("a68n_round", ⟨#[.f64], .i64⟩), ("a68n_echo", ⟨#[u32], .none⟩),
    -- memory access, printed inline: a load or store of the given width at a byte offset from
    -- a pointer; the narrow loads zero-extend to i64, the narrow stores truncate
    ("mem_ld_i8", ⟨#[.ptr, .i64], .i64⟩), ("mem_ld_i16", ⟨#[.ptr, .i64], .i64⟩), ("mem_ld_i32", ⟨#[.ptr, .i64], .i64⟩),
    ("mem_ld_i64", ⟨#[.ptr, .i64], .i64⟩), ("mem_ld_f64", ⟨#[.ptr, .i64], .f64⟩), ("mem_ld_ptr", ⟨#[.ptr, .i64], .ptr⟩),
    ("mem_st_i8", ⟨#[.ptr, .i64, .i64], .none⟩), ("mem_st_i32", ⟨#[.ptr, .i64, .i64], .none⟩),
    ("mem_st_i64", ⟨#[.ptr, .i64, .i64], .none⟩), ("mem_st_f64", ⟨#[.ptr, .i64, .f64], .none⟩) ]
where u32 := Ty.i32

/-- The result type of a runtime call as MIR sees it. -/
def RtRet.ty : RtRet → Option Ty
  | .none => Option.none | .i64 => some .i64 | .f64 => some .f64 | .u8 => some .i1 | .u32 => some .i32 | .ptr => some .ptr

-- ## A readable rendering, for `a68lean dump-mir` and for debugging

def Ty.show : Ty → String
  | .i64 => "i64" | .f64 => "f64" | .i1 => "i1" | .i32 => "i32" | .ptr => "ptr"

def Opnd.show : Opnd → String
  | .v x => s!"%{x.id}"
  | .k _ (.i n) => toString n
  | .k _ (.f x) => toString x

def Callee.show : Callee → String
  | .rt n => n | .fn i => s!"fn{i}" | .hole i => s!"hole{i}" | .nat n => n | .nfn i => s!"nf{i}" | .ind _ _ => "*"

def Rhs.show : Rhs → String
  | .opnd o => o.show
  | .bin op a b => s!"{repr op} {a.show} {b.show}"
  | .un op a => s!"{repr op} {a.show}"
  | .call f as => s!"{f.show}({", ".intercalate (as.toList.map Opnd.show)})"
  | .natTab i => s!"nf_of_fn[{i.show}]"

def Instr.show : Instr → String
  | .set d r => s!"%{d.id} : {d.ty.show} = {r.show}"
  | .call f as => s!"{f.show}({", ".intercalate (as.toList.map Opnd.show)})"
  | .line n => s!"line {n}"

def Term.show : Term → String
  | .br b => s!"br b{b}"
  | .condBr c t f => s!"br {c.show} ? b{t} : b{f}"
  | .switch o cs d => s!"switch {o.show} [{", ".intercalate (cs.toList.map fun (k, b) => s!"{k} -> b{b}")}] default b{d}"
  | .ret => "ret"
  | .retVal o => s!"ret {o.show}"
  | .unreachable => "unreachable"

def Func.show (f : Func) : String := Id.run do
  let mut out := s!"{f.name}({", ".intercalate (f.params.toList.map Ty.show)}):\n"
  for i in [0:f.blocks.size] do
    let b := f.blocks[i]!
    out := out ++ s!"  b{i}:\n"
    for ins in b.instrs do out := out ++ "    " ++ ins.show ++ "\n"
    out := out ++ "    " ++ b.term.show ++ "\n"
  return out

def Program.show (p : Program) : String :=
  String.join (p.fns.toList.map Func.show) ++ String.join (p.nfns.toList.map Func.show) ++ String.join (p.holes.toList.map Func.show)

end A68.MIR
