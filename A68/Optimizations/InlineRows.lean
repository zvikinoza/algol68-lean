import A68.Lower.Mem

/-!
# A68.Optimizations.InlineRows

Optimisation: rows, structures and names the runtime keeps are reached inline through
its own object layout — the cell, the descriptor's bounds and stride, the store's
elements and defined bytes, structure objects, names — with a tag check at every step
that falls back to the runtime entry point.  See docs/OPTIMIZATIONS.md §4.
-/
namespace A68.Lower
open A68.MIR

/-- The descriptor of the row cell `(b, off)` holds: a row value, or a name of a sub-row
    (a view, `REF [] INT v = a[2:5]`); anything else takes `slow` (`rt.c: cell_rowd`). -/
def cellRowd (b : Var) (off : Int) (slow : Nat) : L Var := do
  let r ← newVar .ptr
  let tag ← ld "i32" .i64 b (ki off) KCELL
  let isRow ← binv .i1 .eq (.v tag) (ki T_ROW)
  let rowB ← newBlock; let notRow ← newBlock; let done ← newBlock
  terminate (.condBr (.v isRow) rowB notRow)
  switchTo rowB
  let p ← ld "ptr" .ptr b (ki (off + 8)) KCELL
  emit (.set r (.opnd (.v p)))
  terminate (.br done)
  switchTo notRow
  guard (.v (← binv .i1 .eq (.v tag) (ki T_REF))) slow
  let aux ← ld "i32" .i64 b (ki (off + 4)) KCELL
  guard (.v (← binv .i1 .eq (.v aux) (ki VIEW_OFF))) slow
  let p2 ← ld "ptr" .ptr b (ki (off + 8)) KCELL
  let pk ← ld "i8" .i64 p2 (ki 0) KHDR
  guard (.v (← binv .i1 .eq (.v pk) (ki K_ROWD))) slow
  emit (.set r (.opnd (.v p2)))
  terminate (.br done)
  switchTo done
  return r

/-- The store index of `a[i]` or `a[i, j]` for descriptor `r`, with the evaluator's
    subscript checks (`rt.c: elem_index`); `slow` when the descriptor selects a field. -/
def rowIndex (r : Var) (dims : Nat) (is : Array Opnd) (slow : Nat) : L Var := do
  let field ← ld "i32" .i64 r (ki 40) KHDR
  guard (.v (← binv .i1 .eq (.v field) (ki 0))) slow
  let mut idx : Var ← ld "i64" .i64 r (ki 32) KHDR
  for k in [0:dims] do
    let l ← ld "i64" .i64 r (ki (48 + 24 * k)) KHDR
    let u ← ld "i64" .i64 r (ki (56 + 24 * k)) KHDR
    let stride ← ld "i64" .i64 r (ki (64 + 24 * k)) KHDR
    let i := is[k]!
    let ge ← binv .i1 .ge i (.v l)
    let le ← binv .i1 .le i (.v u)
    let inb ← binv .i1 .andB (.v ge) (.v le)
    let errB ← newBlock
    guard (.v inb) errB
    let cur := (← get).fb.cur
    switchTo errB
    rt "a68rt_index_error" #[i, .v l, .v u]
    terminate .unreachable
    switchTo cur
    let t ← binv .i64 .subW i (.v l)
    let m ← binv .i64 .mulW (.v t) (.v stride)
    idx ← binv .i64 .addW (.v idx) (.v m)
  return idx

/-- The store of descriptor `r`: through the owner when the descriptor is a view. -/
def rowStore (r : Var) : L Var := do
  let base ← ld "ptr" .ptr r (ki 24) KHDR
  let bk ← ld "i8" .i64 base (ki 0) KHDR
  let store ← newVar .ptr
  emit (.set store (.opnd (.v base)))
  let isView ← binv .i1 .eq (.v bk) (ki K_ROWD)
  let viaB ← newBlock; let cont ← newBlock
  terminate (.condBr (.v isView) viaB cont)
  switchTo viaB
  let inner ← ld "ptr" .ptr base (ki 24) KHDR
  emit (.set store (.opnd (.v inner)))
  terminate (.br cont)
  switchTo cont
  return store

/-- The store and store index of `a[i]` or `a[i, j]` for the row cell `(b, off)` holds,
    with the evaluator's subscript checks, continuing in the fast block; `slow` is taken
    when the cell does not hold a row value itself, when its descriptor selects a field,
    or when the store is not a leaf of the element's kind (`rt.c: row_elem`). -/
def rowLeafElem (b : Var) (off : Int) (dims : Nat) (is : Array Opnd) (info : ElemInfo) (slow : Nat) : L (Var × Var × Var) := do
  let r ← cellRowd b off slow
  let idx ← rowIndex r dims is slow
  let store ← rowStore r
  let sk ← ld "i8" .i64 store (ki 0) KHDR
  guard (.v (← binv .i1 .eq (.v sk) (ki K_LEAF))) slow
  let ek ← ld "i16" .i64 store (ki 2) KHDR
  guard (.v (← binv .i1 .eq (.v ek) (ki info.ek))) slow
  return (r, store, idx)

/-- The address of the value the name in cell `(b, off)` refers to: a slot of a structure
    object or a cell of a frame (`rt.c: ref_slot`); `slow` for NIL, an undefined name, or
    a name into a row (which the runtime resolves). -/
def refTarget (b : Var) (off : Int) (slow : Nat) : L (Var × Opnd) := do
  let tag ← ld "i32" .i64 b (ki off) KCELL
  guard (.v (← binv .i1 .eq (.v tag) (ki T_REF))) slow
  let aux ← ld "i32" .i64 b (ki (off + 4)) KCELL
  let obj ← ld "ptr" .ptr b (ki (off + 8)) KCELL
  let kind ← ld "i8" .i64 obj (ki 0) KHDR
  let base ← newVar .i64
  let isSlots ← binv .i1 .eq (.v kind) (ki K_SLOTS)
  let slotsB ← newBlock; let notSlots ← newBlock; let cont ← newBlock
  terminate (.condBr (.v isSlots) slotsB notSlots)
  switchTo slotsB
  emit (.set base (.opnd (ki 24)))
  terminate (.br cont)
  switchTo notSlots
  guard (.v (← binv .i1 .eq (.v kind) (ki K_FRAME))) slow
  emit (.set base (.opnd (ki 40)))
  terminate (.br cont)
  switchTo cont
  let o ← binv .i64 .addW (.v base) (.v aux)
  return (obj, .v o)

/-- Read the primitive value at `(p, off)` as `ty`; `slow` when its tag is not `info.ek`
    (an undefined value included: the runtime reports it). -/
def valGet (p : Var) (off : Opnd) (info : ElemInfo) (ty : Ty) (slow : Nat) (kind : Nat := 0) : L Var := do
  let tag ← ld "i32" .i64 p off kind
  guard (.v (← binv .i1 .eq (.v tag) (ki info.ek))) slow
  let vo ← binv .i64 .addW off (ki 8)
  let raw ← ld (if info.w == "f64" then "f64" else "i64") (if info.w == "f64" then .f64 else .i64) p (.v vo) kind
  match ty with
  | .i1 => binv .i1 .ne (.v raw) (ki 0)
  | .i32 => do let v ← newVar .i32; emit (.set v (.opnd (.v raw))); return v
  | _ => return raw

/-- Write the primitive value `v` at `(p, off)`: tag, aux 0, payload (`rt.c: mk_int`). -/
def valSet (p : Var) (off : Opnd) (info : ElemInfo) (v : Opnd) (kind : Nat := 0) : L Unit := do
  st "i32" p off (ki info.ek) kind
  let ao ← binv .i64 .addW off (ki 4)
  st "i32" p (.v ao) (ki 0) kind
  let vo ← binv .i64 .addW off (ki 8)
  st (if info.w == "f64" then "f64" else "i64") p (.v vo) v kind

/-- The offset of the defined byte of store index `idx` in a leaf: after the elements. -/
def leafFlag (store idx : Var) (es : Nat) (n? : Option Var := none) : L Var := do
  let n ← match n? with
    | some n => pure n
    | none => ld "i32" .i64 store (ki 4) KHDR
  let bytes ← binv .i64 .mulW (.v n) (ki es)
  let o1 ← binv .i64 .addW (.v bytes) (.v idx)
  binv .i64 .addW (.v o1) (ki 24)

/-- The element at store index `idx` of a leaf, as a value of the element's MIR type;
    an undefined element is reported as the evaluator reports it. -/
def leafGet (store idx : Var) (info : ElemInfo) (ty : Ty) (n? : Option Var := none) : L Var := do
  let foff ← leafFlag store idx info.es n?
  let flag ← ld "i8" .i64 store (.v foff) KLEAF
  let undefB ← newBlock
  guard (.v (← binv .i1 .ne (.v flag) (ki 0))) undefB
  let cur := (← get).fb.cur
  switchTo undefB
  rt "a68rt_undef_error" #[ku info.kind]
  terminate .unreachable
  switchTo cur
  let eoff ← binv .i64 .mulW (.v idx) (ki info.es)
  let eoff ← binv .i64 .addW (.v eoff) (ki 24)
  let raw ← ld info.w (if info.w == "f64" then .f64 else .i64) store (.v eoff) KLEAF
  match ty with
  | .i1 => binv .i1 .ne (.v raw) (ki 0)
  | .i32 => do let v ← newVar .i32; emit (.set v (.opnd (.v raw))); return v
  | _ => return raw

/-- Write the element at store index `idx` of a leaf and mark it defined. -/
def leafSet (store idx : Var) (info : ElemInfo) (v : Opnd) (n? : Option Var := none) : L Unit := do
  let foff ← leafFlag store idx info.es n?
  st "i8" store (.v foff) (ki 1) KLEAF
  let eoff ← binv .i64 .mulW (.v idx) (ki info.es)
  let eoff ← binv .i64 .addW (.v eoff) (ki 24)
  st info.w store (.v eoff) v KLEAF

end A68.Lower
