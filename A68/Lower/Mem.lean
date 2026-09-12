import A68.Lower.State

/-!
# A68.Lower.Mem

Inline memory access to the runtime's objects (`csrc/a68rt.h`): loads and stores at
byte offsets with alias kinds, unchecked arithmetic on addresses, the object tags and
kinds, and guarded control flow to a slow path.
-/
namespace A68.Lower
open A68.MIR

-- ## Memory: the runtime's objects, addressed inline

/-- What a memory access touches, for the printer's alias information: accesses of
    different kinds never overlap, and `KANY` may overlap a cell or a slot. -/
def KCELL : Nat := 1   -- a frame cell
def KHDR : Nat := 2    -- an object header, a descriptor's fields included
def KLEAF : Nat := 3   -- the elements and the defined bitmap of a leaf store
def KSLOT : Nat := 4   -- a value in a slots store: a row element, a field, a union's content
def KANY : Nat := 5    -- a cell or a slot

def ld (w : String) (ty : Ty) (p : Var) (off : Opnd) (kind : Nat := 0) : L Var := do
  let v ← newVar ty
  emit (.set v (.call (.nat s!"mem_ld_{w}") #[.v p, off, ki kind]))
  return v

def st (w : String) (p : Var) (off : Opnd) (v : Opnd) (kind : Nat := 0) : L Unit :=
  emit (.call (.nat s!"mem_st_{w}") #[.v p, off, v, ki kind])

def binv (ty : Ty) (op : BinOp) (a b : Opnd) : L Var := do
  let v ← newVar ty
  emit (.set v (.bin op a b))
  return v

/-- Continue in a fresh block when `c` holds, else go to `no`. -/
def guard (c : Opnd) (no : Nat) : L Unit := do
  let yes ← newBlock
  terminate (.condBr c yes no)
  switchTo yes

/-- The layout of the runtime's objects (`csrc/a68rt.h`). -/
def T_ROW : Int := 9
def K_LEAF : Int := 2
def K_ROWD : Int := 3

/-- The address (object, byte offset) of the value `f OF … OF x[i]` names, for the cell
    `(b, off)` holding the value itself: the row element, then each field through the
    structure object (`rt.c: sel_read`); `slow` when a tag is not as expected. -/
def T_NIL : Int := 7
def K_FRAME : Int := 4

end A68.Lower
