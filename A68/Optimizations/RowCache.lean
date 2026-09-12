import A68.Optimizations.InlineRows
import A68.Optimizations.RowPromotion

/-!
# A68.Optimizations.RowCache

Optimisation: the loop row cache.  A loop that calls nothing that could change a cell
or a store keeps each row's descriptor, bounds and store in registers for its duration,
recomputing them after any slow path; runtime calls that change one named cell only
are tagged so that the caches of other rows survive them.  Also the field, element
write and append paths that use the cache.  See docs/OPTIMIZATIONS.md §4.
-/
namespace A68.Lower
open A68.MIR

/-- The cache in scope for the row cell `(fid, slot)` with store kind `ek`. -/
def lookupCache (fid slot : Nat) (ek : Int) : L (Option RowCache) := do
  return (← get).caches.find? fun c => c.fid == fid && c.slot == slot && c.ek == ek

/-- Note an inline access to a row, for the loop that may cache it. -/
def noteRowUse (fid slot : Nat) (ek : Int) (dims : Nat) : L Unit :=
  modify fun st => { st with rowUses := st.rowUses.push (fid, slot, ek, dims) }

/-- A slow path: the block `slow` and every block created by `act` are marked as such, so
    that a loop does not count their runtime calls against caching; afterwards the caches
    of the cell `key` (all of them when `key` is `none`) are recomputed, since the call
    may have changed the cell or its store. -/
def slowPath (slow : Nat) (key : Option (Nat × Nat)) (act : L Unit) : L Unit := do
  let a := (← get).fb.blocks.size
  act
  -- recompute the caches this call may have invalidated
  let cs := (← get).caches.filter fun c => match key with
    | some (fid, slot) => c.fid == fid && c.slot == slot
    | none => true
  for c in cs do recache c
  let b := (← get).fb.blocks.size
  modify fun st => { st with slowRanges := (st.slowRanges.push (slow, slow + 1)).push (a, b) }
where
  /-- compute the cache from the cell: valid only when everything is as the accesses expect -/
  recache (c : RowCache) : L Unit := do
    let done ← newBlock
    emit (.set c.valid (.opnd (kb false)))
    emit (.set c.rcOK (.opnd (kb false)))
    let fb := (← get).fb
    -- the cell's address: this frame's cells, or a captured frame's
    let d? := (List.range fb.frames.length).find? fun d => match fb.frames[d]? with
      | some f => !f.outer && f.fid == c.fid
      | none => false
    let addr : Option (Var × Int) ← match d? with
      | some d => cellAddr d c.slot
      | none =>
        if c.fid ≥ 1000000 then
          let own := (fb.frames.takeWhile (!·.outer)).length
          cellAddr (own + (c.fid - 1000000)) c.slot
        else pure none
    -- the bounds the row was declared with, when the variable keeps them for life
    let known : Option (List (Int × Int)) := match d? with
      | some d => match fb.frames[d]? with
        | some f => (f.bounds[c.slot]?).join
        | none => none
      | none => none
    match addr with
    | none => terminate (.br done); switchTo done
    | some (b, off) =>
      let tag ← ld "i32" .i64 b (ki off) KCELL
      guard (.v (← binv .i1 .eq (.v tag) (ki T_ROW))) done
      let r ← ld "ptr" .ptr b (ki (off + 8)) KCELL
      emit (.set c.r (.opnd (.v r)))
      let field ← ld "i32" .i64 r (ki 40) KHDR
      guard (.v (← binv .i1 .eq (.v field) (ki 0))) done
      match known with
      | some bs =>
        -- a fresh row's descriptor: offset 0, the last dimension's stride 1, each earlier
        -- one's the extent of the next (`rt.c: a68rt_new_row_of`)
        emit (.set c.off (.opnd (ki 0)))
        let mut stride : Int := 1
        let mut strides : Array Int := Array.replicate c.dims 1
        for k' in [0:c.dims] do
          let k := c.dims - 1 - k'
          strides := strides.set! k stride
          let (l, u) := bs[k]!
          let ext := u - l + 1
          stride := stride * (if ext > 0 then ext else 0)
        for k in [0:c.dims] do
          let (lv, uv, sv) := c.dim[k]!
          let (l, u) := bs[k]!
          emit (.set lv (.opnd (ki l))); emit (.set uv (.opnd (ki u))); emit (.set sv (.opnd (ki strides[k]!)))
      | none =>
        let off0 ← ld "i64" .i64 r (ki 32) KHDR
        emit (.set c.off (.opnd (.v off0)))
        for k in [0:c.dims] do
          let (lv, uv, sv) := c.dim[k]!
          let l ← ld "i64" .i64 r (ki (48 + 24 * k)) KHDR
          let u ← ld "i64" .i64 r (ki (56 + 24 * k)) KHDR
          let stride ← ld "i64" .i64 r (ki (64 + 24 * k)) KHDR
          emit (.set lv (.opnd (.v l))); emit (.set uv (.opnd (.v u))); emit (.set sv (.opnd (.v stride)))
      let store ← rowStore r
      emit (.set c.store (.opnd (.v store)))
      let sk ← ld "i8" .i64 store (ki 0) KHDR
      if c.ek == 0 then
        guard (.v (← binv .i1 .eq (.v sk) (ki K_SLOTS))) done
      else
        guard (.v (← binv .i1 .eq (.v sk) (ki K_LEAF))) done
        let ek ← ld "i16" .i64 store (ki 2) KHDR
        guard (.v (← binv .i1 .eq (.v ek) (ki c.ek))) done
      let n ← ld "i32" .i64 store (ki 4) KHDR
      emit (.set c.n (.opnd (.v n)))
      emit (.set c.valid (.opnd (kb true)))
      let rc ← ld "i32" .i64 store (ki 8) KHDR
      let ok ← binv .i1 .le (.v rc) (ki 1)
      emit (.set c.rcOK (.opnd (.v ok)))
      terminate (.br done)
      switchTo done

/-- Recompute the caches of cell `(fid, slot)`. -/
def recacheFor (fid slot : Nat) : L Unit := do
  for c in (← get).caches do
    if c.fid == fid && c.slot == slot then slowPath.recache c

/-- A runtime call whose only effect is on the cell `(fid, slot)` it names (`a68rt_append*`):
    a loop's caches of other rows survive it, and this cell's are recomputed after it. -/
def rtCell (name : String) (fid slot : Nat) (args : Array Opnd) : L Unit := do
  let fb := (← get).fb
  let at_ := (fb.cur, fb.blocks[fb.cur]!.instrs.size)
  rt name args
  modify fun st => { st with cellCalls := st.cellCalls.push at_ }
  recacheFor fid slot

/-- The store index of `a[i]` or `a[i, j]` from a cache, with the subscript checks. -/
def rowIndexCached (c : RowCache) (is : Array Opnd) : L Var := do
  let mut idx : Var := c.off
  for k in [0:c.dims] do
    let (l, u, stride) := c.dim[k]!
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

/-- `rowLeafElem` through the loop's cache when there is one: the store, the index, and
    the store's element count when it is known. -/
def rowLeafElemC (fid : Nat) (b : Var) (off : Int) (s dims : Nat) (is : Array Opnd) (info : ElemInfo) (slow : Nat) : L (Var × Var × Option Var × Option RowCache) := do
  noteRowUse fid s info.ek dims
  match ← lookupCache fid s info.ek with
  | some c =>
    guard (.v c.valid) slow
    let idx ← rowIndexCached c is
    return (c.store, idx, some c.n, some c)
  | none =>
    let (_, store, idx) ← rowLeafElem b off dims is info slow
    return (store, idx, none, none)


def selAddr (b : Var) (off : Int) (rank : Nat) (is : Array Opnd) (fields : List Nat) (slow : Nat) (via : Bool := false)
    (key : Option (Nat × Nat) := none) : L (Var × Opnd × Nat) := do
  let mut cur : Var × Opnd × Nat := (b, ki off, KCELL)
  if via then
    let (p, o) ← refTarget b off slow
    cur := (p, o, KANY)
  if rank > 0 then
    let cached : Option RowCache ← match key with
      | some (fid, slot) =>
        noteRowUse fid slot 0 rank
        lookupCache fid slot 0
      | none => pure none
    let (store, idx) ← match cached with
      | some c =>
        guard (.v c.valid) slow
        let idx ← rowIndexCached c is
        pure (c.store, idx)
      | none =>
        let r ← cellRowd b off slow
        let idx ← rowIndex r rank is slow
        let store ← rowStore r
        let sk ← ld "i8" .i64 store (ki 0) KHDR
        guard (.v (← binv .i1 .eq (.v sk) (ki K_SLOTS))) slow
        pure (store, idx)
    let eo ← binv .i64 .mulW (.v idx) (ki 16)
    let eo ← binv .i64 .addW (.v eo) (ki 24)
    cur := (store, .v eo, KSLOT)
  for f in fields do
    let tag ← ld "i32" .i64 cur.1 cur.2.1 cur.2.2
    guard (.v (← binv .i1 .eq (.v tag) (ki T_STRUCT))) slow
    let po ← binv .i64 .addW cur.2.1 (ki 8)
    let sp ← ld "ptr" .ptr cur.1 (.v po) cur.2.2
    cur := (sp, ki (24 + 16 * f), KSLOT)
  return cur

/-- `s +:= v` for one element `v` on the row variable cell `(d, s)` holds: inline when the
    row starts at 1, is its own owner, unshared, over a leaf store of the element's kind
    with room to spare (`rt.c: append_in_place`): the element and its defined byte are
    written after the last one and the upper bound moves up; otherwise the runtime, which
    grows the store or takes the operator's way. -/
def appendElem (d s : Nat) (em : Mode) (v : Opnd) (fn : String) : L Unit := do
  let fid ← cellFid d
  match ← cellAddr d s, elemInfo em with
  | some (b, off), some info =>
    noteRowUse fid s info.ek 1
    let slow ← newBlock; let done ← newBlock
    let (r, store, u, n?, uv?) : Var × Var × Var × Option Var × Option Var ← match ← lookupCache fid s info.ek with
      | some c =>
        guard (.v c.valid) slow
        guard (.v c.rcOK) slow
        let (l, u, stride) := c.dim[0]!
        guard (.v (← binv .i1 .eq (.v l) (ki 1))) slow
        guard (.v (← binv .i1 .eq (.v c.off) (ki 0))) slow
        guard (.v (← binv .i1 .eq (.v stride) (ki 1))) slow
        pure (c.r, c.store, u, some c.n, some u)
      | none =>
        let r ← cellRowd b off slow
        let field ← ld "i32" .i64 r (ki 40) KHDR
        guard (.v (← binv .i1 .eq (.v field) (ki 0))) slow
        let l ← ld "i64" .i64 r (ki 48) KHDR
        guard (.v (← binv .i1 .eq (.v l) (ki 1))) slow
        let off0 ← ld "i64" .i64 r (ki 32) KHDR
        guard (.v (← binv .i1 .eq (.v off0) (ki 0))) slow
        let stride ← ld "i64" .i64 r (ki 64) KHDR
        guard (.v (← binv .i1 .eq (.v stride) (ki 1))) slow
        let u ← ld "i64" .i64 r (ki 56) KHDR
        let store ← ld "ptr" .ptr r (ki 24) KHDR
        let sk ← ld "i8" .i64 store (ki 0) KHDR
        guard (.v (← binv .i1 .eq (.v sk) (ki K_LEAF))) slow
        let ek ← ld "i16" .i64 store (ki 2) KHDR
        guard (.v (← binv .i1 .eq (.v ek) (ki info.ek))) slow
        let rc ← ld "i32" .i64 store (ki 8) KHDR
        guard (.v (← binv .i1 .le (.v rc) (ki 1))) slow
        pure (r, store, u, none, none)
    -- the row is its own owner (not a view) and has room for one more
    let bk ← ld "i8" .i64 store (ki 0) KHDR
    guard (.v (← binv .i1 .ne (.v bk) (ki K_ROWD))) slow
    let cap ← match n? with
      | some n => pure n
      | none => ld "i32" .i64 store (ki 4) KHDR
    guard (.v (← binv .i1 .lt (.v u) (.v cap))) slow
    if em == .char then guard (.v (← binv .i1 .lt v (.k .i32 (.i 256)))) slow
    leafSet store u info v n?
    let u1 ← binv .i64 .addW (.v u) (ki 1)
    st "i64" r (ki 56) (.v u1) KHDR
    match uv? with
    | some uv => emit (.set uv (.opnd (.v u1)))
    | none => pure ()
    terminate (.br done)
    switchTo slow
    slowPath slow (some (fid, s)) do rt fn #[ku (← rtd d), ku s, v]
    terminate (.br done)
    switchTo done
  | _, _ => rtCell fn fid s #[ku (← rtd d), ku s, v]

/-- `a[i] := v` on the row cell `(d, s)` holds: inline when the cell holds a row value over
    a leaf store of the element's kind that no other kept value shares (`rt.c: store_ref`
    would copy it first), else the runtime entry point `fn`. -/
def rowWrite (d s dims : Nat) (is : Array Opnd) (mr : Mode) (v : Opnd) (fn : String) : L Unit := do
  let j := is[1]?.getD (ki 0)
  match ← prowOf d s with
  | some pr =>
    let ix ← prowIndex pr is
    prowSet pr 0 ix v
    return
  | none => pure ()
  match ← cellAddr d s, elemInfo mr with
  | some (b, off), some info =>
    let fid ← cellFid d
    let slow ← newBlock; let done ← newBlock
    let (store, idx, n?, c?) ← rowLeafElemC fid b off s dims is info slow
    match c? with
    | some c => guard (.v c.rcOK) slow
    | none =>
      let rc ← ld "i32" .i64 store (ki 8) KHDR
      guard (.v (← binv .i1 .le (.v rc) (ki 1))) slow
    if mr == .char then guard (.v (← binv .i1 .lt v (.k .i32 (.i 256)))) slow
    leafSet store idx info v n?
    terminate (.br done)
    switchTo slow
    slowPath slow (some (fid, s)) do rt fn #[ku (← rtd d), ku s, ku dims, is[0]!, j, v]
    terminate (.br done)
    switchTo done
  | _, _ => rt fn #[ku (← rtd d), ku s, ku dims, is[0]!, j, v]

end A68.Lower
