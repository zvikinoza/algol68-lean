import A68.Lower.State

/-!
# A68.Analysis.Repeatable

Analysis: what a loop's lowered body does — which runtime calls it makes (may they be
repeated by a second run? do they leave cells and row stores alone?), which registers it
assigns — and whether its source has jumps, WHILE loops or labels.  Decides both the row
cache and the deferred-trap region.  See docs/OPTIMIZATIONS.md §4–5.
-/
namespace A68.Lower
open A68.MIR

/-- Does the loop body jump, loop by a WHILE (possibly forever), or leave a block by a
    label or EXIT?  Such a body cannot have its traps deferred to the loop's end. -/
partial def hasJumpsOrWhile (c : Core) : Bool :=
  match c with
  | .goto _ => true
  | .loop _ f b t w body =>
    w.isSome || hasJumpsOrWhile f || hasJumpsOrWhile b
      || (match t with | some e => hasJumpsOrWhile e | none => false) || hasJumpsOrWhile body
  | .block _ stmts _ _ =>
    stmts.any (fun st => match st with
      | .label _ | .exit => true
      | .decl _ _ init => hasJumpsOrWhile init
      | .unit e => hasJumpsOrWhile e)
  | _ => (CodeGen.childrenD c).any fun (_, ch) => hasJumpsOrWhile ch

/-- The runtime entry points that change no cell and no row store: a loop calling only
    these (outside its slow paths) may keep what it knows about a row in variables. -/
def harmlessRt : List String :=
  [ "a68rt_enter", "a68rt_leave", "a68rt_set_int", "a68rt_set_cell_int", "a68rt_set_cell_real",
    "a68rt_set_cell_bool", "a68rt_set_cell_char", "a68rt_set_cell_bits", "a68rt_cell_int",
    "a68rt_cell_real", "a68rt_cell_bool", "a68rt_cell_char", "a68rt_cell_bits", "a68rt_cell_isnil",
    "a68rt_cell_cproc", "a68rt_push_int", "a68rt_push_real", "a68rt_push_bool", "a68rt_push_char",
    "a68rt_push_bits", "a68rt_pop_int", "a68rt_pop_real", "a68rt_pop_bool", "a68rt_pop_char",
    "a68rt_pop_bits", "a68rt_pop", "a68rt_jump_pending", "a68rt_jump_clear", "a68rt_index_error",
    "a68rt_undef_error", "a68rt_arith_error", "a68rt_conforms", "a68rt_frame_cells",
    "a68rt_env_depth", "a68rt_stack_depth", "a68rt_env_truncate", "a68rt_stack_truncate" ]

/-- The runtime entry points a loop may call and still be run twice: they change nothing
    a second run could see differently. -/
def repeatableRt : List String :=
  [ "a68rt_enter", "a68rt_leave", "a68rt_cell_int", "a68rt_cell_real", "a68rt_cell_bool",
    "a68rt_cell_char", "a68rt_cell_bits", "a68rt_cell_isnil", "a68rt_cell_cproc", "a68rt_push_int",
    "a68rt_push_real", "a68rt_push_bool", "a68rt_push_char", "a68rt_push_bits", "a68rt_pop_int",
    "a68rt_pop_real", "a68rt_pop_bool", "a68rt_pop_char", "a68rt_pop_bits", "a68rt_pop",
    "a68rt_jump_pending", "a68rt_conforms", "a68rt_frame_cells", "a68rt_env_depth", "a68rt_stack_depth",
    -- the checks: those that cannot be deferred are counted separately (`hardTraps`)
    "a68rt_index_error", "a68rt_undef_error", "a68rt_arith_error" ]

/-- Do blocks `[from, to)` call only what a second run may repeat, and reach no row through
    the runtime (no slow path)?  The registers a second run must restore are those assigned
    in the blocks that existed before it (`v0`). -/
def repeatable (from_ to v0 : Nat) : L (Bool × List Var) := do
  let st ← get
  let ok (f : Callee) : Bool := match f with
    | .rt name => repeatableRt.contains name
    | .nat _ => true
    | _ => false
  let mut mods : List Var := []
  for b in [from_:to] do
    let some blk := st.fb.blocks[b]? | continue
    for ins in blk.instrs do
      match ins with
      | .call f _ => if !ok f then return (false, [])
      | .set d (.call f _) =>
        if !ok f then return (false, [])
        if d.id < v0 && !mods.any (·.id == d.id) then mods := d :: mods
      | .set d _ => if d.id < v0 && !mods.any (·.id == d.id) then mods := d :: mods
      | _ => pure ()
  return (true, mods)

/-- Does every runtime call in blocks `[from, to)` outside the slow paths leave cells and
    row stores alone?  A call of a routine may do anything. -/
def callFree (from_ to : Nat) : L Bool := do
  let st ← get
  let slow (b : Nat) : Bool := st.slowRanges.any fun (a, z) => a ≤ b && b < z
  let ok (f : Callee) : Bool := match f with
    | .rt name => harmlessRt.contains name
    | .nat _ => true
    | _ => false
  for b in [from_:to] do
    if slow b then continue
    let some blk := st.fb.blocks[b]? | continue
    for i in [0:blk.instrs.size] do
      if st.cellCalls.contains (b, i) then continue
      match blk.instrs[i]! with
      | .call f _ => if !ok f then return false
      | .set _ (.call f _) => if !ok f then return false
      | _ => pure ()
  return true

end A68.Lower
