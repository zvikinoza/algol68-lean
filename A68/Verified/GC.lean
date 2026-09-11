/-!
# A68.Verified.GC — the collector of compiled programs, proved on a model

`csrc/rt.c` collects the heap of a compiled program by marking from the roots with a
worklist and sweeping every object left unmarked (docs/GC-DESIGN.md §4–5).  This file
states that algorithm over a model of the heap and proves what the C transcribes:

* `mark_sound`: every object the worklist marks is reachable from the roots;
* `mark_complete`: when the worklist has run to empty, every reachable object is marked;
* `sweep_reachable`: sweeping the unmarked objects leaves every reachable object, and its
  contents, in place, so reachability afterwards is reachability before;
* `alloc_fresh`: an identifier outside the heap is not reachable, so giving it out cannot
  alias a live object.

The model: a heap is a finite map from identifiers to objects, an object is the list of
identifiers it points at (the pointer slots of a `SLOTS` or `FRAME` object, the base of
a `ROWD`, the parent of a frame; a `LEAF` has none), and the roots are a list of
identifiers.  Scalars carry no identifier and are absent from the model, as they are
absent from the marker's work.  The C marker decides "pointer or not" from a slot's tag
alone, which is the only place the transcription needs care.
-/
namespace A68.Verified.GC

abbrev Id := Nat

/-- A heap: which identifiers are allocated, and what each points at. -/
structure Heap where
  dom : List Id
  succ : Id → List Id

/-- Reachability from the roots, following the pointers of allocated objects. -/
inductive Reach (h : Heap) (roots : List Id) : Id → Prop where
  | root {i} : i ∈ roots → Reach h roots i
  | step {i j} : Reach h roots i → i ∈ h.dom → j ∈ h.succ i → Reach h roots j

/-- The state of the marker: the identifiers marked so far and the worklist. -/
structure MState where
  marked : List Id
  work : List Id

/-- One step of the worklist algorithm (`gc_mark` in `csrc/rt.c`): pop an identifier and
    push each of its pointers that is not yet marked, marking it.  An identifier that is
    not allocated (which the C cannot meet: every pointer it holds was allocated) has no
    pointers. -/
def markStep (h : Heap) (s : MState) : MState :=
  match s.work with
  | [] => s
  | i :: rest =>
    let succs := if i ∈ h.dom then h.succ i else []
    -- the C marks an identifier as it pushes it, so a pointer that occurs twice among the
    -- successors is pushed once: `eraseDups` says the same
    let fresh := (succs.filter (fun j => !(s.marked.contains j))).eraseDups
    { marked := fresh ++ s.marked, work := fresh ++ rest }

/-- The marker's initial state: the roots, deduplicated by marking each once. -/
def markInit (roots : List Id) : MState :=
  { marked := roots.eraseDups, work := roots.eraseDups }

/-- `n` steps of the marker. -/
def markN (h : Heap) (roots : List Id) : Nat → MState
  | 0 => markInit roots
  | n + 1 => markStep h (markN h roots n)

/-- The invariant the worklist keeps: everything marked is reachable, and everything on
    the worklist is marked. -/
def Inv (h : Heap) (roots : List Id) (s : MState) : Prop :=
  (∀ i ∈ s.marked, Reach h roots i) ∧ (∀ i ∈ s.work, i ∈ s.marked)

theorem inv_init (h : Heap) (roots : List Id) : Inv h roots (markInit roots) := by
  refine ⟨fun i hi => ?_, fun i hi => hi⟩
  exact Reach.root (List.mem_eraseDups.mp hi)

theorem mem_filter_not_marked {l m : List Id} {j : Id}
    (hj : j ∈ (l.filter (fun j => !(m.contains j))).eraseDups) : j ∈ l ∧ j ∉ m := by
  have := List.mem_filter.mp (List.mem_eraseDups.mp hj)
  refine ⟨this.1, fun hm => ?_⟩
  have h2 := this.2
  simp [List.contains_iff_mem, hm] at h2

theorem inv_step (h : Heap) (roots : List Id) (s : MState) (hs : Inv h roots s) :
    Inv h roots (markStep h s) := by
  unfold markStep
  match hw : s.work with
  | [] => simpa [hw] using hs
  | i :: rest =>
    simp only []
    have hi_marked : i ∈ s.marked := hs.2 i (by rw [hw]; exact List.mem_cons_self ..)
    have hi_reach : Reach h roots i := hs.1 i hi_marked
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rcases List.mem_append.mp hj with hj | hj
      · have ⟨hsucc, _⟩ := mem_filter_not_marked hj
        by_cases hd : i ∈ h.dom
        · simp [hd] at hsucc
          exact Reach.step hi_reach hd hsucc
        · simp [hd] at hsucc
      · exact hs.1 j hj
    · rcases List.mem_append.mp hj with hj | hj
      · exact List.mem_append.mpr (Or.inl hj)
      · exact List.mem_append.mpr (Or.inr (hs.2 j (by rw [hw]; exact List.mem_cons_of_mem _ hj)))

theorem inv_markN (h : Heap) (roots : List Id) : ∀ n, Inv h roots (markN h roots n)
  | 0 => inv_init h roots
  | n + 1 => inv_step h roots _ (inv_markN h roots n)

/-- Soundness: whatever the marker has marked after any number of steps is reachable. -/
theorem mark_sound (h : Heap) (roots : List Id) (n : Nat) :
    ∀ i ∈ (markN h roots n).marked, Reach h roots i :=
  (inv_markN h roots n).1

/-- A marked set that contains the roots and is closed under the pointers of allocated
    objects contains everything reachable. -/
theorem closed_contains_reach (h : Heap) (roots : List Id) (M : List Id)
    (hroots : ∀ i ∈ roots, i ∈ M)
    (hclosed : ∀ i ∈ M, i ∈ h.dom → ∀ j ∈ h.succ i, j ∈ M) :
    ∀ i, Reach h roots i → i ∈ M := by
  intro i hi
  induction hi with
  | root hr => exact hroots _ hr
  | step _ hd hj ih => exact hclosed _ ih hd _ hj

/-- The marked set only grows. -/
theorem marked_mono (h : Heap) (s : MState) : ∀ i ∈ s.marked, i ∈ (markStep h s).marked := by
  intro i hi
  unfold markStep
  match s.work with
  | [] => exact hi
  | _ :: _ => exact List.mem_append.mpr (Or.inr hi)

/-- After a step that pops `i`, every pointer of `i` is marked: it was already, or the step
    marked it. -/
theorem step_marks_succ (h : Heap) (s : MState) (i : Id) (rest : List Id)
    (hw : s.work = i :: rest) (hd : i ∈ h.dom) :
    ∀ j ∈ h.succ i, j ∈ (markStep h s).marked := by
  intro j hj
  unfold markStep
  rw [hw]
  simp only []
  by_cases hm : j ∈ s.marked
  · exact List.mem_append.mpr (Or.inr hm)
  · refine List.mem_append.mpr (Or.inl ?_)
    refine List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨by simp [hd, hj], ?_⟩)
    simp [List.contains_iff_mem, hm]

/-- The second half of the invariant, strengthened: an identifier that is marked and has
    left the worklist has all its pointers marked.  "Left the worklist" is: marked and not
    on the worklist. -/
def Done (h : Heap) (s : MState) : Prop :=
  ∀ i ∈ s.marked, i ∉ s.work → i ∈ h.dom → ∀ j ∈ h.succ i, j ∈ s.marked

theorem done_init (h : Heap) (roots : List Id) : Done h (markInit roots) := by
  intro i hi hw
  exact absurd hi hw

theorem done_step (h : Heap) (s : MState) (hs : Done h s) : Done h (markStep h s) := by
  intro i hi hw hd j hj
  match hwk : s.work with
  | [] =>
    have e : markStep h s = s := by unfold markStep; rw [hwk]
    rw [e] at hi hw ⊢
    exact hs i hi (by rw [hwk]; exact List.not_mem_nil) hd j hj
  | k :: rest =>
    by_cases hik : i = k
    · subst hik
      exact step_marks_succ h s i rest hwk hd j hj
    · -- `i` was marked before this step (it is not the popped one, and the fresh ones are on
      -- the new worklist, where `i` is not), and off the worklist before it
      have hi' : i ∈ s.marked := by
        unfold markStep at hi
        rw [hwk] at hi
        simp only [] at hi
        rcases List.mem_append.mp hi with hf | hm
        · exfalso
          apply hw
          unfold markStep
          rw [hwk]
          simp only []
          exact List.mem_append.mpr (Or.inl hf)
        · exact hm
      have hw' : i ∉ s.work := by
        intro hin
        rw [hwk] at hin
        rcases List.mem_cons.mp hin with e | hr
        · exact hik e
        · apply hw
          unfold markStep
          rw [hwk]
          simp only []
          exact List.mem_append.mpr (Or.inr hr)
      exact marked_mono h s j (hs i hi' hw' hd j hj)

theorem done_markN (h : Heap) (roots : List Id) : ∀ n, Done h (markN h roots n)
  | 0 => done_init h roots
  | n + 1 => done_step h _ (done_markN h roots n)

theorem roots_marked (h : Heap) (roots : List Id) (n : Nat) :
    ∀ i ∈ roots, i ∈ (markN h roots n).marked := by
  induction n with
  | zero => intro i hi; exact List.mem_eraseDups.mpr hi
  | succ n ih => intro i hi; exact marked_mono h _ i (ih i hi)

/-- Completeness: once the worklist is empty, the marked set is closed under pointers and
    contains the roots, hence everything reachable. -/
theorem mark_complete (h : Heap) (roots : List Id) (n : Nat)
    (hdone : (markN h roots n).work = []) :
    ∀ i, Reach h roots i → i ∈ (markN h roots n).marked := by
  apply closed_contains_reach h roots
  · exact roots_marked h roots n
  · intro i hi hd j hj
    exact done_markN h roots n i hi (by rw [hdone]; exact List.not_mem_nil) hd j hj

/-- Sweeping: the objects not in `M` are removed; the rest keep their pointers. -/
def sweep (h : Heap) (M : List Id) : Heap :=
  { dom := h.dom.filter (fun i => M.contains i), succ := h.succ }

/-- Everything reachable before a sweep that keeps every reachable object is reachable
    after it, through the same objects. -/
theorem sweep_reachable (h : Heap) (roots M : List Id)
    (hM : ∀ i, Reach h roots i → i ∈ M) :
    ∀ i, Reach h roots i → Reach (sweep h M) roots i := by
  intro i hi
  induction hi with
  | root hr => exact Reach.root hr
  | step hr hd hj ih =>
    refine Reach.step ih ?_ hj
    exact List.mem_filter.mpr ⟨hd, by simp [List.contains_iff_mem, hM _ hr]⟩

/-- Conversely a sweep introduces no reachability: the surviving heap is a sub-heap. -/
theorem sweep_reachable_rev (h : Heap) (roots M : List Id) :
    ∀ i, Reach (sweep h M) roots i → Reach h roots i := by
  intro i hi
  induction hi with
  | root hr => exact Reach.root hr
  | step _ hd hj ih => exact Reach.step ih (List.mem_filter.mp hd).1 hj

/-- Put together: after marking to a fixpoint and sweeping the unmarked, reachability is
    exactly what it was. -/
theorem collect_correct (h : Heap) (roots : List Id) (n : Nat)
    (hdone : (markN h roots n).work = []) :
    ∀ i, Reach (sweep h (markN h roots n).marked) roots i ↔ Reach h roots i :=
  fun i => ⟨sweep_reachable_rev h roots _ i, sweep_reachable h roots _ (mark_complete h roots n hdone) i⟩

/-- Every object the sweep frees is unreachable: nothing live is lost. -/
theorem sweep_frees_unreachable (h : Heap) (roots : List Id) (n : Nat)
    (hdone : (markN h roots n).work = []) :
    ∀ i ∈ h.dom, i ∉ (sweep h (markN h roots n).marked).dom → ¬ Reach h roots i := by
  intro i hd hnot hr
  apply hnot
  exact List.mem_filter.mpr ⟨hd, by simp [List.contains_iff_mem, mark_complete h roots n hdone i hr]⟩

/-- Allocation: an identifier outside the heap is reachable only if it is a root itself,
    which a fresh identifier is not; so it aliases nothing live. -/
theorem alloc_fresh (h : Heap) (roots : List Id) (i : Id)
    (hnew : i ∉ h.dom) (hnr : i ∉ roots) (hclosed : ∀ j ∈ h.dom, ∀ k ∈ h.succ j, k ∈ h.dom) :
    ¬ Reach h roots i := by
  intro hr
  cases hr with
  | root hroot => exact hnr hroot
  | step _ hd hj => exact hnew (hclosed _ hd _ hj)

/- Termination of the worklist is not stated here: the C marks an identifier as it pushes
   it and pushes only unmarked ones, so the number of pushes is bounded by the number of
   objects.  The theorems above hold for every number of steps, and `mark_complete` for the
   state in which the worklist has emptied. -/

end A68.Verified.GC
