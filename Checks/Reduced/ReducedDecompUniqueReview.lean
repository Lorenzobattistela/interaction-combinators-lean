import InteractionCombinators.Reduced.ReducedDecompUnique
import Checks.Reduced.ReducedDecompUniqueCheck

/-!
# Review of `Net.IsTreesOnWiringN` and Proposition 2, uniqueness (page 79)

Lafont 1997, Proposition 2, page 79: "Any reduced net `ν` with `n` free ports can be uniquely
decomposed as follows", the picture showing `n` trees `τ₁, …, τₙ` whose roots are the `n` free
ports and whose leaves are plugged into a wiring `ω`. The paper works with graphs: "uniquely"
means that the trees and the wiring are determined by `ν`, the free ports being fixed. On the text,
a graph is a net up to `Equiv`, and two texts of the same graph in a normal form can differ only by
the names of the internal wires, the wires of `ω`. This is what `Net.IsTreesOnWiringN.unique`
states. This file checks it.

## Is the conclusion of `unique` the paper's, and no weaker?

* `unique_iff`: for linear nets in normal form, `Equiv N M` holds **if and only if** `M` is `N`
  renamed by a `ρ` that fixes the free ports and is injective on the names of `N`
  (`Net.IsTreesOnWiringN.unique` one way, `Net.equiv_bind_var` the other). So the conclusion of
  `unique` loses no information: it says exactly "the same graph", as the paper's "uniquely".
* `ρ` fixes the free ports: `wireNet_unique` shows that a single wire `0 = 1` between free ports
  has only itself as normal form (no renaming moves `0` or `1`), and `zero_unique` that the empty
  net has only itself.
* Non-vacuity with `ρ` not the identity: `renamed_unique` (in `Checks/ReducedDecompUniqueCheck`,
  verified: `ρ 2 = 5`, so `ρ ≠ id`), and here `twoTrees_unique`, two trees `con(2, 3)` and
  `dup(2, 3)` joined leaf to leaf, plus a wire `4 = 5` between free ports; renamed to `8`, `9`,
  `unique` gives `ρ 2 = 8` and `ρ 3 = 9`.

## Is the normal form a faithful reading of "trees plugged into a wiring"?

* Nothing that is not a reduced net is in the form: `normal_isReduced` (through
  `Net.IsTreesOnWiring.isReduced`).
* No reduced net is excluded: `Net.IsReduced.exists_treesOnWiringN`; non-vacuous on
  `twoCellTrees` (three cells, three internal wires `3`, `4`, `5`), `twoCellTrees_normal`.
* The small cases asked for in #342: the empty net (`zero_normal`), a wire `0 = 1` between free
  ports (`wireNet_normal`), a tree whose two auxiliary ports are joined (`selfCon_normal`), two
  trees joined leaf to leaf (`shared_normal`), a tree with free leaves (`conNet_normal`) are in
  normal form. A cyclic wire `0 = 0` is not (`loopNet_not_normal`), nor a tree beside a cyclic
  wire (`selfConLoop_not_normal`): page 79 calls a cyclic wire a vicious circle of length 0, so
  these nets are not reduced (`selfConLoop_not_isReduced`), and the paper does not decompose them.
* The condition on equations `x = y` is symmetric (`IsTreesOnWiringN.var_var_free`): both ends are
  free ports. So `x = y` and `y = x` with both free are the same net (`wireNet_swap`: an equation
  is unordered), and the proof's "larger name" choice only picks the root, it does not distinguish
  two nets.

## What could not be checked

* The paper's "uniquely" is not stated formally in the paper; the reading "up to a renaming of the
  wires of `ω` fixing the free ports" is the only one under which the paper's claim is true of
  graphs (`renamed_unique` shows that equality of texts fails).
* Uniqueness of the decomposition **as a pair (trees, wiring)**, i.e. that the split of a net in
  normal form into `τᵢ` and `ω` is forced, is not a separate statement in Lean: the trees are the
  equations, read off the text by `Net.rootTree`, so this split is a function of the text.

## Found

No problem. The definition says what the paper says, and the theorem is as strong as possible.
-/

namespace INet.ReducedDecompUniqueReview

open Term Comb ReducedDecompReview ReducedDecompUniqueCheck

/-! ## The conclusion of `unique` is exactly `Equiv` -/

/-- **Uniqueness is an exact characterization** (Lafont 1997, Proposition 2, page 79): two linear
nets in normal form are the same graph if and only if one is the other with its internal names
renamed injectively, the free ports fixed. -/
theorem unique_iff {N M : Net sig ℕ} (hN : N.Linear) (hM : M.Linear)
    (hn : N.IsTreesOnWiringN) (hm : M.IsTreesOnWiringN) :
    Equiv N M ↔ ∃ ρ : ℕ → ℕ, (∀ x, N.vars.count x = 1 → ρ x = x) ∧
      Set.InjOn ρ {x | x ∈ N.vars} ∧ M = N.bind (fun x => var (ρ x)) := by
  constructor
  · exact Net.IsTreesOnWiringN.unique hn hm
  · rintro ⟨ρ, hfix, hinj, rfl⟩
    exact Net.equiv_bind_var hN ρ hinj hfix

/-- In normal form, both ends of an equation `x = y` are free ports (page 79): the condition of
`Net.IsTreesOnWiringN` does not depend on how the equation is written. -/
theorem IsTreesOnWiringN.var_var_free {N : Net sig ℕ} (h : N.IsTreesOnWiringN) {x y : ℕ}
    (he : s(var x, var y) ∈ N) : N.vars.count x = 1 ∧ N.vars.count y = 1 :=
  ⟨h.2 y x (by rw [Sym2.eq_swap]; exact he), h.2 x y he⟩

/-- Every net in normal form is reduced (page 79): the form contains nothing the paper does not
decompose. -/
theorem normal_isReduced {N : Net sig ℕ} (h : N.IsTreesOnWiringN) : N.IsReduced :=
  h.1.isReduced

/-! ## Small cases -/

/-- The empty net is in normal form (page 79, `n = 0`). -/
theorem zero_normal : (0 : Net sig ℕ).IsTreesOnWiringN :=
  ⟨zero_form.1, fun _ _ h => absurd h (Multiset.notMem_zero _)⟩

/-- The empty net has only itself as normal form (page 79). -/
theorem zero_unique {M : Net sig ℕ} (hM : M.Linear) (hm : M.IsTreesOnWiringN)
    (h : Equiv 0 M) : M = 0 := by
  obtain ⟨ρ, -, -, rfl⟩ := Net.IsTreesOnWiringN.unique zero_normal hm h
  simp [Net.bind]

/-- A wire `0 = 1` between two free ports is in normal form (page 79): two trees with no cell,
joined by the wiring. -/
theorem wireNet_normal : wireNet.IsTreesOnWiringN := by
  refine ⟨wireNet_form.1, fun x y h => ?_⟩
  simp only [wireNet, Multiset.mem_cons, Multiset.notMem_zero, or_false] at h
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> injection h1 <;> injection h2 <;>
    subst_vars <;> simp [wireNet]

/-- `1 = 0` is the net `0 = 1`: an equation is unordered, so the proof's choice of the larger name
as root is a choice of reading, not a difference of nets (page 79). -/
theorem wireNet_swap : (s(var 1, var 0) ::ₘ 0 : Net sig ℕ) = wireNet := by
  rw [wireNet, Sym2.eq_swap]

/-- **The renaming fixes the free ports**: `0 = 1` has only itself as normal form (page 79). -/
theorem wireNet_unique {M : Net sig ℕ} (hM : M.Linear) (hm : M.IsTreesOnWiringN)
    (h : Equiv wireNet M) : M = wireNet := by
  obtain ⟨ρ, hfix, -, rfl⟩ :=
    Net.IsTreesOnWiringN.unique wireNet_normal hm h
  have h0 : ρ 0 = 0 := hfix 0 (by simp [wireNet])
  have h1 : ρ 1 = 1 := hfix 1 (by simp [wireNet])
  simp [wireNet, Net.bind, h0, h1]

/-- `0 = con(1, 2)`, a tree whose leaves are free ports, is in normal form. -/
theorem conNet_normal : conNet.IsTreesOnWiringN :=
  ⟨conNet_form, fun x y h => by simp [conNet, mkCon] at h⟩

/-- `0 = con(1, 1)`, a tree whose two auxiliary ports are joined by the wiring, is in normal
form (page 79). -/
theorem selfCon_normal : selfCon.IsTreesOnWiringN :=
  ⟨selfCon_form.1, fun x y h => by simp [selfCon, mkCon] at h⟩

/-- `0 = con(2, 3), 1 = dup(2, 3)`, two trees joined leaf to leaf, is in normal form (page 79). -/
theorem shared_normal : shared.IsTreesOnWiringN :=
  ⟨shared_form.1, fun x y h => by simp [shared, mkCon, mkDup] at h⟩

/-- A cyclic wire `0 = 0` is not in normal form: it is a vicious circle of length 0 (page 79). -/
theorem loopNet_not_normal : ¬ loopNet.IsTreesOnWiringN := fun h => loopNet_not_form h.1

/-- `0 = con(1, 1), 2 = 2`: a tree beside a cyclic wire. -/
def selfConLoop : Net sig ℕ := s(var 0, mkCon (var 1) (var 1)) ::ₘ s(var 2, var 2) ::ₘ 0

/-- `selfConLoop` is not reduced: the cyclic wire is a vicious circle of length 0 (page 79). -/
theorem selfConLoop_not_isReduced : ¬ selfConLoop.IsReduced := fun h =>
  h.2 (Net.hasVicious_of_mem (by simp) (Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)))

/-- `selfConLoop` is not in normal form. -/
theorem selfConLoop_not_normal : ¬ selfConLoop.IsTreesOnWiringN := fun h =>
  selfConLoop_not_isReduced (normal_isReduced h)

/-! ## Existence in normal form, with cells and internal wires -/

/-- `0 = con(dup(3, 4), 6), 1 = con(3, 4)` is in normal form. -/
theorem twoCellTreesForm_normal : twoCellTreesForm.IsTreesOnWiringN :=
  ⟨twoCellTreesForm_form, fun x y h => by simp [twoCellTreesForm, mkCon, mkDup] at h⟩

/-- **Non-vacuity of `Net.IsReduced.exists_treesOnWiringN`** with three cells and three internal
wires (page 79): `twoCellTrees` (`5 = dup(3, 4), 0 = con(5, 6), 1 = con(3, 4)`) satisfies the
hypotheses, and `twoCellTreesForm` is a normal form of it. -/
theorem twoCellTrees_normal : (∃ M, Equiv twoCellTrees M ∧ M.IsTreesOnWiringN) ∧
    Equiv twoCellTrees twoCellTreesForm ∧ twoCellTreesForm.IsTreesOnWiringN :=
  ⟨Net.IsReduced.exists_treesOnWiringN twoCellTrees_linear twoCellTrees_isReduced,
    twoCellTrees_wire.equiv, twoCellTreesForm_normal⟩

/-! ## Two trees joined leaf to leaf, renamed -/

/-- `0 = con(2, 3), 1 = dup(2, 3), 4 = 5`: two trees joined leaf to leaf by the wires `2`, `3`,
and a wire between the free ports `4` and `5`. -/
def twoTrees : Net sig ℕ :=
  s(var 0, mkCon (var 2) (var 3)) ::ₘ s(var 1, mkDup (var 2) (var 3)) ::ₘ s(var 4, var 5) ::ₘ 0

/-- `twoTrees` with the wires `2`, `3` renamed `8`, `9`, and the last equation written `5 = 4`. -/
def twoTreesR : Net sig ℕ :=
  s(var 0, mkCon (var 8) (var 9)) ::ₘ s(var 1, mkDup (var 8) (var 9)) ::ₘ s(var 5, var 4) ::ₘ 0

/-- The renaming `2 ↦ 8`, `3 ↦ 9`. -/
def twoTreesρ (x : ℕ) : ℕ := if x = 2 then 8 else if x = 3 then 9 else x

theorem twoTrees_linear : twoTrees.Linear := by
  intro y
  simp only [twoTrees, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_mkCon, vars_mkDup,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

theorem twoTreesR_linear : twoTreesR.Linear := by
  intro y
  simp only [twoTreesR, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_mkCon,
    vars_mkDup, Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

theorem twoTrees_normal : twoTrees.IsTreesOnWiringN := by
  refine ⟨fun e he => ?_, fun x y h => ?_⟩
  · simp only [twoTrees, Multiset.mem_cons, Multiset.notMem_zero, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨0, _, rfl, by simp [twoTrees]⟩
    · exact ⟨1, _, rfl, by simp [twoTrees]⟩
    · exact ⟨4, _, rfl, by simp [twoTrees]⟩
  · simp only [twoTrees, mkCon, mkDup, Multiset.mem_cons, Multiset.notMem_zero, or_false] at h
    rcases h with h | h | h
    · simp at h
    · simp at h
    · rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> injection h1 <;> injection h2 <;>
        subst_vars <;> simp [twoTrees]

theorem twoTreesR_normal : twoTreesR.IsTreesOnWiringN := by
  refine ⟨fun e he => ?_, fun x y h => ?_⟩
  · simp only [twoTreesR, Multiset.mem_cons, Multiset.notMem_zero, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨0, _, rfl, by simp [twoTreesR]⟩
    · exact ⟨1, _, rfl, by simp [twoTreesR]⟩
    · exact ⟨5, _, rfl, by simp [twoTreesR]⟩
  · simp only [twoTreesR, mkCon, mkDup, Multiset.mem_cons, Multiset.notMem_zero, or_false] at h
    rcases h with h | h | h
    · simp at h
    · simp at h
    · rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> injection h1 <;> injection h2 <;>
        subst_vars <;> simp [twoTreesR]

/-- `twoTreesR` is `twoTrees` renamed by `twoTreesρ`. -/
theorem twoTreesR_eq : twoTreesR = twoTrees.bind (fun x => var (twoTreesρ x)) := by
  simp [twoTrees, twoTreesR, twoTreesρ, Net.bind]

/-- `twoTrees` and `twoTreesR` are the same graph (`Net.equiv_bind_var`, pages 70-72). -/
theorem twoTrees_equiv : Equiv twoTrees twoTreesR := by
  rw [twoTreesR_eq]
  refine Net.equiv_bind_var twoTrees_linear _ ?_ ?_
  · intro a ha b hb hab
    simp only [Set.mem_ofPred_eq, twoTrees, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var,
      vars_mkCon, vars_mkDup, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_false] at ha hb
    simp only [twoTreesρ] at hab
    split_ifs at hab <;> omega
  · intro x hx
    have : x ≠ 2 ∧ x ≠ 3 := by
      constructor <;> rintro rfl <;> simp [twoTrees] at hx
    simp [twoTreesρ, this.1, this.2]

/-- **Proposition 2, uniqueness, applied with a non-trivial renaming** (page 79): for the two
equivalent normal forms `twoTrees` and `twoTreesR`, the renaming given by
`Net.IsTreesOnWiringN.unique` sends the wires `2`, `3` to `8`, `9` and fixes the free ports. -/
theorem twoTrees_unique : ∃ ρ : ℕ → ℕ, ρ 0 = 0 ∧ ρ 1 = 1 ∧ ρ 4 = 4 ∧ ρ 5 = 5 ∧ ρ 2 = 8 ∧
    ρ 3 = 9 ∧ twoTreesR = twoTrees.bind (fun x => var (ρ x)) := by
  obtain ⟨ρ, hfix, -, hb⟩ := Net.IsTreesOnWiringN.unique
    twoTrees_normal twoTreesR_normal twoTrees_equiv
  have h0 : ρ 0 = 0 := hfix 0 (by simp [twoTrees])
  have h1 : ρ 1 = 1 := hfix 1 (by simp [twoTrees])
  have h4 : ρ 4 = 4 := hfix 4 (by simp [twoTrees])
  have h5 : ρ 5 = 5 := hfix 5 (by simp [twoTrees])
  have hm : s(var 0, mkCon (var (ρ 2)) (var (ρ 3))) ∈ twoTreesR := by
    rw [hb]
    simp [twoTrees, Net.bind, h0]
  simp [twoTreesR] at hm
  simp [mkCon, mkDup] at hm
  have e2 := congrFun (eq_of_heq (Term.app.inj hm).2) 0
  have e3 := congrFun (eq_of_heq (Term.app.inj hm).2) 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, var.injEq] at e2 e3
  exact ⟨ρ, h0, h1, h4, h5, e2, e3, hb⟩

end INet.ReducedDecompUniqueReview
