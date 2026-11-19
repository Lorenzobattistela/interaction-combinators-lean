import InteractionCombinators.Lafont.ReducedDecomp
import Checks.ReducedClosedCheck

/-!
# Review of `Net.IsTreesOnWiring` and Proposition 2, existence (page 79)

Lafont 1997, Proposition 2, page 79: "Any reduced net `ν` with `n` free ports can be uniquely
decomposed" as `n` trees `τ₁, …, τₙ`, whose roots are the `n` free ports, with their leaves
plugged into a wiring `ω`. The text form `Net.IsTreesOnWiring N` asks that every equation be
`x = t` with `x` a free port. This file checks the definition against the picture on small nets.

## Number of trees

The picture has one tree per free port; the text has one equation per tree **that is not a bare
wire**, plus one equation per wire between two free ports. A free port that occurs only as a leaf
of some `t` is, in the picture, a tree with no cell (a wire from the free port to `ω`), plugged by
`ω` into that leaf of `t`. So the text form and the picture describe the same nets, with this
correspondence:

* `x = t`, `t` with a cell: the tree `τₓ = t`; its leaves that are free ports are trees with no
  cell, joined to it by `ω`; its leaves that occur twice are wires of `ω`.
* `x = y`, `y` free: two trees with no cell, `τₓ` and `τ_y`, joined by a wire of `ω`.
* `x = y`, `y` occurring twice: `τₓ` with no cell, joined by `ω` to the other occurrence of `y`.

`conNet` (`0 = con(1, 2)`: three free ports, one equation) and `wireNet` (`0 = 1`: two free
ports, one equation) show the first two cases; `pendant` shows the third.

## Part 2: uniqueness

The text form is **not** unique up to renaming: `pendant` (`0 = 7, 2 = con(7, 3)`) and `merged`
(`2 = con(0, 3)`) are both in the form, are the same graph (one wire substitution), and have
different numbers of equations. Uniqueness has to be stated up to `Equiv`, which also covers
renaming the wires of `ω` (`renamedA_equiv_renamedB`), or for a normal form that forbids
`x = y` with `y` internal.
-/

namespace INet.ReducedDecompReview

open Term Comb

/-! ## Number of trees -/

/-- `0 = con(1, 2)`: one `con` cell, three free ports (Lafont 1997, page 79). -/
def conNet : Net sig ℕ := s(var 0, mkCon (var 1) (var 2)) ::ₘ 0

/-- `conNet` is linear. -/
theorem conNet_linear : conNet.Linear := by
  intro y
  simp only [conNet, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_mkCon,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- `conNet` has three free ports, `0`, `1`, `2`, and one equation: the picture of page 79 has
three trees, `con(1, 2)` on `0` and two trees with no cell on `1` and `2`, joined to the leaves of
the first by the wiring. -/
theorem conNet_free : conNet.vars.count 0 = 1 ∧ conNet.vars.count 1 = 1 ∧
    conNet.vars.count 2 = 1 ∧ Multiset.card conNet = 1 := by
  simp [conNet]

/-- `conNet` is in the form (Lafont 1997, page 79). -/
theorem conNet_form : conNet.IsTreesOnWiring := by
  intro e he
  simp only [conNet, Multiset.mem_cons, Multiset.notMem_zero, or_false] at he
  subst he
  exact ⟨0, _, rfl, by simp [conNet]⟩

/-- The free port on the right side of the equation: `con(1, 2) = 0` is the same net as
`conNet`, since an equation is unordered, so it is in the form too (page 79). -/
theorem conNet_right : (s(mkCon (var 1) (var 2), var 0) ::ₘ 0 : Net sig ℕ) = conNet := by
  rw [conNet, Sym2.eq_swap]

/-- The free port on the right side of the equation is in the form. -/
theorem conNet_right_form :
    Net.IsTreesOnWiring (s(mkCon (var 1) (var 2), var 0) ::ₘ 0 : Net sig ℕ) :=
  conNet_right ▸ conNet_form

/-- `0 = 1`: a wire between two free ports (Lafont 1997, page 79). -/
def wireNet : Net sig ℕ := s(var 0, var 1) ::ₘ 0

/-- `wireNet` is linear. -/
theorem wireNet_linear : wireNet.Linear := by
  intro y
  simp only [wireNet, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- `wireNet` has two free ports and one equation: the picture has two trees with no cell, joined
by one wire of the wiring. -/
theorem wireNet_free : wireNet.vars.count 0 = 1 ∧ wireNet.vars.count 1 = 1 ∧
    Multiset.card wireNet = 1 := by
  simp [wireNet]

/-- `wireNet` is in the form, with root `0`; and with root `1`, since `1 = 0` is the same
equation: which end is called the root does not matter. -/
theorem wireNet_form : wireNet.IsTreesOnWiring ∧
    ∀ e ∈ wireNet, e = s(var 1, var 0) ∧ wireNet.vars.count 1 = 1 := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩ <;>
    simp only [wireNet, Multiset.mem_cons, Multiset.notMem_zero, or_false] at he <;>
    subst he
  · exact ⟨0, _, rfl, by simp [wireNet]⟩
  · exact ⟨Sym2.eq_swap, by simp [wireNet]⟩

/-- `wireNet` is reduced (`Net.IsTreesOnWiring.isReduced`, page 79). -/
theorem wireNet_isReduced : wireNet.IsReduced := wireNet_form.1.isReduced

/-! ## Cyclic wires -/

/-- `0 = 0`: a cyclic wire (Lafont 1997, page 71). -/
def loopNet : Net sig ℕ := s(var 0, var 0) ::ₘ 0

/-- `loopNet` is linear: `0` occurs twice. -/
theorem loopNet_linear : loopNet.Linear := by
  intro y
  simp only [loopNet, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- A cyclic wire is a vicious circle of length 0 (page 79), on the text and up to `Equiv`. -/
theorem loopNet_vicious : loopNet.ChainVicious ∧ loopNet.HasVicious :=
  ⟨Net.chainVicious_of_mem (by simp) (Multiset.mem_cons_self _ _),
    Net.hasVicious_of_mem (by simp) (Multiset.mem_cons_self _ _)⟩

/-- `loopNet` is not reduced. -/
theorem loopNet_not_isReduced : ¬ loopNet.IsReduced := fun h => h.2 loopNet_vicious.2

/-- `loopNet` is not in the form: `0` is not a free port. -/
theorem loopNet_not_form : ¬ loopNet.IsTreesOnWiring := by
  intro h
  obtain ⟨x, t, he, hx⟩ := h _ (Multiset.mem_cons_self _ _)
  have h0 : x = 0 := by
    rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨-, h1⟩ <;> injection h1 with h1 <;> exact h1.symm
  subst h0
  simp [loopNet] at hx

/-- `0 = 1, 1 = 0`, the cycle of two wires of `ReducedClosedCheck.wireCycle`, is a written vicious
circle (page 79). -/
theorem wireCycle_chainVicious : ReducedClosedCheck.wireCycle.ChainVicious :=
  ⟨ReducedClosedCheck.wireCycle, 0, ⟨0, 1, var 1, s(var 1, var 0) ::ₘ 0, by simp,
    .cons (by simp) (.nil 0), rfl⟩, by simp⟩

/-- `0 = 1, 1 = 0` is not in the form: no name is a free port. -/
theorem wireCycle_not_form : ¬ ReducedClosedCheck.wireCycle.IsTreesOnWiring :=
  fun h => ReducedClosedCheck.wireCycle_not_isReduced h.isReduced

/-! ## Attempts at refutation -/

/-- The empty net is in the form and reduced: no free port, no tree (page 79, `n = 0`). -/
theorem zero_form : (0 : Net sig ℕ).IsTreesOnWiring ∧ (0 : Net sig ℕ).IsReduced :=
  ⟨fun e he => absurd he (Multiset.notMem_zero e), Net.isReduced_zero⟩

/-- `0 = con(1, 1)`: a `con` cell whose two auxiliary ports are joined by a wire of the wiring. -/
def selfCon : Net sig ℕ := s(var 0, mkCon (var 1) (var 1)) ::ₘ 0

/-- `selfCon` is linear. -/
theorem selfCon_linear : selfCon.Linear := by
  intro y
  simp only [selfCon, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_mkCon,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- `selfCon` is in the form, hence reduced: the wire `1` joins two leaves of the same tree. -/
theorem selfCon_form : selfCon.IsTreesOnWiring ∧ selfCon.IsReduced := by
  have h : selfCon.IsTreesOnWiring := by
    intro e he
    simp only [selfCon, Multiset.mem_cons, Multiset.notMem_zero, or_false] at he
    subst he
    exact ⟨0, _, rfl, by simp [selfCon]⟩
  exact ⟨h, h.isReduced⟩

/-- `0 = con(2, 3), 1 = dup(2, 3)`: two trees whose leaves are joined two by two. -/
def shared : Net sig ℕ :=
  s(var 0, mkCon (var 2) (var 3)) ::ₘ s(var 1, mkDup (var 2) (var 3)) ::ₘ 0

/-- `shared` is linear. -/
theorem shared_linear : shared.Linear := by
  intro y
  simp only [shared, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_mkCon, vars_mkDup,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- `shared` is in the form, hence reduced (page 79). -/
theorem shared_form : shared.IsTreesOnWiring ∧ shared.IsReduced := by
  have h : shared.IsTreesOnWiring := by
    intro e he
    simp only [shared, Multiset.mem_cons, Multiset.notMem_zero, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨0, _, rfl, by simp [shared]⟩
    · exact ⟨1, _, rfl, by simp [shared]⟩
  exact ⟨h, h.isReduced⟩

/-- `0 = con(1, 1), 2 = con(1, 3)`: the name `1` occurs three times. This is not a net of the
paper (a port has one wire), yet it is in the form; the converse
`Net.IsTreesOnWiring.isReduced` holds for it without linearity, which is harmless: it says no
more than that no equation joins two cells and no name closes a circle. -/
def nonLinear : Net sig ℕ :=
  s(var 0, mkCon (var 1) (var 1)) ::ₘ s(var 2, mkCon (var 1) (var 3)) ::ₘ 0

/-- `nonLinear` is not linear. -/
theorem nonLinear_not_linear : ¬ nonLinear.Linear := by
  intro h
  have := h 1
  simp [nonLinear] at this

/-- `nonLinear` is in the form, and reduced. -/
theorem nonLinear_form : nonLinear.IsTreesOnWiring ∧ nonLinear.IsReduced := by
  have h : nonLinear.IsTreesOnWiring := by
    intro e he
    simp only [nonLinear, Multiset.mem_cons, Multiset.notMem_zero, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨0, _, rfl, by simp [nonLinear]⟩
    · exact ⟨2, _, rfl, by simp [nonLinear]⟩
  exact ⟨h, h.isReduced⟩

/-! ## The theorem applied to two trees with cells -/

/-- `5 = dup(3, 4), 0 = con(5, 6), 1 = con(3, 4)`: two trees with cells, on the free ports `0`
and `1`, and a third free port `6`; the first equation hangs from the internal name `5`, so the
net is not in the form. -/
def twoCellTrees : Net sig ℕ :=
  s(var 5, mkDup (var 3) (var 4)) ::ₘ s(var 0, mkCon (var 5) (var 6)) ::ₘ
    s(var 1, mkCon (var 3) (var 4)) ::ₘ 0

/-- Its decomposition: `0 = con(dup(3, 4), 6), 1 = con(3, 4)`. -/
def twoCellTreesForm : Net sig ℕ :=
  s(var 0, mkCon (mkDup (var 3) (var 4)) (var 6)) ::ₘ s(var 1, mkCon (var 3) (var 4)) ::ₘ 0

/-- `twoCellTrees` is linear. -/
theorem twoCellTrees_linear : twoCellTrees.Linear := by
  intro y
  simp only [twoCellTrees, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_mkCon,
    vars_mkDup, Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- `twoCellTrees` becomes `twoCellTreesForm` by the wire substitution of `5` (page 71). -/
theorem twoCellTrees_wire : Wire twoCellTrees twoCellTreesForm := by
  have h := Wire.mk 5 (mkDup (var 3) (var 4)) (var 0) (mkCon (var 5) (var 6))
    (s(var 1, mkCon (var 3) (var 4)) ::ₘ 0) twoCellTrees_linear (by simp)
  rw [subst_mkCon, Cut.subst_var_ne (by decide), Cut.subst_var_self,
    Cut.subst_var_ne (by decide)] at h
  exact h

/-- `twoCellTreesForm` is in the form. -/
theorem twoCellTreesForm_form : twoCellTreesForm.IsTreesOnWiring := by
  intro e he
  simp only [twoCellTreesForm, Multiset.mem_cons, Multiset.notMem_zero, or_false] at he
  rcases he with rfl | rfl
  · exact ⟨0, _, rfl, by simp [twoCellTreesForm]⟩
  · exact ⟨1, _, rfl, by simp [twoCellTreesForm]⟩

/-- `twoCellTrees` is reduced. -/
theorem twoCellTrees_isReduced : twoCellTrees.IsReduced :=
  twoCellTreesForm_form.isReduced.of_equiv twoCellTrees_wire.equiv.symm

/-- `twoCellTrees` is not in the form. -/
theorem twoCellTrees_not_form : ¬ twoCellTrees.IsTreesOnWiring := by
  intro h
  obtain ⟨x, t, he, hx⟩ := h _ (Multiset.mem_cons_self _ _)
  rcases Sym2.eq_iff.1 he with ⟨hx2, -⟩ | ⟨-, ht⟩
  · cases hx2
    simp [twoCellTrees] at hx
  · simp [mkDup] at ht

/-- **Non-vacuity of Proposition 2, existence, with two trees with cells** (Lafont 1997,
page 79): the hypotheses hold for `twoCellTrees`. -/
theorem twoCellTrees_decomp : ∃ M, Equiv twoCellTrees M ∧ M.IsTreesOnWiring :=
  Net.IsReduced.exists_treesOnWiring twoCellTrees_linear twoCellTrees_isReduced

/-! ## For part 2: the text form is not unique -/

/-- `0 = 7, 2 = con(7, 3)`: the free port `0` is a tree with no cell, joined by the wire `7` to a
leaf of `con(7, 3)`. -/
def pendant : Net sig ℕ := s(var 0, var 7) ::ₘ s(var 2, mkCon (var 7) (var 3)) ::ₘ 0

/-- `2 = con(0, 3)`: the same graph, with the free port `0` directly on the leaf. -/
def merged : Net sig ℕ := s(var 2, mkCon (var 0) (var 3)) ::ₘ 0

/-- `pendant` is linear. -/
theorem pendant_linear : pendant.Linear := by
  intro y
  simp only [pendant, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_mkCon,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- `pendant` is in the form: `0` and `2` are free ports. -/
theorem pendant_form : pendant.IsTreesOnWiring := by
  intro e he
  simp only [pendant, Multiset.mem_cons, Multiset.notMem_zero, or_false] at he
  rcases he with rfl | rfl
  · exact ⟨0, _, rfl, by simp [pendant]⟩
  · exact ⟨2, _, rfl, by simp [pendant]⟩

/-- `merged` is in the form. -/
theorem merged_form : merged.IsTreesOnWiring := by
  intro e he
  simp only [merged, Multiset.mem_cons, Multiset.notMem_zero, or_false] at he
  subst he
  exact ⟨2, _, rfl, by simp [merged]⟩

/-- `pendant` becomes `merged` by the wire substitution of `7` (page 71). -/
theorem pendant_wire : Wire pendant merged := by
  have h := Wire.mk 7 (var 0) (var 2) (mkCon (var 7) (var 3)) 0
    (by rw [Sym2.eq_swap]; exact pendant_linear) (by simp)
  rw [subst_mkCon, Cut.subst_var_ne (by decide), Cut.subst_var_self,
    Cut.subst_var_ne (by decide)] at h
  rw [pendant, Sym2.eq_swap]
  exact h

/-- **The text form is not unique up to renaming**: two nets in the form, the same graph, with
different numbers of equations (page 79). A uniqueness statement must be up to `Equiv`. -/
theorem pendant_merged : pendant.IsTreesOnWiring ∧ merged.IsTreesOnWiring ∧
    Equiv pendant merged ∧ Multiset.card pendant ≠ Multiset.card merged :=
  ⟨pendant_form, merged_form, pendant_wire.equiv, by simp [pendant, merged]⟩

/-- `5 = 2, 0 = con(5, 2)`: a common expansion of `0 = con(2, 2)` and `0 = con(5, 5)`. -/
def renamedMid : Net sig ℕ := s(var 5, var 2) ::ₘ s(var 0, mkCon (var 5) (var 2)) ::ₘ 0

/-- `renamedMid` is linear. -/
theorem renamedMid_linear : renamedMid.Linear := by
  intro y
  simp only [renamedMid, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_mkCon,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- **Renaming a wire of the wiring is within `Equiv`**: `0 = con(2, 2)` and `0 = con(5, 5)`
are `Equiv`, through `renamedMid` (page 71). So uniqueness up to `Equiv` includes uniqueness up to
renaming of the wiring. -/
theorem renamedA_equiv_renamedB :
    Equiv (s(var 0, mkCon (var 2) (var 2)) ::ₘ 0 : Net sig ℕ)
      (s(var 0, mkCon (var 5) (var 5)) ::ₘ 0) := by
  have h1 := Wire.mk 5 (var 2) (var 0) (mkCon (var 5) (var 2)) 0 renamedMid_linear (by simp)
  rw [subst_mkCon, Cut.subst_var_ne (by decide), Cut.subst_var_self,
    Cut.subst_var_ne (by decide)] at h1
  have h2 := Wire.mk 2 (var 5) (var 0) (mkCon (var 5) (var 2)) 0
    (by rw [Sym2.eq_swap]; exact renamedMid_linear) (by simp)
  rw [subst_mkCon, Cut.subst_var_ne (by decide), Cut.subst_var_self,
    Cut.subst_var_ne (by decide)] at h2
  rw [Sym2.eq_swap] at h2
  exact (Relation.EqvGen.rel _ _ h1).symm.trans _ _ _ (Relation.EqvGen.rel _ _ h2)

end INet.ReducedDecompReview
