import InteractionCombinators.Reduced.ReducedDecomp
import Checks.Reduced.ReducedClosedCheck

/-!
# Checks for Proposition 2, existence (page 79)

* `twoTrees` — `2 = dup(3, 4), 0 = con(2, 1)`: a reduced linear net that is **not** in the form
  `Net.IsTreesOnWiring` (the equation `2 = dup(3, 4)` hangs from the internal name `2`), to which
  `Net.IsReduced.exists_treesOnWiring` applies. Its decomposition is `0 = con(dup(3, 4), 1)`,
  obtained by one wire substitution.
* `ReducedClosedCheck.cutNet` — `con(0, 1) = con(1, 0)`, a net with a cut: no net `Equiv` to it is
  in the form.
-/

namespace INet.ReducedDecompCheck

open Term Comb

/-- `2 = dup(3, 4), 0 = con(2, 1)`: a `dup` cell whose principal port is on the left auxiliary
port of a `con` cell, joined through the internal name `2` (Lafont 1997, page 79). -/
def twoTrees : Net sig ℕ :=
  s(var 2, mkDup (var 3) (var 4)) ::ₘ s(var 0, mkCon (var 2) (var 1)) ::ₘ 0

/-- `0 = con(dup(3, 4), 1)`: the same graph, one tree on the free port `0`. -/
def oneTree : Net sig ℕ := s(var 0, mkCon (mkDup (var 3) (var 4)) (var 1)) ::ₘ 0

/-- `twoTrees` is linear. -/
theorem twoTrees_linear : twoTrees.Linear := by
  intro y
  simp only [twoTrees, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_mkCon,
    vars_mkDup, Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- `twoTrees` becomes `oneTree` by the wire substitution of `2` (Lafont 1997, page 71). -/
theorem twoTrees_wire : Wire twoTrees oneTree := by
  have h := Wire.mk 2 (mkDup (var 3) (var 4)) (var 0) (mkCon (var 2) (var 1)) 0
    twoTrees_linear (by simp)
  rw [subst_mkCon, Cut.subst_var_ne (by decide), Cut.subst_var_self,
    Cut.subst_var_ne (by decide)] at h
  exact h

/-- `oneTree` is in the form: its one equation hangs from the free port `0`. -/
theorem oneTree_form : oneTree.IsTreesOnWiring := by
  intro e he
  simp only [oneTree, Multiset.mem_cons, Multiset.notMem_zero, or_false] at he
  subst he
  exact ⟨0, _, rfl, by simp [oneTree]⟩

/-- `twoTrees` is reduced: it is the same graph as a net in the form
(`Net.IsTreesOnWiring.isReduced`, page 79). -/
theorem twoTrees_isReduced : twoTrees.IsReduced :=
  oneTree_form.isReduced.of_equiv twoTrees_wire.equiv.symm

/-- `twoTrees` is not in the form: `2 = dup(3, 4)` has the internal name `2` on its only name
side, and the cell `dup` on the other. -/
theorem twoTrees_not_form : ¬ twoTrees.IsTreesOnWiring := by
  intro h
  obtain ⟨x, t, he, hx⟩ := h _ (Multiset.mem_cons_self _ _)
  rcases Sym2.eq_iff.1 he with ⟨hx2, -⟩ | ⟨-, ht⟩
  · cases hx2
    simp [twoTrees] at hx
  · simp [mkDup] at ht

/-- **Non-vacuity of Proposition 2, existence** (Lafont 1997, page 79): the hypotheses hold for
`twoTrees`, which is not already in the form, and the theorem gives a decomposition. -/
theorem twoTrees_decomp : ∃ M, Equiv twoTrees M ∧ M.IsTreesOnWiring :=
  Net.IsReduced.exists_treesOnWiring twoTrees_linear twoTrees_isReduced

/-- A net with a cut is not trees on a wiring, up to wires: no net `Equiv` to
`con(0, 1) = con(1, 0)` is in the form (Lafont 1997, page 79). -/
theorem cutNet_no_form :
    ∀ M, Equiv ReducedClosedCheck.cutNet M → ¬ M.IsTreesOnWiring :=
  fun _ hE hM => hM.isReduced.1 (ReducedClosedCheck.cutNet_hasCut.of_equiv hE)

end INet.ReducedDecompCheck
