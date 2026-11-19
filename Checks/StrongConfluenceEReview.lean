import Checks.StrongConfluenceECheck

/-!
# Review of `StepE.strong_confluence` (Proposition 1 up to wires, page 73)

Checks written for the review of issue #257.

* The net `N` of `Checks/StrongConfluenceECheck.lean` (`x = con(1, 2), x = con(3, 4), era = era`)
  has two `StepE` to nets that are not the same graph (`not_equiv`: `Equiv` keeps the cells,
  `Equiv.cells_eq`). The theorem then gives its second branch (`second_branch`), so it is not
  only used through its first one; the common reduct is given by hand as well (`common`), and is
  reached from `M₁` only through the wire `0`.
* An active pair fired in its two orientations: for `con`–`con` (which exchanges the auxiliary
  ports) and for `dup`–`dup` (which does not), the two results are the same net, so the first
  branch is the one that holds (`con_con_orientations`, `dup_dup_orientations`).
-/

namespace INet

open Comb Term

namespace StrongConfluenceEReview

open StrongConfluenceECheck

theorem cells_mkCon (a b : Term sig ℕ) :
    (mkCon a b).cells = (Comb.con : sig.Sym) ::ₘ (a.cells + b.cells) := by
  simp [mkCon, sig, Fin.sum_univ_two]
  rfl

theorem cells_mkEra : (mkEra : Term sig ℕ).cells = {(Comb.era : sig.Sym)} := by
  simp [mkEra, sig]
  rfl

/-- The two reducts of `N` are not the same graph: `M₁` has two `con` cells, `M₂` two `era`
cells. -/
theorem not_equiv : ¬ Equiv M₁ M₂ := by
  intro h
  have hc := h.cells_eq
  have h0 : Net.cells (0 : CNet) = 0 := rfl
  simp only [M₁, M₂, Net.cells_cons, eqCells_mk, cells_mkCon, cells_mkEra, Term.cells_var,
    h0] at hc
  have := congrArg (Multiset.count (Comb.era : sig.Sym)) hc
  revert this
  decide

/-- Non-vacuity of the second branch of `StepE.strong_confluence` (page 73): for two `StepE` to
different graphs, the theorem gives a common reduct up to wires. -/
theorem second_branch :
    ∃ P₁ P₂, StepE system M₁ P₁ ∧ StepE system M₂ P₂ ∧ Equiv P₁ P₂ :=
  (StepE.strong_confluence system_wellFormed N_linear stepE₁ stepE₂).resolve_left not_equiv

/-- The common reduct of `M₁` and `M₂`: two wires. -/
def P : CNet := s(var 1, var 4) ::ₘ s(var 2, var 3) ::ₘ 0

theorem M₁_linear : M₁.Linear := by
  intro y
  simp [M₁, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- `M₁` reaches `P` by the `con`–`con` interaction behind the wire `0`. -/
theorem stepE_M₁ : StepE system M₁ P := by
  have W := Wire.mk 0 (mkCon (var 1) (var 2)) (var 0) (mkCon (var 3) (var 4)) 0 M₁_linear
    (by simp)
  have e : (mkCon (var 3) (var 4) : Term sig ℕ).subst 0 (mkCon (var 1) (var 2)) =
      mkCon (var 3) (var 4) := Term.subst_of_notMem (by simp)
  rw [Comb.subst_var_self, e] at W
  exact ⟨_, W.equiv, step_con_con _ _ _ _ _⟩

/-- `M₂` reaches `P` by the `era`–`era` interaction. -/
theorem stepE_M₂ : StepE system M₂ P := by
  refine ⟨s(mkEra, mkEra) ::ₘ P, Equiv.of_eq ?_, step_era_era _⟩
  simp only [M₂, P, Multiset.cons_swap (s(mkEra, mkEra))]

/-- The second branch of `StepE.strong_confluence` for `N`, by hand, with the same net `P` on
both sides. -/
theorem common : ∃ P₁ P₂, StepE system M₁ P₁ ∧ StepE system M₂ P₂ ∧ Equiv P₁ P₂ :=
  ⟨P, P, stepE_M₁, stepE_M₂, Equiv.refl _⟩

/-- A `con`–`con` pair fired in its two orientations (page 73: `ν̄_{i,i} = ν_{i,i}`) gives the
same net: `0 = 3, 1 = 2` and `2 = 1, 3 = 0`. -/
theorem con_con_orientations :
    Step system (s(mkCon (var 0) (var 1), mkCon (var 2) (var 3)) ::ₘ 0)
        (s(var 0, var 3) ::ₘ s(var 1, var 2) ::ₘ 0) ∧
      Step system (s(mkCon (var 0) (var 1), mkCon (var 2) (var 3)) ::ₘ 0)
        (s(var 2, var 1) ::ₘ s(var 3, var 0) ::ₘ 0) ∧
      (s(var 0, var 3) ::ₘ s(var 1, var 2) ::ₘ 0 : CNet) =
        s(var 2, var 1) ::ₘ s(var 3, var 0) ::ₘ 0 := by
  refine ⟨step_con_con _ _ _ _ _, ?_, ?_⟩
  · rw [Sym2.eq_swap]
    exact step_con_con _ _ _ _ _
  · rw [Sym2.eq_swap (a := var 2), Sym2.eq_swap (a := var 3), Multiset.cons_swap]

/-- A `dup`–`dup` pair fired in its two orientations gives the same net: `0 = 2, 1 = 3` and
`2 = 0, 3 = 1`. -/
theorem dup_dup_orientations :
    Step system (s(mkDup (var 0) (var 1), mkDup (var 2) (var 3)) ::ₘ 0)
        (s(var 0, var 2) ::ₘ s(var 1, var 3) ::ₘ 0) ∧
      Step system (s(mkDup (var 0) (var 1), mkDup (var 2) (var 3)) ::ₘ 0)
        (s(var 2, var 0) ::ₘ s(var 3, var 1) ::ₘ 0) ∧
      (s(var 0, var 2) ::ₘ s(var 1, var 3) ::ₘ 0 : CNet) =
        s(var 2, var 0) ::ₘ s(var 3, var 1) ::ₘ 0 := by
  refine ⟨step_dup_dup _ _ _ _ _, ?_, ?_⟩
  · rw [Sym2.eq_swap]
    exact step_dup_dup _ _ _ _ _
  · rw [Sym2.eq_swap (a := var 2), Sym2.eq_swap (a := var 3)]

end StrongConfluenceEReview

end INet
