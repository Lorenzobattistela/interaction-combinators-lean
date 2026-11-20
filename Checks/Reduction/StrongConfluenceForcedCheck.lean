import InteractionCombinators.Reduction.StrongConfluenceNoReduced
import InteractionCombinators.Core.Combinators

/-!
# `strong_confluence_of` on two results that differ (Lafont 1997, Proposition 1, page 73)

The conclusion of `Step.strong_confluence_of` is a disjunction: the two results are the same
graph, or they have a common reduct in one step. `StrongConfluenceNoReducedCheck.lean` applies the
theorem where the first case holds. Here the net has two different cuts, `era = era` and
`con(0, 1) = con(2, 3)`; the two results have different cells, so they are not the same graph and
the second case is the one that holds. Written during the review of 20 November 2026.
-/

namespace INet.StrongConfluenceForcedCheck
open Comb

/-- A net with two cuts: `era = era` and `con(0, 1) = con(2, 3)`. -/
def N : Net sig ℕ :=
  s(mkEra, mkEra) ::ₘ s(mkCon (.var 0) (.var 1), mkCon (.var 2) (.var 3)) ::ₘ 0
/-- `N` after the `era`–`era` interaction. -/
def M₁ : Net sig ℕ := s(mkCon (.var 0) (.var 1), mkCon (.var 2) (.var 3)) ::ₘ 0
/-- `N` after the `con`–`con` interaction, which exchanges the auxiliary ports. -/
def M₂ : Net sig ℕ := s(.var 0, .var 3) ::ₘ s(.var 1, .var 2) ::ₘ s(mkEra, mkEra) ::ₘ 0

/-- The net `N` is linear. -/
theorem N_lin : N.Linear := by
  intro x
  simp only [N, Net.vars_cons, eqVars_mk, vars_mkEra, vars_mkCon, Term.vars_var, Net.vars_zero,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- `N` reduces to `M₁`. -/
theorem s1 : Step system N M₁ := step_era_era _

/-- `N` reduces to `M₂`. -/
theorem s2 : Step system N M₂ := by
  have h := step_con_con (.var 0) (.var 1) (.var 2) (.var 3) (s(mkEra, mkEra) ::ₘ 0)
  have e : N = s(mkCon (.var 0) (.var 1), mkCon (.var 2) (.var 3)) ::ₘ s(mkEra, mkEra) ::ₘ 0 :=
    Multiset.cons_swap _ _ _
  rw [e]
  exact h

/-- The cells of a `con` tree. -/
theorem mkCon_cells (a b : Term sig ℕ) :
    (mkCon a b).cells = (show sig.Sym from Comb.con) ::ₘ (a.cells + b.cells) := by
  change _ ::ₘ ∑ i : Fin 2, _ = _
  rw [Fin.sum_univ_two]; rfl

/-- The cells of an `era` tree. -/
theorem mkEra_cells :
    (mkEra : Term sig ℕ).cells = {(show sig.Sym from Comb.era)} := by
  change _ ::ₘ ∑ i : Fin 0, _ = _
  rw [Finset.univ_eq_empty, Finset.sum_empty]; rfl

/-- The two results are not the same graph: `M₁` has no `era` cell and `M₂` has two. -/
theorem notEquiv : ¬ Equiv M₁ M₂ := by
  intro h
  have hc := h.cells_eq
  have e1 : M₁.cells = (Comb.con : sig.Sym) ::ₘ (Comb.con : sig.Sym) ::ₘ 0 := by
    simp only [M₁, Net.cells_cons, eqCells_mk]
    change (mkCon _ _).cells + (mkCon _ _).cells + Net.cells 0 = _
    rw [mkCon_cells, mkCon_cells]
    rfl
  have e2 : Comb.era ∈ M₂.cells := by
    simp only [M₂, Net.cells_cons, eqCells_mk]
    rw [mkEra_cells]
    exact Multiset.mem_add.2 (Or.inr (Multiset.mem_add.2 (Or.inr (Multiset.mem_add.2 (Or.inl
      (Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self _))))))))
  rw [← hc, e1] at e2
  rcases Multiset.mem_cons.1 e2 with h | h
  · cases h
  · rcases Multiset.mem_cons.1 h with h | h
    · cases h
    · simp at h

/-- **The right disjunct of `Step.strong_confluence_of` is exercised** (Lafont 1997,
Proposition 1, page 73): the two results differ, so they have a common reduct in one step. -/
theorem forced : ∃ P₁ P₂, Step system M₁ P₁ ∧ Step system M₂ P₂ ∧ Equiv P₁ P₂ :=
  (Step.strong_confluence_of system_wellFormed.linear system_wellFormed.unique
    system_wellFormed.symm N_lin s1 s2).resolve_left notEquiv

/-- The same for `StepE.strong_confluence_of`, reduction up to wires. -/
theorem forcedE : ∃ P₁ P₂, StepE system M₁ P₁ ∧ StepE system M₂ P₂ ∧ Equiv P₁ P₂ :=
  (StepE.strong_confluence_of system_wellFormed.linear system_wellFormed.unique
    system_wellFormed.symm N_lin s1.stepE s2.stepE).resolve_left notEquiv

end INet.StrongConfluenceForcedCheck
