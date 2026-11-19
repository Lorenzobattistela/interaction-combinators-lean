import InteractionCombinators.Lafont.StrongConfluenceE

/-!
# A concrete check of `StepE.strong_confluence` (page 73)

The net `x = con(1, 2), x = con(3, 4), era = era` (with `x` the name `0`) has two active pairs. The
pair `era = era` is an equation of the text; the pair of the two `con` cells is behind the wire
`0`, and no equation of the text joins two `con` cells (`no_con_con`). Firing it needs another text
of the same graph, `con(3, 4) = con(1, 2), era = era`. So the two `StepE` start from different
texts, and Proposition 1 up to wires applies to them.
-/

namespace INet

open Comb Term

namespace StrongConfluenceECheck

/-- The net: two `con` cells joined by the wire `0`, and two `era` cells joined directly. -/
def N : CNet :=
  s(var 0, mkCon (var 1) (var 2)) ::ₘ s(var 0, mkCon (var 3) (var 4)) ::ₘ s(mkEra, mkEra) ::ₘ 0

/-- After the interaction of the two `era` cells. -/
def M₁ : CNet := s(var 0, mkCon (var 1) (var 2)) ::ₘ s(var 0, mkCon (var 3) (var 4)) ::ₘ 0

/-- After the interaction of the two `con` cells. -/
def M₂ : CNet := s(var 1, var 4) ::ₘ s(var 2, var 3) ::ₘ s(mkEra, mkEra) ::ₘ 0

theorem N_linear : N.Linear := by
  intro y
  simp [N, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- No equation of the text `N` joins two `con` cells: the `con`–`con` pair is not a literal
active pair of `N`. -/
theorem no_con_con (a b c d : Term sig ℕ) : s(mkCon a b, mkCon c d) ∉ N := by
  have hne : ∀ ts us, (Term.app (Comb.con : sig.Sym) ts : Term sig ℕ) ≠ Term.app Comb.era us := by
    intro ts us h
    cases h
  simp only [N, Multiset.mem_cons, Sym2.eq_iff, Multiset.notMem_zero, or_false, mkCon, mkEra,
    reduceCtorEq, false_and, and_false, or_self, false_or]
  exact fun h => hne _ _ h.1

theorem stepE₁ : StepE system N M₁ := by
  refine ⟨s(mkEra, mkEra) ::ₘ M₁, Equiv.of_eq ?_, step_era_era _⟩
  simp only [N, M₁, Multiset.cons_swap (s(mkEra, mkEra))]

/-- The `con`–`con` pair is fired after the wire `0` is substituted. -/
theorem stepE₂ : StepE system N M₂ := by
  have W := Wire.mk 0 (mkCon (var 1) (var 2)) (var 0) (mkCon (var 3) (var 4))
    (s(mkEra, mkEra) ::ₘ 0) N_linear (by simp)
  have e : (mkCon (var 3) (var 4) : Term sig ℕ).subst 0 (mkCon (var 1) (var 2)) =
      mkCon (var 3) (var 4) := Term.subst_of_notMem (by simp)
  rw [Comb.subst_var_self, e] at W
  exact ⟨_, W.equiv, step_con_con _ _ _ _ _⟩

/-- Non-vacuity of `StepE.strong_confluence`: its hypotheses hold for `N`, `M₁`, `M₂`, with the
second interaction reachable only through a wire. -/
example : Equiv M₁ M₂ ∨ ∃ P₁ P₂, StepE system M₁ P₁ ∧ StepE system M₂ P₂ ∧ Equiv P₁ P₂ :=
  StepE.strong_confluence system_wellFormed N_linear stepE₁ stepE₂

end StrongConfluenceECheck

end INet
