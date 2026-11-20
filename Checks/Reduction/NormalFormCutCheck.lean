import InteractionCombinators.Reduction.NormalFormCut
import InteractionCombinators.Core.Combinators

/-!
# Checks of `InteractionCombinators/Reduction/NormalFormCut.lean`

"Irreducible if and only if without a cut" on small nets of the combinators: the empty net, a cut
written as one equation, a cut through a named wire, and a system with no rule, where a cut is
irreducible, so that the completeness hypothesis of `StepE.Normal.iff_not_hasCut` cannot be
dropped. Written during the review of 20 November 2026.
-/

namespace INet.NormalFormCutCheck
open Comb

/-- The empty net is irreducible, through `normal_iff_not_hasCut`. -/
theorem empty_normal : StepE.Normal system (0 : Net sig ℕ) :=
  normal_iff_not_hasCut.2 (by
    intro h
    obtain ⟨a, b, xs, D, -, -, h⟩ := h.chainCut
    have := congrArg Multiset.card h
    cases xs <;> simp [Cut.chain] at this)

/-- The cut `era = era` is not irreducible. -/
theorem cut_not_normal : ¬ StepE.Normal system (s(mkEra, mkEra) ::ₘ 0) :=
  fun h => normal_iff_not_hasCut.1 h (Net.hasCut_of_mem (Multiset.mem_cons_self _ _))

/-- A cut through a named wire: `era = 0, 0 = era`. -/
def wireCut : Net sig ℕ := Cut.chain mkEra [0] mkEra + 0

/-- The text of `wireCut`. -/
theorem wireCut_eq : wireCut = s(mkEra, .var 0) ::ₘ s(.var 0, mkEra) ::ₘ 0 := by
  simp [wireCut, Cut.chain]

/-- `wireCut` is linear. -/
theorem wireCut_lin : wireCut.Linear := by
  intro x
  rw [wireCut_eq]
  simp only [Net.vars_cons, eqVars_mk, vars_mkEra, Term.vars_var, Net.vars_zero,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- A cut through a named wire is seen by `Net.HasCut`, and the net is not irreducible. -/
theorem wireCut_not_normal : ¬ StepE.Normal system wireCut :=
  fun h => normal_iff_not_hasCut.1 h
    ((Net.hasCut_iff_chainCut wireCut_lin).2
      ⟨mkEra, mkEra, [0], 0, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, rfl⟩)

/-- The system with no rule at all. -/
def noRules : System sig := ⟨fun _ _ => none⟩

/-- **The completeness hypothesis of `StepE.Normal.iff_not_hasCut` is needed**: with no rule,
`era = era` has a cut and is irreducible (Lafont 1997, page 79: "it may contain irreducible
cuts"). -/
theorem noRules_counter :
    StepE.Normal noRules (s(mkEra, mkEra) ::ₘ 0) ∧
      Net.HasCut (s(mkEra, mkEra) ::ₘ 0 : Net sig ℕ) := by
  refine ⟨?_, Net.hasCut_of_mem (Multiset.mem_cons_self _ _)⟩
  rintro M ⟨N', -, hs⟩
  cases hs with
  | mk α β r hr => cases hr

end INet.NormalFormCutCheck
