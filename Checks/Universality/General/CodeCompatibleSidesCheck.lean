import InteractionCombinators.Universality.General.CodeCompatibleSides
import Checks.Universality.General.CodeGammaMeetCheck

/-!
# Checks for `System.SidesPlug` (pages 86, 89–90)

Non-vacuity of the hypothesis of `codeTranslation_compatible_of_sides`
(`InteractionCombinators/Universality/General/CodeCompatibleSides.lean`): on the combinators
`Comb.system`, which are well formed, the sides of the decomposition data `decData
system_wellFormed` satisfy `System.SidesPlug`, and the property says something about an actual rule,
`con`–`dup`.
-/

namespace INet.Comb.CodeCompatibleSidesCheck

open CodeGammaMeetCheck

/-- **`SidesPlug` is satisfiable** (page 86): the sides of decomposition data of the combinators
plug back into their rules. -/
theorem sidesPlug_system :
    system.SidesPlug (System.WellFormed.decData system_wellFormed).side :=
  (System.WellFormed.decData system_wellFormed).sidesPlug system_wellFormed

/-- **`SidesPlug` applies to a rule** (page 86): for the rule `con`–`dup` of the combinators, it
gives two defined sides that plug back the rule, so the property is not vacuous. -/
theorem sidesPlug_system_conDup :
    ∃ (k : ℕ) (φ : Rule sig 2 k) (ψ : Rule sig 2 k) (σ : _root_.Equiv.Perm (Fin k)),
      (System.WellFormed.decData system_wellFormed).side Comb.con Comb.dup ≠ none ∧
      (System.WellFormed.decData system_wellFormed).side Comb.dup Comb.con ≠ none ∧
      (⟨k, φ, ψ, σ⟩ : Decomposition sig 2 2).Plugs ruleConDup := by
  obtain ⟨k, φ, ψ, σ, hσ, hl, he, hl', he', hs, hs', hP⟩ :=
    sidesPlug_system (α := Comb.con) (β := Comb.dup) (r := ruleConDup) rfl
  refine ⟨k, φ, ψ, σ, ?_, ?_, hP⟩
  · rw [hs]
    exact Option.some_ne_none _
  · rw [hs']
    exact Option.some_ne_none _

/-- **The translation of Fig. 10 for these sides is compatible** (pages 89–90), through
`codeTranslation_compatible_of_sides`. -/
theorem codeTranslation_compatible_system :
    (codeTranslation (System.WellFormed.decData system_wellFormed).side).Compatible system
      system :=
  codeTranslation_compatible_of_sides sidesPlug_system

end INet.Comb.CodeCompatibleSidesCheck
