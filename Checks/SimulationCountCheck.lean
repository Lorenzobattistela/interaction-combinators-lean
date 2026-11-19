import InteractionCombinators.Lafont.SimulationCount
import Checks.SimulationCheck

/-!
# Checks of Proposition 4 with the bounds (page 81)

`Translation.CompatibleWithin.steps` is applied to the identity translation of the combinators,
with `L = M = 1`, on the one-step net `src` of `SimulationCheck`: an `era`–`con` cut beside a
`dup` cell. The translation of `src` reduces in exactly one interaction.
-/

namespace INet.SimulationCountCheck

open Term Comb SimulationCheck

/-- `src` reduces to `tgt` in exactly one interaction. -/
theorem stepsN_src : StepsN system 1 src tgt := (StepsN.refl src).tail (step_src system rfl)

/-- Proposition 4 with the bounds, for the identity translation (`L = M = 1`) and one
interaction: the translation of `src` reduces in `n'` interactions, `1 ≤ n' ≤ 1`, to a net that is
the same graph as a translation of `tgt`. -/
example : ∃ n' M₁ M', StepsEN system n' src M₁ ∧ 1 * 1 ≤ n' ∧ n' ≤ 1 * 1 ∧ Equiv M₁ M' ∧
    (Translation.id sig).NetTr tgt M' :=
  (Translation.id_compatibleWithin system system_wellFormed).steps system_wellFormed.linear
    system_wellFormed.linear stepsN_src
    ⟨Multiset.rel_refl_of_refl_on fun e _ => Translation.eqTr_id e, src_linear⟩

/-- The same, read off: the length is exactly one. -/
example : ∃ M₁ M', StepsEN system 1 src M₁ ∧ Equiv M₁ M' ∧
    (Translation.id sig).NetTr tgt M' := by
  obtain ⟨n', M₁, M', h, h1, h2, hE, hT⟩ :=
    (Translation.id_compatibleWithin system system_wellFormed).steps system_wellFormed.linear
      system_wellFormed.linear stepsN_src
      ⟨Multiset.rel_refl_of_refl_on fun e _ => Translation.eqTr_id e, src_linear⟩
  obtain rfl : n' = 1 := by omega
  exact ⟨M₁, M', h, hE, hT⟩

/-- `CompatibleWithin` gives back `Compatible`. -/
example : (Translation.id sig).Compatible system system :=
  (Translation.id_compatibleWithin system system_wellFormed).compatible

end INet.SimulationCountCheck
