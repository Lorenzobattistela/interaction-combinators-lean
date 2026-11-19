import InteractionCombinators.Lafont.DecompositionSymm
import Checks.DecompositionReview

/-!
# Non-vacuity of `Rule.exists_symm_decomposition` (page 86)

The hypotheses of `Rule.exists_symm_decomposition` (linear, reduced, `Equiv r.swap.net r.net`)
hold for concrete rules of a symbol with itself, which therefore get a symmetric decomposition.

* `selfRule` (`Checks/DecompositionReview.lean`): symmetric only up to `Equiv`
  (`selfRule_symm`), and its *canonical* decomposition is not symmetric (its `σ` is a 3-cycle,
  `selfRule_σ`).
* `ruleConCon` (`a₀ = b₁, a₁ = b₀`): not in expanded form (`ExpandCheck.ruleConCon_not_expanded`),
  so the expansion step of the proof is used.
* `ruleDupDup` and `ruleEraEra`, the other rules `α`–`α` of the combinators.
-/

namespace INet.Comb.DecompositionSymmCheck

open Term Rule INet.Comb.DecompositionReview

/-- **Non-vacuity.** `selfRule`, symmetric up to `Equiv` only, has a symmetric decomposition
(`ψ = φ`, `σ` involutive) whose plug is the rule (page 86). -/
theorem selfRule_symm_decomposition :
    ∃ D : Decomposition sig 3 3, D.ψ = D.φ ∧ (∀ l, D.σ (D.σ l) = l) ∧ D.φ.Linear ∧
      D.φ.Reduced ∧
      ∃ ι : Fin selfRule.internal → Fin (Rule.plug D.φ D.ψ D.σ).internal, Function.Injective ι ∧
        Equiv (Rule.plug D.φ D.ψ D.σ).net
          (selfRule.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) :=
  selfRule.exists_symm_decomposition selfRule_linear selfRule_reduced selfRule_symm

/-- **Non-vacuity.** `ruleConCon`, which is not in expanded form, has a symmetric decomposition
(page 86). -/
theorem ruleConCon_symm_decomposition :
    ∃ D : Decomposition sig 2 2, D.ψ = D.φ ∧ (∀ l, D.σ (D.σ l) = l) ∧ D.φ.Linear ∧
      D.φ.Reduced ∧
      ∃ ι : Fin ruleConCon.internal → Fin (Rule.plug D.φ D.ψ D.σ).internal,
        Function.Injective ι ∧ Equiv (Rule.plug D.φ D.ψ D.σ).net
          (ruleConCon.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) :=
  ruleConCon.exists_symm_decomposition ruleConCon_linear ruleConCon_reduced
    (Equiv.of_eq ruleConCon_swap)

/-- **Non-vacuity.** `ruleDupDup` has a symmetric decomposition (page 86). -/
theorem ruleDupDup_symm_decomposition :
    ∃ D : Decomposition sig 2 2, D.ψ = D.φ ∧ (∀ l, D.σ (D.σ l) = l) ∧ D.φ.Linear ∧
      D.φ.Reduced ∧
      ∃ ι : Fin ruleDupDup.internal → Fin (Rule.plug D.φ D.ψ D.σ).internal,
        Function.Injective ι ∧ Equiv (Rule.plug D.φ D.ψ D.σ).net
          (ruleDupDup.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) :=
  ruleDupDup.exists_symm_decomposition ruleDupDup_linear ruleDupDup_reduced
    (Equiv.of_eq ruleDupDup_swap)

/-- **Non-vacuity.** `ruleEraEra` (the empty net) has a symmetric decomposition (page 86). -/
theorem ruleEraEra_symm_decomposition :
    ∃ D : Decomposition sig 0 0, D.ψ = D.φ ∧ (∀ l, D.σ (D.σ l) = l) ∧ D.φ.Linear ∧
      D.φ.Reduced ∧
      ∃ ι : Fin ruleEraEra.internal → Fin (Rule.plug D.φ D.ψ D.σ).internal,
        Function.Injective ι ∧ Equiv (Rule.plug D.φ D.ψ D.σ).net
          (ruleEraEra.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) :=
  ruleEraEra.exists_symm_decomposition ruleEraEra_linear ruleEraEra_reduced
    (Equiv.of_eq ruleEraEra_swap)

end INet.Comb.DecompositionSymmCheck
