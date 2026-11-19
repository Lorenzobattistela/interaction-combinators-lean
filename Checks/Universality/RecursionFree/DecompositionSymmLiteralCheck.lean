import InteractionCombinators.Universality.RecursionFree.DecompositionSymmLiteral
import Checks.Universality.RecursionFree.DecompositionReview

/-!
# Non-vacuity of `Rule.SymmLit.exists_symm_decomposition` (page 86)

The hypotheses of `Rule.SymmLit.exists_symm_decomposition` hold for two concrete rules of a symbol
with itself.

* `selfRule` (`Checks/DecompositionReview.lean`) is already in expanded form, and is literally
  symmetric with `π` the exchange of `w₀` and `w₂`. It is the rule whose *canonical*
  decomposition is not symmetric (its `σ` is a 3-cycle); the theorem gives a symmetric one.
* `conConExp`, the expanded form of `ruleConCon`: `a₀ = x₀, b₁ = x₀, a₁ = x₁, b₀ = x₁`, literally
  symmetric with `π` the exchange of `x₀` and `x₁`.
-/

namespace INet.Comb.DecompositionSymmLiteralCheck

open Term Rule INet.Comb.DecompositionReview

/-- `selfRule` is in expanded form: every equation is rooted at a port, with only internal wires
below. -/
theorem selfRule_expanded : selfRule.Expanded := by
  change ∀ e ∈ (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4) from selfRule.net),
    ∃ (p : Fin 3 ⊕ Fin 3 ⊕ Fin 4) (t : Term sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4)),
      e = s(Term.var p, t) ∧ (∀ w : Fin 4, p ≠ .inr (.inr w)) ∧
        ∀ x ∈ t.vars, ∃ w : Fin 4, x = .inr (.inr w)
  intro e he
  have key : ∀ e ∈ (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4) from selfRule.net),
      e ∈ [s(pl 0, mkCon (pw 0) (pw 1)), s(pl 1, mkCon (pw 2) mkEra), s(pl 2, pw 3),
        s(pr 0, mkCon (pw 2) (pw 1)), s(pr 1, mkCon (pw 0) mkEra), s(pr 2, pw 3)] := by
    decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, rfl, (fun w h => by cases h), (by decide)⟩

/-- `selfRule` read from the other cell is `selfRule` with `w₀` and `w₂` exchanged, literally. -/
theorem selfRule_swap :
    selfRule.swap.net =
      selfRule.net.bind fun x => var (Sum.map id (Sum.map id (Equiv.swap (0 : Fin 4) 2)) x) := by
  change (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4) from selfRule.swap.net) =
    (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4) from
      selfRule.net.bind fun x => var (Sum.map id (Sum.map id (Equiv.swap (0 : Fin 4) 2)) x))
  decide

/-- **Non-vacuity.** `selfRule` has a symmetric decomposition (`ψ = φ`, `σ` involutive) whose plug
is the rule (page 86). -/
theorem selfRule_symm_decomposition :
    ∃ D : Decomposition sig 3 3, D.ψ = D.φ ∧ (∀ l, D.σ (D.σ l) = l) ∧ D.φ.Linear ∧
      D.φ.Reduced ∧
      ∃ ι : Fin selfRule.internal → Fin (Rule.plug D.φ D.ψ D.σ).internal, Function.Injective ι ∧
        Equiv (Rule.plug D.φ D.ψ D.σ).net
          (selfRule.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) :=
  SymmLit.exists_symm_decomposition selfRule selfRule_linear selfRule_expanded
    _ selfRule_swap

/-- The expanded form of `ruleConCon`: `a₀ = x₀, b₁ = x₀, a₁ = x₁, b₀ = x₁`. -/
def conConExp : Rule sig 2 2 :=
  ⟨2, s(pl 0, pw 0) ::ₘ s(pr 1, pw 0) ::ₘ s(pl 1, pw 1) ::ₘ {s(pr 0, pw 1)}⟩

/-- `conConExp` is linear. -/
theorem conConExp_linear : conConExp.Linear := ⟨by decide, by decide, by decide⟩

/-- `conConExp` is in expanded form. -/
theorem conConExp_expanded : conConExp.Expanded := by
  change ∀ e ∈ (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2) from conConExp.net),
    ∃ (p : Fin 2 ⊕ Fin 2 ⊕ Fin 2) (t : Term sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2)),
      e = s(Term.var p, t) ∧ (∀ w : Fin 2, p ≠ .inr (.inr w)) ∧
        ∀ x ∈ t.vars, ∃ w : Fin 2, x = .inr (.inr w)
  intro e he
  have key : ∀ e ∈ (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2) from conConExp.net),
      e ∈ [s(pl 0, pw 0), s(pr 1, pw 0), s(pl 1, pw 1), s(pr 0, pw 1)] := by
    decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl, (fun w h => by cases h), (by decide)⟩

/-- `conConExp` read from the other cell is itself with `x₀` and `x₁` exchanged. -/
theorem conConExp_swap :
    conConExp.swap.net =
      conConExp.net.bind fun x => var (Sum.map id (Sum.map id (Equiv.swap (0 : Fin 2) 1)) x) := by
  change (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2) from conConExp.swap.net) =
    (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2) from
      conConExp.net.bind fun x => var (Sum.map id (Sum.map id (Equiv.swap (0 : Fin 2) 1)) x))
  decide

/-- **Non-vacuity.** The expanded `ruleConCon` has a symmetric decomposition (page 86). -/
theorem conConExp_symm_decomposition :
    ∃ D : Decomposition sig 2 2, D.ψ = D.φ ∧ (∀ l, D.σ (D.σ l) = l) ∧ D.φ.Linear ∧
      D.φ.Reduced ∧
      ∃ ι : Fin conConExp.internal → Fin (Rule.plug D.φ D.ψ D.σ).internal, Function.Injective ι ∧
        Equiv (Rule.plug D.φ D.ψ D.σ).net
          (conConExp.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) :=
  SymmLit.exists_symm_decomposition conConExp conConExp_linear conConExp_expanded _
    conConExp_swap

end INet.Comb.DecompositionSymmLiteralCheck
