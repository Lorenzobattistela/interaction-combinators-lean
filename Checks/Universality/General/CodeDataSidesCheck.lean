import InteractionCombinators.Universality.General.CodeDataSides
import Checks.Universality.General.CodeGammaMeetCheck

/-!
# Checks for `System.DecData.sides_expand` (pages 85–86, 90)

Non-vacuity of `System.DecData.sides_expand` (`Lafont/CodeDataSides.lean`) on the combinators
`Comb.system`, with the decomposition data `decData system_wellFormed`: for the rule `con`–`dup`
(`α ≠ β`), for the rule `con`–`con` (`α = β`), and for the rule `dup`–`dup`, where the result
feeds `codeCells_meet_end` on a net whose linearity is proved (`linear_netDupDup`). In each case
the sides it gives are exactly the hypotheses `hs`, `hs'` of `codeCells_meet_end` (Fig. 10,
pages 89–90).
-/

namespace INet.Comb.CodeDataSidesCheck

open Term Translation CodeCellsMeetCheck CodeGammaMeetCheck RecursionFreeFig7Check

/-- **`sides_expand` for `con`–`dup`** (`α ≠ β`, pages 86 and 90): the two sides exist, share `k`
and `σ`, plug back `ruleConDup`, and feed `codeCells_meet_end` for `[con]` against `[dup]` on any
net whose linearity holds. -/
theorem sides_expand_conDup (xs : Fin 2 → ℕ) (ys : Fin 2 → ℕ)
    (f : Fin (codeNet sd Comb.con).internal → ℕ) (g : Fin (codeNet sd Comb.dup).internal → ℕ)
    (Δ : CNet)
    (hlin : Net.Linear (s((codeNet sd Comb.con).inst (fun i => var (xs i)) f,
      (codeNet sd Comb.dup).inst (fun j => var (ys j)) g) ::ₘ Δ)) :
    (∃ (k : ℕ) (φ : Rule sig 2 k) (ψ : Rule sig 2 k) (σ : Equiv.Perm (Fin k)),
      (⟨k, φ, ψ, σ⟩ : Decomposition sig 2 2).Plugs ruleConDup) ∧
    ∃ M : CNet, StepsE system (s((codeNet sd Comb.con).inst (fun i => var (xs i)) f,
      (codeNet sd Comb.dup).inst (fun j => var (ys j)) g) ::ₘ Δ) M := by
  obtain ⟨k, φ, ψ, σ, hσ, hl, he, hl', he', hs, hs', hP⟩ :=
    (System.WellFormed.decData system_wellFormed).sides_expand system_wellFormed
      (α := Comb.con) (β := Comb.dup) (r := ruleConDup) rfl
  obtain ⟨-, -, M, hM, -⟩ := codeCells_meet_end sd Comb.con Comb.dup xs ys f g Δ φ ψ σ hσ hl he
    hl' he' hs hs' hlin
  exact ⟨⟨k, φ, ψ, σ, hP⟩, M, hM⟩

/-- **`sides_expand` for `con`–`con`** (`α = β`, page 86, `φ_{i,i} = ψ_{i,i}`): the two sides
exist, share `k` and `σ`, plug back `ruleConCon`, and feed `codeCells_meet_end` for `[con]`
against `[con]` on any net whose linearity holds. -/
theorem sides_expand_conCon (xs : Fin 2 → ℕ) (ys : Fin 2 → ℕ)
    (f : Fin (codeNet sd Comb.con).internal → ℕ) (g : Fin (codeNet sd Comb.con).internal → ℕ)
    (Δ : CNet)
    (hlin : Net.Linear (s((codeNet sd Comb.con).inst (fun i => var (xs i)) f,
      (codeNet sd Comb.con).inst (fun j => var (ys j)) g) ::ₘ Δ)) :
    (∃ (k : ℕ) (φ : Rule sig 2 k) (ψ : Rule sig 2 k) (σ : Equiv.Perm (Fin k)),
      (⟨k, φ, ψ, σ⟩ : Decomposition sig 2 2).Plugs ruleConCon) ∧
    ∃ M : CNet, StepsE system (s((codeNet sd Comb.con).inst (fun i => var (xs i)) f,
      (codeNet sd Comb.con).inst (fun j => var (ys j)) g) ::ₘ Δ) M := by
  obtain ⟨k, φ, ψ, σ, hσ, hl, he, hl', he', hs, hs', hP⟩ :=
    (System.WellFormed.decData system_wellFormed).sides_expand system_wellFormed
      (α := Comb.con) (β := Comb.con) (r := ruleConCon) rfl
  obtain ⟨-, -, M, hM, -⟩ := codeCells_meet_end sd Comb.con Comb.con xs ys f g Δ φ ψ σ hσ hl he
    hl' he' hs hs' hlin
  exact ⟨⟨k, φ, ψ, σ, hP⟩, M, hM⟩

/-- **`sides_expand` for `dup`–`dup` with every hypothesis proved** (pages 86, 89–90): the sides
plug back `ruleDupDup`, and `codeCells_meet_end` applies to the concrete net `netDupDup`, whose
linearity is `linear_netDupDup`. -/
theorem sides_expand_dupDup :
    (∃ (k : ℕ) (φ : Rule sig 2 k) (ψ : Rule sig 2 k) (σ : Equiv.Perm (Fin k)),
      (⟨k, φ, ψ, σ⟩ : Decomposition sig 2 2).Plugs ruleDupDup) ∧
    ∃ M : CNet, StepsE system netDupDup M := by
  obtain ⟨k, φ, ψ, σ, hσ, hl, he, hl', he', hs, hs', hP⟩ :=
    (System.WellFormed.decData system_wellFormed).sides_expand system_wellFormed
      (α := Comb.dup) (β := Comb.dup) (r := ruleDupDup) rfl
  obtain ⟨-, -, M, hM, -⟩ := codeCells_meet_end sd Comb.dup Comb.dup zeroOne twoThree _ _ 0 φ ψ σ
    hσ hl he hl' he' hs hs' linear_netDupDup
  exact ⟨⟨k, φ, ψ, σ, hP⟩, M, hM⟩

end INet.Comb.CodeDataSidesCheck
