import InteractionCombinators.Reduced.RuleReduced
import InteractionCombinators.Core.Combinators
import InteractionCombinators.Universality.RecursionFree.DecompositionLemmas

/-!
# Check of `InteractionCombinators/Reduced/RuleReduced.lean`

Lafont 1997, page 79 (reduced nets) and page 72 (right members are reduced).

* The hypotheses of both theorems hold for the `con`–`dup` rule of `Comb.system`, with the names
  `0, 1` on the ports of `con`, `2, 3` on those of `dup` and `4, 5, 6, 7` on the new wires
  (`conDup_isReduced`, `conDup_rewritten`).
* A rule `bad` with one internal wire `w`, `w = con(l₀, r₀), r₁ = dup(w, era)`, is linear but not
  in the syntactic form `Rule.Reduced` (`bad_not_reduced`): its first equation has no auxiliary
  port on either side. Its instance `4 = con(0, 1), 2 = dup(4, era)` is nevertheless reduced, one
  wire substitution from `2 = dup(con(0, 1), era)` (`badInst_isReduced`). So the converse
  `Rule.exists_reduced_of_isReduced` applies to a rule that is not in the form (`bad_rewritten`):
  it is not vacuous, and the form is narrower than "reduced" before the rule is rewritten.
-/

namespace INet.RuleReducedCheck

open Comb Term

/-- A net over `ℕ` is linear if its names that occur occur at most twice; this form is
decidable. -/
theorem linear_of_mem {N : Net sig ℕ} (h : ∀ x ∈ N.vars, N.vars.count x ≤ 2) : N.Linear := by
  intro x
  by_cases hx : x ∈ N.vars
  · exact h x hx
  · rw [Multiset.count_eq_zero.2 hx]; omega

/-! ## The `con`–`dup` rule -/

/-- The names on the ports of `con`. -/
def xs : Fin 2 → ℕ := ![0, 1]
/-- The names on the ports of `dup`. -/
def ys : Fin 2 → ℕ := ![2, 3]
/-- The names of the four new wires. -/
def hw : Fin ruleConDup.internal → ℕ := fun w => 4 + w.1

theorem xs_inj : Function.Injective xs := by unfold xs; decide
theorem ys_inj : Function.Injective ys := by unfold ys; decide
theorem xs_ne_ys : ∀ i j, xs i ≠ ys j := by unfold xs ys; decide

/-- The instance of the `con`–`dup` rule is
`0 = dup(4, 5), 1 = dup(6, 7), 2 = con(4, 6), 3 = con(5, 7)`. -/
theorem conDup_inst :
    ruleConDup.inst (fun i => var (xs i)) (fun j => var (ys j)) hw =
      s(var 0, mkDup (var 4) (var 5)) ::ₘ s(var 1, mkDup (var 6) (var 7)) ::ₘ
        s(var 2, mkCon (var 4) (var 6)) ::ₘ s(var 3, mkCon (var 5) (var 7)) ::ₘ 0 := by
  decide

theorem conDup_linear :
    (ruleConDup.inst (fun i => var (xs i)) (fun j => var (ys j)) hw).Linear := by
  rw [conDup_inst]; exact linear_of_mem (by decide)

/-- The forward theorem applies to the `con`–`dup` rule (page 79): its instance is reduced. -/
theorem conDup_isReduced :
    (ruleConDup.inst (fun i => var (xs i)) (fun j => var (ys j)) hw).IsReduced :=
  ruleConDup_reduced.isReduced_inst ruleConDup_linear xs_inj ys_inj xs_ne_ys conDup_linear

/-- The converse applies to the `con`–`dup` rule too. -/
theorem conDup_rewritten : ∃ (r' : Rule sig 2 2) (h' : Fin r'.internal → ℕ), r'.Linear ∧
    r'.Reduced ∧ Function.Injective h' ∧
    Equiv (ruleConDup.inst (fun i => var (xs i)) (fun j => var (ys j)) hw)
      (r'.inst (fun i => var (xs i)) (fun j => var (ys j)) h') :=
  Rule.exists_reduced_of_isReduced ruleConDup_linear xs_inj ys_inj xs_ne_ys conDup_linear
    conDup_isReduced

/-! ## A rule that is not in the syntactic form -/

/-- `w = con(l₀, r₀), r₁ = dup(w, era)`: one port on the first cell, two on the second, one
internal wire `w`. -/
def bad : Rule sig 1 2 :=
  ⟨1, s(var (.inr (.inr 0)), mkCon (var (.inl 0)) (var (.inr (.inl 0)))) ::ₘ
    s(var (.inr (.inl 1)), mkDup (var (.inr (.inr 0))) mkEra) ::ₘ 0⟩

theorem bad_linear : bad.Linear := by
  refine ⟨fun i => ?_, fun j => ?_, fun w => ?_⟩
  · change Multiset.count _ (Net.vars (show Net sig (Fin 1 ⊕ Fin 2 ⊕ Fin 1) from bad.net)) = 1
    revert i; decide
  · change Multiset.count _ (Net.vars (show Net sig (Fin 1 ⊕ Fin 2 ⊕ Fin 1) from bad.net)) = 1
    revert j; decide
  · change Multiset.count _ (Net.vars (show Net sig (Fin 1 ⊕ Fin 2 ⊕ Fin 1) from bad.net)) = 2
    revert w; decide

/-- `bad` is not in the form `Rule.Reduced`: the equation `w = con(l₀, r₀)` has no auxiliary port
on either side. -/
theorem bad_not_reduced : ¬ bad.Reduced := by
  intro h
  unfold Rule.Reduced bad at h
  dsimp only at h
  obtain ⟨p, t, he, hp⟩ := h _ (Multiset.mem_cons_self _ _)
  rcases Sym2.eq_iff.1 he with ⟨hv, -⟩ | ⟨-, hv⟩
  · injection hv with hv
    exact hp 0 hv.symm
  · cases hv

/-- The names on the ports of the second cell of `bad`. -/
def ys' : Fin 2 → ℕ := ![1, 2]
/-- The name of the internal wire of `bad`. -/
def hw' : Fin bad.internal → ℕ := fun _ => 4

theorem xs0_inj : Function.Injective (![0] : Fin 1 → ℕ) := by decide
theorem ys'_inj : Function.Injective ys' := by unfold ys'; decide
theorem xs0_ne_ys' : ∀ i j, (![0] : Fin 1 → ℕ) i ≠ ys' j := by unfold ys'; decide

/-- The instance of `bad` is `4 = con(0, 1), 2 = dup(4, era)`. -/
theorem bad_inst : bad.inst (fun i => var ((![0] : Fin 1 → ℕ) i)) (fun j => var (ys' j)) hw' =
    s(var 4, mkCon (var 0) (var 1)) ::ₘ s(var 2, mkDup (var 4) mkEra) ::ₘ 0 := by
  decide

theorem badInst_linear :
    (bad.inst (fun i => var ((![0] : Fin 1 → ℕ) i)) (fun j => var (ys' j)) hw').Linear := by
  rw [bad_inst]; exact linear_of_mem (by decide)

/-- The instance of `bad` is reduced: one wire substitution gives `2 = dup(con(0, 1), era)`,
which is trees on a wiring. -/
theorem badInst_isReduced :
    (bad.inst (fun i => var ((![0] : Fin 1 → ℕ) i)) (fun j => var (ys' j)) hw').IsReduced := by
  rw [bad_inst]
  have hl : Net.Linear (s(var 4, mkCon (var 0) (var 1)) ::ₘ
      s(var 2, mkDup (var 4) mkEra) ::ₘ (0 : Net sig ℕ)) := linear_of_mem (by decide)
  have hW : Wire (s(var 4, mkCon (var 0) (var 1)) ::ₘ s(var 2, mkDup (var 4) mkEra) ::ₘ 0)
      (s(var 2, mkDup (mkCon (var 0) (var 1)) mkEra) ::ₘ (0 : Net sig ℕ)) :=
    Wire.cast (Wire.mk 4 (mkCon (var 0) (var 1)) (var 2) (mkDup (var 4) mkEra) 0 hl
      (by decide)) rfl (by decide)
  have hT : Net.IsTreesOnWiring
      (s(var 2, mkDup (mkCon (var 0) (var 1)) mkEra) ::ₘ (0 : Net sig ℕ)) := by
    intro e he
    rw [Multiset.mem_cons, or_iff_left (Multiset.notMem_zero _)] at he
    exact ⟨2, _, he, by decide⟩
  exact hT.isReduced.of_equiv hW.equiv.symm

/-- The converse applies to `bad`, which is not in the form: some rule in the form has the same
instance up to wires. -/
theorem bad_rewritten : ∃ (r' : Rule sig 1 2) (h' : Fin r'.internal → ℕ), r'.Linear ∧
    r'.Reduced ∧ Function.Injective h' ∧
    Equiv (bad.inst (fun i => var ((![0] : Fin 1 → ℕ) i)) (fun j => var (ys' j)) hw')
      (r'.inst (fun i => var ((![0] : Fin 1 → ℕ) i)) (fun j => var (ys' j)) h') :=
  Rule.exists_reduced_of_isReduced bad_linear xs0_inj ys'_inj xs0_ne_ys' badInst_linear
    badInst_isReduced

end INet.RuleReducedCheck
