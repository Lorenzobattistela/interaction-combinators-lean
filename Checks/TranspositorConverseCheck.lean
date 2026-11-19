import InteractionCombinators.Lafont.TranspositorConverse
import InteractionCombinators.Lafont.CodeTr
import InteractionCombinators.Lafont.RecursionFreeFig7

/-!
# Checks of `Lafont/TranspositorConverse.lean` (page 84)

`involutive_of_transpositor` says: if two copies of a principal net `p`, plugged by their roots,
reduce up to wires to the wiring σ, then σ is involutive (Lafont 1997, page 84).

* `hyp_transpositorPerm` — the hypotheses are not vacuous: for every involutive σ, the transpositor
  `T_σ` of `TranspositorPerm.lean`, read as a principal net by `treePNet`, satisfies them (from
  `transpositorPerm_transpositorPerm`, via `Steps.stepsE`). `involutive_of_transpositorPerm`
  applies the theorem to it.
* `no_transpositor_finRotate` — the 3-cycle on `Fin 3` is not involutive, so no principal net
  over the combinators is a `T_σ` for it, whatever the names of its internal wires.
-/

namespace INet.Comb.TranspositorConverseCheck

open Term TranspositorConverse

/-- Two copies of `p` plugged by their roots, the ports of the first named `0, …, n - 1`, those of
the second `n, …, 2n - 1` (page 84). -/
def copies {n : ℕ} (p : PNet sig n) (f g : Fin p.internal → ℕ) : CNet :=
  s(p.inst (fun i => var (i : ℕ)) f, p.inst (fun i => var (n + (i : ℕ))) g) ::ₘ 0

/-- The hypothesis of `involutive_of_transpositor` for the combinators: `p` is a `T_σ`. -/
def IsTranspositor {n : ℕ} (σ : _root_.Equiv.Perm (Fin n)) (p : PNet sig n)
    (f g : Fin p.internal → ℕ) : Prop :=
  Net.Linear (copies p f g) ∧ ∃ M, StepsE system (copies p f g) M ∧
    INet.Equiv M (Finset.univ.val.map fun i : Fin n => s(var (i : ℕ), var (n + (σ i : ℕ))))

/-! ## The hypotheses hold for `T_σ` -/

variable {n : ℕ} (σ : _root_.Equiv.Perm (Fin n)) (hσ : Function.Involutive σ)

/-- The names of `T_σ` with the port `i` named `k + i` (page 84): each of `k, …, k + n - 1` once. -/
theorem count_vars_transpositorPerm (k z : ℕ) :
    (transpositorPerm σ hσ fun i => var (k + (i : ℕ))).vars.count z =
      if k ≤ z ∧ z < k + n then 1 else 0 := by
  rw [vars_transpositorPerm, Multiset.count_bind]
  change ∑ i : Fin n, _ = _
  simp only [Term.vars_var, Multiset.count_singleton]
  exact sum_ite_add k z

/-- `T_σ` with the port `i` named `i`. -/
abbrev tσ : Term sig ℕ := transpositorPerm σ hσ fun i => var (i : ℕ)

/-- The names of `T_σ` with the port `i` named `i` (page 84): each of `0, …, n - 1` once. -/
theorem count_vars_tσ (z : ℕ) : (tσ σ hσ).vars.count z = if z < n then 1 else 0 := by
  have h := count_vars_transpositorPerm σ hσ 0 z
  simp only [zero_add, Nat.zero_le, true_and] at h
  exact h

/-- Each port of `T_σ` occurs once (page 80, a principal net). -/
theorem tσ_port : ∀ i < n, (tσ σ hσ).vars.count i = 1 := fun i hi => by
  simp [count_vars_tσ, hi]

/-- `T_σ` has no name `≥ n`, so the condition on internal wires (page 80) holds. -/
theorem tσ_wire : ∀ x ∈ (tσ σ hσ).vars, n ≤ x → (tσ σ hσ).vars.count x = 2 := by
  intro x hx hn
  have h := Multiset.count_pos.2 hx
  rw [count_vars_tσ] at h
  split_ifs at h <;> omega

/-- `T_σ` as a principal net (page 80): its names `< n` are its ports; it has no other name. -/
def pσ : PNet sig n := treePNet n (tσ σ hσ) (tσ_port σ hσ) (tσ_wire σ hσ)

/-- The names of the internal wires of the first copy. -/
def fσ : Fin (pσ σ hσ).internal → ℕ := fun w => ((wireNum n (tσ σ hσ)).symm w).1

/-- The first copy of `pσ` is `T_σ` (page 80, `treePNet_inst`). -/
theorem inst_pσ : (pσ σ hσ).inst (fun i => var (i : ℕ)) (fσ σ hσ) = tσ σ hσ :=
  treePNet_inst _ _ _ _

/-- The second copy of `pσ`, ports and internal wires shifted by `n`, is `T_σ` on `n, …, 2n - 1`. -/
theorem inst_pσ_shift :
    (pσ σ hσ).inst (fun i => var (n + (i : ℕ))) (fun w => n + fσ σ hσ w) =
      transpositorPerm σ hσ fun i => var (n + (i : ℕ)) := by
  have h := inst_bind_var (pσ σ hσ) (fun i => (i : ℕ)) (fσ σ hσ) (fun y => n + y)
  rw [inst_pσ, bind_transpositorPerm] at h
  exact h.symm

/-- **The hypotheses of `involutive_of_transpositor` hold for `T_σ`** (page 84): for an involutive
σ, two copies of `T_σ` form a linear net that reduces to the wiring σ. -/
theorem hyp_transpositorPerm :
    IsTranspositor σ (pσ σ hσ) (fσ σ hσ) (fun w => n + fσ σ hσ w) := by
  unfold IsTranspositor copies
  rw [inst_pσ, inst_pσ_shift]
  refine ⟨fun z => ?_, _, (transpositorPerm_transpositorPerm σ hσ _ _ 0).stepsE, ?_⟩
  · simp only [Net.vars_cons, eqVars_mk, Net.vars_zero, add_zero, Multiset.count_add]
    rw [count_vars_tσ, count_vars_transpositorPerm]
    split_ifs <;> omega
  · rw [add_zero]
    exact INet.Equiv.refl _

include hσ in
/-- The theorem applied to `T_σ` gives back that σ is involutive. -/
theorem involutive_of_transpositorPerm : Function.Involutive σ :=
  let h := hyp_transpositorPerm σ hσ
  involutive_of_transpositor system_wellFormed _ σ _ _ h.1 h.2

/-! ## No `T_σ` for a 3-cycle -/

/-- The 3-cycle `0 → 1 → 2 → 0` is not involutive. -/
theorem not_involutive_finRotate : ¬ Function.Involutive (finRotate 3) := by
  unfold Function.Involutive
  decide

/-- **There is no transpositor for a 3-cycle** (page 84). For σ the 3-cycle `0 → 1 → 2 → 0`, no
principal net `p` over the combinators, with any names of its internal wires, makes two copies
plugged by their roots reduce up to wires to the wiring σ. -/
theorem no_transpositor_finRotate (p : PNet sig 3) (f g : Fin p.internal → ℕ) :
    ¬ IsTranspositor (finRotate 3) p f g := fun h =>
  not_involutive_finRotate (involutive_of_transpositor system_wellFormed p _ f g h.1 h.2)

end INet.Comb.TranspositorConverseCheck
