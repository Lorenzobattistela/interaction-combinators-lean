import InteractionCombinators.EquivAdd
import InteractionCombinators.RenameStep
import InteractionCombinators.WantedCheck

/-!
# Reduction up to wires inside a larger net

Reduction is defined on graphs and is local: an interaction replaces an active pair and leaves
the rest of the net untouched (Lafont 1997, Section 1.3, pages 71 to 73). In the text
presentation, a reduction `StepsE I N M` can be done beside a context `Γ` (`StepsE.add_right`).

The wires created by a rule, and the intermediate names of a wire substitution, may clash with
the names of `Γ`. Each step is therefore renamed first, by an injective `f` that fixes the names
of the starting net and sends every other name above all the names of the net and of `Γ`. The
result is the renamed net, which is `M` up to equivalence (`Net.equiv_bind_var`).
-/

namespace INet

variable {S : Signature}

open Term

/-- One interaction keeps every name except the wires it creates, which were unused and occur
twice afterwards (Lafont 1997, Section 1.3, page 72: the right-hand side of a rule replaces the
active pair, its internal wires are new). -/
theorem Step.count_vars {I : System S} (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    {N M : Net S ℕ} (h : Step I N M) (y : ℕ) :
    M.vars.count y = N.vars.count y ∨ (N.vars.count y = 0 ∧ M.vars.count y = 2) := by
  obtain ⟨α, β, r, hr, as, bs, Δ, f, hf, hfresh⟩ := h
  simp only [Net.vars_cons, Net.vars_add, eqVars_mk, Term.vars_app, Multiset.count_add,
    Multiset.count_sum']
  rw [Rule.count_vars_inst r (hI _ _ _ hr)]
  by_cases hex : ∃ w, y = f w
  · obtain ⟨w0, rfl⟩ := hex
    have hsum : ∑ w, (if f w0 = f w then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single w0]
      · simp
      · intro w _ hw
        exact ite_eq_right fun h => hw (hf h).symm
      · simp
    have h0 := Multiset.count_eq_zero_of_notMem (hfresh w0)
    simp only [Net.vars_cons, eqVars_mk, Term.vars_app, Multiset.count_add,
      Multiset.count_sum'] at h0
    right
    omega
  · have hsum : ∑ w, (if y = f w then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun w _ => ite_eq_right fun h => hex ⟨w, h⟩
    left
    omega

/-- One interaction keeps the free ports (Lafont 1997, Section 1.3, page 72: the interface of
the active pair is the interface of the right-hand side). -/
theorem Step.free_iff {I : System S} (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    {N M : Net S ℕ} (h : Step I N M) (y : ℕ) :
    M.vars.count y = 1 ↔ N.vars.count y = 1 := by
  rcases h.count_vars hI y with h | h <;> omega

/-- A renaming `f`, injective, fixing the names of `N₀` and sending the other names out of `Γ`,
places beside `Γ` every linear net with the free ports of `N₀`, when `N₀ + Γ` is linear
(Lafont 1997, Section 1.2, page 71: `Γ` is plugged only into free ports). -/
theorem Net.Linear.bind_var_add_right {N₀ Γ K : Net S ℕ} (f : ℕ → ℕ)
    (hf : Function.Injective f) (hN₀ : (N₀ + Γ).Linear) (hfix : ∀ x ∈ N₀.vars, f x = x)
    (hout : ∀ x, x ∉ N₀.vars → f x ∉ Γ.vars) (hK : K.Linear)
    (hKf : ∀ y, K.vars.count y = 1 ↔ N₀.vars.count y = 1) :
    ((K.bind fun y => var (f y)) + Γ).Linear := by
  intro z
  have hNz := hN₀ z
  rw [Net.vars_add, Multiset.count_add] at hNz ⊢
  rw [Net.vars_bind_var]
  by_cases hz : ∃ x, f x = z
  · obtain ⟨x, rfl⟩ := hz
    rw [Multiset.count_map_eq_count' f _ hf x]
    by_cases hx : x ∈ N₀.vars
    · rw [hfix x hx] at hNz ⊢
      have hKx := hK x
      have hKfx := hKf x
      have := Multiset.one_le_count_iff_mem.2 hx
      omega
    · rw [Multiset.count_eq_zero_of_notMem (hout x hx)]
      simpa using hK x
  · have hm : z ∉ K.vars.map f := fun hm => by
      obtain ⟨x, -, hx⟩ := Multiset.mem_map.1 hm
      exact hz ⟨x, hx⟩
    rw [Multiset.count_eq_zero_of_notMem hm]
    omega

/-- **One interaction up to wires, inside a larger net.** If `N` reduces to `M` by one `StepE`
and `N + Γ` is linear, then `N + Γ` reduces by one `StepE` to `M' + Γ`, where `M'` is `M` with
its internal wires renamed away from the names of `Γ` (Lafont 1997, Section 1.3, pages 72 to
73: reduction is local, and the names of wires do not matter). -/
theorem StepE.add_right {I : System S} (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    {N M : Net S ℕ} (Γ : Net S ℕ) (h : StepE I N M) (hN : (N + Γ).Linear) :
    ∃ M', StepE I (N + Γ) (M' + Γ) ∧ Equiv M' M ∧ (M' + Γ).Linear := by
  obtain ⟨N', hE, hS⟩ := h
  have hNl : N.Linear := fun y => by
    have := hN y
    rw [Net.vars_add, Multiset.count_add] at this
    omega
  have hN'l : N'.Linear := hE.linear hNl
  have hMl : M.Linear := hS.linear hI hN'l
  -- a bound on the names of `N` and `Γ`
  set B := (N.vars + Γ.vars).sup + 1 with hB
  have hlt : ∀ x ∈ N.vars + Γ.vars, x < B := fun x hx =>
    Nat.lt_succ_of_le (Multiset.le_sup hx)
  have hltN : ∀ x ∈ N.vars, x < B := fun x hx => hlt x (by simp [hx])
  have hltΓ : ∀ x ∈ Γ.vars, x < B := fun x hx => hlt x (by simp [hx])
  -- fix the names of `N`, send the others above `B`
  let f : ℕ → ℕ := fun x => if x ∈ N.vars then x else x + B
  have hfV : ∀ x ∈ N.vars, f x = x := fun x hx => by simp [f, hx]
  have hfO : ∀ x, x ∉ N.vars → f x = x + B := fun x hx => by simp [f, hx]
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : x ∈ N.vars <;> by_cases hy : y ∈ N.vars
    · rwa [hfV x hx, hfV y hy] at hxy
    · rw [hfV x hx, hfO y hy] at hxy
      have := hltN x hx
      omega
    · rw [hfO x hx, hfV y hy] at hxy
      have := hltN y hy
      omega
    · rw [hfO x hx, hfO y hy] at hxy
      omega
  have hout : ∀ x, x ∉ N.vars → f x ∉ Γ.vars := fun x hx hm => by
    have := hltΓ _ hm
    rw [hfO x hx] at this
    omega
  have hfixN : (N.bind fun y => var (f y)) = N := by
    rw [Net.bind_congr (g := var) fun x hx => by rw [hfV x hx]]
    exact Net.bind_var_self N
  have hgood : ∀ K : Net S ℕ, K.Linear → (∀ y, K.vars.count y = 1 ↔ N.vars.count y = 1) →
      ((K.bind fun y => var (f y)) + Γ).Linear := fun K hK hKf =>
    Net.Linear.bind_var_add_right f hf hN hfV hout hK hKf
  have hMf : ∀ y, M.vars.count y = 1 ↔ N.vars.count y = 1 := fun y =>
    (hS.free_iff hI y).trans (hE.free_iff y).symm
  have hM'Γ := hgood M hMl hMf
  -- the equivalence, beside `Γ`
  have E := Equiv.bind_var_add_right f hf Γ hgood hE hNl fun _ => Iff.rfl
  rw [hfixN] at E
  -- the interaction, beside `Γ`
  have S' := (hS.bind_var f hf).add_right hI Γ hM'Γ
  refine ⟨M.bind fun y => var (f y), ⟨_, E, S'⟩, ?_, hM'Γ⟩
  -- the renaming moves only internal wires of `M`
  refine (Net.equiv_bind_var hMl f hf.injOn fun x hx => hfV x ?_).symm
  exact Multiset.one_le_count_iff_mem.1 (by have := (hMf x).1 hx; omega)

/-- An equivalence followed by one interaction up to wires is one interaction up to wires. -/
theorem StepE.of_equiv {I : System S} {N K M : Net S ℕ} (hE : Equiv N K) (h : StepE I K M) :
    StepE I N M := by
  obtain ⟨K', hK, hS⟩ := h
  exact ⟨K', hE.trans hK, hS⟩

/-- **Reduction up to wires inside a larger net.** If `N` reduces to `M` (`StepsE`) and `N + Γ`
is linear, then `N + Γ` reduces to `M' + Γ`, where `M'` is equivalent to `M`: the wires created
along the way are given names that avoid those of `Γ`. Reduction is local and defined on graphs
(Lafont 1997, Section 1.3, pages 72 to 73), so it can be done inside any context. -/
theorem StepsE.add_right {I : System S} (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    {N M : Net S ℕ} (Γ : Net S ℕ) (h : StepsE I N M) (hN : (N + Γ).Linear) :
    ∃ M', StepsE I (N + Γ) (M' + Γ) ∧ Equiv M' M ∧ (M' + Γ).Linear := by
  induction h with
  | refl => exact ⟨N, Relation.ReflTransGen.refl, Equiv.refl N, hN⟩
  | tail _ hstep ih =>
    obtain ⟨M₁, hs, hE, hl⟩ := ih
    obtain ⟨M₂, hs₂, hE₂, hl₂⟩ := (StepE.of_equiv hE hstep).add_right hI Γ hl
    exact ⟨M₂, hs.tail hs₂, hE₂, hl₂⟩

section Example

open Comb

/-- Non-vacuity: two `con` cells annihilate beside a context `Γ` that plugs an `era` cell into
the free port `0` of the active pair. -/
example : ∃ M', StepsE system
    (({s(mkCon (var 0) (var 1), mkCon (var 2) (var 3))} : CNet) + {s(var 0, mkEra)})
    (M' + {s(var 0, mkEra)}) ∧
    Equiv M' {s(var 0, var 3), s(var 1, var 2)} ∧ (M' + {s(var 0, mkEra)}).Linear := by
  refine StepsE.add_right system_wellFormed.linear _ ?_ ?_
  · have h := step_con_con (var 0) (var 1) (var 2) (var 3) 0
    simpa [Multiset.insert_eq_cons] using (Steps.single h).stepsE
  · intro y
    simp only [Multiset.singleton_add, Net.vars_cons, Net.vars_singleton, eqVars_mk,
      vars_mkCon, vars_mkEra, vars_var, Multiset.count_add, Multiset.count_singleton,
      Multiset.count_cons, Multiset.count_zero]
    split_ifs <;> omega

/-- Non-vacuity where renaming is necessary: the interaction of `con` and `dup` in
`WantedCheck.cut` creates a wire named `4`, which the context `WantedCheck.ctx` uses, so
`cutResult + ctx` is not linear (`WantedCheck.stepsE_add_right_must_rename`). The reduction is
still done beside `ctx`, to a renamed copy of `cutResult`. -/
example : ∃ M', StepsE system (WantedCheck.cut + WantedCheck.ctx) (M' + WantedCheck.ctx) ∧
    Equiv M' WantedCheck.cutResult ∧ (M' + WantedCheck.ctx).Linear ∧
    ¬ (WantedCheck.cutResult + WantedCheck.ctx).Linear :=
  have h := WantedCheck.stepsE_add_right_must_rename
  have ⟨M', hs, hE, hl⟩ := StepsE.add_right system_wellFormed.linear _ h.1 h.2.1
  ⟨M', hs, hE, hl, h.2.2⟩

end Example

end INet
