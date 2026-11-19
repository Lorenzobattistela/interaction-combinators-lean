import InteractionCombinators.Lafont.ExpandedIso
import InteractionCombinators.Lafont.DecompositionTools

/-!
# Every linear reduced rule has an expanded form

Part 2 of the symmetric decomposition of a rule `α`–`α` (Lafont 1997, page 86). A linear reduced
rule is written as trees rooted at the auxiliary ports, but a port may also be a leaf of a tree, or
two ports may be joined by an equation. Such a port `Q`, below the root `P` of an equation
`P = t`, is pulled out on a new wire `x`: the equation becomes `P = t[x/Q]` and `Q = x` is added.
The old net is obtained back by one wire substitution, so the two are `Equiv`.

* `Expand.card_le`: a linear reduced rule has at most `a + b` equations (one root port each).
* `Expand.step`: one port is pulled out; the rule stays linear and reduced and gains an equation.
* `Rule.exists_expanded`: every linear reduced rule is `Equiv`, up to an injective renaming of its
  internal wires, to a linear rule in expanded form.
-/

namespace INet

variable {S : Signature} {a b : ℕ}

open Term

namespace Expand

open ExpandedIso

/-- A linear reduced rule has at most `a + b` equations: each equation contains a port, and each
port occurs once (page 86). -/
theorem card_le (r : Rule S a b) (hl : r.Linear) (hr : r.Reduced) :
    Multiset.card r.net ≤ a + b := by
  classical
  have h1 : ∀ e ∈ r.net, 1 ≤ ∑ p, (eqVars e).count (port (n := r.internal) p) := by
    intro e he
    obtain ⟨q, t, rfl, hq⟩ := hr e he
    obtain ⟨p, rfl⟩ := exists_port hq
    calc 1 ≤ (eqVars s(var (port p), t)).count (port (n := r.internal) p) := by
          simp [eqVars_mk]
      _ ≤ _ := Finset.single_le_sum
          (f := fun p' => (eqVars s(var (port p), t)).count (port (n := r.internal) p'))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
  have h2 : Multiset.card r.net ≤
      (r.net.map fun e => ∑ p, (eqVars e).count (port (n := r.internal) p)).sum := by
    have : Multiset.card (r.net.map fun e => ∑ p, (eqVars e).count (port (n := r.internal) p)) • 1
        ≤ (r.net.map fun e => ∑ p, (eqVars e).count (port (n := r.internal) p)).sum :=
      Multiset.card_nsmul_le_sum fun x hx => by
        obtain ⟨e, he, rfl⟩ := Multiset.mem_map.1 hx
        exact h1 e he
    simpa using this
  have h3 : ∀ N : Net S (Fin a ⊕ Fin b ⊕ Fin r.internal),
      (N.map fun e => ∑ p, (eqVars e).count (port (n := r.internal) p)).sum =
        ∑ p : Fin a ⊕ Fin b, (Net.vars N).count (port p) := by
    intro N
    induction N using Multiset.induction_on with
    | empty => simp [Net.vars]
    | cons e N ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, Net.vars_cons]
      simp only [Multiset.count_add]
      rw [Finset.sum_add_distrib]
  rw [h3] at h2
  have h4 : ∑ p : Fin a ⊕ Fin b, r.net.vars.count (port p) = a + b := by
    simp [count_port (n := r.internal) (N := r.net) hl]
  omega

/-- A reduced rule that is not expanded has a port `Q` among the leaves of the tree of an equation
`P = t` rooted at a port `P`. -/
theorem exists_defect (r : Rule S a b) (hr : r.Reduced) (he : ¬ r.Expanded) :
    ∃ P Q t, s(var (port P), t) ∈ r.net ∧ port Q ∈ t.vars := by
  by_contra hno
  apply he
  intro e hmem
  obtain ⟨q, t, rfl, hq⟩ := hr e hmem
  obtain ⟨P, rfl⟩ := exists_port hq
  refine ⟨port P, t, rfl, hq, fun x hx => ?_⟩
  rcases x with i | j | w
  · exact (hno ⟨P, .inl i, t, hmem, hx⟩).elim
  · exact (hno ⟨P, .inr j, t, hmem, hx⟩).elim
  · exact ⟨w, rfl⟩

/-- The old internal wires, in the rule with one more internal wire. -/
def ρ {n : ℕ} : Fin a ⊕ Fin b ⊕ Fin n → Fin a ⊕ Fin b ⊕ Fin (n + 1) :=
  Sum.map id (Sum.map id Fin.castSucc)

/-- The new internal wire. -/
def X {n : ℕ} : Fin a ⊕ Fin b ⊕ Fin (n + 1) := .inr (.inr (Fin.last n))

/-- The renaming of a step: the port `Q` becomes the new wire, the rest is kept. -/
def σ {n : ℕ} (Q : Fin a ⊕ Fin b) (y : Fin a ⊕ Fin b ⊕ Fin n) : Fin a ⊕ Fin b ⊕ Fin (n + 1) :=
  if y = port Q then X else ρ y

theorem ρ_injective {n : ℕ} : Function.Injective (ρ (a := a) (b := b) (n := n)) :=
  Sum.map_injective.2 ⟨Function.injective_id,
    Sum.map_injective.2 ⟨Function.injective_id, Fin.castSucc_injective n⟩⟩

theorem ρ_ne_X {n : ℕ} (y : Fin a ⊕ Fin b ⊕ Fin n) : ρ y ≠ X := by
  rcases y with i | j | w
  · simp [ρ, X]
  · simp [ρ, X]
  · simp only [ρ, X, Sum.map_inr, ne_eq, Sum.inr.injEq]
    exact Fin.castSucc_ne_last w

theorem ρ_port {n : ℕ} (p : Fin a ⊕ Fin b) : ρ (port (n := n) p) = port p := by
  rcases p with i | j <;> rfl

theorem port_ne_X {n : ℕ} (p : Fin a ⊕ Fin b) : (port p : Fin a ⊕ Fin b ⊕ Fin (n + 1)) ≠ X :=
  port_ne_internal p _

theorem σ_injective {n : ℕ} (Q : Fin a ⊕ Fin b) :
    Function.Injective (σ (n := n) Q) := by
  intro y₁ y₂ h
  unfold σ at h
  by_cases h₁ : y₁ = port Q <;> by_cases h₂ : y₂ = port Q
  · rw [h₁, h₂]
  · simp only [h₁, h₂, ite_true, ite_false] at h; exact absurd h.symm (ρ_ne_X _)
  · simp only [h₁, h₂, ite_true, ite_false] at h; exact absurd h (ρ_ne_X _)
  · simp only [h₁, h₂, ite_false] at h; exact ρ_injective h

/-- The net of a step: the port `Q` is replaced by the new wire `x`, and `x = Q` is added. -/
def stepNet (r : Rule S a b) (Q : Fin a ⊕ Fin b) : Net S (Fin a ⊕ Fin b ⊕ Fin (r.internal + 1)) :=
  s(var X, var (port Q)) ::ₘ r.net.bind fun y => var (σ Q y)

theorem vars_stepNet (r : Rule S a b) (Q : Fin a ⊕ Fin b) :
    (stepNet r Q).vars = X ::ₘ port Q ::ₘ r.net.vars.map (σ Q) := by
  rw [stepNet, Net.vars_cons, Net.vars_bind_var]
  simp [eqVars_mk]

/-- The rule after one step. -/
def stepRule (r : Rule S a b) (Q : Fin a ⊕ Fin b) : Rule S a b := ⟨r.internal + 1, stepNet r Q⟩

theorem stepRule_linear (r : Rule S a b) (hl : r.Linear) (Q : Fin a ⊕ Fin b) :
    (stepRule r Q).Linear := by
  classical
  have hσ := σ_injective (n := r.internal) Q
  have hport : ∀ R : Fin a ⊕ Fin b,
      (stepNet r Q).vars.count (port R) = 1 := by
    intro R
    rw [vars_stepNet, Multiset.count_cons, Multiset.count_cons]
    by_cases hRQ : R = Q
    · subst hRQ
      have h0 : (r.net.vars.map (σ R)).count (port R) = 0 := by
        rw [Multiset.count_eq_zero]
        intro hm
        obtain ⟨z, -, hz⟩ := Multiset.mem_map.1 hm
        unfold σ at hz
        split_ifs at hz with hzQ
        · exact port_ne_X R hz.symm
        · rw [← ρ_port R] at hz
          exact hzQ (ρ_injective hz)
      simp [h0, port_ne_X R]
    · have hne : (port R : Fin a ⊕ Fin b ⊕ Fin r.internal) ≠ port Q :=
        fun h => hRQ (port_injective h)
      have hσR : σ (n := r.internal) Q (port R) = port R := by
        simp only [σ, hne, if_false, ρ_port]
      have hc := Multiset.count_map_eq_count' (σ Q) r.net.vars hσ (port R)
      rw [hσR] at hc
      rw [hc, count_port (n := r.internal) (N := r.net) hl R]
      have h1 : (port R : Fin a ⊕ Fin b ⊕ Fin (r.internal + 1)) ≠ port Q :=
        fun h => hRQ (port_injective h)
      simp [port_ne_X R, h1]
  refine ⟨fun i => hport (.inl i), fun j => hport (.inr j), fun w => ?_⟩
  show (stepNet r Q).vars.count (.inr (.inr w)) = 2
  rw [vars_stepNet, Multiset.count_cons, Multiset.count_cons]
  induction w using Fin.lastCases with
  | last =>
    have hc := Multiset.count_map_eq_count' (σ Q) r.net.vars hσ (port Q)
    have hσQ : σ (n := r.internal) Q (port Q) = X := by simp [σ]
    rw [hσQ] at hc
    have : (X : Fin a ⊕ Fin b ⊕ Fin (r.internal + 1)) = .inr (.inr (Fin.last _)) := rfl
    rw [← this, hc, count_port (n := r.internal) (N := r.net) hl Q]
    simp [Ne.symm (port_ne_X Q)]
  | cast w =>
    have hc := Multiset.count_map_eq_count' (σ Q) r.net.vars hσ (.inr (.inr w))
    have hσw : σ Q (.inr (.inr w) : Fin a ⊕ Fin b ⊕ Fin r.internal) = .inr (.inr w.castSucc) := by
      simp only [σ, ρ]
      rw [if_neg (fun h => port_ne_internal Q w h.symm)]
      rfl
    rw [hσw] at hc
    rw [hc, hl.internal w]
    have h1 : (.inr (.inr w.castSucc) : Fin a ⊕ Fin b ⊕ Fin (r.internal + 1)) ≠ X := by
      simp only [X, ne_eq, Sum.inr.injEq]
      exact Fin.castSucc_ne_last w
    have h2 : (.inr (.inr w.castSucc) : Fin a ⊕ Fin b ⊕ Fin (r.internal + 1)) ≠ port Q :=
      fun h => port_ne_internal Q _ h.symm
    simp [h1, h2]

theorem stepRule_reduced (r : Rule S a b) (hl : r.Linear) (hr : r.Reduced)
    {P Q : Fin a ⊕ Fin b} {t : Term S (Fin a ⊕ Fin b ⊕ Fin r.internal)}
    (hmem : s(var (port P), t) ∈ r.net) (hQ : port Q ∈ t.vars) : (stepRule r Q).Reduced := by
  classical
  have hPQ : P ≠ Q := by
    rintro rfl
    have hle : (eqVars s(var (port P), t)).count (port P) ≤ r.net.vars.count (port P) :=
      Multiset.count_le_of_le _ (Multiset.le_bind _ hmem)
    have := count_port (n := r.internal) (N := r.net) hl P
    simp only [eqVars_mk, vars_var, Multiset.count_add, Multiset.count_singleton_self] at hle
    have := Multiset.one_le_count_iff_mem.2 hQ
    omega
  intro e he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨port Q, var X, Sym2.eq_swap, port_ne_internal Q⟩
  obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.1 he
  obtain ⟨q, t₀, rfl, hq⟩ := hr e₀ he₀
  obtain ⟨p, rfl⟩ := exists_port hq
  by_cases hpQ : p = Q
  · subst hpQ
    have hee := eq_of_mem_of_count_one hmem he₀ (x := port p)
      (by simp [eqVars_mk]; exact Or.inr hQ) (by simp [eqVars_mk])
      (count_port (n := r.internal) (N := r.net) hl p)
    rw [← hee]
    refine ⟨port P, t.bind fun y => var (σ p y), ?_, port_ne_internal P⟩
    show s((var (port P)).bind _, t.bind _) = _
    have hσP : σ (n := r.internal) p (port P) = port P := by
      rw [σ, if_neg (fun h => hPQ (port_injective h)), ρ_port]
    rw [bind_var, hσP]
    rfl
  · refine ⟨port p, t₀.bind fun y => var (σ Q y), ?_, port_ne_internal p⟩
    show s((var (port p)).bind _, t₀.bind _) = _
    have hσp : σ (n := r.internal) Q (port p) = port p := by
      rw [σ, if_neg (fun h => hpQ (port_injective h)), ρ_port]
    rw [bind_var, hσp]
    rfl

theorem card_stepRule (r : Rule S a b) (Q : Fin a ⊕ Fin b) :
    Multiset.card (stepRule r Q).net = Multiset.card r.net + 1 := by
  show Multiset.card (stepNet r Q) = _
  simp [stepNet, Net.bind]

/-- The old net, with its internal wires renamed into the new rule, is obtained from the new net by
one wire substitution: `x := Q`. -/
theorem stepRule_equiv (r : Rule S a b) (hl : r.Linear) (Q : Fin a ⊕ Fin b) :
    Equiv (stepRule r Q).net (r.net.bind fun y => var (ρ y)) := by
  classical
  have hlin : Net.Linear (stepNet r Q) := fun y => by
    have h := stepRule_linear r hl Q
    rcases y with i | j | w
    · exact (h.left i).le.trans (by omega)
    · exact (h.right j).le.trans (by omega)
    · exact (h.internal w).le
  have hX : X ∈ Net.vars (r.net.bind fun y => var (σ (n := r.internal) Q y)) := by
    rw [Net.vars_bind_var]
    refine Multiset.mem_map.2 ⟨port Q, ?_, by simp [σ]⟩
    exact Multiset.one_le_count_iff_mem.1 (count_port (n := r.internal) (N := r.net) hl Q).ge
  have hw := Net.wire_var hlin hX
  refine hw.equiv.trans (Equiv.of_eq ?_)
  rw [Net.bind_bind]
  refine Net.bind_congr fun y _ => ?_
  rw [bind_var]
  by_cases h1 : y = port Q
  · subst h1
    have hσQ : σ (n := r.internal) Q (port Q) = X := if_pos rfl
    rw [hσQ, if_pos rfl, ρ_port]
    rfl
  · have hσy : σ (n := r.internal) Q y = ρ y := if_neg h1
    rw [hσy, if_neg (ρ_ne_X y)]
    rfl

end Expand

open Expand in
/-- **Expanded form** (page 86). Every linear reduced rule is `Equiv` to a linear rule in expanded
form, up to an injective renaming `ι` of its internal wires: the expanded rule has extra internal
wires, one for each port that was a leaf of a tree or joined to another port. -/
theorem Rule.exists_expanded {a b : ℕ} (r : Rule S a b) (hl : r.Linear) (hr : r.Reduced) :
    ∃ (r' : Rule S a b) (ι : Fin r.internal → Fin r'.internal), Function.Injective ι ∧
      r'.Linear ∧ r'.Expanded ∧
      Equiv r'.net (r.net.bind fun x => Term.var (Sum.map id (Sum.map id ι) x)) := by
  classical
  suffices H : ∀ k (r : Rule S a b), r.Linear → r.Reduced → a + b ≤ Multiset.card r.net + k →
      ∃ (r' : Rule S a b) (ι : Fin r.internal → Fin r'.internal), Function.Injective ι ∧
        r'.Linear ∧ r'.Expanded ∧
        Equiv r'.net (r.net.bind fun x => Term.var (Sum.map id (Sum.map id ι) x)) from
    H (a + b) r hl hr (by omega)
  intro k
  induction k with
  | zero =>
    intro r hl hr hk
    by_cases he : r.Expanded
    · refine ⟨r, id, Function.injective_id, hl, he, Equiv.of_eq ?_⟩
      rw [Net.bind_congr (g := var) fun x _ => by simp]
      exact (Net.bind_var_self _).symm
    · obtain ⟨P, Q, t, hmem, hQ⟩ := exists_defect r hr he
      have := card_le _ (stepRule_linear r hl Q) (stepRule_reduced r hl hr hmem hQ)
      rw [card_stepRule] at this
      omega
  | succ k ih =>
    intro r hl hr hk
    by_cases he : r.Expanded
    · refine ⟨r, id, Function.injective_id, hl, he, Equiv.of_eq ?_⟩
      rw [Net.bind_congr (g := var) fun x _ => by simp]
      exact (Net.bind_var_self _).symm
    · obtain ⟨P, Q, t, hmem, hQ⟩ := exists_defect r hr he
      obtain ⟨r', ι, hι, hl', he', heq⟩ := ih (stepRule r Q) (stepRule_linear r hl Q)
        (stepRule_reduced r hl hr hmem hQ) (by rw [card_stepRule]; omega)
      refine ⟨r', ι ∘ Fin.castSucc, hι.comp (Fin.castSucc_injective _), hl', he', ?_⟩
      have h2 := Equiv.bind_var (Sum.map id (Sum.map id ι))
        (Sum.map_injective.2 ⟨Function.injective_id,
          Sum.map_injective.2 ⟨Function.injective_id, hι⟩⟩) (stepRule_equiv r hl Q)
      refine heq.trans (h2.trans (Equiv.of_eq ?_))
      rw [Net.bind_bind]
      refine Net.bind_congr fun x _ => ?_
      rcases x with i | j | w <;> rfl

end INet
