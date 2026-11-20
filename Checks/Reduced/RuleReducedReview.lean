import InteractionCombinators.Reduced.RuleReduced
import InteractionCombinators.Core.Combinators
import InteractionCombinators.Universality.RecursionFree.DecompositionLemmas

/-!
# Review of `Reduced/RuleReduced.lean` (issue #370; Lafont 1997, pages 73 and 79)

**Verdict: no defect.** `Net.IsReduced` is the paper's "reduced" (no cut, no vicious circle,
page 79), the forward theorems say that a right member in the syntactic form `Rule.Reduced` is
reduced, and the converse `Rule.exists_reduced_of_isReduced` says that every reduced right member
can be written in the form, with the same `a`, `b` and the same names on the ports, at the names it
is given. Each hypothesis of the forward theorems is needed (below). No protected file is changed.

## Against page 79

Page 79: "Say that a net is reduced if it contains no cut and no vicious circle"; page 79 also
asks every right member to be reduced ("From now on, we shall only consider interaction systems
satisfying this extra condition"). `Net.IsReduced N` is `¬ N.HasCut ∧ ¬ N.HasVicious`, both
up to `Equiv`, so it is the paper's definition read on graphs. The right member of a rule is a net
whose free ports are the `a + b` auxiliary ports of the two cells, all distinct: this is what the
hypotheses `hx`, `hy`, `hxy` (distinct names on the ports) and `hl` (the instance is a net, that is
linear) describe. The converse concludes with a rule `r' : Rule S a b`, linear, in the form, and
an instance of it with the *same* `xs`, `ys` that is `Equiv` to the instance of `r`. That is
"every reduced right member can be written in the syntactic form", with no narrowing: the only
hypotheses are that `r` is linear and that its instance is a reduced net.

## Each hypothesis of the forward theorems is needed

* `hx` (`twoEra_fwd_fails`): the rule `l₀ = era, l₁ = era` is linear and in the form. With
  `xs 0 = xs 1 = 0` its instance `0 = era, 0 = era` is linear, and the other hypotheses hold
  (`ys` has no values), but one wire substitution gives the cut `era = era`: it is not reduced.
  This is the case the PR mentions: `hl` does not give `hx`.
* `hy` (`twoEraR_fwd_fails`) and `hxy` (`eraEra_fwd_fails`): the same net, with the two ports on
  the second cell, or one on each cell with the same name.
* `hl` (`loopRule_fwd_fails`): the rule `l₀ = con(w, w), r₀ = era` is linear and in the form; with
  distinct names `0`, `1` on the ports and the name `0` also on the internal wire `w`, its instance
  `0 = con(0, 0), 1 = era` has a vicious circle.

## The converse without `hl`

`shareRule_conv_fails`: the rule `l₀ = con(w₀, w₁), r₀ = con(w₀, w₁)`, with both internal wires
named `5`, has the instance `0 = con(5, 5), 1 = con(5, 5)`. It is reduced (trees on free ports)
but not linear, and no linear rule in the form has an instance `Equiv` to it: a non-linear net is
`Equiv` only to itself (`eq_of_equiv_of_not_linear`), and an instance of a linear rule with
injective names puts a name at most `1 + 2` times, not 4. So `hl` is needed in the converse.
Whether `hx` is needed in the converse is **not settled**: with `xs 0 = xs 1`, I found no reduced
linear instance for which the conclusion fails (in `l₀ = era, r₀ = con(l₁, era)` with
`xs 0 = xs 1 = 0`, the instance `0 = era, 1 = con(0, era)` is reduced and the rule itself is in the
form). The paper has distinct free ports, so `hx` is the faithful hypothesis either way.

## The converse is not vacuous

* A wire between two auxiliary ports, `l₀ = r₀` (`wireRule_rewritten`).
* An internal wire between two leaves, `l₀ = con(w, era), r₀ = dup(w, era)`
  (`leafRule_rewritten`), and, already in `Checks/Reduced/RuleReducedCheck.lean`, an internal wire
  from a root to a leaf (`bad_rewritten`, a rule not in the form).
* An internal wire between two roots, `w = con(l₀, l₁), w = dup(r₀, r₁)`, is a cut: the instance
  is not reduced (`rootRule_not_isReduced`) and the converse does not apply.
* A vicious circle, `w = con(w, l₀)`, and a cyclic wire, `w = w`: the instances are not reduced
  (`viciousRule_not_isReduced`, `cyclicRule_not_isReduced`).

## The new rule can replace the old one, and the gap in `PAPER.md`

`r'` has type `Rule S a b`, the same `a` and `b`, and its instance is taken at the same `xs`,
`ys`: the graph is the same with the same free ports. Only the number of internal wires may
change. What the theorem does **not** say is that `r'` gives the same graph at *every* instance:
`Step` plugs arbitrary trees `as`, `bs` into the ports, and `r'` is built from one choice of names.
To replace `r` by `r'` inside a system one would need `Equiv (r.inst as bs f) (r'.inst as bs f')`
for all trees, which I did not prove (I expect it to follow by substitution of trees for free
ports, a lemma not in the library).

`PAPER.md`, "Known gaps", item 2 (protected, report only) says that Proposition 2 is not
formalized and that `Rule.Reduced` is not related to `Net.IsReduced` beyond
`Rule.not_hasCut_inst`. Both parts are now out of date: Proposition 2 is
`Net.IsReduced.exists_treesOnWiring` (`ReducedDecomp.lean`) with uniqueness in
`ReducedDecompUnique.lean`, and `RuleReduced.lean` relates the two notions in both directions on
instances with distinct names. The last sentence of the item still holds: `System.WellFormed`
asks `Rule.Reduced`, so a rule whose text is reduced only up to wires must be written in the
substituted form, and the rewriting is guaranteed at one naming, not at every instance.
-/

namespace INet.RuleReducedReview

open Comb Term

/-- A net over `ℕ` is linear if its names that occur occur at most twice; this form is
decidable. -/
theorem linear_of_mem' {N : Net sig ℕ} (h : ∀ x ∈ N.vars, N.vars.count x ≤ 2) : N.Linear := by
  intro x
  by_cases hx : x ∈ N.vars
  · exact h x hx
  · rw [Multiset.count_eq_zero.2 hx]; omega

/-- A net that is not linear is `Equiv` only to itself: a wire substitution needs a linear net and
gives one (`Wire.linear_left`, `Wire.linear_right`). -/
theorem eq_of_equiv_of_not_linear {N M : Net sig ℕ} (h : Equiv N M) :
    ¬ N.Linear ∨ ¬ M.Linear → N = M := by
  induction h with
  | rel x y hw =>
    rintro (hc | hc)
    · exact absurd hw.linear_left hc
    · exact absurd hw.linear_right hc
  | refl => intro _; rfl
  | symm x y _ ih => intro hc; exact (ih hc.symm).symm
  | trans x y z _ _ ih1 ih2 =>
    rintro (hc | hc)
    · have e1 := ih1 (Or.inl hc)
      subst e1
      exact ih2 (Or.inl hc)
    · have e2 := ih2 (Or.inr hc)
      subst e2
      exact ih1 (Or.inr hc)

/-! ## The cut `0 = era, 0 = era` -/

/-- The net `0 = era, 0 = era`. -/
def cutNet : Net sig ℕ := s(var 0, mkEra) ::ₘ s(var 0, mkEra) ::ₘ 0

theorem cutNet_linear : cutNet.Linear := linear_of_mem' (by decide)

/-- `0 = era, 0 = era` has a cut: substituting the wire `0` gives `era = era` (page 79). -/
theorem cutNet_not_isReduced : ¬ cutNet.IsReduced := by
  intro h
  have hW : Wire cutNet (s(mkEra, mkEra) ::ₘ (0 : Net sig ℕ)) :=
    Wire.cast (Wire.mk 0 mkEra (var 0) mkEra 0 cutNet_linear (by decide)) rfl (by decide)
  exact h.1 ⟨_, hW.equiv, Comb.era, Comb.era, ![], ![], Multiset.mem_cons_self _ _⟩

/-! ## `hx` is needed -/

/-- `l₀ = era, l₁ = era`. -/
def twoEra : Rule sig 2 0 :=
  ⟨0, s(var (.inl 0), mkEra) ::ₘ s(var (.inl 1), mkEra) ::ₘ 0⟩

theorem twoEra_linear : twoEra.Linear := by
  refine ⟨fun i => ?_, fun j => j.elim0, fun w => w.elim0⟩
  change Multiset.count _ (Net.vars (show Net sig (Fin 2 ⊕ Fin 0 ⊕ Fin 0) from twoEra.net)) = 1
  revert i; decide

theorem twoEra_reduced : twoEra.Reduced := by
  intro e he
  unfold twoEra at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 0, _, rfl, by simp⟩
  obtain rfl := Multiset.mem_singleton.1 he
  exact ⟨.inl 1, _, rfl, by simp⟩

/-- The names `0, 0` on the two ports. -/
def xs00 : Fin 2 → ℕ := ![0, 0]

theorem twoEra_inst :
    twoEra.inst (fun i => var (xs00 i)) (fun j : Fin 0 => var (j.elim0 : ℕ)) (fun _ => 0) =
      cutNet := by
  decide

/-- **`hx` is needed in the forward theorems** (page 79). `l₀ = era, l₁ = era` is linear and in the
form; with the same name `0` on both ports, every other hypothesis of
`Rule.Reduced.isReduced_inst` holds, the instance is linear, and it is not reduced. -/
theorem twoEra_fwd_fails :
    twoEra.Linear ∧ twoEra.Reduced ∧ ¬ Function.Injective xs00 ∧
      Function.Injective (fun j : Fin 0 => (j.elim0 : ℕ)) ∧
      (∀ i j, xs00 i ≠ (fun j : Fin 0 => (j.elim0 : ℕ)) j) ∧
      (twoEra.inst (fun i => var (xs00 i)) (fun j : Fin 0 => var (j.elim0 : ℕ))
        (fun _ => 0)).Linear ∧
      ¬ (twoEra.inst (fun i => var (xs00 i)) (fun j : Fin 0 => var (j.elim0 : ℕ))
        (fun _ => 0)).IsReduced := by
  refine ⟨twoEra_linear, twoEra_reduced, fun h => ?_, fun j => j.elim0, fun _ j => j.elim0,
    ?_, ?_⟩
  · exact absurd (h (a₁ := 0) (a₂ := 1) rfl) (by decide)
  · rw [twoEra_inst]; exact cutNet_linear
  · rw [twoEra_inst]; exact cutNet_not_isReduced

/-! ## `hy` is needed -/

/-- `r₀ = era, r₁ = era`. -/
def twoEraR : Rule sig 0 2 :=
  ⟨0, s(var (.inr (.inl 0)), mkEra) ::ₘ s(var (.inr (.inl 1)), mkEra) ::ₘ 0⟩

theorem twoEraR_linear : twoEraR.Linear := by
  refine ⟨fun i => i.elim0, fun j => ?_, fun w => w.elim0⟩
  change Multiset.count _ (Net.vars (show Net sig (Fin 0 ⊕ Fin 2 ⊕ Fin 0) from twoEraR.net)) = 1
  revert j; decide

theorem twoEraR_reduced : twoEraR.Reduced := by
  intro e he
  unfold twoEraR at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inr (.inl 0), _, rfl, by simp⟩
  obtain rfl := Multiset.mem_singleton.1 he
  exact ⟨.inr (.inl 1), _, rfl, by simp⟩

theorem twoEraR_inst :
    twoEraR.inst (fun i : Fin 0 => var (i.elim0 : ℕ)) (fun j => var (xs00 j)) (fun _ => 0) =
      cutNet := by
  decide

/-- **`hy` is needed in the forward theorems** (page 79): the same net as `twoEra_fwd_fails`, with
the two ports on the second cell. -/
theorem twoEraR_fwd_fails :
    twoEraR.Linear ∧ twoEraR.Reduced ∧ ¬ Function.Injective xs00 ∧
      (twoEraR.inst (fun i : Fin 0 => var (i.elim0 : ℕ)) (fun j => var (xs00 j))
        (fun _ => 0)).Linear ∧
      ¬ (twoEraR.inst (fun i : Fin 0 => var (i.elim0 : ℕ)) (fun j => var (xs00 j))
        (fun _ => 0)).IsReduced := by
  refine ⟨twoEraR_linear, twoEraR_reduced, fun h => ?_, ?_, ?_⟩
  · exact absurd (h (a₁ := 0) (a₂ := 1) rfl) (by decide)
  · rw [twoEraR_inst]; exact cutNet_linear
  · rw [twoEraR_inst]; exact cutNet_not_isReduced

/-! ## `hxy` is needed -/

/-- `l₀ = era, r₀ = era`. -/
def eraEra : Rule sig 1 1 :=
  ⟨0, s(var (.inl 0), mkEra) ::ₘ s(var (.inr (.inl 0)), mkEra) ::ₘ 0⟩

theorem eraEra_linear : eraEra.Linear := by
  refine ⟨fun i => ?_, fun j => ?_, fun w => w.elim0⟩
  · change Multiset.count _ (Net.vars (show Net sig (Fin 1 ⊕ Fin 1 ⊕ Fin 0) from eraEra.net)) = 1
    revert i; decide
  · change Multiset.count _ (Net.vars (show Net sig (Fin 1 ⊕ Fin 1 ⊕ Fin 0) from eraEra.net)) = 1
    revert j; decide

theorem eraEra_reduced : eraEra.Reduced := by
  intro e he
  unfold eraEra at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 0, _, rfl, by simp⟩
  obtain rfl := Multiset.mem_singleton.1 he
  exact ⟨.inr (.inl 0), _, rfl, by simp⟩

/-- The name `0` on one port. -/
def x0 : Fin 1 → ℕ := ![0]
/-- The name `1` on one port. -/
def x1 : Fin 1 → ℕ := ![1]

theorem x0_inj : Function.Injective x0 := by unfold x0; decide
theorem x1_inj : Function.Injective x1 := by unfold x1; decide
theorem x0_ne_x1 : ∀ i j, x0 i ≠ x1 j := by unfold x0 x1; decide

theorem eraEra_inst :
    eraEra.inst (fun i => var (x0 i)) (fun j => var (x0 j)) (fun _ => 0) = cutNet := by
  decide

/-- **`hxy` is needed in the forward theorems** (page 79): `l₀ = era, r₀ = era`, linear and in the
form, with the same name `0` on the port of each cell. The names on each cell are injective, the
instance is linear, and it is not reduced. -/
theorem eraEra_fwd_fails :
    eraEra.Linear ∧ eraEra.Reduced ∧ Function.Injective x0 ∧ ¬ (∀ i j, x0 i ≠ x0 j) ∧
      (eraEra.inst (fun i => var (x0 i)) (fun j => var (x0 j)) (fun _ => 0)).Linear ∧
      ¬ (eraEra.inst (fun i => var (x0 i)) (fun j => var (x0 j)) (fun _ => 0)).IsReduced := by
  refine ⟨eraEra_linear, eraEra_reduced, x0_inj, fun h => h 0 0 rfl, ?_, ?_⟩
  · rw [eraEra_inst]; exact cutNet_linear
  · rw [eraEra_inst]; exact cutNet_not_isReduced

/-! ## `hl` is needed in the forward theorems -/

/-- `l₀ = con(w, w), r₀ = era`. -/
def loopRule : Rule sig 1 1 :=
  ⟨1, s(var (.inl 0), mkCon (var (.inr (.inr 0))) (var (.inr (.inr 0)))) ::ₘ
    s(var (.inr (.inl 0)), mkEra) ::ₘ 0⟩

theorem loopRule_linear : loopRule.Linear := by
  refine ⟨fun i => ?_, fun j => ?_, fun w => ?_⟩
  · change Multiset.count _ (Net.vars (show Net sig (Fin 1 ⊕ Fin 1 ⊕ Fin 1) from loopRule.net)) = 1
    revert i; decide
  · change Multiset.count _ (Net.vars (show Net sig (Fin 1 ⊕ Fin 1 ⊕ Fin 1) from loopRule.net)) = 1
    revert j; decide
  · change Multiset.count _ (Net.vars (show Net sig (Fin 1 ⊕ Fin 1 ⊕ Fin 1) from loopRule.net)) = 2
    revert w; decide

theorem loopRule_reduced : loopRule.Reduced := by
  intro e he
  unfold loopRule at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 0, _, rfl, by simp⟩
  obtain rfl := Multiset.mem_singleton.1 he
  exact ⟨.inr (.inl 0), _, rfl, by simp⟩

theorem loopRule_inst :
    loopRule.inst (fun i => var (x0 i)) (fun j => var (x1 j)) (fun _ => 0) =
      s(var 0, mkCon (var 0) (var 0)) ::ₘ s(var 1, mkEra) ::ₘ 0 := by
  decide

/-- **`hl` is needed in the forward theorems** (page 79): `l₀ = con(w, w), r₀ = era` is linear and
in the form, the names `0`, `1` on the ports are distinct, and with the name `0` on `w` the
instance `0 = con(0, 0), 1 = era` has a vicious circle. -/
theorem loopRule_fwd_fails :
    loopRule.Linear ∧ loopRule.Reduced ∧ Function.Injective x0 ∧ Function.Injective x1 ∧
      (∀ i j, x0 i ≠ x1 j) ∧
      ¬ (loopRule.inst (fun i => var (x0 i)) (fun j => var (x1 j)) (fun _ => 0)).IsReduced := by
  refine ⟨loopRule_linear, loopRule_reduced, x0_inj, x1_inj, x0_ne_x1, fun h => h.2 ?_⟩
  rw [loopRule_inst]
  exact Net.hasVicious_of_mem (x := 0) (t := mkCon (var 0) (var 0)) (by decide)
    (Multiset.mem_cons_self _ _)

/-! ## `hl` is needed in the converse -/

/-- `l₀ = con(w₀, w₁), r₀ = con(w₀, w₁)`. -/
def shareRule : Rule sig 1 1 :=
  ⟨2, s(var (.inl 0), mkCon (var (.inr (.inr 0))) (var (.inr (.inr 1)))) ::ₘ
    s(var (.inr (.inl 0)), mkCon (var (.inr (.inr 0))) (var (.inr (.inr 1)))) ::ₘ 0⟩

theorem shareRule_linear : shareRule.Linear := by
  refine ⟨fun i => ?_, fun j => ?_, fun w => ?_⟩
  · change Multiset.count _
      (Net.vars (show Net sig (Fin 1 ⊕ Fin 1 ⊕ Fin 2) from shareRule.net)) = 1
    revert i; decide
  · change Multiset.count _
      (Net.vars (show Net sig (Fin 1 ⊕ Fin 1 ⊕ Fin 2) from shareRule.net)) = 1
    revert j; decide
  · change Multiset.count _
      (Net.vars (show Net sig (Fin 1 ⊕ Fin 1 ⊕ Fin 2) from shareRule.net)) = 2
    revert w; decide

/-- The net `0 = con(5, 5), 1 = con(5, 5)`. -/
def shareNet : Net sig ℕ :=
  s(var 0, mkCon (var 5) (var 5)) ::ₘ s(var 1, mkCon (var 5) (var 5)) ::ₘ 0

theorem shareRule_inst :
    shareRule.inst (fun i => var (x0 i)) (fun j => var (x1 j)) (fun _ => 5) = shareNet := by
  decide

theorem shareNet_count : shareNet.vars.count 5 = 4 := by decide

theorem shareNet_isReduced : shareNet.IsReduced := by
  refine Net.IsTreesOnWiring.isReduced fun e he => ?_
  unfold shareNet at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨0, _, rfl, by decide⟩
  obtain rfl := Multiset.mem_singleton.1 he
  exact ⟨1, _, rfl, by decide⟩

/-- **`hl` is needed in the converse** (page 79). The instance of the linear rule
`l₀ = con(w₀, w₁), r₀ = con(w₀, w₁)` with distinct names `0`, `1` on the ports and the name `5` on
both internal wires is reduced, but no linear rule, in the form or not, has an instance at the same
port names, with injective names on its internal wires, `Equiv` to it: the instance is not linear,
so it is `Equiv` only to itself, and it puts the name `5` four times. -/
theorem shareRule_conv_fails :
    shareRule.Linear ∧ Function.Injective x0 ∧ Function.Injective x1 ∧ (∀ i j, x0 i ≠ x1 j) ∧
      (shareRule.inst (fun i => var (x0 i)) (fun j => var (x1 j)) (fun _ => 5)).IsReduced ∧
      ¬ ∃ (r' : Rule sig 1 1) (h' : Fin r'.internal → ℕ), r'.Linear ∧ Function.Injective h' ∧
        Equiv (shareRule.inst (fun i => var (x0 i)) (fun j => var (x1 j)) (fun _ => 5))
          (r'.inst (fun i => var (x0 i)) (fun j => var (x1 j)) h') := by
  refine ⟨shareRule_linear, x0_inj, x1_inj, x0_ne_x1, shareRule_inst ▸ shareNet_isReduced, ?_⟩
  rintro ⟨r', h', hr', hh', hE⟩
  rw [shareRule_inst] at hE
  have hnl : ¬ shareNet.Linear := fun hl => by have := hl 5; rw [shareNet_count] at this; omega
  have e := eq_of_equiv_of_not_linear hE (Or.inl hnl)
  have hc := Rule.count_vars_inst r' hr' (fun i => var (x0 i)) (fun j => var (x1 j)) h' 5
  rw [← e, shareNet_count] at hc
  have hle : (∑ w, if 5 = h' w then 1 else 0) ≤ 1 := by
    rw [Finset.sum_boole]
    refine Finset.card_le_one.2 fun w hw w' hw' => hh' ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
    exact hw.symm.trans hw'
  simp [x0, x1] at hc
  simp only [Finset.sum_boole, Nat.cast_id] at hle
  omega

/-! ## The converse is not vacuous -/

/-- `l₀ = r₀`: a wire between two auxiliary ports. -/
def wireRule : Rule sig 1 1 := ⟨0, s(var (.inl 0), var (.inr (.inl 0))) ::ₘ 0⟩

theorem wireRule_linear : wireRule.Linear := by
  refine ⟨fun i => ?_, fun j => ?_, fun w => w.elim0⟩
  · change Multiset.count _ (Net.vars (show Net sig (Fin 1 ⊕ Fin 1 ⊕ Fin 0) from wireRule.net)) = 1
    revert i; decide
  · change Multiset.count _ (Net.vars (show Net sig (Fin 1 ⊕ Fin 1 ⊕ Fin 0) from wireRule.net)) = 1
    revert j; decide

theorem wireRule_reduced : wireRule.Reduced := by
  intro e he
  unfold wireRule at he
  dsimp only at he
  obtain rfl := Multiset.mem_singleton.1 he
  exact ⟨.inl 0, _, rfl, by simp⟩

theorem wireRule_inst_linear :
    (wireRule.inst (fun i => var (x0 i)) (fun j => var (x1 j)) (fun w => w.elim0)).Linear := by
  have e : wireRule.inst (fun i => var (x0 i)) (fun j => var (x1 j)) (fun w => w.elim0) =
      s(var 0, var 1) ::ₘ (0 : Net sig ℕ) := by decide
  rw [e]; exact linear_of_mem' (by decide)

/-- The converse applies to the wire `l₀ = r₀` between two auxiliary ports (page 79). -/
theorem wireRule_rewritten : ∃ (r' : Rule sig 1 1) (h' : Fin r'.internal → ℕ), r'.Linear ∧
    r'.Reduced ∧ Function.Injective h' ∧
    Equiv (wireRule.inst (fun i => var (x0 i)) (fun j => var (x1 j)) (fun w => w.elim0))
      (r'.inst (fun i => var (x0 i)) (fun j => var (x1 j)) h') :=
  Rule.exists_reduced_of_isReduced wireRule_linear x0_inj x1_inj x0_ne_x1 wireRule_inst_linear
    (wireRule_reduced.isReduced_inst wireRule_linear x0_inj x1_inj x0_ne_x1 wireRule_inst_linear)

/-- `l₀ = con(w, era), r₀ = dup(w, era)`: an internal wire between two leaves. -/
def leafRule : Rule sig 1 1 :=
  ⟨1, s(var (.inl 0), mkCon (var (.inr (.inr 0))) mkEra) ::ₘ
    s(var (.inr (.inl 0)), mkDup (var (.inr (.inr 0))) mkEra) ::ₘ 0⟩

theorem leafRule_linear : leafRule.Linear := by
  refine ⟨fun i => ?_, fun j => ?_, fun w => ?_⟩
  · change Multiset.count _ (Net.vars (show Net sig (Fin 1 ⊕ Fin 1 ⊕ Fin 1) from leafRule.net)) = 1
    revert i; decide
  · change Multiset.count _ (Net.vars (show Net sig (Fin 1 ⊕ Fin 1 ⊕ Fin 1) from leafRule.net)) = 1
    revert j; decide
  · change Multiset.count _ (Net.vars (show Net sig (Fin 1 ⊕ Fin 1 ⊕ Fin 1) from leafRule.net)) = 2
    revert w; decide

theorem leafRule_reduced : leafRule.Reduced := by
  intro e he
  unfold leafRule at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 0, _, rfl, by simp⟩
  obtain rfl := Multiset.mem_singleton.1 he
  exact ⟨.inr (.inl 0), _, rfl, by simp⟩

theorem leafRule_inst_linear :
    (leafRule.inst (fun i => var (x0 i)) (fun j => var (x1 j)) (fun _ => 4)).Linear := by
  have e : leafRule.inst (fun i => var (x0 i)) (fun j => var (x1 j)) (fun _ => 4) =
      s(var 0, mkCon (var 4) mkEra) ::ₘ s(var 1, mkDup (var 4) mkEra) ::ₘ (0 : Net sig ℕ) := by
    decide
  rw [e]; exact linear_of_mem' (by decide)

/-- The converse applies to a rule with an internal wire between two leaves (page 79). -/
theorem leafRule_rewritten : ∃ (r' : Rule sig 1 1) (h' : Fin r'.internal → ℕ), r'.Linear ∧
    r'.Reduced ∧ Function.Injective h' ∧
    Equiv (leafRule.inst (fun i => var (x0 i)) (fun j => var (x1 j)) (fun _ => 4))
      (r'.inst (fun i => var (x0 i)) (fun j => var (x1 j)) h') :=
  Rule.exists_reduced_of_isReduced leafRule_linear x0_inj x1_inj x0_ne_x1 leafRule_inst_linear
    (leafRule_reduced.isReduced_inst leafRule_linear x0_inj x1_inj x0_ne_x1 leafRule_inst_linear)

/-! ## Where the converse must not apply -/

/-- `w = con(l₀, l₁), w = dup(r₀, r₁)`: an internal wire between two roots. -/
def rootRule : Rule sig 2 2 :=
  ⟨1, s(var (.inr (.inr 0)), mkCon (var (.inl 0)) (var (.inl 1))) ::ₘ
    s(var (.inr (.inr 0)), mkDup (var (.inr (.inl 0))) (var (.inr (.inl 1)))) ::ₘ 0⟩

/-- The names `0, 1` on the ports of the first cell. -/
def xs01 : Fin 2 → ℕ := ![0, 1]
/-- The names `2, 3` on the ports of the second cell. -/
def ys23 : Fin 2 → ℕ := ![2, 3]

/-- **An internal wire between two roots is a cut** (page 79): the instance
`4 = con(0, 1), 4 = dup(2, 3)` of `w = con(l₀, l₁), w = dup(r₀, r₁)` is not reduced, so the
converse does not apply to it. -/
theorem rootRule_not_isReduced :
    ¬ (rootRule.inst (fun i => var (xs01 i)) (fun j => var (ys23 j)) (fun _ => 4)).IsReduced := by
  have e : rootRule.inst (fun i => var (xs01 i)) (fun j => var (ys23 j)) (fun _ => 4) =
      s(var 4, mkCon (var 0) (var 1)) ::ₘ s(var 4, mkDup (var 2) (var 3)) ::ₘ (0 : Net sig ℕ) := by
    decide
  rw [e]
  intro h
  have hl : Net.Linear (s(var 4, mkCon (var 0) (var 1)) ::ₘ
      s(var 4, mkDup (var 2) (var 3)) ::ₘ (0 : Net sig ℕ)) := linear_of_mem' (by decide)
  have hW : Wire (s(var 4, mkCon (var 0) (var 1)) ::ₘ s(var 4, mkDup (var 2) (var 3)) ::ₘ 0)
      (s(mkCon (var 0) (var 1), mkDup (var 2) (var 3)) ::ₘ (0 : Net sig ℕ)) :=
    Wire.cast (Wire.mk 4 (mkCon (var 0) (var 1)) (var 4) (mkDup (var 2) (var 3)) 0 hl
      (by decide)) rfl (by decide)
  exact h.1 ⟨_, hW.equiv, Comb.con, Comb.dup, _, _, Multiset.mem_cons_self _ _⟩

/-- `w = con(w, l₀)`: a vicious circle of length 1. -/
def viciousRule : Rule sig 1 0 :=
  ⟨1, s(var (.inr (.inr 0)), mkCon (var (.inr (.inr 0))) (var (.inl 0))) ::ₘ 0⟩

/-- **A vicious circle is not reduced** (page 79): the instance `4 = con(4, 0)` of
`w = con(w, l₀)` is not reduced, so the converse does not apply to it. -/
theorem viciousRule_not_isReduced :
    ¬ (viciousRule.inst (fun i => var (x0 i)) (fun j : Fin 0 => var (j.elim0 : ℕ))
      (fun _ => 4)).IsReduced := by
  have e : viciousRule.inst (fun i => var (x0 i)) (fun j : Fin 0 => var (j.elim0 : ℕ))
      (fun _ => 4) = s(var 4, mkCon (var 4) (var 0)) ::ₘ (0 : Net sig ℕ) := by
    decide
  rw [e]
  exact fun h => h.2 (Net.hasVicious_of_mem (x := 4) (t := mkCon (var 4) (var 0)) (by decide)
    (Multiset.mem_cons_self _ _))

/-- `w = w`: a cyclic wire. -/
def cyclicRule : Rule sig 0 0 := ⟨1, s(var (.inr (.inr 0)), var (.inr (.inr 0))) ::ₘ 0⟩

/-- **A cyclic wire is not reduced** (page 79: a vicious circle of length 0): the instance
`4 = 4` of `w = w` is not reduced. -/
theorem cyclicRule_not_isReduced :
    ¬ (cyclicRule.inst (fun i : Fin 0 => var (i.elim0 : ℕ)) (fun j : Fin 0 => var (j.elim0 : ℕ))
      (fun _ => 4)).IsReduced := by
  have e : cyclicRule.inst (fun i : Fin 0 => var (i.elim0 : ℕ))
      (fun j : Fin 0 => var (j.elim0 : ℕ)) (fun _ => 4) = s(var 4, var 4) ::ₘ (0 : Net sig ℕ) := by
    decide
  rw [e]
  exact fun h => h.2 (Net.hasVicious_of_mem (x := 4) (t := var 4) (by decide)
    (Multiset.mem_cons_self _ _))

end INet.RuleReducedReview
