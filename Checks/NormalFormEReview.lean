import Checks.NormalFormECheck
import InteractionCombinators.Lafont.NormalFormCut

/-!
# Review of `NormalFormE.lean` (issue #260, pages 73-74)

Checks written for the review of `StepE.Normal` and `StepsEN.normal_unique`.

* `not_both_orders` — no well-formed system with two distinct symbols has a rule in *both*
  orders, the hypothesis that `Net.HasCut.stepE` used to take. The library now takes "one order
  or the other" (`Net.HasCut.stepE`, `StepE.Normal.iff_not_hasCut`, `Comb.system_complete` in
  `Lafont/Cut.lean` and `Lafont/NormalFormCut.lean`), and a check below applies it.
* `emptySys` — a well-formed system without rules: the cut `era = era` is irreducible there, so
  without completeness "irreducible" and "no cut" differ. In that system no counted reduction has
  a positive length (`emptySys_stepsEN_zero`), although wire substitutions exist: `StepsEN` counts
  interactions and not wire substitutions.
* `twoPairs` — a `con`–`con` pair beside a `dup`–`dup` pair. It reduces to normal form in two
  interactions in either order, the two first steps give different nets, and
  `StepsEN.normal_unique` identifies the two results and fixes the length of every reduction to
  normal form at `2`.
-/

namespace INet.NormalFormEReview

open Term Comb

variable {S : Signature}

/-! ## Irreducible and "no cut" -/

/-- No well-formed system has a rule for two distinct symbols in both orders. This is why
`Net.HasCut.stepE` asks for a rule in one order *or* the other: the earlier hypothesis, a rule in
both orders, held for no well-formed system with two distinct symbols. -/
theorem not_both_orders {I : System S} (hI : I.WellFormed) {α β : S.Sym} (hαβ : α ≠ β) :
    ¬ ((I.rule α β).isSome ∧ (I.rule β α).isSome) := by
  rintro ⟨h1, h2⟩
  rw [hI.unique α β hαβ h1] at h2
  exact absurd h2 (by simp)

/-- The combinators have no rule in both orders for `con` and `dup`: a rule for every ordered pair
of symbols is impossible for them. -/
example : ¬ ∀ α β : sig.Sym, (system.rule α β).isSome := fun h =>
  not_both_orders system_wellFormed (α := (Comb.con : sig.Sym)) (β := Comb.dup)
    (show (Comb.con : Comb) ≠ Comb.dup by decide)
    ⟨h _ _, h _ _⟩

/-- The library hypothesis of `Net.HasCut.stepE` holds for the combinators, so a cut of
`con(0, 1) = dup(2, 3)` fires. -/
example : ∃ M, StepE system
    (s(Term.app (Comb.con : sig.Sym) ![.var 0, .var 1],
      Term.app (Comb.dup : sig.Sym) ![(.var 2 : Term sig ℕ), .var 3]) ::ₘ 0) M :=
  Net.HasCut.stepE Comb.system_complete (Net.hasCut_of_mem (Multiset.mem_cons_self _ _))

/-! ## A system without rules -/

/-- The combinators' signature with no rule at all. -/
def emptySys : System sig := ⟨fun _ _ => none⟩

/-- The system without rules is well formed: every field is about a rule. -/
theorem emptySys_wellFormed : emptySys.WellFormed where
  linear _ _ _ h := by simp [emptySys] at h
  reduced _ _ _ h := by simp [emptySys] at h
  unique _ _ _ _ := rfl
  symm _ _ h := by simp [emptySys] at h

/-- No interaction exists in the system without rules. -/
theorem emptySys_not_stepE (N M : Net sig ℕ) : ¬ StepE emptySys N M := by
  rintro ⟨_, -, ⟨α, β, r, hr, -⟩⟩
  simp [emptySys] at hr

/-- The cut `era = era`. -/
abbrev eraPair : Net sig ℕ := s((mkEra : Term sig ℕ), mkEra) ::ₘ 0

/-- **Without completeness, an irreducible net may have a cut** (Lafont 1997, page 73): in the
well-formed system without rules, `era = era` is a cut and is irreducible. So `StepE.Normal` is
"no active pair *that has a rule*", and `of_not_hasCut` has no converse in general. -/
theorem eraPair_normal_hasCut : StepE.Normal emptySys eraPair ∧ eraPair.HasCut :=
  ⟨emptySys_not_stepE eraPair, Net.hasCut_of_mem (Multiset.mem_cons_self _ _)⟩

/-- **`StepsEN` counts interactions, not wire substitutions** (Lafont 1997, page 74: "in `n`
steps"). In the system without rules every counted reduction has length `0`. -/
theorem emptySys_stepsEN_zero {n : ℕ} {N M : Net sig ℕ} (h : StepsEN emptySys n N M) : n = 0 := by
  cases h with
  | refl => rfl
  | tail _ hs => exact absurd hs (emptySys_not_stepE _ _)

/-- A wire substitution of the system without rules: `x = era, x = y` is the same graph as
`era = y`, and still no counted reduction of positive length relates them. -/
example : Equiv (s((Term.var 0 : Term sig ℕ), mkEra) ::ₘ s((Term.var 0 : Term sig ℕ), .var 1) ::ₘ 0)
    (s((mkEra : Term sig ℕ), .var 1) ::ₘ 0) := by
  refine Wire.equiv ?_
  have h := Wire.mk (0 : ℕ) (mkEra : Term sig ℕ) (.var 0) (.var 1) 0
    (fun y => by simp [Multiset.count_cons, Multiset.count_singleton]; split_ifs <;> omega)
    (by simp)
  simpa [Term.subst] using h

/-! ## Two pairs, fired in either order -/

/-- The cut `con(0, 1) = con(2, 3)`. -/
abbrev conEq : Sym2 (Term sig ℕ) :=
  s(Term.app (Comb.con : sig.Sym) ![.var 0, .var 1],
    Term.app (Comb.con : sig.Sym) ![.var 2, .var 3])

/-- The cut `dup(4, 5) = dup(6, 7)`. -/
abbrev dupEq : Sym2 (Term sig ℕ) :=
  s(Term.app (Comb.dup : sig.Sym) ![.var 4, .var 5],
    Term.app (Comb.dup : sig.Sym) ![.var 6, .var 7])

/-- The right-hand side of the `con`–`con` pair: `0 = 3, 1 = 2`. -/
abbrev conRes : Net sig ℕ :=
  ruleConCon.inst ![(Term.var 0 : Term sig ℕ), .var 1] ![(Term.var 2 : Term sig ℕ), .var 3]
    (fun w => w.elim0)

/-- The right-hand side of the `dup`–`dup` pair: `4 = 6, 5 = 7`. -/
abbrev dupRes : Net sig ℕ :=
  ruleDupDup.inst ![(Term.var 4 : Term sig ℕ), .var 5] ![(Term.var 6 : Term sig ℕ), .var 7]
    (fun w => w.elim0)

/-- Two independent active pairs. -/
abbrev twoPairs : Net sig ℕ := conEq ::ₘ dupEq ::ₘ 0

/-- The two pairs are linear: every name occurs once. -/
theorem twoPairs_linear : twoPairs.Linear := by
  have hn : (Net.vars twoPairs).Nodup := by decide
  intro y
  exact (Multiset.nodup_iff_count_le_one.1 hn y).trans (by norm_num)

/-- The `con` pair fires first. -/
theorem step_con_first : StepE system twoPairs (conRes + (dupEq ::ₘ 0)) :=
  Step.stepE (Step.mk (Comb.con : sig.Sym) (Comb.con : sig.Sym) ruleConCon rfl
    ![(Term.var 0 : Term sig ℕ), .var 1] ![(Term.var 2 : Term sig ℕ), .var 3] (dupEq ::ₘ 0)
    (fun w => w.elim0) (fun w => w.elim0) (fun w => w.elim0))

/-- Then the `dup` pair. -/
theorem step_dup_second : StepE system (conRes + (dupEq ::ₘ 0)) (dupRes + (conRes + 0)) :=
  ⟨_, Equiv.of_eq (Multiset.add_cons _ _ _), Step.mk (Comb.dup : sig.Sym) (Comb.dup : sig.Sym)
    ruleDupDup rfl ![(Term.var 4 : Term sig ℕ), .var 5] ![(Term.var 6 : Term sig ℕ), .var 7]
    (conRes + 0) (fun w => w.elim0) (fun w => w.elim0) (fun w => w.elim0)⟩

/-- The `dup` pair fires first. -/
theorem step_dup_first : StepE system twoPairs (dupRes + (conEq ::ₘ 0)) :=
  ⟨_, Equiv.of_eq (Multiset.cons_swap _ _ _), Step.mk (Comb.dup : sig.Sym) (Comb.dup : sig.Sym)
    ruleDupDup rfl ![(Term.var 4 : Term sig ℕ), .var 5] ![(Term.var 6 : Term sig ℕ), .var 7]
    (conEq ::ₘ 0) (fun w => w.elim0) (fun w => w.elim0) (fun w => w.elim0)⟩

/-- Then the `con` pair. -/
theorem step_con_second : StepE system (dupRes + (conEq ::ₘ 0)) (conRes + (dupRes + 0)) :=
  ⟨_, Equiv.of_eq (Multiset.add_cons _ _ _), Step.mk (Comb.con : sig.Sym) (Comb.con : sig.Sym)
    ruleConCon rfl ![(Term.var 0 : Term sig ℕ), .var 1] ![(Term.var 2 : Term sig ℕ), .var 3]
    (dupRes + 0) (fun w => w.elim0) (fun w => w.elim0) (fun w => w.elim0)⟩

/-- A net without cells has no cut (Lafont 1997, page 80). -/
theorem not_hasCut_of_cells {N : Net S ℕ} (h : N.cells = 0) : ¬ N.HasCut := by
  rintro ⟨N', hE, α, β, ts, us, hm⟩
  have hα : α ∈ Net.cells N' :=
    Multiset.mem_bind.2 ⟨_, hm, by simp⟩
  rw [← hE.cells_eq, h] at hα
  simp at hα

/-- The result of the first order is irreducible: it has no cell. -/
theorem normal_A : StepE.Normal system (dupRes + (conRes + 0)) :=
  StepE.Normal.of_not_hasCut (not_hasCut_of_cells (by decide))

/-- The result of the second order is irreducible. -/
theorem normal_B : StepE.Normal system (conRes + (dupRes + 0)) :=
  StepE.Normal.of_not_hasCut (not_hasCut_of_cells (by decide))

/-- The two first steps give different nets: one still has two `dup` cells, the other two `con`
cells. -/
theorem first_steps_differ : conRes + (dupEq ::ₘ 0) ≠ dupRes + (conEq ::ₘ 0) := by
  intro h
  have := congrArg Net.cells h
  revert this
  decide

/-- **`normal_unique` where the order of interactions differs** (Lafont 1997, pages 73-74). The
two pairs reduce to normal form in two interactions in either order, the two orders start with
different steps, the two normal forms are the same graph, and every reduction of the two pairs to
an irreducible net has length `2` and ends at that graph. -/
theorem twoPairs_normal_unique :
    StepsEN system 2 twoPairs (dupRes + (conRes + 0)) ∧
      StepsEN system 2 twoPairs (conRes + (dupRes + 0)) ∧
      conRes + (dupEq ::ₘ 0) ≠ dupRes + (conEq ::ₘ 0) ∧
      Equiv (dupRes + (conRes + 0)) (conRes + (dupRes + 0)) ∧
      ∀ m Q, StepsEN system m twoPairs Q → StepE.Normal system Q →
        m = 2 ∧ Equiv (dupRes + (conRes + 0)) Q := by
  have hA : StepsEN system 2 twoPairs (dupRes + (conRes + 0)) :=
    (StepsEN.single step_con_first).tail step_dup_second
  have hB : StepsEN system 2 twoPairs (conRes + (dupRes + 0)) :=
    (StepsEN.single step_dup_first).tail step_con_second
  exact ⟨hA, hB, first_steps_differ,
    (StepsEN.normal_unique system_wellFormed twoPairs_linear normal_A normal_B hA hB).2,
    fun m Q ht hQ => StepsEN.normal_unique system_wellFormed twoPairs_linear normal_A hQ hA ht⟩

/-- No reduction of the two pairs has more than two interactions (`StepsEN.le_of_normal`). -/
example (k : ℕ) (Q : Net sig ℕ) (h : StepsEN system k twoPairs Q) : k ≤ 2 :=
  StepsEN.le_of_normal system_wellFormed twoPairs_linear normal_A
    ((StepsEN.single step_con_first).tail step_dup_second) h

end INet.NormalFormEReview
