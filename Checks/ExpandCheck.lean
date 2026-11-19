import InteractionCombinators.Lafont.Expand
import Checks.ExpandedIsoCheck

/-!
# Checks for `Lafont/Expand.lean`

Non-vacuity of `Rule.exists_expanded` (page 86). Its hypotheses hold for two rules that are not
expanded:

* `ruleConCon` (`a₀ = b₁, a₁ = b₀`), where both equations join two ports;
* `leafRule` (`a₀ = con(b₀, b₁), a₁ = ε`), where two ports are leaves of a tree.

`ruleConDup` is already expanded (every leaf is an internal wire), so it does not exercise the
induction; `selfRule` is expanded too (`ExpandedIsoCheck.selfRule_expanded`). For both
non-expanded rules the expected expanded form is given explicitly, proved linear and expanded, and
proved `Equiv` to the rule, renamed into its new internal wires.
-/

namespace INet.Comb.ExpandCheck

open Term Rule DecompositionReview ExpandedIsoCheck

/-! ### `con`–`con`: two equations between ports -/

/-- `ruleConCon` is not expanded: it has no internal wire, but each equation has a name below its
root. -/
theorem ruleConCon_not_expanded : ¬ ruleConCon.Expanded := by
  intro h
  have hmem : (s(pl 0, pr 1) : Sym2 (Term sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0))) ∈
      (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0) from ruleConCon.net) := by
    decide
  obtain ⟨p, t, he, -, ht⟩ := h _ hmem
  rcases Sym2.eq_iff.1 he with ⟨-, rfl⟩ | ⟨rfl, -⟩
  · exact (ht _ (Multiset.mem_singleton_self _)).choose.elim0
  · exact (ht _ (Multiset.mem_singleton_self _)).choose.elim0

/-- `Rule.exists_expanded` applies to `ruleConCon`. -/
theorem ruleConCon_exists_expanded :
    ∃ (r' : Rule sig 2 2) (ι : Fin ruleConCon.internal → Fin r'.internal), Function.Injective ι ∧
      r'.Linear ∧ r'.Expanded ∧
      Equiv r'.net (ruleConCon.net.bind fun x => Term.var (Sum.map id (Sum.map id ι) x)) :=
  ruleConCon.exists_expanded ruleConCon_linear ruleConCon_reduced

/-- The expected expanded `con`–`con` rule `a₀ = x₀, b₁ = x₀, a₁ = x₁, b₀ = x₁`
(`ExpandedIsoCheck.conConExp`) is linear and expanded, and is `Equiv` to `ruleConCon` with its
(zero) internal wires renamed into the two wires of the expanded rule. -/
theorem conConExp_spec :
    (⟨2, conConExp⟩ : Rule sig 2 2).Linear ∧ (⟨2, conConExp⟩ : Rule sig 2 2).Expanded ∧
      Equiv conConExp (ruleConCon.net.bind fun x =>
        Term.var (Sum.map id (Sum.map id (Fin.elim0 : Fin 0 → Fin 2)) x)) := by
  refine ⟨conConExp_linear, conConExp_expanded, conConExp_equiv_contr.trans (Equiv.of_eq ?_)⟩
  decide

/-! ### A rule with ports as leaves -/

/-- A rule with two ports as leaves of a tree: `a₀ = con(b₀, b₁)`, `a₁ = ε`. -/
def leafRule : Rule sig 2 2 := ⟨0, s(pl 0, mkCon (pr 0) (pr 1)) ::ₘ {s(pl 1, mkEra)}⟩

theorem leafRule_linear : leafRule.Linear := ⟨by decide, by decide, by decide⟩

theorem leafRule_reduced : leafRule.Reduced := by
  intro e he
  have key : ∀ e ∈ (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0) from leafRule.net),
      e ∈ [s(pl 0, mkCon (pr 0) (pr 1)), s(pl 1, mkEra)] := by decide
  rcases List.mem_pair.1 (key e he) with rfl | rfl
  · exact ⟨_, _, rfl, fun w => w.elim0⟩
  · exact ⟨_, _, rfl, fun w => w.elim0⟩

/-- `leafRule` is not expanded: the ports `b₀`, `b₁` are leaves of the tree of `a₀`. -/
theorem leafRule_not_expanded : ¬ leafRule.Expanded := by
  intro h
  have hmem : (s(pl 0, mkCon (pr 0) (pr 1)) : Sym2 (Term sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0))) ∈
      (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0) from leafRule.net) := by decide
  obtain ⟨p, t, he, -, ht⟩ := h _ hmem
  rcases Sym2.eq_iff.1 he with ⟨-, rfl⟩ | ⟨rfl, -⟩
  · exact (ht (.inr (.inl 0)) (by decide)).choose.elim0
  · exact (ht _ (Multiset.mem_singleton_self _)).choose.elim0

/-- `Rule.exists_expanded` applies to `leafRule`. -/
theorem leafRule_exists_expanded :
    ∃ (r' : Rule sig 2 2) (ι : Fin leafRule.internal → Fin r'.internal), Function.Injective ι ∧
      r'.Linear ∧ r'.Expanded ∧
      Equiv r'.net (leafRule.net.bind fun x => Term.var (Sum.map id (Sum.map id ι) x)) :=
  leafRule.exists_expanded leafRule_linear leafRule_reduced

/-- The expected expanded form of `leafRule`: `a₀ = con(x₀, x₁)`, `a₁ = ε`, `b₀ = x₀`, `b₁ = x₁`. -/
def leafExp : Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2) :=
  s(pl 0, mkCon (pw 0) (pw 1)) ::ₘ s(pl 1, mkEra) ::ₘ s(pr 0, pw 0) ::ₘ {s(pr 1, pw 1)}

theorem leafExp_linear : (⟨2, leafExp⟩ : Rule sig 2 2).Linear := ⟨by decide, by decide, by decide⟩

theorem leafExp_expanded : (⟨2, leafExp⟩ : Rule sig 2 2).Expanded := by
  intro e he
  have key : ∀ e ∈ leafExp,
      e ∈ [s(pl 0, mkCon (pw 0) (pw 1)), s(pl 1, mkEra), s(pr 0, pw 0), s(pr 1, pw 1)] := by
    decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl, fun w h => (by cases h), by decide⟩

/-- `leafExp` is `Equiv` to `leafRule` renamed into two internal wires: two wire substitutions
`x₀ := b₀`, `x₁ := b₁`. -/
theorem leafExp_equiv : Equiv leafExp (leafRule.net.bind fun x =>
    Term.var (Sum.map id (Sum.map id (Fin.elim0 : Fin 0 → Fin 2)) x)) := by
  have h₁ := equiv_wire_of_eq (ν := Fin 2 ⊕ Fin 2 ⊕ Fin 2) (N := leafExp)
    (M := s(pl 0, mkCon (pr 0) (pw 1)) ::ₘ s(pl 1, mkEra) ::ₘ {s(pr 1, pw 1)})
    (.inr (.inr 0)) (pr 0) (pl 0) (mkCon (pw 0) (pw 1)) (s(pl 1, mkEra) ::ₘ {s(pr 1, pw 1)})
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have h₂ := equiv_wire_of_eq (ν := Fin 2 ⊕ Fin 2 ⊕ Fin 2)
    (N := s(pl 0, mkCon (pr 0) (pw 1)) ::ₘ s(pl 1, mkEra) ::ₘ {s(pr 1, pw 1)})
    (M := s(pl 0, mkCon (pr 0) (pr 1)) ::ₘ {s(pl 1, mkEra)})
    (.inr (.inr 1)) (pr 1) (pl 0) (mkCon (pr 0) (pw 1)) {s(pl 1, mkEra)}
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  exact h₁.trans (h₂.trans (Equiv.of_eq (by decide)))

end INet.Comb.ExpandCheck
