import InteractionCombinators.Lafont.TranslationCompReview
import InteractionCombinators.Lafont.SimulationInvertible
import InteractionCombinators.Lafont.PairStepE
import InteractionCombinators.Combinators

/-!
# Checks of `SimulationInvertible.lean` (page 81)

* The hypotheses of `Translation.CompatibleWithin.of_distinct` hold: the identity translation of
  the combinators, compatible within `1` and `1` for all names, is so for distinct names, and
  `of_distinct` gives back the bound for all names.
* `Translation.Invertible.strict` and `Translation.Invertible.inst_eq` apply to a translation
  that is not the identity: `permTr σ` (`TranslationCompReview.lean`) permutes the auxiliary
  ports of its one symbol by any permutation `σ`.

* `System.WellFormed.stepE_pair_not_hasCut` (`PairStepE.lean`) applies to a reduction of the
  `con`–`con` pair of the combinators that is not literal: a wire is put on a port of the pair
  before the interaction. The net reached has no cut.
* `Translation.Invertible.compatibleWithin_one_of_wellFormed` gives `L = M = 1` for the identity
  translation of the combinators, from its compatibility alone.
-/

namespace INet.SimulationInvertibleCheck

open Term Comb TranslationCompReview

/-- `of_distinct` recovers `L = M = 1` for the identity translation of the combinators from its
distinct-names form (Lafont 1997, page 81): the hypotheses of `of_distinct` can hold. -/
example : (Translation.id sig).CompatibleWithin system system 1 1 :=
  Translation.CompatibleWithin.of_distinct system_wellFormed system_wellFormed.linear
    (Translation.id_compatibleWithin system system_wellFormed).distinct

/-- The translation `permTr σ`, invertible for every permutation `σ`, is strict (Lafont 1997,
page 81). -/
theorem permTr_strict {k : ℕ} (σ : _root_.Equiv.Perm (Fin k)) : (permTr σ).Strict :=
  (permTr_invertible σ).strict

/-- An instance of `permTr σ` of the symbol of `sigN k` is one cell with permuted names
(Lafont 1997, page 81, top): `Invertible.inst_eq` applies to a translation other than the
identity. -/
theorem permTr_inst_eq {k : ℕ} (σ : _root_.Equiv.Perm (Fin k)) (α : (sigN k).Sym) :
    ∃ (α' : (sigN k).Sym) (ρ : Fin ((sigN k).arity α') ≃ Fin ((sigN k).arity α)),
      ∀ (xs : Fin ((sigN k).arity α) → ℕ) (f : Fin ((permTr σ).net α).internal → ℕ),
        ((permTr σ).net α).inst (fun i => .var (xs i)) f = .app α' fun j => .var (xs (ρ j)) :=
  (permTr_invertible σ).inst_eq α

/-- The cell `con(5, 1)`. -/
abbrev conL : Term sig ℕ := .app (Comb.con : sig.Sym) ![.var 5, .var 1]

/-- The cell `con(2, 3)`. -/
abbrev conR : Term sig ℕ := .app (Comb.con : sig.Sym) ![.var 2, .var 3]

/-- The pair `con(5, 1) = con(2, 3)` with a wire `5 = 0` on its first port: the same graph as the
pair `con(0, 1) = con(2, 3)`, but not the same text. -/
abbrev conPairWire : Net sig ℕ := s(conL, conR) ::ₘ s(.var 5, .var 0) ::ₘ 0

/-- The pair with a wire on a port is the same graph as the pair (Lafont 1997, page 71). -/
theorem conPairWire_equiv :
    Equiv (PairStepE.pairNet (Comb.con : sig.Sym) Comb.con ![0, 1] ![2, 3]) conPairWire := by
  have hv1 : conL.vars = {5, 1} := by decide
  have hv2 : conR.vars = {2, 3} := by decide
  have hlin : Net.Linear (s(.var 5, .var 0) ::ₘ s(conL, conR) ::ₘ (0 : Net sig ℕ)) := by
    intro y
    simp only [Net.vars_cons, eqVars_mk, hv1, hv2, Net.vars_zero, Term.vars_var]
    simp [Multiset.count_cons, Multiset.count_singleton]
    split_ifs <;> omega
  have W := Wire.mk 5 (.var 0) conL conR 0 hlin (by decide)
  have h1 : conL.subst 5 (.var 0) = Term.app (Comb.con : sig.Sym) fun i => .var (![0, 1] i) := by
    unfold Term.subst
    show Term.app _ _ = Term.app _ _
    congr 1
    funext i
    fin_cases i <;> rfl
  have h2 : conR.subst 5 (.var 0) = Term.app (Comb.con : sig.Sym) fun i => .var (![2, 3] i) := by
    unfold Term.subst
    show Term.app _ _ = Term.app _ _
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [h1, h2] at W
  exact W.equiv.symm.trans (Equiv.of_eq (Multiset.cons_swap _ _ _))

/-- **A reduction up to wires of the `con`–`con` pair leaves no cut** (Lafont 1997, page 81):
`System.WellFormed.stepE_pair_not_hasCut` applies to an interaction done after a wire
substitution, which is not a literal interaction of the pair. -/
theorem conPair_stepE_not_hasCut :
    ∃ K, StepE system (PairStepE.pairNet (Comb.con : sig.Sym) Comb.con ![0, 1] ![2, 3]) K ∧
      ¬ K.HasCut := by
  have hs : StepE system (PairStepE.pairNet (Comb.con : sig.Sym) Comb.con ![0, 1] ![2, 3])
      (ruleConCon.inst ![(Term.var 5 : Term sig ℕ), .var 1] ![(Term.var 2 : Term sig ℕ), .var 3]
        (fun w => w.elim0) +
        s((Term.var 5 : Term sig ℕ), .var 0) ::ₘ 0) :=
    ⟨_, conPairWire_equiv, Step.mk (Comb.con : sig.Sym) (Comb.con : sig.Sym) ruleConCon rfl
      ![(Term.var 5 : Term sig ℕ), .var 1] ![(Term.var 2 : Term sig ℕ), .var 3]
      (s((Term.var 5 : Term sig ℕ), .var 0) ::ₘ 0) (fun w => w.elim0)
      (fun w => w.elim0) (fun w => w.elim0)⟩
  have hu : Function.Injective (![0, 1] : Fin (sig.arity (Comb.con : sig.Sym)) → ℕ) := by
    intro a b; revert a b; decide
  have hv : Function.Injective (![2, 3] : Fin (sig.arity (Comb.con : sig.Sym)) → ℕ) := by
    intro a b; revert a b; decide
  have huv : ∀ i j : Fin (sig.arity (Comb.con : sig.Sym)),
      (![0, 1] : Fin 2 → ℕ) i ≠ (![2, 3] : Fin 2 → ℕ) j := by
    change ∀ i j : Fin 2, _
    decide
  exact ⟨_, hs, system_wellFormed.stepE_pair_not_hasCut hu hv huv hs⟩

/-- **`L = M = 1` for the identity translation of the combinators** (Lafont 1997, page 81), from
its compatibility (`Translation.id_compatible`) alone, by
`Translation.Invertible.compatibleWithin_one_of_wellFormed`. -/
example : (Translation.id sig).CompatibleWithin system system 1 1 :=
  (Translation.invertible_id sig).compatibleWithin_one_of_wellFormed system_wellFormed
    system_wellFormed
    (Translation.id_compatible system system_wellFormed)

end INet.SimulationInvertibleCheck
