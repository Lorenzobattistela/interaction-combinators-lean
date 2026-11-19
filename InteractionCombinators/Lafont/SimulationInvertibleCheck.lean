import InteractionCombinators.Lafont.SimulationInvertible
import InteractionCombinators.Combinators

/-!
# Checks of `SimulationInvertible.lean` (page 81)

* The hypotheses of `Translation.CompatibleWithin.of_distinct` hold: the identity translation of
  the combinators, compatible within `1` and `1` for all names, is so for distinct names, and
  `of_distinct` gives back the bound for all names.
* `Translation.Invertible.strict` and `Translation.Invertible.inst_eq` apply to a translation
  that is not the identity: `permTr σ` (`TranslationCompReview.lean`) permutes the auxiliary
  ports of its one symbol by any permutation `σ`.

`Translation.Invertible.compatibleWithin_one` is not instantiated here: its hypothesis `hpair`
is not proved for any system yet (see the module docstring of `SimulationInvertible.lean`).
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

end INet.SimulationInvertibleCheck
