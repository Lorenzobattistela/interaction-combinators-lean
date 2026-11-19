import InteractionCombinators.Lafont.TranslationInvertible

/-!
# Checks of `Translation.Invertible.net_eq` (page 81)

* `sym_id` — the renaming of the identity translation is the identity.
* `permTr_net_eq` — for the port permutation `permTr σ` of `TranslationCompReview`, the bijection
  `ρ` of `net_eq` is `σ` itself: `net_eq` reads the permutation the right way round.
* `not_invertible_of_two_cells` — a translation that sends some symbol to two cells is not
  invertible (the contrapositive of `card_cells`), which gives back `twoCells_not_invertible`.
-/

namespace INet

open Term Translation TranslationCompReview

namespace TranslationInvertibleCheck

/-- **The identity renames nothing** (page 81): the renaming of symbols of `id_S` is the identity,
whichever proof of invertibility is used. -/
theorem sym_id {S : Signature} (h : (Translation.id S).Invertible) (α : S.Sym) : h.sym α = α := by
  obtain ⟨ρ, hρ⟩ := h.net_eq_sym α
  exact (Term.app.inj hρ).1.symm

/-- **The renaming of `id_S` is the identity equivalence** (page 81). -/
theorem symEquiv_id (S : Signature) :
    (invertible_id S).symEquiv = _root_.Equiv.refl S.Sym :=
  _root_.Equiv.ext fun α => sym_id (invertible_id S) α

/-- **The permutation of `net_eq` is read the right way round** (page 81): for `permTr σ`, the cell
whose auxiliary port `j` is the port `σ j`, every `ρ` given by `net_eq` is `σ`. -/
theorem permTr_net_eq {k : ℕ} (σ : _root_.Equiv.Perm (Fin k)) {α' : (sigN k).Sym}
    {ρ : Fin ((sigN k).arity α') ≃ Fin k}
    (hρ : ((permTr σ).net (star k)).tree = Term.app α' (fun j => Term.var (Sum.inl (ρ j)))) :
    HEq ρ σ := by
  have h := Term.app.inj hρ
  obtain ⟨-, h2⟩ := h
  cases α'
  have h3 := eq_of_heq h2
  refine heq_of_eq (_root_.Equiv.ext fun j => ?_)
  have h4 : (Term.var (Sum.inl (σ j)) : Term (sigN k) (Fin k ⊕ Fin 0)) =
      Term.var (Sum.inl (ρ j)) := congrFun h3 j
  simp only [Term.var.injEq, Sum.inl.injEq] at h4
  exact h4.symm

/-- `net_eq` applies to `permTr σ`, which is invertible, and returns `σ` (page 81). -/
theorem permTr_net_eq_exists {k : ℕ} (σ : _root_.Equiv.Perm (Fin k)) :
    ∃ (α' : (sigN k).Sym) (ρ : Fin ((sigN k).arity α') ≃ Fin k),
      ((permTr σ).net (star k)).tree = Term.app α' (fun j => Term.var (Sum.inl (ρ j))) ∧
        HEq ρ σ := by
  obtain ⟨α', ρ, hρ⟩ := (permTr_invertible σ).net_eq (star k)
  exact ⟨α', ρ, hρ, permTr_net_eq σ hρ⟩

/-- **Two cells are not invertible** (page 81): a translation with a symbol sent to a principal
net with two cells is not invertible. -/
theorem not_invertible_of_two_cells {S S' : Signature} {Φ : Translation S S'} {α : S.Sym}
    (h2 : Multiset.card (Φ.net α).tree.cells = 2) : ¬ Φ.Invertible := fun h => by
  have := h.card_cells α
  omega

/-- `twoCellsTr` of `TranslationCompReview`, which sends the symbol to `β(γ(x₀), x₁)`, is not
invertible, by `not_invertible_of_two_cells` (page 81). -/
theorem twoCellsTr_not_invertible : ¬ twoCellsTr.Invertible :=
  not_invertible_of_two_cells (α := star 2) (by decide)

end TranslationInvertibleCheck

end INet
