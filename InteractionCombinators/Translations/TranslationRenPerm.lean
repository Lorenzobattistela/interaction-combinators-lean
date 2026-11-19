import InteractionCombinators.Translations.TranslationCompAssoc
import InteractionCombinators.Translations.TranslationInvertible

/-!
# Renamings plus permutations are the invertible translations (page 81)

Lafont 1997, page 81, top: if `Φ` is invertible, "each `Φ(α)` is necessarily of the following
form [a cell `α'` under a box `σ` on its auxiliary ports] where `α'` is a symbol of `Σ'` and `σ` is
a permutation. In other words, `Φ` is given by a renaming of the symbols and a permutation of the
auxiliary ports of each symbol."

`Translation.Invertible.exists_symEquiv` (`Lafont/TranslationInvertible.lean`) proves that an
invertible translation has this form. This file gives the converse and the characterization.

The figure draws `σ` as a box with no arrow, so the paper fixes no direction for it; here, as in
`Invertible.net_eq`, it is read from the ports of `α'` to the ports of `Φ(α)`.

* `PNet.permCell β σ`, `Translation.renPermTr e ρ`: a renaming of the symbols and a permutation
  of the ports.
* `renPermTr_invertible`: every renaming plus permutation is invertible.
* `Invertible.of_iso`: invertibility depends only on the nets `Φ(α)` up to `Iso`.
* `invertible_iff_renPermTr`: the invertible translations are exactly the renamings plus
  permutations, up to `Iso`.
* `net_eq_renPermTr`, `sym_renPermTr`, `symEquiv_renPermTr`: on a renaming plus permutation,
  `net_eq` returns the given permutation and `sym`, `symEquiv` the given renaming.
* `Invertible.sym_eq_of_tree`, `Invertible.symEquiv_symm_eq`, `Invertible.sym_inverse_unique`:
  `sym` depends only on `Φ`, and the inverse of `symEquiv` is the renaming of every inverse of
  `Φ`, not only of the inverse chosen in its definition.

These results were first proved in `Checks/TranslationInvertibleReview.lean`.
-/

namespace INet

open Term

namespace PNet

variable {S : Signature}

/-- **A permuted cell** (page 81, the figure at the top): the cell `β` with its auxiliary ports
permuted by `σ`, its auxiliary port `j` being the port `σ j` of the net. It has no internal
wire. -/
def permCell {n : ℕ} (β : S.Sym) (σ : Fin (S.arity β) ≃ Fin n) : PNet S n where
  internal := 0
  tree := .app β fun j => .var (.inl (σ j))
  port_count i := by
    rw [Term.vars_app, Multiset.count_sum']
    simp only [Term.vars_var, Multiset.count_singleton, Sum.inl.injEq]
    rw [← _root_.Equiv.sum_comp σ.symm]
    simp
  internal_count w := w.elim0

/-- A permuted cell whose symbol is `α` and whose permutation keeps every port is the cell `α`
(page 81). -/
theorem permCell_eq_cell {α β : S.Sym} (hβ : β = α) (σ : Fin (S.arity β) ≃ Fin (S.arity α))
    (hσ : ∀ j, (σ j : ℕ) = j) : permCell β σ = PNet.cell α := by
  subst hβ
  have : σ = _root_.Equiv.refl _ := _root_.Equiv.ext fun j => Fin.ext (hσ j)
  subst this
  rfl

end PNet

namespace Translation

open PNet

variable {S S' S'' : Signature}

/-! ## Renamings plus permutations -/

/-- **A renaming of the symbols and a permutation of the ports** (page 81): `α` is translated to
the cell `e α`, its auxiliary port `j` plugged into the port `ρ α j`. -/
def renPermTr (e : S.Sym → S'.Sym) (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α)) :
    Translation S S' :=
  ⟨fun α => permCell (e α) (ρ α)⟩

/-- **The translation of a permuted cell by a renaming plus permutation** (pages 80-81): it is
the renamed cell, with the two permutations composed. -/
theorem trPNet_permCell (e : S'.Sym → S''.Sym)
    (ρ : ∀ β, Fin (S''.arity (e β)) ≃ Fin (S'.arity β))
    {n : ℕ} (β : S'.Sym) (σ : Fin (S'.arity β) ≃ Fin n) :
    ((renPermTr e ρ).trPNet (permCell β σ)).Iso (permCell (e β) ((ρ β).trans σ)) := by
  have hs : (renPermTr e ρ).size (permCell β σ).natTree = 0 := by
    show 0 + ∑ i, (renPermTr e ρ).size (Term.var (σ i : ℕ)) = 0
    simp [Translation.size]
  have hm : (permCell (e β) ((ρ β).trans σ)).internal =
      0 + (renPermTr e ρ).size (permCell β σ).natTree := by
    rw [hs]
    rfl
  have hy := (renPermTr e ρ).trPNet_hyps (permCell β σ)
  exact PNet.iso_ofNat (permCell (e β) ((ρ β).trans σ)) (finCongr hm) hy.1 hy.2.1 hy.2.2 rfl

/-- The permutation of the inverse of a renaming plus permutation, applied after `ρ β`, keeps the
ports (page 81). -/
theorem val_renPerm_symm_finCongr (e : S.Sym → S'.Sym)
    (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α))
    {α β : S.Sym} (hβ : β = α) (h : S'.arity (e β) = S'.arity (e α)) (j : Fin (S.arity β)) :
    (ρ α (finCongr h ((ρ β).symm j)) : ℕ) = j := by
  subst hβ
  simp

/-- The permutations of the inverse of `renPermTr e ρ` (page 81): the port `j` of the cell
`e.symm α'` is the port `ρ⁻¹ j` of the net, read back in the arity of `α'`. -/
def renPermInv (e : S.Sym ≃ S'.Sym) (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α))
    (α' : S'.Sym) : Fin (S.arity (e.symm α')) ≃ Fin (S'.arity α') :=
  (ρ (e.symm α')).symm.trans (finCongr (congrArg S'.arity (e.apply_symm_apply α')))

/-- **Every renaming plus permutation is invertible** (page 81, the converse of
`Translation.Invertible.net_eq`): its inverse renames by `e⁻¹` and permutes by `ρ⁻¹`. -/
theorem renPermTr_invertible (e : S.Sym ≃ S'.Sym)
    (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α)) : (renPermTr e ρ).Invertible := by
  refine ⟨renPermTr e.symm (renPermInv e ρ), fun α => ?_, fun α' => ?_⟩
  · refine (trPNet_permCell _ _ _ _).trans ?_
    rw [permCell_eq_cell (e.symm_apply_apply α)]
    · exact PNet.Iso.refl _
    · intro j
      exact val_renPerm_symm_finCongr e ρ (e.symm_apply_apply α)
        (congrArg S'.arity (e.apply_symm_apply (e α))) j
  · refine (trPNet_permCell _ _ _ _).trans ?_
    rw [permCell_eq_cell (e.apply_symm_apply α')]
    · exact PNet.Iso.refl _
    · intro j
      simp [renPermInv]

/-! ## The characterization -/

/-- **Invertibility depends only on the graphs `Φ(α)`** (page 80): if `Φ` is invertible and
`Φ'(α)` is the same graph as `Φ(α)` for every `α`, then `Φ'` is invertible, with the same
inverse. -/
theorem Invertible.of_iso {Φ Φ' : Translation S S'} (h : Φ.Invertible)
    (hΦ : ∀ α, (Φ.net α).Iso (Φ'.net α)) : Φ'.Invertible := by
  obtain ⟨Ψ, h1, h2⟩ := h
  exact ⟨Ψ, fun α => ((comp_iso_right Ψ hΦ α).symm).trans (h1 α),
    fun α' => ((comp_iso_left Ψ hΦ α').symm).trans (h2 α')⟩

/-- An invertible translation sends `α` to the permuted cell of its root, up to the names of
internal wires (page 81): `Φ(α)` has no internal wire and is the cell `e α` with its port `j`
plugged into `ρ j`. -/
theorem Invertible.iso_permCell {Φ : Translation S S'} (h : Φ.Invertible) {α : S.Sym}
    {β : S'.Sym} (ρ : Fin (S'.arity β) ≃ Fin (S.arity α))
    (hρ : (Φ.net α).tree = Term.app β (fun j => Term.var (Sum.inl (ρ j)))) :
    (Φ.net α).Iso (permCell β ρ) := by
  refine ⟨finCongr (h.internal_eq_zero α), ?_⟩
  rw [hρ, Term.bind_app]
  rfl

/-- **The invertible translations are the renamings plus permutations** (page 81, top: "`Φ` is
given by a renaming of the symbols and a permutation of the auxiliary ports of each symbol"):
`Φ` is invertible if and only if there are a bijection `e` of the symbols and, for each `α`, a
bijection `ρ α` from the auxiliary ports of `e α` to those of `α`, such that every `Φ(α)` is the
same graph as the cell `e α` with its port `j` plugged into the port `ρ α j`. -/
theorem invertible_iff_renPermTr (Φ : Translation S S') :
    Φ.Invertible ↔ ∃ (e : S.Sym ≃ S'.Sym) (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α)),
      ∀ α, (Φ.net α).Iso ((renPermTr e ρ).net α) := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := h.exists_symEquiv
    choose ρ hρ using he
    exact ⟨e, ρ, fun α => h.iso_permCell (ρ α) (hρ α)⟩
  · rintro ⟨e, ρ, hΦ⟩
    exact (renPermTr_invertible e ρ).of_iso fun α => (hΦ α).symm

/-! ## What `net_eq`, `sym` and `symEquiv` return -/

/-- **`net_eq` returns the given renaming and permutation** (page 81): if the tree of
`renPermTr e ρ` at `α` is the cell `α'` with its port `j` plugged into `ρ' j`, then `α' = e α` and
`ρ'` is `ρ α`. -/
theorem net_eq_renPermTr (e : S.Sym → S'.Sym) (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α))
    {α : S.Sym} {α' : S'.Sym} {ρ' : Fin (S'.arity α') ≃ Fin (S.arity α)}
    (hρ : ((renPermTr e ρ).net α).tree = Term.app α' (fun j => Term.var (Sum.inl (ρ' j)))) :
    α' = e α ∧ HEq ρ' (ρ α) := by
  obtain ⟨h1, h2⟩ := Term.app.inj hρ
  subst h1
  refine ⟨rfl, heq_of_eq (_root_.Equiv.ext fun j => ?_)⟩
  have h3 := congrFun (eq_of_heq h2) j
  exact (Sum.inl_injective (Term.var.inj h3)).symm

/-- **`sym` depends only on `Φ`** (page 81): whatever proof of invertibility is used, `h.sym α` is
the root symbol of `Φ(α)`. -/
theorem Invertible.sym_eq_of_tree {Φ : Translation S S'} (h : Φ.Invertible) {α : S.Sym}
    {β : S'.Sym} {ts : Fin (S'.arity β) → Term S' (Fin (S.arity α) ⊕ Fin (Φ.net α).internal)}
    (ht : (Φ.net α).tree = Term.app β ts) : h.sym α = β := by
  obtain ⟨ρ, hρ⟩ := h.net_eq_sym α
  rw [hρ] at ht
  exact (Term.app.inj ht).1

/-- The renaming of `renPermTr e ρ` is `e` (page 81). -/
theorem sym_renPermTr (e : S.Sym → S'.Sym) (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α))
    (h : (renPermTr e ρ).Invertible) (α : S.Sym) : h.sym α = e α :=
  h.sym_eq_of_tree rfl

/-- **The inverse of `symEquiv` is the renaming of any inverse of `Φ`** (page 81), not only of
the inverse chosen by `symEquiv`. -/
theorem Invertible.symEquiv_symm_eq {Φ : Translation S S'} (h : Φ.Invertible)
    {Ψ : Translation S' S}
    (h1 : ∀ α, ((Ψ.comp Φ).net α).Iso ((Translation.id S).net α))
    (h2 : ∀ α', ((Φ.comp Ψ).net α').Iso ((Translation.id S').net α')) (α' : S'.Sym) :
    h.symEquiv.symm α' = (Invertible.inverse h1 h2).sym α' := by
  rw [_root_.Equiv.symm_apply_eq]
  exact (Invertible.sym_sym (Invertible.inverse h1 h2) h (h2 α')).symm

/-- **Two inverses of `Φ` rename the symbols in the same way** (page 81). -/
theorem Invertible.sym_inverse_unique {Φ : Translation S S'} (h : Φ.Invertible)
    {Ψ Ψ' : Translation S' S}
    (h1 : ∀ α, ((Ψ.comp Φ).net α).Iso ((Translation.id S).net α))
    (h2 : ∀ α', ((Φ.comp Ψ).net α').Iso ((Translation.id S').net α'))
    (h1' : ∀ α, ((Ψ'.comp Φ).net α).Iso ((Translation.id S).net α))
    (h2' : ∀ α', ((Φ.comp Ψ').net α').Iso ((Translation.id S').net α')) :
    (Invertible.inverse h1 h2).sym = (Invertible.inverse h1' h2').sym :=
  funext fun α' => (h.symEquiv_symm_eq h1 h2 α').symm.trans (h.symEquiv_symm_eq h1' h2' α')

/-- `symEquiv` of a renaming plus permutation is the renaming (page 81). -/
theorem symEquiv_renPermTr (e : S.Sym ≃ S'.Sym)
    (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α)) (h : (renPermTr e ρ).Invertible) :
    h.symEquiv = e :=
  _root_.Equiv.ext fun α => sym_renPermTr e ρ h α

end Translation

end INet
