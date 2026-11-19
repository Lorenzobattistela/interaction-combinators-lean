import InteractionCombinators.Lafont.TranslationInvertibleCheck

/-!
# Review of `Translation.Invertible.net_eq`, `sym` and `symEquiv` (page 81)

Lafont 1997, page 81, top: if `Φ` is invertible, "each `Φ(α)` is necessarily of the following
form [a cell `α'` under a box `σ` on its auxiliary ports] where `α'` is a symbol of `Σ'` and `σ` is
a permutation. In other words, `Φ` is given by a renaming of the symbols and a permutation of the
auxiliary ports of each symbol."

The figure draws `σ` as a box with no arrow, so the paper fixes no direction for it; `net_eq`
reads it from the ports of `α'` to the ports of `Φ(α)`, as `permNet` does (`permNet_eq_permCell`).

* `permCell β σ`, `renPermTr e ρ` — a renaming of the symbols and a permutation of the ports.
* `renPermTr_invertible` — **the converse of `net_eq`**: every renaming plus permutation is
  invertible. With `exists_symEquiv`, the invertible translations are exactly those of the figure.
* `net_eq_renPermTr`, `sym_renPermTr` — on such a translation, `net_eq` returns the given `ρ` and
  `sym` the given renaming.
* `sym_eq_of_tree`, `symEquiv_symm_eq`, `sym_inverse_unique` — `sym` depends only on `Φ`, and
  the inverse of `symEquiv` is the renaming of *every* inverse of `Φ`, not only of the inverse
  chosen in its definition.
* `trAB` — a concrete invertible translation between two signatures that swaps two symbols and
  rotates the three ports of one of them (`finRotate 3`, not an involution).
* `loopTr_not_invertible`, `no_repeated_port` — a single cell with an internal wire is not
  invertible, and a single cell with a repeated port is not a principal net.
-/

namespace INet

open Term Translation TranslationCompReview

namespace TranslationInvertibleReview

variable {S S' S'' : Signature}

/-! ## Renamings plus permutations -/

/-- The cell `β` with its auxiliary ports permuted by `σ`: its auxiliary port `j` is the port
`σ j` of the net (the form of the figure of page 81). -/
def permCell {n : ℕ} (β : S.Sym) (σ : Fin (S.arity β) ≃ Fin n) : PNet S n where
  internal := 0
  tree := .app β fun j => .var (.inl (σ j))
  port_count i := by
    rw [Term.vars_app, Multiset.count_sum']
    simp only [Term.vars_var, Multiset.count_singleton, Sum.inl.injEq]
    rw [← _root_.Equiv.sum_comp σ.symm]
    simp
  internal_count w := w.elim0

/-- `permNet` of `TranslationCompReview` is a `permCell`, with the same direction of the
permutation (page 81). -/
theorem permNet_eq_permCell {k : ℕ} (σ : _root_.Equiv.Perm (Fin k)) :
    permNet σ = permCell (star k) σ :=
  rfl

/-- **A renaming of the symbols and a permutation of the ports** (page 81): `α` is translated to
the cell `e α`, its auxiliary port `j` plugged into the port `ρ α j`. -/
def renPermTr (e : S.Sym → S'.Sym) (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α)) :
    Translation S S' :=
  ⟨fun α => permCell (e α) (ρ α)⟩

/-- `permTr σ` is the renaming plus permutation with the identity renaming (page 81). -/
theorem permTr_eq_renPermTr {k : ℕ} (σ : _root_.Equiv.Perm (Fin k)) :
    permTr σ = renPermTr (fun a => a) (fun _ => σ) :=
  rfl

/-- **The translation of a permuted cell by a renaming plus permutation** (pages 80–81): it is the
renamed cell, with the two permutations composed. -/
theorem trPNet_permCell (e : S'.Sym → S''.Sym) (ρ : ∀ β, Fin (S''.arity (e β)) ≃ Fin (S'.arity β))
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

/-- A permuted cell whose symbol is `α` and whose permutation keeps every port is the cell `α`. -/
theorem permCell_eq_cell {α β : S.Sym} (hβ : β = α) (σ : Fin (S.arity β) ≃ Fin (S.arity α))
    (hσ : ∀ j, (σ j : ℕ) = j) : permCell β σ = PNet.cell α := by
  subst hβ
  have : σ = _root_.Equiv.refl _ := _root_.Equiv.ext fun j => Fin.ext (hσ j)
  subst this
  rfl

/-- The permutation of the inverse, applied after `ρ β`, keeps the ports. -/
theorem val_symm_finCongr (e : S.Sym → S'.Sym) (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α))
    {α β : S.Sym} (hβ : β = α) (h : S'.arity (e β) = S'.arity (e α)) (j : Fin (S.arity β)) :
    (ρ α (finCongr h ((ρ β).symm j)) : ℕ) = j := by
  subst hβ
  simp

/-- The permutations of the inverse of `renPermTr e ρ`: the port `j` of the cell `e.symm α'` is
the port `ρ⁻¹ j` of the net, read back in the arity of `α'`. -/
def invPerm (e : S.Sym ≃ S'.Sym) (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α)) (α' : S'.Sym) :
    Fin (S.arity (e.symm α')) ≃ Fin (S'.arity α') :=
  (ρ (e.symm α')).symm.trans (finCongr (congrArg S'.arity (e.apply_symm_apply α')))

/-- **Every renaming plus permutation is invertible** (page 81, the converse of
`Translation.Invertible.net_eq`): its inverse renames by `e⁻¹` and permutes by `ρ⁻¹`. -/
theorem renPermTr_invertible (e : S.Sym ≃ S'.Sym)
    (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α)) : (renPermTr e ρ).Invertible := by
  refine ⟨renPermTr e.symm (invPerm e ρ), fun α => ?_, fun α' => ?_⟩
  · refine (trPNet_permCell _ _ _ _).trans ?_
    rw [permCell_eq_cell (e.symm_apply_apply α)]
    · exact PNet.Iso.refl _
    · intro j
      exact val_symm_finCongr e ρ (e.symm_apply_apply α)
        (congrArg S'.arity (e.apply_symm_apply (e α))) j
  · refine (trPNet_permCell _ _ _ _).trans ?_
    rw [permCell_eq_cell (e.apply_symm_apply α')]
    · exact PNet.Iso.refl _
    · intro j
      simp [invPerm]

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
theorem sym_eq_of_tree {Φ : Translation S S'} (h : Φ.Invertible) {α : S.Sym} {β : S'.Sym}
    {ts : Fin (S'.arity β) → Term S' (Fin (S.arity α) ⊕ Fin (Φ.net α).internal)}
    (ht : (Φ.net α).tree = Term.app β ts) : h.sym α = β := by
  obtain ⟨ρ, hρ⟩ := h.net_eq_sym α
  rw [hρ] at ht
  exact (Term.app.inj ht).1

/-- The renaming of `renPermTr e ρ` is `e` (page 81). -/
theorem sym_renPermTr (e : S.Sym → S'.Sym) (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α))
    (h : (renPermTr e ρ).Invertible) (α : S.Sym) : h.sym α = e α :=
  sym_eq_of_tree h rfl

/-- **The inverse of `symEquiv` is the renaming of any inverse of `Φ`** (page 81), not only of
the inverse chosen by `symEquiv`. -/
theorem symEquiv_symm_eq {Φ : Translation S S'} (h : Φ.Invertible) {Ψ : Translation S' S}
    (h1 : ∀ α, ((Ψ.comp Φ).net α).Iso ((Translation.id S).net α))
    (h2 : ∀ α', ((Φ.comp Ψ).net α').Iso ((Translation.id S').net α')) (α' : S'.Sym) :
    h.symEquiv.symm α' = (Invertible.inverse h1 h2).sym α' := by
  rw [_root_.Equiv.symm_apply_eq]
  exact (Invertible.sym_sym (Invertible.inverse h1 h2) h (h2 α')).symm

/-- **Two inverses of `Φ` rename the symbols in the same way** (page 81). -/
theorem sym_inverse_unique {Φ : Translation S S'} (h : Φ.Invertible) {Ψ Ψ' : Translation S' S}
    (h1 : ∀ α, ((Ψ.comp Φ).net α).Iso ((Translation.id S).net α))
    (h2 : ∀ α', ((Φ.comp Ψ).net α').Iso ((Translation.id S').net α'))
    (h1' : ∀ α, ((Ψ'.comp Φ).net α).Iso ((Translation.id S).net α))
    (h2' : ∀ α', ((Φ.comp Ψ').net α').Iso ((Translation.id S').net α')) :
    (Invertible.inverse h1 h2).sym = (Invertible.inverse h1' h2').sym :=
  funext fun α' => (symEquiv_symm_eq h h1 h2 α').symm.trans (symEquiv_symm_eq h h1' h2' α')

/-- `symEquiv` of a renaming plus permutation is the renaming (page 81). -/
theorem symEquiv_renPermTr (e : S.Sym ≃ S'.Sym)
    (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α)) (h : (renPermTr e ρ).Invertible) :
    h.symEquiv = e :=
  _root_.Equiv.ext fun α => sym_renPermTr e ρ h α

/-! ## A concrete invertible translation between two signatures -/

/-- Two symbols: `true` of arity `3` and `false` of arity `0`. -/
def sigA : Signature := ⟨Bool, fun b => match b with | true => 3 | false => 0⟩

/-- Two symbols: `true` of arity `0` and `false` of arity `3`. -/
def sigB : Signature := ⟨Bool, fun b => match b with | true => 0 | false => 3⟩

/-- The renaming that swaps the two symbols. -/
def eAB : sigA.Sym ≃ sigB.Sym := ⟨not, not, Bool.not_not, Bool.not_not⟩

/-- The permutations: the three ports of `true` are rotated by `finRotate 3`. -/
def ρAB : ∀ α : sigA.Sym, Fin (sigB.arity (eAB α)) ≃ Fin (sigA.arity α)
  | true => finRotate 3
  | false => _root_.Equiv.refl (Fin 0)

/-- The translation of `sigA` into `sigB` that swaps the symbols and rotates the ports of the
symbol of arity `3`. -/
def trAB : Translation sigA sigB := renPermTr eAB ρAB

/-- The rotation of three ports is not an involution: the check below is not one where `ρ` and
its inverse could be confused. -/
theorem finRotate_three_not_involutive :
    (finRotate 3).trans (finRotate 3) ≠ _root_.Equiv.refl (Fin 3) := fun h => by
  have h0 := congrArg (fun f : _root_.Equiv.Perm (Fin 3) => f 0) h
  revert h0
  decide

/-- **`trAB` is invertible** (page 81). -/
theorem trAB_invertible : trAB.Invertible :=
  renPermTr_invertible eAB ρAB

/-- **The renaming of `trAB` is the swap of the symbols** (page 81). -/
theorem trAB_symEquiv : trAB_invertible.symEquiv = eAB :=
  symEquiv_renPermTr eAB ρAB trAB_invertible

/-- **`net_eq` on `trAB` at the symbol of arity `3`** (page 81): it returns the symbol `false` of
`sigB` and the rotation `finRotate 3`. -/
theorem trAB_net_eq : ∃ (α' : sigB.Sym) (ρ : Fin (sigB.arity α') ≃ Fin (sigA.arity true)),
    (trAB.net true).tree = Term.app α' (fun j => Term.var (Sum.inl (ρ j))) ∧
      α' = false ∧ HEq ρ (finRotate 3) := by
  obtain ⟨α', ρ, hρ⟩ := trAB_invertible.net_eq true
  obtain ⟨h1, h2⟩ := net_eq_renPermTr eAB ρAB hρ
  exact ⟨α', ρ, hρ, h1, h2⟩

/-! ## A single cell with an internal wire, or with a repeated port -/

/-- The cell of arity `2` whose two auxiliary ports are joined by an internal wire: a principal
net of arity `0` with one cell and one internal wire. -/
def loopNet : PNet (sigN 2) 0 where
  internal := 1
  tree := .app (star 2) fun _ => .var (.inr 0)
  port_count i := i.elim0
  internal_count w := by
    fin_cases w
    rw [Term.vars_app, Multiset.count_sum']
    simp
    rfl

/-- The translation of the symbol of arity `0` to the loop. -/
def loopTr : Translation (sigN 0) (sigN 2) := ⟨fun _ => loopNet⟩

/-- The loop has one cell, so `card_cells` alone does not exclude it. -/
theorem loopTr_card_cells : Multiset.card (loopTr.net (star 0)).tree.cells = 1 := by
  show Multiset.card (Term.app (star 2) fun _ => Term.var (Sum.inr 0) :
    Term (sigN 2) (Fin 0 ⊕ Fin 1)).cells = 1
  rw [Term.cells_app]
  simp

/-- **A single cell with an internal wire is not invertible** (page 81), by
`Translation.Invertible.internal_eq_zero`. -/
theorem loopTr_not_invertible : ¬ loopTr.Invertible := fun h =>
  Nat.one_ne_zero (h.internal_eq_zero (star 0))

/-- **A single cell with a repeated port is not a principal net** (page 80): no principal net of
arity `1` is the cell of arity `2` with both auxiliary ports on the port `0`. -/
theorem no_repeated_port :
    ¬ ∃ p : PNet (sigN 2) 1, p.tree = Term.app (star 2) fun _ => .var (.inl 0) := by
  rintro ⟨p, hp⟩
  have h := p.port_count 0
  rw [hp] at h
  rw [Term.vars_app, Multiset.count_sum'] at h
  simp at h
  exact absurd h (by decide)

end TranslationInvertibleReview

end INet
