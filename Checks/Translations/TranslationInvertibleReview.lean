import Checks.Translations.TranslationCompReview
import Checks.Translations.TranslationInvertibleCheck
import InteractionCombinators.Translations.TranslationRenPerm

/-!
# Review of `Translation.Invertible.net_eq`, `sym` and `symEquiv` (page 81)

Lafont 1997, page 81, top: if `Φ` is invertible, "each `Φ(α)` is necessarily of the following
form [a cell `α'` under a box `σ` on its auxiliary ports] where `α'` is a symbol of `Σ'` and `σ` is
a permutation. In other words, `Φ` is given by a renaming of the symbols and a permutation of the
auxiliary ports of each symbol."

The figure draws `σ` as a box with no arrow, so the paper fixes no direction for it; `net_eq`
reads it from the ports of `α'` to the ports of `Φ(α)`, as `permNet` does (`permNet_eq_permCell`).

The renamings plus permutations (`PNet.permCell`, `Translation.renPermTr`), the converse of
`net_eq` (`Translation.renPermTr_invertible`), the characterization
(`Translation.invertible_iff_renPermTr`) and the lemmas on `sym` and `symEquiv`
(`Translation.net_eq_renPermTr`, `Translation.sym_renPermTr`, `Translation.symEquiv_renPermTr`,
`Translation.Invertible.sym_eq_of_tree`, `Translation.Invertible.symEquiv_symm_eq`,
`Translation.Invertible.sym_inverse_unique`) were first proved here; they are now in the library,
in `InteractionCombinators/Lafont/TranslationRenPerm.lean`. This file keeps:

* `permNet_eq_permCell`, `permTr_eq_renPermTr` — the permutations of `TranslationCompReview` are
  renamings plus permutations, with the same direction.
* `trAB` — a concrete invertible translation between two signatures that swaps two symbols and
  rotates the three ports of one of them (`finRotate 3`, not an involution).
* `trAB_iso_renPermTr` — the characterization applied to `trAB`.
* `loopTr_not_invertible`, `no_repeated_port` — a single cell with an internal wire is not
  invertible, and a single cell with a repeated port is not a principal net.
-/

namespace INet

open Term Translation TranslationCompReview PNet

namespace TranslationInvertibleReview

/-! ## The permutations of `TranslationCompReview` -/

/-- `permNet` of `TranslationCompReview` is a `permCell`, with the same direction of the
permutation (page 81). -/
theorem permNet_eq_permCell {k : ℕ} (σ : _root_.Equiv.Perm (Fin k)) :
    permNet σ = permCell (star k) σ :=
  rfl

/-- `permTr σ` is the renaming plus permutation with the identity renaming (page 81). -/
theorem permTr_eq_renPermTr {k : ℕ} (σ : _root_.Equiv.Perm (Fin k)) :
    permTr σ = renPermTr (fun a => a) (fun _ => σ) :=
  rfl

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

/-- **The characterization on `trAB`** (page 81): the forward direction of
`invertible_iff_renPermTr` applies to `trAB`, and the backward direction gives back that it is
invertible. -/
theorem trAB_iso_renPermTr : ∃ (e : sigA.Sym ≃ sigB.Sym)
    (ρ : ∀ α, Fin (sigB.arity (e α)) ≃ Fin (sigA.arity α)),
      ∀ α, (trAB.net α).Iso ((renPermTr e ρ).net α) :=
  (invertible_iff_renPermTr trAB).1 trAB_invertible

/-- The backward direction of `invertible_iff_renPermTr`, applied to `trAB` itself. -/
theorem trAB_invertible' : trAB.Invertible :=
  (invertible_iff_renPermTr trAB).2 ⟨eAB, ρAB, fun α => PNet.Iso.refl _⟩

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
