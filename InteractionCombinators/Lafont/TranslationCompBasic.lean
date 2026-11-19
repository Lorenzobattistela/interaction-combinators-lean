import InteractionCombinators.Lafont.TranslationComp

/-!
# The tree of `Ψ(p)` over `ℕ` (page 80)

Lafont 1997, page 80: "a translation extends to nets in an obvious way".

* `PNet.natTree_ofNat`, `Translation.natTree_trPNet`, `Translation.termTr_trPNet`: the tree of
  `Ψ(p)` over `ℕ` is exactly `Ψ.trTerm` applied to the tree of `p` over `ℕ`, which is a
  translation of it in the sense of `TermTr`. So `trPNet` translates nets "in the obvious way".
* `PNet.Iso.cells_eq`, `Translation.cells_trPNet`: `Iso` keeps the cells.
-/

namespace INet

open Term

namespace PNet

variable {S : Signature} {n : ℕ}

/-- **`ofNat` read back over `ℕ`** (principal nets, page 80): the tree over `ℕ` of `ofNat n m t`,
its port `i` named `i` and its internal wire `w` named `n + w`, is `t`. -/
theorem natTree_ofNat (n m : ℕ) (t : Term S ℕ) (hb : ∀ x ∈ t.vars, x < n + m)
    (hp : ∀ i < n, t.vars.count i = 1) (hw : ∀ w < m, t.vars.count (n + w) = 2) :
    (ofNat n m t hb hp hw).natTree = t := by
  show (((t.toFin hb).bind fun x => var (finSumFinEquiv.symm x)).bind
    fun x => var (Sum.elim (fun i : Fin n => (i : ℕ)) (fun w : Fin m => n + (w : ℕ)) x)) = t
  rw [Term.bind_bind]
  conv_rhs => rw [← Term.bind_toFin t hb]
  refine Term.bind_congr fun x _ => ?_
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective x
  rw [_root_.Equiv.symm_apply_apply]
  cases y <;> simp

/-- Renaming the leaves of a tree keeps its cells. -/
theorem cells_bind_var {ν μ : Type} (g : ν → μ) (t : Term S ν) :
    (t.bind fun x => var (g x)).cells = t.cells := by
  rw [cells_bind]
  simp

/-- **`Iso` keeps the cells** (page 80): principal nets that are the same graph have the same
cells. -/
theorem Iso.cells_eq {p q : PNet S n} (h : p.Iso q) : p.tree.cells = q.tree.cells := by
  obtain ⟨e, he⟩ := h
  rw [← he, cells_bind_var]

/-- The tree over `ℕ` of a principal net has its cells. -/
theorem cells_natTree (p : PNet S n) : p.natTree.cells = p.tree.cells :=
  cells_bind_var _ _

end PNet

namespace Translation

variable {S' S'' : Signature} {n : ℕ}

/-- **`Ψ(p)` is `Ψ` applied to the tree of `p`** (page 80, "a translation extends to nets in an
obvious way"): the tree over `ℕ` of `Ψ.trPNet p` is `Ψ.trTerm` of the tree over `ℕ` of `p`, the
internal wires of the new instances numbered from `n + p.internal`. -/
theorem natTree_trPNet (Ψ : Translation S' S'') (p : PNet S' n) :
    (Ψ.trPNet p).natTree = Ψ.trTerm (n + p.internal) p.natTree :=
  PNet.natTree_ofNat _ _ _ _ _ _

/-- **`Ψ(p)` is a translation of `p`** (page 80): the tree over `ℕ` of `Ψ.trPNet p` is a
translation, in the sense of `TermTr`, of the tree over `ℕ` of `p`. -/
theorem termTr_trPNet (Ψ : Translation S' S'') (p : PNet S' n) :
    Ψ.TermTr p.natTree (Ψ.trPNet p).natTree := by
  rw [natTree_trPNet]
  exact Ψ.termTr_trTerm _ _

/-- The cells of `Ψ(p)` are those of `Ψ.trTerm` of the tree of `p` (page 80). -/
theorem cells_trPNet (Ψ : Translation S' S'') (p : PNet S' n) :
    (Ψ.trPNet p).tree.cells = (Ψ.trTerm (n + p.internal) p.natTree).cells := by
  rw [← PNet.cells_natTree, natTree_trPNet]

end Translation

end INet
