import InteractionCombinators.Universality.RecursionFree.RecursionFreeTr

/-!
# The translation `[α]` of a recursion-free system is strict (Fig. 6, page 86)

Lafont 1997, Section 1.7, journal page 80: a translation is *strict* when no `[α]` is a wire.
Section 2.4, page 86, Fig. 6: the principal port of `[α]` is the root of the transpositor
`T_{1,1}`, a `dup` cell (`δ`), so `[α]` is never a wire.

* `cellSkel_eq_mkDup` — the root of the tree of Fig. 6 is a `dup` cell.
* `cellPNet_strict`, `cellNet_strict` — the cell of Fig. 6 is strict, whatever the translation
  used for its packages.
* `System.RecursionFreeData.translation_strict` — the translation of a recursion-free system is
  strict.
-/

namespace INet

open Term

namespace Comb

/-- **The root of the cell of Fig. 6** (page 86): the transpositor `T_{1,1}` applied to the menu
`Γ`, the selector on `M_{n+1}` and the loop `ℓ` is a `dup` cell whose left auxiliary port carries
the `con` cell pairing `Γ` with the selector, and whose right auxiliary port is the loop. -/
theorem cellSkel_eq_mkDup (Γ : Term sig ℕ) (m i : ℕ) (ts : List (Term sig ℕ)) (ℓ : ℕ) :
    cellSkel Γ m i ts ℓ = mkDup (mkCon Γ (cellSel m i (mux (ts ++ [var ℓ])))) (var ℓ) :=
  rfl

/-- The root of the cell of Fig. 6 is an application of `dup` (page 86). -/
theorem exists_cellSkel_eq_mkDup (Γ : Term sig ℕ) (m i : ℕ) (ts : List (Term sig ℕ)) (ℓ : ℕ) :
    ∃ a b, cellSkel Γ m i ts ℓ = mkDup a b :=
  ⟨_, _, cellSkel_eq_mkDup Γ m i ts ℓ⟩

/-- **The cell of Fig. 6 is strict** (definition page 80, Fig. 6 page 86): its tree has a `dup`
cell at the root, so it is not a wire. -/
theorem cellPNet_strict (n I : ℕ) (G : List (Term sig ℕ)) (i : ℕ)
    (hG : (menu G).vars = 2 • Multiset.Ico (n + 1) (n + 1 + I)) :
    (cellPNet n I G i hG).Strict := by
  intro x h
  change (cellSkel (menu G) G.length i (List.ofFn fun j : Fin n => var (j : ℕ)) n).bind
    (fun x => var (cellName n I x)) = var x at h
  rw [cellSkel_eq_mkDup] at h
  cases h

variable {S : Signature} [Finite S.Sym] {I : System S}

/-- **`[α]` of Fig. 6 is strict for every translation of its packages** (definition page 80,
Fig. 6 page 86). -/
theorem cellNet_strict (Φ : Translation S sig) (D : I.RecursionFreeData) (α : S.Sym) :
    (cellNet Φ D α).Strict :=
  cellPNet_strict _ _ _ _ _

/-- **The translation of a recursion-free system is strict** (Lafont 1997, definition page 80,
Fig. 6 page 86): no `[α]` is a wire, since its principal port is the root of `T_{1,1}`. -/
theorem _root_.INet.System.RecursionFreeData.translation_strict (D : I.RecursionFreeData) :
    D.translation.Strict := fun α => by
  rw [D.translation_net α]
  exact cellNet_strict _ D α

/-- The translation of the system `systemNoConDup` of page 87 is strict (pages 80, 86–87). -/
theorem translation_noConDup_strict : recursionFreeDataNoConDup.translation.Strict :=
  recursionFreeDataNoConDup.translation_strict

end Comb

end INet
