import InteractionCombinators.Lafont.TranslationComp

/-!
# Checks of `Translation.comp` and `Translation.Invertible` (page 80)

`Invertible` is neither trivially true nor reduced to the identity:

* `merge_not_invertible` — the translation sending two symbols of arity `0` to the same cell is
  not invertible: an inverse would send that cell to both symbols.
* `swap_invertible` — the translation exchanging two symbols of arity `0` is invertible, its own
  inverse.
-/

namespace INet.TranslationCompCheck

open Translation PNet

/-- Two symbols, `true` and `false`, both of arity `0`. -/
def twoSig : Signature := ⟨Bool, fun _ => 0⟩

/-- Both symbols are translated to the cell `true`. -/
def merge : Translation twoSig twoSig := ⟨fun _ => PNet.cell (S := twoSig) true⟩

/-- **A translation that is not invertible** (page 80): `merge` sends the symbols `true` and
`false` to the same cell. An inverse `Ψ` would make `Ψ(merge(true)) = Ψ(merge(false))` equal both
to the cell `true` and to the cell `false` up to the names of internal wires, but `Iso` keeps the
root symbol. -/
theorem merge_not_invertible : ¬ merge.Invertible := by
  rintro ⟨Ψ, h, -⟩
  have h1 : (Ψ.trPNet (PNet.cell (S := twoSig) true)).Iso (PNet.cell (S := twoSig) true) :=
    h true
  have h2 : (Ψ.trPNet (PNet.cell (S := twoSig) true)).Iso (PNet.cell (S := twoSig) false) :=
    h false
  obtain ⟨ts1, e1⟩ := h1.symm.root (α := true) rfl
  obtain ⟨ts2, e2⟩ := h2.symm.root (α := false) rfl
  rw [e1] at e2
  injection e2 with e3
  cases e3

/-- The symbols `true` and `false` exchanged. -/
def swap : Translation twoSig twoSig := ⟨fun b => PNet.cell (S := twoSig) (!b)⟩

/-- **An invertible translation other than the identity** (page 80): `swap` is its own inverse. -/
theorem swap_invertible : swap.Invertible := by
  have key : ∀ b : Bool, ((swap.comp swap).net b).Iso ((Translation.id twoSig).net b) := by
    intro b
    cases b
    · exact swap.comp_id true
    · exact swap.comp_id false
  exact ⟨swap, key, key⟩

end INet.TranslationCompCheck
