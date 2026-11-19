import InteractionCombinators.Lafont.TranslationCompAssoc

/-!
# Checks for `Lafont/TranslationCompAssoc.lean`

The translations `permTr σ` of `TranslationCompReview.lean` send the single symbol of `sigN 3` to
itself with its three auxiliary ports permuted by `σ`. For `σ` the rotation of the ports, `permTr σ`
is not the identity (`rot_not_id`), so these checks use `comp_assoc`, `comp_iso_left` and
`Invertible.comp` on translations that move ports, not on the identity.
-/

namespace INet.TranslationCompAssocCheck

open Translation PNet TranslationCompReview

/-- The rotation of the three ports. -/
abbrev ρ : _root_.Equiv.Perm (Fin 3) := finRotate 3

/-- The transposition of the ports `0` and `1`. -/
abbrev σ : _root_.Equiv.Perm (Fin 3) := _root_.Equiv.swap 0 1

/-- The transposition of the ports `1` and `2`. -/
abbrev τ : _root_.Equiv.Perm (Fin 3) := _root_.Equiv.swap 1 2

/-- `permTr ρ` is not the identity translation (page 81): `Iso` keeps the ports, so it sees the
rotation. -/
theorem rot_not_id : ¬ ((permTr ρ).net (star 3)).Iso ((Translation.id (sigN 3)).net (star 3)) := by
  intro h
  rw [show (Translation.id (sigN 3)).net (star 3) = permNet (_root_.Equiv.refl (Fin 3)) from rfl]
    at h
  have hst := congrArg (fun f : _root_.Equiv.Perm (Fin 3) => f 0) (permNet_iso h)
  revert hst
  decide

/-- **Associativity on three translations that move ports** (page 80). -/
theorem assoc_perm :
    ((((permTr τ).comp (permTr σ)).comp (permTr ρ)).net (star 3)).Iso
      (((permTr τ).comp ((permTr σ).comp (permTr ρ))).net (star 3)) :=
  comp_assoc _ _ _ _

/-- **Composing respects `Iso` on the left, on an example** (page 80): replacing
`permTr τ ∘ permTr σ` by `permTr (τ.trans σ)`, the composite with `permTr ρ` is the cell with its
ports permuted by `(τ.trans σ).trans ρ`. -/
theorem comp_iso_left_perm :
    ((((permTr τ).comp (permTr σ)).comp (permTr ρ)).net (star 3)).Iso
      (permNet ((τ.trans σ).trans ρ)) :=
  (comp_iso_left (permTr ρ) (fun _ => comp_permTr τ σ) (star 3)).trans (comp_permTr _ _)

/-- **Both bracketings give the same permutation** (page 80): the permutations of the ports read
from the two sides of `assoc_perm` agree. -/
theorem assoc_perm_eq :
    ((τ.trans σ).trans ρ : _root_.Equiv.Perm (Fin 3)) = τ.trans (σ.trans ρ) := by
  have h2 : (((permTr τ).comp ((permTr σ).comp (permTr ρ))).net (star 3)).Iso
      (permNet (τ.trans (σ.trans ρ))) :=
    (comp_iso_right (permTr τ) (fun _ => comp_permTr σ ρ) (star 3)).trans (comp_permTr _ _)
  exact permNet_iso ((comp_iso_left_perm.symm.trans assoc_perm).trans h2)

/-- **The composite of invertible translations is invertible, on an example** (page 80):
`permTr ρ ∘ permTr ρ` is invertible, and it is not the identity
(`permTr_rot_comp_self_not_iso`). -/
theorem rot_comp_rot_invertible : ((permTr ρ).comp (permTr ρ)).Invertible :=
  (permTr_invertible ρ).comp (permTr_invertible ρ)

/-- `permTr ρ ∘ permTr ρ` is not the identity, so `rot_comp_rot_invertible` is not about the
identity. -/
theorem rot_comp_rot_not_id :
    ¬ (((permTr ρ).comp (permTr ρ)).net (star 3)).Iso ((Translation.id (sigN 3)).net (star 3)) :=
  permTr_rot_comp_self_not_iso

end INet.TranslationCompAssocCheck
