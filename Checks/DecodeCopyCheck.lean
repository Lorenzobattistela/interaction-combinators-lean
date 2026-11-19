import InteractionCombinators.Lafont.DecodeCopy
import Checks.DecodeReview

/-!
# A concrete check of `code_decoder_copy` (pages 89 and 90)

`code_decoder_copy` on the renamed copy `DecodeReview.copy` of `code 3 πn`, whose cut names are
not in the order `decomp` would choose.
-/

namespace INet.Comb.DecodeCopy

open Term CodeCheck DecodeReview

/-- `code_decoder_copy` (pages 89 and 90) on the copy of `DecodeReview`: `code 3 πn` renamed by
`fwd`, whose cut names `50`, `47` are not in the order `decomp` would choose, against the decoder
with free port `2` and loop `30`. It reduces to `πn` renamed by `fwd`, that is
`dup(dup(40, 41), con(40, 41))`, on `2`. -/
theorem decode_copy_instance : ∃ M, StepsE system ({s(copy, decoder 2 30)} : CNet) M ∧
    Equiv M {s(var 2, mkDup (mkDup (var 40) (var 41)) (mkCon (var 40) (var 41)))} := by
  have hinj : ∀ x ∈ (code 3 πn).vars, ∀ y ∈ (code 3 πn).vars, fwd x = fwd y → x = y := by decide
  have hπ : πn.bind (fun x => var (fwd x)) =
      mkDup (mkDup (var 40) (var 41)) (mkCon (var 40) (var 41)) := by decide
  have h := code_decoder_copy πn (by unfold Term.IsPackage; decide) 3
    (by unfold Term.Below; decide) fwd (fun x hx y hy hxy => hinj x hx y hy hxy) 2 30 0
    (Net.linear_of_forall_mem (by decide))
  rw [hπ] at h
  exact h

end INet.Comb.DecodeCopy
