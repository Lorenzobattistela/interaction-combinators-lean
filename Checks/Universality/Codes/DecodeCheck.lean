import InteractionCombinators.Universality.Codes.Decode
import Checks.Universality.Codes.CodeCheck

/-!
# Checks of `InteractionCombinators/Universality/Codes/Decode.lean` (Fig. 9, page 89)

* The hypotheses of `code_decoder_package` hold on the package `π₂` of `CodeCheck.lean`, which has
  two `dup` cells with different left and right trees: `π₂` on the free port `2`, new names of the
  code from `3`, loop of the decoder at `(decomp 3 π₂).k = 13`.
* The same on a package without `dup` (`n = 0`, where `M_0 = ε` erases the `dup` of the decoder)
  and on a package with one `dup` (`n = 1`, where `M_1` is a wire), in a context `Δ` that is not
  empty.
-/

namespace INet.Comb.DecodeCheck

open Term CodeCheck

/-- The next unused name of the code of `π₂` with new names from `3`. -/
theorem decomp_π₂_k : (decomp 3 π₂).k = 13 := rfl

/-- Fig. 9 on `π₂` (page 89), from the general theorem: the hypotheses are checked by
computation. -/
theorem decode_π₂_general : ∃ M, StepsE system {s(code 3 π₂, decoder 2 13)} M ∧
    Equiv M {s(var 2, π₂)} :=
  code_decoder_package π₂ π₂_isPackage 3 2 13 0
    (Net.linear_of_forall_mem (by decide)) (by unfold Net.Below; decide) (by decide)

/-- Fig. 9 for `n = 0`: the package `con(0, 0)` on `1`, next to the equation `6 = 7` of the
context; new names of the code from `8`, loop at `10`. -/
theorem decode_dupFree : ∃ M, StepsE system
    {s(code 8 (mkCon (var 0) (var 0)), decoder 1 10), s(var 6, var 7)} M ∧
    Equiv M {s(var 1, mkCon (var 0) (var 0)), s(var 6, var 7)} :=
  code_decoder_package (mkCon (var 0) (var 0)) (by unfold Term.IsPackage; decide) 8 1 10
    {s(var 6, var 7)} (Net.linear_of_forall_mem (by decide)) (by unfold Net.Below; decide)
    (by decide)

/-- Fig. 9 for `n = 1`: the package `dup(0, 0)` on `1`. -/
theorem decode_oneDup : ∃ M, StepsE system {s(code 2 (mkDup (var 0) (var 0)), decoder 1 5)} M ∧
    Equiv M {s(var 1, mkDup (var 0) (var 0))} :=
  code_decoder_package (mkDup (var 0) (var 0)) (by unfold Term.IsPackage; decide) 2 1 5 0
    (Net.linear_of_forall_mem (by decide)) (by unfold Net.Below; decide) (by decide)

end INet.Comb.DecodeCheck
