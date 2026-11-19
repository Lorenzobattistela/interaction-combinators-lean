import InteractionCombinators.Lafont.DecodeCopyChain
import InteractionCombinators.Lafont.DecodeReview

/-!
# Review of `code_decoder_copy` and `Decomp.rename` (Figs. 9 and 10, pages 89 and 90)

Checks recorded by the review of issue #105.

* `copy_of_copy`, `copier_decoder_copy`: in Fig. 10 (page 89, the translation `⟨α_k⟩`) the code
  `!Γ` reaches the decoder `D` only after two copiers. `C_{p_{i,j}}` in `Γ_{i,j}` makes a copy, and
  `C_2` in `⟨α_k⟩` copies that copy again. A copy of a copy is still of the form
  `(code k π).bind (var ∘ f)` with `f` injective on the names of the code. `copier_decoder_copy`
  chains `C_2` (`copier_package`) with `code_decoder_copy`, with every hypothesis taken from the
  first copier. So the form of `code_decoder_copy` is what Fig. 10 needs. Both lemmas now live in
  `DecodeCopyChain.lean`, namespace `INet.Comb`.
* `decode_copy_adversarial`: the hypotheses of `code_decoder_copy` all hold at once, with `f`
  non-monotone (it puts the two cut names in reverse order and sends `1` below `0`). The decoder
  has free port `4` and loop `0, 1` (names *below* those of the copy, and two of them names of the
  original code). The context is not empty and uses the original cut names `3`, `6`, which the
  copy no longer uses.
* `copier_decoder_instance`: `copier_decoder_copy` on a concrete copy, with a non-empty context.
* `decomp_rename_instance`, `decomp_rename_needs_shift`: `decomp_bind_var` on a concrete
  instance. It also needs its hypothesis: a renaming that does not shift the counter gives
  different cut names from the ones `decomp` chooses.
-/

namespace INet.Comb.DecodeCopyReview

open Term CodeCheck DecodeReview

/-! ## The hypotheses of `code_decoder_copy` hold together on adversarial instances -/

/-- A non-monotone renaming of the names `0, 1, 3, 6` of `code 3 πn`: `0 ↦ 7`, `1 ↦ 2`,
`3 ↦ 9`, `6 ↦ 5`. It reverses the order of the two cut names `3 < 6` and of `0 < 1`. -/
def rev (x : ℕ) : ℕ :=
  if x = 0 then 7 else if x = 1 then 2 else if x = 3 then 9 else if x = 6 then 5 else x

/-- The copy written out: `M_n` on the cut names `9, 5`, in this order. -/
theorem copy_rev_eq : (code 3 πn).bind (fun x => var (rev x)) =
    mux [mux [var 9, var 5], muxStar [mkCon (var 7) (var 2), var 2], muxStar [var 5, var 7],
      var 9] := by decide

/-- `code_decoder_copy` (pages 89 and 90) with every hypothesis proved and nothing chosen to suit
it. The renaming `rev` is not monotone. The decoder has free port `4` and loop `0, 1`, which are
below the names of the copy (and `0`, `1` are names of the original code). The context
`3 = 6` is not empty and joins the two original cut names, which the copy no longer uses. The
package comes out renamed, `dup(dup(7, 2), con(7, 2))`, on `4`. -/
theorem decode_copy_adversarial : ∃ M, StepsE system
    (s((code 3 πn).bind (fun x => var (rev x)), decoder 4 0) ::ₘ {s(var 3, var 6)}) M ∧
    Equiv M (s(var 4, mkDup (mkDup (var 7) (var 2)) (mkCon (var 7) (var 2))) ::ₘ
      {s(var 3, var 6)}) := by
  have hinj : ∀ x ∈ (code 3 πn).vars, ∀ y ∈ (code 3 πn).vars, rev x = rev y → x = y := by decide
  have hπ : πn.bind (fun x => var (rev x)) =
      mkDup (mkDup (var 7) (var 2)) (mkCon (var 7) (var 2)) := by decide
  have h := code_decoder_copy πn (by unfold Term.IsPackage; decide) 3
    (by unfold Term.Below; decide) rev (fun x hx y hy hxy => hinj x hx y hy hxy) 4 0
    {s(var 3, var 6)} (Net.linear_of_forall_mem (by decide))
  rw [hπ] at h
  exact h

/-- `copier_decoder_copy` (page 89, Fig. 10) on the copy by `rev`: `C_2` with the decoder (free
port `4`, loop `0, 1`) on its first auxiliary port and the extra port `8` on its second, in the
context `3 = 6`. Every hypothesis is proved. -/
theorem copier_decoder_instance : ∃ (g g' : ℕ → ℕ) (M : CNet),
    Set.InjOn g {x | x ∈ (code 3 πn).vars} ∧ Set.InjOn g' {x | x ∈ (code 3 πn).vars} ∧
    StepsE system (s(copier [decoder 4 0, var 8], (code 3 πn).bind (fun x => var (rev x))) ::ₘ
      {s(var 3, var 6)}) M ∧
    Equiv M (s(var 4, πn.bind (fun x => var (g x))) ::ₘ
      s(var 8, (code 3 πn).bind (fun x => var (g' x))) ::ₘ {s(var 3, var 6)}) := by
  have hinj : ∀ x ∈ (code 3 πn).vars, ∀ y ∈ (code 3 πn).vars, rev x = rev y → x = y := by decide
  exact copier_decoder_copy πn (by unfold Term.IsPackage; decide) 3
    (by unfold Term.Below; decide) rev (fun x hx y hy hxy => hinj x hx y hy hxy) 4 0 (var 8)
    {s(var 3, var 6)} (Net.linear_of_forall_mem (by decide))

/-! ## `Decomp.rename` -/

/-- `decomp_bind_var` (page 88) on `πn` renamed by `rev` on its names and shifted from `3` to
`10`: the cut names are `10`, `13`, the images of `3`, `6`, and the auxiliary trees are renamed
by `rev`. -/
theorem decomp_rename_instance :
    (decomp 10 (πn.bind fun x => var (if x < 3 then rev x else x + 7))).cells.map (·.1) = [10, 13] ∧
    ((decomp 3 πn).rename (fun x => if x < 3 then rev x else x + 7) 0).cells.map (·.1) =
      [10, 13] ∧
    (decomp 10 (πn.bind fun x => var (if x < 3 then rev x else x + 7))).cells.map (·.2) =
      ((decomp 3 πn).rename (fun x => if x < 3 then rev x else x + 7) 0).cells.map (·.2) := by
  decide

/-- The hypothesis of `decomp_bind_var` is needed (page 88): renaming by `rev`, which does not
send `3 + i` to `K + i`, renames the cut names `3, 6` to `9, 5`. Decomposing the renamed package
from `3` still cuts at `3, 6`. -/
theorem decomp_rename_needs_shift :
    (decomp 3 (πn.bind fun x => var (rev x))).cells.map (·.1) = [3, 6] ∧
    ((decomp 3 πn).rename rev 0).cells.map (·.1) = [9, 5] := by
  decide

end INet.Comb.DecodeCopyReview
