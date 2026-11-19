import InteractionCombinators.Text.StepsEAdd
import Checks.Misc.WantedCheck

/-!
# A concrete check of `StepsE.add_right`

Lafont 1997, Section 1.3, pages 72 to 73. The reduction of `WantedCheck.cut` beside
`WantedCheck.ctx` needs a renaming, and `StepsE.add_right` provides it.
-/

namespace INet

open Comb

/-- Non-vacuity where renaming is necessary: the interaction of `con` and `dup` in
`WantedCheck.cut` creates a wire named `4`, which the context `WantedCheck.ctx` uses, so
`cutResult + ctx` is not linear (`WantedCheck.stepsE_add_right_must_rename`). The reduction is
still done beside `ctx`, to a renamed copy of `cutResult`. -/
example : ∃ M', StepsE system (WantedCheck.cut + WantedCheck.ctx) (M' + WantedCheck.ctx) ∧
    Equiv M' WantedCheck.cutResult ∧ (M' + WantedCheck.ctx).Linear ∧
    ¬ (WantedCheck.cutResult + WantedCheck.ctx).Linear :=
  have h := WantedCheck.stepsE_add_right_must_rename
  have ⟨M', hs, hE, hl⟩ := StepsE.add_right system_wellFormed.linear _ h.1 h.2.1
  ⟨M', hs, hE, hl, h.2.2⟩

end INet
