import InteractionCombinators.Graphs.GraphStepEConverse
import Checks.Graphs.GraphStepECheck

/-!
# Check of `Lafont/GraphStepEConverse.lean`

`Net.Linear.interact_stepE` applied to two interactions of the combinators from
`Checks/GraphStepCheck.lean` (Lafont 1997, Section 1.2, page 73), so that its hypotheses are shown
to hold: a linear net, a graph of it, and an interaction of that graph.

* `conConFree_interact_stepE`: `con(0, 1) = con(2, 3)`, its graph `conConFree` and the
  interaction `conCon_free`.
* `dupDupShared_interact_stepE`: `dup(x, 1) = dup(x, 2)`, its graph `dupDupShared` and the
  interaction `dupDup_shared`, whose result has a cyclic wire.

The uniqueness theorem `Graph.interact_unique` is used inside the proof; its hypotheses hold for
these interactions because `Interact.mk` provides them.
-/

namespace INet.GraphStepEConverseCheck

open Comb Graph Term

/-- `con(0, 1) = con(2, 3)` is linear: every name occurs once. -/
theorem conConFreeText_linear : (Net.ofList GraphStepCheck.conConFreeText).Linear :=
  Net.linear_of_forall_mem (by decide)

/-- **The converse on `con(0, 1) = con(2, 3)`** (page 73): the interaction `conCon_free` of the
graph `conConFree` is, up to `Iso`, the graph of a `StepE` of the text. -/
theorem conConFree_interact_stepE :
    ∃ M H', StepE system (Net.ofList GraphStepCheck.conConFreeText) M ∧ M.HasGraph H' ∧
      GraphStepCheck.conConFreeAfter.Iso H' :=
  Net.Linear.interact_stepE GraphStepECheck.comb_linear conConFreeText_linear
    GraphStepCheck.conConFree_hasGraph GraphStepCheck.conCon_free

/-- **The converse on `dup(x, 1) = dup(x, 2)`** (page 73): the interaction `dupDup_shared`, which
creates a cyclic wire, is, up to `Iso`, the graph of a `StepE` of the text. -/
theorem dupDupShared_interact_stepE :
    ∃ M H', StepE system (Net.ofList GraphStepCheck.dupDupText2) M ∧ M.HasGraph H' ∧
      GraphStepCheck.dupDupSharedAfter.Iso H' := by
  obtain ⟨hN, hG, -, -, hI, -⟩ := GraphStepReview.dupDupShared_agree
  exact Net.Linear.interact_stepE GraphStepECheck.comb_linear hN hG hI

end INet.GraphStepEConverseCheck
