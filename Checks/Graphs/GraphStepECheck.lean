import InteractionCombinators.Graphs.GraphStepE
import Checks.Graphs.GraphStepReview
import Checks.Universality.Codes.CodeCheck

/-!
# Check of `InteractionCombinators/Graphs/GraphStepE.lean`

`Net.Linear.stepE_interact` applied to two interactions of the combinators (Lafont 1997,
Section 1.2, page 73), so that its hypotheses are shown to hold.

* `dupDupShared_stepE_interact`: the literal step of `dup(x, 1) = dup(x, 2)`, with its concrete
  graph `dupDupShared` (from `Checks/Graphs/GraphStepCheck.lean`).
* `wireText_stepE_interact`: `4 = con(0, 1), 4 = con(2, 3)`, two `con` cells whose principal
  ports are joined by the named wire `4`. The step needs a wire substitution first, so this is a
  `StepE` that is not a `Step`; the graph is any graph of the text.
-/

namespace INet.GraphStepECheck

open Comb Graph Term

/-- The rules of the combinators are linear (page 72). -/
theorem comb_linear : ∀ α β r, system.rule α β = some r → r.Linear :=
  system_wellFormed.linear

/-- **The theorem on `dup(x, 1) = dup(x, 2)`** (page 73): the linear net, its graph
`dupDupShared` and one step of `ruleDupDup` meet the hypotheses of `Net.Linear.stepE_interact`. -/
theorem dupDupShared_stepE_interact :
    ∃ H H', Interact system GraphStepCheck.dupDupShared H ∧
      (Net.ofList GraphStepReview.dupDupSharedAfterText).HasGraph H' ∧ H.Iso H' := by
  obtain ⟨hN, hG, hS, -⟩ := GraphStepReview.dupDupShared_agree
  exact Net.Linear.stepE_interact comb_linear hN hS.stepE hG

/-- The text `4 = con(0, 1), 4 = con(2, 3)`. -/
def wireText : CNet := s(var 4, mkCon (var 0) (var 1)) ::ₘ {s(var 4, mkCon (var 2) (var 3))}

theorem wireText_linear : wireText.Linear :=
  Net.linear_of_forall_mem (by decide)

/-- `4 = con(0, 1), 4 = con(2, 3)` reduces up to wires to `0 = 3, 1 = 2` (page 73): plug
`con(0, 1)` into the other end of `4`, then `ruleConCon` exchanges the auxiliary ports. -/
theorem wireText_stepE : StepE system wireText (s(var 0, var 3) ::ₘ s(var 1, var 2) ::ₘ 0) :=
  ⟨s(mkCon (var 0) (var 1), mkCon (var 2) (var 3)) ::ₘ 0,
    CodeCheck.wire_of 4 (mkCon (var 0) (var 1)) (var 4) (mkCon (var 2) (var 3)) 0 wireText _
      rfl (by decide) (by decide) (by decide), step_con_con (var 0) (var 1) (var 2) (var 3) 0⟩

/-- **The theorem on `4 = con(0, 1), 4 = con(2, 3)`** (page 73): the text has a graph, and an
interaction of that graph gives a graph of `0 = 3, 1 = 2` up to isomorphism. -/
theorem wireText_stepE_interact : ∃ G, wireText.HasGraph G ∧
    ∃ H H', Interact system G H ∧
      Net.HasGraph (s(var 0, var 3) ::ₘ s(var 1, var 2) ::ₘ 0 : CNet) H' ∧ H.Iso H' := by
  obtain ⟨G, hG, -⟩ := Net.exists_graph wireText
  exact ⟨G, hG, Net.Linear.stepE_interact comb_linear wireText_linear wireText_stepE hG⟩

end INet.GraphStepECheck
