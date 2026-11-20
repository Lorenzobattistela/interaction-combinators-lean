import Checks.Graphs.GraphStepCheck

/-!
# `Graph.Interact` with a rule that is not linear

`Graph.Interact.wf` does not ask the rule to be linear. This file shows what that leaves open. With
a `con`–`con` rule whose right member is empty, the interaction of a pair with four free ports
gives a graph that is well formed and has eight free ports: the four names that replace the cut
ends are consumed by nothing. So for such a rule "well formed" does not say that the free ports
are kept, as an interaction of the paper keeps them (Lafont 1997, page 73). The rules of a
well-formed system are linear. Written during the review of 20 November 2026.
-/

namespace INet.GraphStepNonLinearCheck

open Comb Graph GraphReview GraphStepCheck

/-- A rule for `con`–`con` that is not linear: the right member is empty, so the four ports do
not occur in it. -/
def dropRule : Rule sig 2 2 := ⟨0, 0⟩

/-- The system whose only rule is `dropRule`. -/
def sysDrop : System sig where
  rule
    | con, con => some dropRule
    | _, _ => none

/-- `dropRule` is not linear. -/
theorem dropRule_not_linear : ¬ dropRule.Linear := by
  intro h
  have := h.left 0
  simp [dropRule] at this

/-- The empty text. -/
def emptyText : List (Term sig RN × Term sig RN) := []

/-- The graph of the empty right member is the empty graph. -/
theorem drop_hasGraph : dropRule.net.HasGraph (raw 0 emptyText) :=
  ⟨emptyText, 0, rfl, .refl, by decide⟩

/-- The graph after the interaction: each of the four old free ports on a wire to one of the
fresh names `4` to `7`, which nothing consumes. -/
def after : Graph sig ℕ :=
  ⟨0, s(.name 4, .name 0) ::ₘ s(.name 5, .name 1) ::ₘ s(.name 6, .name 2) ::ₘ
    {s(.name 7, .name 3)}, 0⟩

/-- `Graph.Interact` holds from the `con`–`con` pair to `after`. -/
theorem drop_interact : Interact sysDrop conConFree after := by
  refine Interact.mk (I := sysDrop) 0 1 Comb.con Comb.con 0 conConFreeW 0 dropRule rfl
    (raw 0 emptyText)
    drop_hasGraph id (Set.injOn_id _) (by decide) (fresh 4) (fresh_injective 4) (by decide)
    after ?_ (count_le_one_of_nodup (by decide))
  have e : (⟨0 + Multiset.map (Prod.map id id) (raw 0 emptyText).cells,
      Multiset.map (Sym2.map (cutEnd 0 1 (fun i => fresh 4 (Sum.inl i))
        fun j => fresh 4 (Sum.inr (Sum.inl j)))) conConFreeW +
        Multiset.map (Sym2.map (End.map id (fresh 4))) (raw 0 emptyText).wires,
      0 + (raw 0 emptyText).loops⟩ : Graph sig ℕ) = after :=
    graph_eq rfl (by decide) rfl
  have h : Relation.ReflTransGen (Contract (S := sig) (ν := ℕ)) after after := .refl
  convert h using 1
  exact graph_eq rfl (by decide) rfl

/-- The result is well formed, by `Graph.Interact.wf`. -/
theorem after_wf : after.WF := drop_interact.wf ((wf_iff _).2 (by decide))

/-- The graph before the interaction has four free ports. -/
theorem free_before : Multiset.card conConFree.free = 4 := by decide
/-- **A rule that is not linear does not keep the free ports**: the graph after has eight. -/
theorem free_after : Multiset.card after.free = 8 := by decide

end INet.GraphStepNonLinearCheck
