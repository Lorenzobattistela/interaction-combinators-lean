import InteractionCombinators.Graphs.GraphContract
import Checks.Core.GraphReview

/-!
# Check of `Lafont/GraphContract.lean` on two texts

* `con(a, b) = x, x = y, y = dup(b, a)`, with `a, b, x, y = 0, 1, 2, 3`: the names `x` and `y`
  form a chain between two principal ports, and `a`, `b` join auxiliary ports of the two cells.
  Four contractions lead from its raw graph to the graph of two cells joined principal port to
  principal port, with crossed auxiliary ports. That graph is checked `WF` by a direct
  computation (`GraphReview.wf_iff`), and also follows from `Graph.raw_contracts_wf`.
* `x = y, y = x`: two contractions give a cyclic wire, `loops = 1`.

`Net.Linear.exists_graph` is applied to both (Lafont 1997, page 71).
-/

namespace INet.GraphContractCheck

open Comb Graph GraphReview

/-! ## A chain between two cells -/

/-- `con(a, b) = x, x = y, y = dup(b, a)`. -/
def text : List (Term sig ℕ × Term sig ℕ) :=
  [(mkCon (.var 0) (.var 1), .var 2), (.var 2, .var 3), (.var 3, mkDup (.var 1) (.var 0))]

/-- The cells: `0` is the `con` cell, `1` the `dup` cell. -/
def cells : Multiset (ℕ × sig.Sym) := (0, Comb.con) ::ₘ {(1, Comb.dup)}

/-- The raw graph, written out: every name ends two wires. -/
def G0 : Graph sig ℕ :=
  ⟨cells, {s(.port 0 0, .name 2), s(.port 0 1, .name 0), s(.port 0 2, .name 1),
    s(.name 2, .name 3), s(.name 3, .port 1 0), s(.port 1 1, .name 1), s(.port 1 2, .name 0)}, 0⟩

/-- After erasing `x`. -/
def G1 : Graph sig ℕ :=
  ⟨cells, {s(.port 0 0, .name 3), s(.port 0 1, .name 0), s(.port 0 2, .name 1),
    s(.name 3, .port 1 0), s(.port 1 1, .name 1), s(.port 1 2, .name 0)}, 0⟩

/-- After erasing `y`: the two principal ports are joined. -/
def G2 : Graph sig ℕ :=
  ⟨cells, {s(.port 0 0, .port 1 0), s(.port 0 1, .name 0), s(.port 0 2, .name 1),
    s(.port 1 1, .name 1), s(.port 1 2, .name 0)}, 0⟩

/-- After erasing `a`. -/
def G3 : Graph sig ℕ :=
  ⟨cells, {s(.port 0 0, .port 1 0), s(.port 0 1, .port 1 2), s(.port 0 2, .name 1),
    s(.port 1 1, .name 1)}, 0⟩

/-- After erasing `b`: the graph of the text, with no free port. -/
def G4 : Graph sig ℕ :=
  ⟨cells, {s(.port 0 0, .port 1 0), s(.port 0 1, .port 1 2), s(.port 0 2, .port 1 1)}, 0⟩

/-- The raw graph of the text, computed. -/
theorem raw_text : Graph.raw 0 text = G0 := by
  simp [text, G0, cells, Graph.raw, Term.rawCells, Term.rawWires, Term.rootEnd, Term.size,
    Term.childBase, mkCon, mkDup, sig, Fin.sum_univ_two]
  constructor
  · rfl
  · decide

/-- The four contractions, from the raw graph to `G4` (page 71). -/
theorem contracts : Relation.ReflTransGen Contract (Graph.raw 0 text) G4 := by
  rw [raw_text]
  refine .head (b := G1) ?_ (.head (b := G2) ?_ (.head (b := G3) ?_ (.single ?_)))
  · exact join_of 2 (.port 0 0) (.name 3) {s(.port 0 1, .name 0), s(.port 0 2, .name 1),
      s(.name 3, .port 1 0), s(.port 1 1, .name 1), s(.port 1 2, .name 0)}
      (by decide) (by decide) rfl rfl
  · exact join_of 3 (.port 0 0) (.port 1 0) {s(.port 0 1, .name 0), s(.port 0 2, .name 1),
      s(.port 1 1, .name 1), s(.port 1 2, .name 0)} (by decide) (by decide) rfl rfl
  · exact join_of 0 (.port 0 1) (.port 1 2) {s(.port 0 0, .port 1 0), s(.port 0 2, .name 1),
      s(.port 1 1, .name 1)} (by decide) (by decide) rfl rfl
  · exact join_of 1 (.port 0 2) (.port 1 1) {s(.port 0 0, .port 1 0), s(.port 0 1, .port 1 2)}
      (by decide) (by decide) rfl rfl

/-- `G4` is well formed, by a direct computation (page 71). -/
theorem G4_wf : G4.WF := (wf_iff _).2 (by decide)

/-- No name ends a wire of `G4`. -/
theorem G4_names (x : ℕ) : G4.ends.count (.name x) ≤ 1 := G4_wf.name x

/-- `G4` is the graph of the text, and `Graph.raw_contracts_wf` gives its well-formedness without
computation. -/
theorem hasGraph_text : (Net.ofList text).HasGraph G4 ∧ G4.WF :=
  ⟨⟨text, 0, rfl, contracts, G4_names⟩, Graph.raw_contracts_wf 0 text contracts G4_names⟩

/-- The text is linear. -/
theorem linear_text : (Net.ofList text).Linear := by
  have h : (Net.ofList text).vars = {0, 1, 2, 2, 3, 3, 1, 0} := by decide
  intro x
  rw [h]
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- `Net.Linear.exists_graph` on the text (page 71). -/
theorem exists_graph_text : ∃ G, (Net.ofList text).HasGraph G ∧ G.WF :=
  linear_text.exists_graph

/-- One contraction removes two ends: `Graph.Contract.card_ends` on the first step. -/
theorem card_first : Multiset.card G0.ends = Multiset.card G1.ends + 2 := by decide

/-! ## A cyclic wire -/

/-- `x = y, y = x`. -/
def loopText : List (Term sig ℕ × Term sig ℕ) := [(.var 0, .var 1), (.var 1, .var 0)]

/-- Erasing `x` gives a wire from `y` to itself, and erasing `y` a cyclic wire (page 71). -/
theorem loop_contracts :
    Relation.ReflTransGen Contract (Graph.raw 0 loopText) (⟨0, 0, 1⟩ : Graph sig ℕ) :=
  .head (b := ⟨0, {s(.name 1, .name 1)}, 0⟩)
    (join_of 0 (.name 1) (.name 1) 0 (by decide) rfl rfl rfl)
    (.single (loop_of 1 0 rfl rfl rfl rfl))

/-- The graph of `x = y, y = x` is one cyclic wire, and it is well formed. -/
theorem hasGraph_loopText : (Net.ofList loopText).HasGraph (⟨0, 0, 1⟩ : Graph sig ℕ) ∧
    (⟨0, 0, 1⟩ : Graph sig ℕ).WF ∧ (⟨0, 0, 1⟩ : Graph sig ℕ).loops = 1 :=
  ⟨⟨loopText, 0, rfl, loop_contracts, cyclic_wf.name⟩,
    Graph.raw_contracts_wf 0 loopText loop_contracts cyclic_wf.name, rfl⟩

/-- `x = y, y = x` is linear, and `Net.Linear.exists_graph` applies (page 71). -/
theorem exists_graph_loopText : ∃ G, (Net.ofList loopText).HasGraph G ∧ G.WF :=
  Net.Linear.exists_graph (fun x => by
    have h : (Net.ofList loopText).vars = {0, 1, 1, 0} := by decide
    rw [h]
    simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
    split_ifs <;> omega)

end INet.GraphContractCheck
