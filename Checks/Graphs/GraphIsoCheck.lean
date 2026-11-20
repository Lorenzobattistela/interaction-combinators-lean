import InteractionCombinators.Graphs.GraphIso
import Checks.Core.GraphReview
import InteractionCombinators.Universality.RecursionFree.DecompositionLemmas

/-!
# Check of `InteractionCombinators/Graphs/GraphIso.lean`

The net `con(a, b) = x, x = dup(c, d)`, with `a, b, c, d, x = 0, 1, 2, 3, 4`, written as two lists
of equations: `text1` in this order, cells numbered from `0`; `text2` as
`dup(c, d) = x, x = con(a, b)`, with the other order and both equations the other way round, cells
numbered from `7`. Both are texts of one linear net (`ofList_text`, `linear_text`).

* `Graph.raw_iso_of_ofList_eq` shows the two raw graphs isomorphic, and so does the explicit
  renaming `c ↦ 8 - c` (`raw_iso_explicit`), which sends the `con` cell `0` to `8` and the `dup`
  cell `1` to `7`.
* `Net.Linear.hasGraph_iso` on the two graphs `graph1`, `graph2` obtained by erasing `x`; both
  `HasGraph` hypotheses are proved, so the instance is not vacuous; the explicit renaming proves the
  same isomorphism.
* The negative check, that exchanging the two auxiliary ports of a `con` cell gives a graph that is
  not isomorphic, is `GraphReview.not_iso_exchange_aux`.

Lafont 1997, Section 1.1, page 71.
-/

namespace INet.GraphIsoCheck

open Comb Graph GraphReview

/-- `con(a, b) = x, x = dup(c, d)`. -/
def text1 : List (Term sig ℕ × Term sig ℕ) :=
  [(mkCon (.var 0) (.var 1), .var 4), (.var 4, mkDup (.var 2) (.var 3))]

/-- `dup(c, d) = x, x = con(a, b)`: the other order, each equation the other way round. -/
def text2 : List (Term sig ℕ × Term sig ℕ) :=
  [(mkDup (.var 2) (.var 3), .var 4), (.var 4, mkCon (.var 0) (.var 1))]

/-- The two lists are texts of one net. -/
theorem ofList_text : Net.ofList text1 = Net.ofList text2 := by decide

/-- The lists are not equal: they differ by the order and the orientation of the equations. -/
theorem text1_ne_text2 : text1 ≠ text2 := by decide

/-- The text is linear. -/
theorem linear_text : (Net.ofList text1).Linear := by
  have h : (Net.ofList text1).vars = {0, 1, 4, 4, 2, 3} := by decide
  intro x
  rw [h]
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- `Graph.raw_iso_of_ofList_eq` on the two texts (page 71). -/
theorem raw_iso : (raw 0 text1).Iso (raw 7 text2) := raw_iso_of_ofList_eq ofList_text 0 7

/-- The cells of the first raw graph: `con` numbered `0`, `dup` numbered `1`. -/
theorem raw1_cells : (raw 0 text1).cells = (0, Comb.con) ::ₘ {(1, Comb.dup)} := rfl

/-- The cells of the second raw graph: `dup` numbered `7`, `con` numbered `8`. -/
theorem raw2_cells : (raw 7 text2).cells = (7, Comb.dup) ::ₘ {(8, Comb.con)} := rfl

/-- The same isomorphism, by the explicit renaming `c ↦ 8 - c` (page 71). -/
theorem raw_iso_explicit : (raw 0 text1).Iso (raw 7 text2) := by
  refine ⟨fun c => 8 - c, fun a ha b hb h => ?_, by decide, by decide, rfl⟩
  have hle : ∀ c ∈ (raw 0 text1).cells.map Prod.fst, c ≤ 1 := by rw [raw1_cells]; decide
  have := hle a ha
  have := hle b hb
  simp only at h
  omega

/-- The graph of `text1`: the name `x` erased, the principal ports of the two cells joined. -/
def graph1 : Graph sig ℕ :=
  ⟨(0, Comb.con) ::ₘ {(1, Comb.dup)},
    s(.port 0 0, .port 1 0) ::ₘ s(.port 0 1, .name 0) ::ₘ s(.port 0 2, .name 1) ::ₘ
      s(.port 1 1, .name 2) ::ₘ {s(.port 1 2, .name 3)}, 0⟩

/-- The graph of `text2`, cells numbered from `7`. -/
def graph2 : Graph sig ℕ :=
  ⟨(7, Comb.dup) ::ₘ {(8, Comb.con)},
    s(.port 7 0, .port 8 0) ::ₘ s(.port 7 1, .name 2) ::ₘ s(.port 7 2, .name 3) ::ₘ
      s(.port 8 1, .name 0) ::ₘ {s(.port 8 2, .name 1)}, 0⟩

theorem graph1_wf : graph1.WF := (wf_iff _).2 (by decide)

theorem graph2_wf : graph2.WF := (wf_iff _).2 (by decide)

/-- `graph1` is a graph of the net (page 71): erase `x` in the raw graph of `text1`. -/
theorem hasGraph1 : (Net.ofList text1).HasGraph graph1 :=
  ⟨text1, 0, rfl,
    .single (join_of 4 (.port 0 0) (.port 1 0)
      (s(.port 0 1, .name 0) ::ₘ s(.port 0 2, .name 1) ::ₘ
        s(.port 1 1, .name 2) ::ₘ {s(.port 1 2, .name 3)}) (by decide) rfl (by decide) rfl),
    graph1_wf.name⟩

/-- `graph2` is a graph of the same net (page 71): erase `x` in the raw graph of `text2`. -/
theorem hasGraph2 : (Net.ofList text1).HasGraph graph2 :=
  ⟨text2, 7, ofList_text,
    .single (join_of 4 (.port 7 0) (.port 8 0)
      (s(.port 7 1, .name 2) ::ₘ s(.port 7 2, .name 3) ::ₘ
        s(.port 8 1, .name 0) ::ₘ {s(.port 8 2, .name 1)}) (by decide) rfl (by decide) rfl),
    graph2_wf.name⟩

/-- `Net.Linear.hasGraph_iso` with its hypotheses satisfied (page 71). -/
theorem graph_iso : graph1.Iso graph2 := linear_text.hasGraph_iso hasGraph1 hasGraph2

/-- The same isomorphism by the explicit renaming `c ↦ 8 - c`. -/
theorem graph_iso_explicit : graph1.Iso graph2 := by
  refine ⟨fun c => 8 - c, fun a ha b hb h => ?_, by decide, by decide, rfl⟩
  have hle : ∀ c ∈ graph1.cells.map Prod.fst, c ≤ 1 := by decide
  have := hle a ha
  have := hle b hb
  simp only at h
  omega

/-- The graphs are not equal: the isomorphism is needed. -/
theorem graph1_ne_graph2 : graph1 ≠ graph2 := fun h => by
  have := congrArg Graph.loops h
  have hc := congrArg Graph.cells h
  revert hc
  decide

end INet.GraphIsoCheck
