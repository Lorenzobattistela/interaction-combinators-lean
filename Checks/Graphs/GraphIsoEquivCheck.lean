import InteractionCombinators.Graphs.GraphIsoEquiv
import Checks.Core.GraphReview
import Checks.Graphs.GraphEquivCheck

/-!
# Check of `Lafont/GraphIsoEquiv.lean`

Lafont 1997, Section 1.1, page 71. Names `a, b, c, d, x = 0, 1, 2, 3, 4`.

* Two texts of one graph: `a = con(b, dup(c, d))` and `dup(c, d) = x, a = con(b, x)`. In the
  second, the `dup` cell is at the root of an equation of its own, read from the tree to the
  name. Their graphs are isomorphic (the two cells numbered the other way round), so
  `Net.Linear.equiv_of_hasGraph_iso` gives `Equiv` (`textA_equiv_textB`), although the texts are
  different (`textA_ne_textB`).
* A cyclic wire under two names: `a = a` and `b = b` (`loop_equiv`).
* Two linear texts whose graphs are not isomorphic: `a = con(b, c)` and `a = con(c, b)`, the two
  auxiliary ports exchanged. Through `Net.Linear.equiv_iff_hasGraph_iso` they are not `Equiv`
  (`not_equiv_exchange`).
-/

namespace INet.GraphIsoEquivCheck

open Comb Graph GraphReview GraphEquivCheck

/-! ## Two texts of one graph -/

/-- `a = con(b, dup(c, d))`. -/
def textA : List (Term sig ℕ × Term sig ℕ) := [(.var 0, mkCon (.var 1) (mkDup (.var 2) (.var 3)))]

/-- `dup(c, d) = x, a = con(b, x)`. -/
def textB : List (Term sig ℕ × Term sig ℕ) :=
  [(mkDup (.var 2) (.var 3), .var 4), (.var 0, mkCon (.var 1) (.var 4))]

/-- The graph of `textA`: the `con` cell `0`, the `dup` cell `1` on its second auxiliary port. -/
def graphA : Graph sig ℕ :=
  ⟨(0, Comb.con) ::ₘ {(1, Comb.dup)},
    s(.name 0, .port 0 0) ::ₘ s(.port 0 1, .name 1) ::ₘ s(.port 0 2, .port 1 0) ::ₘ
      s(.port 1 1, .name 2) ::ₘ {s(.port 1 2, .name 3)}, 0⟩

/-- The graph of `textB`: the `dup` cell `0`, the `con` cell `1`, the name `x` erased. -/
def graphB : Graph sig ℕ :=
  ⟨(0, Comb.dup) ::ₘ {(1, Comb.con)},
    s(.port 0 0, .port 1 2) ::ₘ s(.port 0 1, .name 2) ::ₘ s(.port 0 2, .name 3) ::ₘ
      s(.name 0, .port 1 0) ::ₘ {s(.port 1 1, .name 1)}, 0⟩

theorem raw_textA : Graph.raw 0 textA = graphA := by
  simp [textA, graphA, Graph.raw, Term.rawCells, Term.rawWires, Term.rootEnd, Term.size,
    Term.childBase, mkCon, mkDup, sig, Fin.sum_univ_two]
  decide

/-- The raw graph of `textB`, where the name `x` ends two wires. -/
def rawB : Graph sig ℕ :=
  ⟨(0, Comb.dup) ::ₘ {(1, Comb.con)},
    s(.name 4, .port 0 0) ::ₘ s(.name 4, .port 1 2) ::ₘ s(.port 0 1, .name 2) ::ₘ
      s(.port 0 2, .name 3) ::ₘ s(.name 0, .port 1 0) ::ₘ {s(.port 1 1, .name 1)}, 0⟩

theorem raw_textB : Graph.raw 0 textB = rawB := by
  simp [textB, rawB, Graph.raw, Term.rawCells, Term.rawWires, Term.rootEnd, Term.size,
    Term.childBase, mkCon, mkDup, sig, Fin.sum_univ_two]
  decide

theorem graphA_wf : graphA.WF := (wf_iff _).2 (by decide)
theorem graphB_wf : graphB.WF := (wf_iff _).2 (by decide)

/-- `graphA` is the graph of `textA`: no name ends two wires. -/
theorem hasGraph_textA : (Net.ofList textA).HasGraph graphA :=
  ⟨textA, 0, rfl, raw_textA ▸ .refl, graphA_wf.name⟩

/-- `graphB` is the graph of `textB`: erase the name `x`. -/
theorem hasGraph_textB : (Net.ofList textB).HasGraph graphB := by
  refine ⟨textB, 0, rfl, .single (join_of 4 (.port 0 0) (.port 1 2)
    (s(.port 0 1, .name 2) ::ₘ s(.port 0 2, .name 3) ::ₘ s(.name 0, .port 1 0) ::ₘ
      {s(.port 1 1, .name 1)}) ?_ ?_ ?_ ?_), graphB_wf.name⟩ <;>
    (try rw [raw_textB]) <;> decide

/-- The two graphs are isomorphic: exchange the numbers of the two cells (page 71). -/
theorem iso_AB : graphA.Iso graphB := by
  refine ⟨fun c => 1 - c, fun a ha b hb h => ?_, by decide, by decide, rfl⟩
  have hle : ∀ c ∈ graphA.cells.map Prod.fst, c ≤ 1 := by decide
  have := hle a ha
  have := hle b hb
  simp only at h
  omega

theorem textA_linear : (Net.ofList textA).Linear := linear_of_mem (by decide)
theorem textB_linear : (Net.ofList textB).Linear := linear_of_mem (by decide)

/-- **The two texts are equivalent, through their graphs** (page 71):
`Net.Linear.equiv_of_hasGraph_iso` applied to concrete texts, graphs and an isomorphism. -/
theorem textA_equiv_textB : Equiv (Net.ofList textA) (Net.ofList textB) :=
  textA_linear.equiv_of_hasGraph_iso textB_linear hasGraph_textA hasGraph_textB iso_AB

/-- The texts are different: one has one equation, the other two. -/
theorem textA_ne_textB : Net.ofList textA ≠ Net.ofList textB := fun h => by
  have := congrArg Multiset.card h
  simp [textA, textB, Net.ofList] at this

/-! ## A cyclic wire under two names -/

/-- `a = a` and `b = b` have the same graph, one cyclic wire, so they are equivalent. The flat
texts of the proof give the cyclic wire a third name. -/
theorem loop_equiv : Equiv (Net.ofList [((.var 0 : Term sig ℕ), .var 0)])
    (Net.ofList [((.var 1 : Term sig ℕ), .var 1)]) := by
  have h0 : (Net.ofList [((.var 0 : Term sig ℕ), .var 0)]).HasGraph cyclic :=
    ⟨_, 0, rfl, .single (loop_of 0 0 (by decide) (by decide) rfl rfl), cyclic_wf.name⟩
  have h1 : (Net.ofList [((.var 1 : Term sig ℕ), .var 1)]).HasGraph cyclic :=
    ⟨_, 0, rfl, .single (loop_of 1 0 (by decide) (by decide) rfl rfl), cyclic_wf.name⟩
  exact (linear_of_mem (by decide)).equiv_of_hasGraph_iso (linear_of_mem (by decide)) h0 h1
    (Iso.refl _)

/-! ## Exchanged auxiliary ports -/

/-- `a = con(b, c)`. -/
def textC : List (Term sig ℕ × Term sig ℕ) := [(.var 0, mkCon (.var 1) (.var 2))]

/-- `a = con(c, b)`. -/
def textD : List (Term sig ℕ × Term sig ℕ) := [(.var 0, mkCon (.var 2) (.var 1))]

/-- The graph of `textD`. -/
def graphD : Graph sig ℕ :=
  ⟨{(0, Comb.con)}, s(.name 0, .port 0 0) ::ₘ s(.port 0 1, .name 2) ::ₘ {s(.port 0 2, .name 1)},
    0⟩

/-- The graph of `textC`. -/
def graphC : Graph sig ℕ :=
  ⟨{(0, Comb.con)}, s(.name 0, .port 0 0) ::ₘ s(.port 0 1, .name 1) ::ₘ {s(.port 0 2, .name 2)},
    0⟩

theorem hasGraph_textC : (Net.ofList textC).HasGraph graphC := by
  have h : Graph.raw 0 textC = graphC := by
    simp [textC, graphC, Graph.raw, Term.rawCells, Term.rawWires, Term.rootEnd, Term.size,
      Term.childBase, mkCon, sig, Fin.sum_univ_two]
    decide
  exact ⟨textC, 0, rfl, h ▸ .refl, ((wf_iff _).2 (by decide)).name⟩

theorem hasGraph_textD : (Net.ofList textD).HasGraph graphD := by
  have h : Graph.raw 0 textD = graphD := by
    simp [textD, graphD, Graph.raw, Term.rawCells, Term.rawWires, Term.rootEnd, Term.size,
      Term.childBase, mkCon, sig, Fin.sum_univ_two]
    decide
  exact ⟨textD, 0, rfl, h ▸ .refl, ((wf_iff _).2 (by decide)).name⟩

/-- The graphs are not isomorphic: the free port `b` is on the first auxiliary port in one and on
the second in the other (page 71: the auxiliary ports are not interchangeable). -/
theorem not_iso_CD : ¬ graphC.Iso graphD := by
  rintro ⟨σ, -, -, hw, -⟩
  have hm : s(End.port (σ 0) 1, End.name 1) ∈ graphD.wires := by
    rw [hw]; simp [graphC, End.mapCell]
  simp [graphD] at hm

/-- **`a = con(b, c)` and `a = con(c, b)` are not equivalent** (page 71), concluded through
`Net.Linear.equiv_iff_hasGraph_iso` from the graphs. -/
theorem not_equiv_exchange : ¬ Equiv (Net.ofList textC) (Net.ofList textD) := fun h =>
  not_iso_CD (((linear_of_mem (by decide)).equiv_iff_hasGraph_iso (linear_of_mem (by decide))
    hasGraph_textC hasGraph_textD).1 h)

end INet.GraphIsoEquivCheck
