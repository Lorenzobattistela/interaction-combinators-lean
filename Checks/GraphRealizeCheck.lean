import InteractionCombinators.Lafont.GraphRealize
import Checks.GraphReview

/-!
# Check of `Lafont/GraphRealize.lean`

Lafont 1997, Section 1.1, page 71. `Graph.WF.exists_net_free` applied to two well-formed graphs
written by hand, with cells numbered out of prefix order, so its hypothesis can hold.

* `pair`: a `con` cell `7` and a `dup` cell `3` joined principal port to principal port, their
  four auxiliary ports free, called `0, 1, 2, 3`.
* `loopAux`: one cyclic wire, and a `con` cell `5` whose two auxiliary ports are joined to each
  other, its principal port free, called `0`.
-/

namespace INet.GraphRealizeCheck

open Comb Graph

/-- A `con` cell `7` and a `dup` cell `3`, principal port to principal port, four free ports. -/
def pair : Graph sig ℕ :=
  ⟨(7, Comb.con) ::ₘ {(3, Comb.dup)},
    s(.port 7 0, .port 3 0) ::ₘ s(.port 7 1, .name 0) ::ₘ s(.port 7 2, .name 1) ::ₘ
      s(.port 3 1, .name 2) ::ₘ {s(.port 3 2, .name 3)}, 0⟩

/-- `pair` is well formed (page 71). -/
theorem pair_wf : pair.WF := (GraphReview.wf_iff _).2 (by decide)

/-- The free ports of `pair` are `0, 1, 2, 3`. -/
theorem pair_free : ∀ x, x ∈ pair.free ↔ x ∈ [0, 1, 2, 3] := by
  intro x
  simp only [mem_free]
  simp [pair, ends, Multiset.insert_eq_cons]
  omega

/-- **`pair` is the graph of a linear net** (page 71), whose free ports are `0, 1, 2, 3`. -/
theorem pair_net : ∃ (N : Net sig ℕ) (G' : Graph sig ℕ), N.Linear ∧ N.HasGraph G' ∧
    G'.Iso pair ∧ ∀ x, N.vars.count x = 1 ↔ x ∈ [0, 1, 2, 3] := by
  obtain ⟨N, G', h1, h2, h3, h4⟩ := pair_wf.exists_net_free
  exact ⟨N, G', h1, h2, h3, fun x => (h4 x).trans (pair_free x)⟩

/-- One cyclic wire, and a `con` cell `5` whose auxiliary ports are joined, principal port free. -/
def loopAux : Graph sig ℕ :=
  ⟨{(5, Comb.con)}, s(.port 5 1, .port 5 2) ::ₘ {s(.port 5 0, .name 0)}, 1⟩

/-- `loopAux` is well formed (page 71). -/
theorem loopAux_wf : loopAux.WF := (GraphReview.wf_iff _).2 (by decide)

/-- The only free port of `loopAux` is `0`. -/
theorem loopAux_free : ∀ x, x ∈ loopAux.free ↔ x = 0 := by
  intro x
  simp only [mem_free]
  simp [loopAux, ends, Multiset.insert_eq_cons]

/-- **`loopAux` is the graph of a linear net** (page 71), whose only free port is `0`. -/
theorem loopAux_net : ∃ (N : Net sig ℕ) (G' : Graph sig ℕ), N.Linear ∧ N.HasGraph G' ∧
    G'.Iso loopAux ∧ ∀ x, N.vars.count x = 1 ↔ x = 0 := by
  obtain ⟨N, G', h1, h2, h3, h4⟩ := loopAux_wf.exists_net_free
  exact ⟨N, G', h1, h2, h3, fun x => (h4 x).trans (loopAux_free x)⟩

/-- The graph found for `loopAux` keeps its cyclic wire. -/
theorem loopAux_net_loops : ∃ (N : Net sig ℕ) (G' : Graph sig ℕ), N.Linear ∧ N.HasGraph G' ∧
    G'.loops = 1 := by
  obtain ⟨N, G', h1, h2, ⟨σ, -, -, -, hl⟩, -⟩ := loopAux_wf.exists_net_free
  exact ⟨N, G', h1, h2, by rw [← hl]; rfl⟩

end INet.GraphRealizeCheck
