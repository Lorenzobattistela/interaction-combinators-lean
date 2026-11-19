import InteractionCombinators.Core.Graph
import InteractionCombinators.Core.Combinators

/-!
# Check of `Graph.lean` on one net

The net `con(x, y) = dup(x, y)`: a `con` cell and a `dup` cell joined by their principal ports,
with the auxiliary ports of one wired to those of the other in order. Its graph has two cells and
three wires, and no free port.
-/

namespace INet.GraphCheck

open Comb

/-- The text. -/
def text : List (Term sig ℕ × Term sig ℕ) :=
  [(mkCon (.var 0) (.var 1), mkDup (.var 0) (.var 1))]

/-- The cells of the example. -/
def cells : Multiset (ℕ × sig.Sym) := (0, Comb.con) ::ₘ {(1, Comb.dup)}

/-- The raw graph: two cells, the wire of the equation, and four wires from the auxiliary ports to
the names. -/
theorem raw_text : Graph.raw 0 text =
    ⟨cells,
      s(.port 0 0, .port 1 0) ::ₘ s(.port 1 1, .name 0) ::ₘ s(.port 0 1, .name 0) ::ₘ
        s(.port 0 2, .name 1) ::ₘ {s(.port 1 2, .name 1)}, 0⟩ := by
  simp [text, cells, Graph.raw, Term.rawCells, Term.rawWires, Term.rootEnd, Term.size,
    Term.childBase, mkCon, mkDup, sig, Fin.sum_univ_two]
  rfl

/-- The graph of the net: the two cells, a wire between the principal ports, and a wire between
the auxiliary ports of the same rank. -/
def graph : Graph sig ℕ :=
  ⟨cells, s(.port 0 2, .port 1 2) ::ₘ s(.port 1 1, .port 0 1) ::ₘ {s(.port 0 0, .port 1 0)}, 0⟩

/-- `graph` is the graph of the text: the two names are erased one after the other. -/
theorem hasGraph : (Net.ofList text).HasGraph graph := by
  refine ⟨text, 0, rfl, ?_, ?_⟩
  · rw [raw_text]
    have e1 : (s(.port 0 0, .port 1 0) ::ₘ s(.port 1 1, .name 0) ::ₘ s(.port 0 1, .name 0) ::ₘ
        s(.port 0 2, .name 1) ::ₘ {s(.port 1 2, .name 1)} : Multiset (Sym2 (End ℕ))) =
        s(.name 0, .port 1 1) ::ₘ s(.name 0, .port 0 1) ::ₘ
          (s(.port 0 0, .port 1 0) ::ₘ s(.port 0 2, .name 1) ::ₘ {s(.port 1 2, .name 1)}) := by
      decide
    have e2 : (s(.port 1 1, .port 0 1) ::ₘ
        (s(.port 0 0, .port 1 0) ::ₘ s(.port 0 2, .name 1) ::ₘ {s(.port 1 2, .name 1)}) :
        Multiset (Sym2 (End ℕ))) =
        s(.name 1, .port 0 2) ::ₘ s(.name 1, .port 1 2) ::ₘ
          (s(.port 1 1, .port 0 1) ::ₘ {s(.port 0 0, .port 1 0)}) := by
      decide
    have c1 := Graph.Contract.join (S := sig) (0 : ℕ) (.port 1 1) (.port 0 1) cells
      (s(.port 0 0, .port 1 0) ::ₘ s(.port 0 2, .name 1) ::ₘ {s(.port 1 2, .name 1)}) 0
    have c2 := Graph.Contract.join (S := sig) (1 : ℕ) (.port 0 2) (.port 1 2) cells
      (s(.port 1 1, .port 0 1) ::ₘ {s(.port 0 0, .port 1 0)}) 0
    rw [← e1] at c1
    rw [← e2] at c2
    exact (Relation.ReflTransGen.single c1).trans (Relation.ReflTransGen.single c2)
  · intro x
    have : graph.ends = ({.port 0 2, .port 1 2, .port 1 1, .port 0 1, .port 0 0, .port 1 0} :
        Multiset (End ℕ)) := by
      decide
    rw [this]
    simp

/-- The graph is well formed: each of the three ports of each cell ends exactly one wire, and
there is no free port. -/
theorem graph_wf : graph.WF := by
  have he : graph.ends = ({.port 0 2, .port 1 2, .port 1 1, .port 0 1, .port 0 0, .port 1 0} :
      Multiset (End ℕ)) := by
    decide
  have hc : ((0, Comb.con) : ℕ × sig.Sym) ∈ graph.cells := by
    show ((0, Comb.con) : ℕ × sig.Sym) ∈ (0, Comb.con) ::ₘ ({(1, Comb.dup)} : Multiset _)
    exact Multiset.mem_cons.2 (Or.inl rfl)
  have hd : ((1, Comb.dup) : ℕ × sig.Sym) ∈ graph.cells := by
    show ((1, Comb.dup) : ℕ × sig.Sym) ∈ (0, Comb.con) ::ₘ ({(1, Comb.dup)} : Multiset _)
    exact Multiset.mem_cons.2 (Or.inr (Multiset.mem_singleton.2 rfl))
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro c α h i hi
    rw [he]
    have h0 : (c, α) ∈ (0, Comb.con) ::ₘ ({(1, Comb.dup)} : Multiset (ℕ × sig.Sym)) := h
    rcases Multiset.mem_cons.1 h0 with h' | h'
    · cases h'
      have : i ≤ 2 := hi
      interval_cases i <;> decide
    · cases Multiset.mem_singleton.1 h'
      have : i ≤ 2 := hi
      interval_cases i <;> decide
  · intro c i h
    rw [he] at h
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
      End.port.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [⟨_, hc, by decide⟩, ⟨_, hd, by decide⟩, ⟨_, hd, by decide⟩, ⟨_, hc, by decide⟩,
      ⟨_, hc, by decide⟩, ⟨_, hd, by decide⟩]
  · intro x
    rw [he]
    simp

end INet.GraphCheck
