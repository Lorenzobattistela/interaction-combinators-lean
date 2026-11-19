import InteractionCombinators.Graphs.GraphRaw
import InteractionCombinators.Core.Combinators

/-!
# Check of `Lafont/GraphRaw.lean` on one text

The text `0 = con(1, 1)`, `2 = dup(3, 0)`: a `con` cell whose two auxiliary ports are joined by
the name `1`, and a `dup` cell. Each result of `GraphRaw.lean` is applied to it, and its conclusion
is compared with a direct computation of the raw graph (Lafont 1997, page 71).
-/

namespace INet.GraphRawCheck

open Comb

/-- The text. -/
def text : List (Term sig ℕ × Term sig ℕ) :=
  [(.var 0, mkCon (.var 1) (.var 1)), (.var 2, mkDup (.var 3) (.var 0))]

/-- The cells `0` (`con`) and `1` (`dup`). -/
def cells : Multiset (ℕ × sig.Sym) := (0, Comb.con) ::ₘ {(1, Comb.dup)}

/-- The raw graph of the text, computed directly: the cells `0` (`con`) and `1` (`dup`). -/
theorem raw_cells : (Graph.raw 0 text).cells = cells := by
  simp [text, cells, Graph.raw, Term.rawCells, Term.size, Term.childBase, mkCon, mkDup, sig,
    Fin.sum_univ_two]
  rfl

/-- The raw graph of the text, computed directly: the ends of its wires. -/
theorem raw_ends_direct : (Graph.raw 0 text).ends =
    {.name 0, .port 0 0, .port 0 1, .name 1, .port 0 2, .name 1,
      .name 2, .port 1 0, .port 1 1, .name 3, .port 1 2, .name 0} := by
  decide

/-- `Graph.raw_cells_fst` on the text (page 71): the cells are numbered `0, 1`, as computed. -/
theorem cells_fst : (Graph.raw 0 text).cells.map Prod.fst = {0, 1} := by
  rw [Graph.raw_cells_fst]
  decide

/-- The same numbers, read off the direct computation. -/
theorem cells_fst_direct : (Graph.raw 0 text).cells.map Prod.fst = {0, 1} := by
  rw [raw_cells]
  decide

/-- `Graph.raw_nodup` and `Graph.raw_loops` on the text (page 71). -/
theorem nodup_loops :
    ((Graph.raw 0 text).cells.map Prod.fst).Nodup ∧ (Graph.raw 0 text).loops = 0 :=
  ⟨Graph.raw_nodup 0 text, Graph.raw_loops 0 text⟩

/-- `Graph.raw_port` on the text (page 71): every port of the `con` cell, including the two
auxiliary ports joined by the name `1`, ends one wire; and so does every port of the `dup` cell. -/
theorem ports :
    (∀ i ≤ 2, (Graph.raw 0 text).ends.count (.port 0 i) = 1) ∧
      (∀ i ≤ 2, (Graph.raw 0 text).ends.count (.port 1 i) = 1) :=
  ⟨fun i hi => Graph.raw_port 0 text 0 Comb.con (by rw [raw_cells]; exact Multiset.mem_cons_self _ _) i hi,
    fun i hi => Graph.raw_port 0 text 1 Comb.dup
      (by rw [raw_cells]; exact Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _)) i hi⟩

/-- The same counts, read off the direct computation. -/
theorem ports_direct :
    (∀ i : Fin 3, (Graph.raw 0 text).ends.count (.port 0 i) = 1) ∧
      (∀ i : Fin 3, (Graph.raw 0 text).ends.count (.port 1 i) = 1) := by
  rw [raw_ends_direct]
  decide

/-- `Graph.raw_cell` on the text (page 71): the port `2` of the cell `0` is an end, so the cell
`0` is a cell of the graph with at least two auxiliary ports. -/
theorem cell_of_port : ∃ α, (0, α) ∈ (Graph.raw 0 text).cells ∧ 2 ≤ sig.arity α :=
  Graph.raw_cell 0 text 0 2 (by rw [raw_ends_direct]; decide)

/-- No end is a port of a cell that is not there, nor a port beyond the arity: computed
directly. -/
theorem no_stray_port : End.port 2 0 ∉ (Graph.raw 0 text).ends ∧
    End.port 0 3 ∉ (Graph.raw 0 text).ends := by
  rw [raw_ends_direct]
  decide

/-- `Graph.raw_count_name` on the text (page 71): the name `1`, which joins the two auxiliary ports
of the `con` cell, ends two wires, and the name `0` ends two wires; the names `2` and `3` end one.
-/
theorem names : (Graph.raw 0 text).ends.count (.name 1) = 2 ∧
    (Graph.raw 0 text).ends.count (.name 0) = 2 ∧
    (Graph.raw 0 text).ends.count (.name 2) = 1 ∧
    (Graph.raw 0 text).ends.count (.name 3) = 1 := by
  simp only [Graph.raw_count_name]
  decide

/-- The same counts, read off the direct computation. -/
theorem names_direct : (Graph.raw 0 text).ends.count (.name 1) = 2 ∧
    (Graph.raw 0 text).ends.count (.name 0) = 2 ∧
    (Graph.raw 0 text).ends.count (.name 2) = 1 ∧
    (Graph.raw 0 text).ends.count (.name 3) = 1 := by
  rw [raw_ends_direct]
  decide

/-- The text is linear, so `Graph.raw_count_name_le_two` applies to it (page 71). -/
theorem linear : (Net.ofList text).Linear := by
  have h : (Net.ofList text).vars = {0, 1, 1, 2, 3, 0} := by decide
  intro x
  rw [h]
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- `Graph.raw_count_name_le_two` on the text. -/
theorem names_le_two (x : ℕ) : (Graph.raw 0 text).ends.count (.name x) ≤ 2 :=
  Graph.raw_count_name_le_two 0 text linear x

end INet.GraphRawCheck
