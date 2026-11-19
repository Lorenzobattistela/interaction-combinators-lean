import InteractionCombinators.Graphs.GraphContractUnique
import Checks.Core.GraphReview

/-!
# Check of `Lafont/GraphContractUnique.lean`

* The chain `a = x, x = y, y = b`, with `a, x, y, b = 0, 1, 2, 3`: the names `x` and `y` share the
  wire `s(x, y)`. Erasing `x` first gives the wire `s(a, b)`, erasing `y` first gives `s(b, a)`;
  `Graph.contracts_unique` and `Net.Linear.contracts_unique` prove the two results equal.
* The cycle `x = y, y = x`: erasing `x` or `y` first, both orders give one cyclic wire.
* `EraseName.unique` and `EraseName.comm` on the chain, with their hypotheses satisfied.

Lafont 1997, page 71.
-/

namespace INet.GraphContractUniqueCheck

open Comb Graph GraphReview

/-! ## A chain of names -/

/-- `a = x, x = y, y = b`. -/
def chain : List (Term sig ℕ × Term sig ℕ) := [(.var 0, .var 1), (.var 1, .var 2), (.var 2, .var 3)]

/-- Its raw graph: three wires, the names `1` and `2` end two of them. -/
theorem raw_chain : Graph.raw 0 chain =
    (⟨0, s(.name 0, .name 1) ::ₘ s(.name 1, .name 2) ::ₘ {s(.name 2, .name 3)}, 0⟩ :
      Graph sig ℕ) := rfl

/-- The text is linear. -/
theorem linear_chain : (Net.ofList chain).Linear := by
  have h : (Net.ofList chain).vars = {0, 1, 1, 2, 2, 3} := by decide
  intro x
  rw [h]
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- Erasing `x`, then `y`: the wire `s(a, b)`. -/
def endX : Graph sig ℕ := ⟨0, {s(.name 0, .name 3)}, 0⟩

/-- Erasing `y`, then `x`: the wire `s(b, a)`. -/
def endY : Graph sig ℕ := ⟨0, {s(.name 3, .name 0)}, 0⟩

/-- First order: `x`, then `y` (page 71). -/
theorem contracts_x_first : Relation.ReflTransGen Contract (Graph.raw 0 chain) endX :=
  .head (b := ⟨0, s(.name 0, .name 2) ::ₘ {s(.name 2, .name 3)}, 0⟩)
    (join_of 1 (.name 0) (.name 2) {s(.name 2, .name 3)} (by decide) rfl rfl rfl)
    (.single (join_of 2 (.name 0) (.name 3) 0 (by decide) rfl rfl rfl))

/-- Second order: `y`, then `x` (page 71). -/
theorem contracts_y_first : Relation.ReflTransGen Contract (Graph.raw 0 chain) endY :=
  .head (b := ⟨0, s(.name 1, .name 3) ::ₘ {s(.name 0, .name 1)}, 0⟩)
    (join_of 2 (.name 1) (.name 3) {s(.name 0, .name 1)} (by decide) rfl rfl rfl)
    (.single (join_of 1 (.name 3) (.name 0) 0 (by decide) rfl rfl rfl))

theorem endX_names (x : ℕ) : endX.ends.count (.name x) ≤ 1 := ((wf_iff _).2 (by decide)).name x

theorem endY_names (x : ℕ) : endY.ends.count (.name x) ≤ 1 := ((wf_iff _).2 (by decide)).name x

/-- `Graph.contracts_unique` on the two orders: the results are equal. -/
theorem endX_eq_endY : endX = endY :=
  Graph.contracts_unique
    (Graph.raw_count_name_le_two 0 chain linear_chain)
    contracts_x_first contracts_y_first endX_names endY_names

/-- `Net.Linear.contracts_unique` on the two orders. -/
theorem endX_eq_endY' : endX = endY :=
  linear_chain.contracts_unique rfl 0 contracts_x_first contracts_y_first endX_names endY_names

/-- The same equality, by computation: it is not vacuous. -/
theorem endX_eq_endY_decide : endX = endY := by
  unfold endX endY
  rw [Sym2.eq_swap]

/-- `EraseName.unique` with its hypothesis satisfied: two ways of writing the wires at `x`. -/
theorem unique_chain :
    ((s(.name 2, .name 0) : Sym2 (End ℕ)) ::ₘ {s(.name 2, .name 3)}) =
      s(.name 0, .name 2) ::ₘ {s(.name 2, .name 3)} ∧ (0 : ℕ) = 0 := by
  have A : (s(.name 0, .name 1) ::ₘ s(.name 1, .name 2) ::ₘ {s(.name 2, .name 3)} :
      Multiset (Sym2 (End ℕ))) = s(.name 1, .name 2) ::ₘ s(.name 1, .name 0) ::ₘ
        {s(.name 2, .name 3)} := by decide
  have A' : (s(.name 0, .name 1) ::ₘ s(.name 1, .name 2) ::ₘ {s(.name 2, .name 3)} :
      Multiset (Sym2 (End ℕ))) = s(.name 1, .name 0) ::ₘ s(.name 1, .name 2) ::ₘ
        {s(.name 2, .name 3)} := by decide
  have h := EraseName.join (x := 1) (.name 2) (.name 0) {s(.name 2, .name 3)}
  have h' := EraseName.join (x := 1) (.name 0) (.name 2) {s(.name 2, .name 3)}
  rw [← A] at h
  rw [← A'] at h'
  exact EraseName.unique (by decide) h h'

/-- `EraseName.comm` on the chain, with `x = 1`, `y = 2`, which share the wire `s(x, y)`. -/
theorem comm_chain : ∃ B₂ d₂ K e₁ e₂,
    EraseName 2 (s(.name 1, .name 0) ::ₘ s(.name 1, .name 2) ::ₘ {s(.name 2, .name 3)})
      B₂ d₂ ∧ EraseName 2 (s(.name 0, .name 2) ::ₘ {s(.name 2, .name 3)}) K e₁ ∧
      EraseName (1 : ℕ) B₂ K e₂ ∧ 0 + e₁ = d₂ + e₂ :=
  EraseName.comm (by decide) (.join (.name 0) (.name 2) _) (by decide)

/-! ## A cycle -/

/-- `x = y, y = x`. -/
def cycle : List (Term sig ℕ × Term sig ℕ) := [(.var 0, .var 1), (.var 1, .var 0)]

/-- The text is linear. -/
theorem linear_cycle : (Net.ofList cycle).Linear := by
  have h : (Net.ofList cycle).vars = {0, 1, 1, 0} := by decide
  intro x
  rw [h]
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- Erasing `x` first: the wire `s(y, y)`, then a cyclic wire. -/
theorem cycle_x_first :
    Relation.ReflTransGen Contract (Graph.raw 0 cycle) (⟨0, 0, 1⟩ : Graph sig ℕ) :=
  .head (b := ⟨0, {s(.name 1, .name 1)}, 0⟩)
    (join_of 0 (.name 1) (.name 1) 0 (by decide) rfl rfl rfl)
    (.single (loop_of 1 0 rfl rfl rfl rfl))

/-- Erasing `y` first: the wire `s(x, x)`, then a cyclic wire. -/
theorem cycle_y_first :
    Relation.ReflTransGen Contract (Graph.raw 0 cycle) (⟨0, 0, 1⟩ : Graph sig ℕ) :=
  .head (b := ⟨0, {s(.name 0, .name 0)}, 0⟩)
    (join_of 1 (.name 0) (.name 0) 0 (by decide) rfl rfl rfl)
    (.single (loop_of 0 0 rfl rfl rfl rfl))

/-- The two intermediate graphs differ, and the local diamond closes them in one step each. -/
theorem cycle_diamond :
    (⟨0, {s(.name 1, .name 1)}, 0⟩ : Graph sig ℕ) ≠ ⟨0, {s(.name 0, .name 0)}, 0⟩ ∧
    ∃ K, Contract (⟨0, {s(.name 1, .name 1)}, 0⟩ : Graph sig ℕ) K ∧
      Contract (⟨0, {s(.name 0, .name 0)}, 0⟩ : Graph sig ℕ) K := by
  have ne : (⟨0, {s(.name 1, .name 1)}, 0⟩ : Graph sig ℕ) ≠ ⟨0, {s(.name 0, .name 0)}, 0⟩ :=
    fun h => absurd (congrArg Graph.wires h) (by decide)
  refine ⟨ne, ?_⟩
  rcases Contract.diamond (G := Graph.raw 0 cycle)
    (Graph.raw_count_name_le_two 0 cycle linear_cycle)
    (join_of (H := ⟨0, {s(.name 1, .name 1)}, 0⟩) 0 (.name 1) (.name 1) 0 (by decide) rfl rfl rfl)
    (join_of (H := ⟨0, {s(.name 0, .name 0)}, 0⟩) 1 (.name 0) (.name 0) 0 (by decide) rfl rfl
      rfl) with h | h
  · exact absurd h ne
  · exact h

/-- `Net.Linear.contracts_unique` on the cycle (page 71). -/
theorem cycle_unique : (⟨0, 0, 1⟩ : Graph sig ℕ) = ⟨0, 0, 1⟩ :=
  linear_cycle.contracts_unique rfl 0 cycle_x_first cycle_y_first cyclic_wf.name cyclic_wf.name

end INet.GraphContractUniqueCheck
