import InteractionCombinators.Universality.RecursionFree.CellSkeleton

/-!
# Checks of `Lafont/CellSkeleton.lean` against Fig. 6 and Fig. 7 (page 86)

* `cellSkel_two` — the cell `[αᵢ]` of Fig. 6 for `m = 2`, `i = 0`, one auxiliary port: the tree
  drawn by hand.
* `cellSkel_cellSkel_instance` — `cellSkel_cellSkel` for `m = 2`, `i = 0`, `j = 1`, two-package
  menus, free wires on the auxiliary ports and empty context. Its linearity hypothesis is checked
  by computation, so the theorem is not vacuous.
-/

namespace INet.Comb.CellSkeletonCheck

open Term

/-- Fig. 6 (page 86) for `m = 2`, `i = 0`, one auxiliary port `2` and loop `4`: `T_{1,1}` is a `dup`
whose left auxiliary port carries a `con` on the menu `Γ` and the selector `S¹₂`, and whose right
auxiliary port is the loop. `S¹₂` is `M₂*`, a `con` with an eraser on its first auxiliary port and
its free port on the second; that free port is the root of `M₂`, a `con` on `2` and the loop `4`. -/
theorem cellSkel_two (Γ : Term sig ℕ) :
    cellSkel Γ 2 0 [var 2] 4 =
      mkDup (mkCon Γ (mkCon mkEra (mkCon (var 2) (var 4)))) (var 4) :=
  rfl

/-- The first two rows of Fig. 7 (page 86) on a concrete pair of cells: menus `ε & γ(0, 0)` and
`γ(1, 1) & ε`, auxiliary wires `2` and `3`, loops `4` and `5`. The selector `S¹₂` (index 0) of the
first cell extracts `γ(1, 1)` from the second menu, the selector `S²₂` (index 1) of the second cell
extracts `γ(0, 0)` from the first menu, and both multiplexors end on the joined loop `4`. -/
theorem cellSkel_cellSkel_instance :
    ∃ M, StepsE system
      ({s(cellSkel (menu [mkEra, mkCon (var 0) (var 0)]) 2 0 [var 2] 4,
          cellSkel (menu [mkCon (var 1) (var 1), mkEra]) 2 1 [var 3] 5)} : CNet) M ∧
      Equiv M (s(mux [var 2, var 4], mkCon (var 1) (var 1)) ::ₘ
        {s(mux [var 3, var 4], mkCon (var 0) (var 0))}) := by
  have hpi : ∀ π ∈ [mkEra, mkCon (var 0) (var 0)], (π : Term sig ℕ).IsPackage := by
    intro π hπ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hπ
    rcases hπ with rfl | rfl
    · exact isPackage_mkEra
    · exact isPackage_mkCon_var 0
  have hpj : ∀ π ∈ [mkCon (var 1) (var 1), mkEra], (π : Term sig ℕ).IsPackage := by
    intro π hπ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hπ
    rcases hπ with rfl | rfl
    · exact isPackage_mkCon_var 1
    · exact isPackage_mkEra
  have hlin : Net.Linear
      ({s(cellSkel (menu [mkEra, mkCon (var 0) (var 0)]) 2 0 [var 2] 4,
          cellSkel (menu [mkCon (var 1) (var 1), mkEra]) 2 1 [var 3] 5)} : CNet) := by
    intro y
    simp only [cellSkel, menu, Net.vars_singleton, eqVars_mk, vars_transpositor, vars_cellSel,
      vars_mux, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.sum_cons,
      List.sum_nil, vars_mkEra, vars_mkCon, vars_var, Multiset.count_add, Multiset.count_singleton,
      Multiset.count_zero]
    split_ifs <;> omega
  exact cellSkel_cellSkel _ _ 2 0 1 rfl rfl (by omega) (by omega) hpi hpj [var 2] [var 3] 4 5 0
    hlin

end INet.Comb.CellSkeletonCheck
