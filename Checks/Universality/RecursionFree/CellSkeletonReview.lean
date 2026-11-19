import Checks.Universality.RecursionFree.CellSkeletonCheck

/-!
# Review of `Lafont/CellSkeleton.lean` against Figs. 6 and 7 (page 86)

Attempts to refute `cellSkel_cellSkel` on instances that `cellSkel_cellSkel_instance` does not
cover, and checks on the two loops.

* `cellSkel_cellSkel_diag` — the case `αᵢ ⋈ αᵢ` (`i = j = 1`, `m = 2`), with a non-empty context
  that closes the auxiliary wires of the two cells.
* `cellSkel_cellSkel_nullary` — a cell of arity 0 (`ts = []`) against a cell of arity 2.
* `cellSkel_cellSkel_three` — `m = 3`, `i = 2`, `j = 0`.
* `count_cellSkel_loop`, `cellSkel_same_loop_not_linear` — the loop `ℓ` occurs twice in a cell, so
  two cells sharing the same loop name never form a linear net: the hypothesis of
  `cellSkel_cellSkel` forces `ℓ ≠ ℓ'`, and the conclusion names the joined wire `ℓ`.
* `cellSkel_cellSkel_linear` — the conclusion of `cellSkel_cellSkel` is a linear net, so the
  joined loop `ℓ` occurs exactly as a wire between the two multiplexors.
-/

namespace INet.Comb.CellSkeletonReview

open Term

/-- The case `αᵢ ⋈ αᵢ` of Fig. 7 (page 86): two cells with the same index `i = j = 1` among
`m = 2` symbols, menus `ε & γ(0, 0)` and `γ(1, 1) & ε`, auxiliary wires `2` and `3` joined by the
context `2 = 3`, loops `4` and `5`. The first cell gets the package of index 1 of the second menu
(`ε`), the second cell the package of index 1 of the first menu (`γ(0, 0)`), and the context is
kept. -/
theorem cellSkel_cellSkel_diag :
    ∃ M, StepsE system
      (s(cellSkel (menu [mkEra, mkCon (var 0) (var 0)]) 2 1 [var 2] 4,
          cellSkel (menu [mkCon (var 1) (var 1), mkEra]) 2 1 [var 3] 5) ::ₘ
        {s(var 2, var 3)} : CNet) M ∧
      Equiv M (s(mux [var 2, var 4], mkEra) ::ₘ s(mux [var 3, var 4], mkCon (var 0) (var 0)) ::ₘ
        {s(var 2, var 3)}) := by
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
      (s(cellSkel (menu [mkEra, mkCon (var 0) (var 0)]) 2 1 [var 2] 4,
          cellSkel (menu [mkCon (var 1) (var 1), mkEra]) 2 1 [var 3] 5) ::ₘ
        {s(var 2, var 3)} : CNet) := by
    intro y
    simp only [cellSkel, menu, Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_transpositor,
      vars_cellSel, vars_mux, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.sum_cons, List.sum_nil, vars_mkEra, vars_mkCon, vars_var, Multiset.count_add,
      Multiset.count_singleton, Multiset.count_zero]
    split_ifs <;> omega
  exact cellSkel_cellSkel _ _ 2 1 1 rfl rfl (by omega) (by omega) hpi hpj [var 2] [var 3] 4 5 _
    hlin

/-- A cell of arity 0 (Fig. 7, page 86): `ts = []`, so `M₁` is a wire and the free port of the
selector is the loop itself. Against a cell of arity 2 with auxiliary wires `3`, `6`: the cell of
arity 0 ends as the loop `4` against the package `γ(1, 1)`, the other as `M₃` on `3, 6, 4` against
`γ(0, 0)`. -/
theorem cellSkel_cellSkel_nullary :
    ∃ M, StepsE system
      ({s(cellSkel (menu [mkEra, mkCon (var 0) (var 0)]) 2 0 [] 4,
          cellSkel (menu [mkCon (var 1) (var 1), mkEra]) 2 1 [var 3, var 6] 5)} : CNet) M ∧
      Equiv M (s(var 4, mkCon (var 1) (var 1)) ::ₘ
        {s(mux [var 3, var 6, var 4], mkCon (var 0) (var 0))}) := by
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
      ({s(cellSkel (menu [mkEra, mkCon (var 0) (var 0)]) 2 0 [] 4,
          cellSkel (menu [mkCon (var 1) (var 1), mkEra]) 2 1 [var 3, var 6] 5)} : CNet) := by
    intro y
    simp only [cellSkel, menu, Net.vars_singleton, eqVars_mk, vars_transpositor, vars_cellSel,
      vars_mux, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.sum_cons,
      List.sum_nil, vars_mkEra, vars_mkCon, vars_var, Multiset.count_add,
      Multiset.count_singleton, Multiset.count_zero]
    split_ifs <;> omega
  exact cellSkel_cellSkel _ _ 2 0 1 rfl rfl (by omega) (by omega) hpi hpj [] [var 3, var 6] 4 5 0
    hlin

/-- `cellSkel_cellSkel` for `m = 3`, `i = 2`, `j = 0` (Fig. 7, page 86): menus
`ε & ε & γ(0, 0)` and `γ(1, 1) & ε & ε`. The selector `S³₃` of the first cell takes the last
package `ε` of the second menu, the selector `S¹₃` of the second cell takes the first package
`ε` of the first menu: the packages `γ(0, 0)` and `γ(1, 1)` are not the ones selected. -/
theorem cellSkel_cellSkel_three :
    ∃ M, StepsE system
      ({s(cellSkel (menu [mkEra, mkEra, mkCon (var 0) (var 0)]) 3 2 [var 2] 4,
          cellSkel (menu [mkCon (var 1) (var 1), mkEra, mkEra]) 3 0 [var 3] 5)} : CNet) M ∧
      Equiv M (s(mux [var 2, var 4], mkEra) ::ₘ {s(mux [var 3, var 4], mkEra)}) := by
  have hpi : ∀ π ∈ [mkEra, mkEra, mkCon (var 0) (var 0)], (π : Term sig ℕ).IsPackage := by
    intro π hπ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hπ
    rcases hπ with rfl | rfl | rfl
    · exact isPackage_mkEra
    · exact isPackage_mkEra
    · exact isPackage_mkCon_var 0
  have hpj : ∀ π ∈ [mkCon (var 1) (var 1), mkEra, mkEra], (π : Term sig ℕ).IsPackage := by
    intro π hπ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hπ
    rcases hπ with rfl | rfl | rfl
    · exact isPackage_mkCon_var 1
    · exact isPackage_mkEra
    · exact isPackage_mkEra
  have hlin : Net.Linear
      ({s(cellSkel (menu [mkEra, mkEra, mkCon (var 0) (var 0)]) 3 2 [var 2] 4,
          cellSkel (menu [mkCon (var 1) (var 1), mkEra, mkEra]) 3 0 [var 3] 5)} : CNet) := by
    intro y
    simp only [cellSkel, menu, Net.vars_singleton, eqVars_mk, vars_transpositor, vars_cellSel,
      vars_mux, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.sum_cons,
      List.sum_nil, vars_mkEra, vars_mkCon, vars_var, Multiset.count_add,
      Multiset.count_singleton, Multiset.count_zero]
    split_ifs <;> omega
  exact cellSkel_cellSkel _ _ 3 2 0 rfl rfl (by omega) (by omega) hpi hpj [var 2] [var 3] 4 5 0
    hlin

/-- The loop `ℓ` of a cell `[αᵢ]` (Fig. 6, page 86) occurs at least twice in it: on the last port
of `T_{1,1}` and on the last auxiliary port of `M_{nᵢ+1}`. -/
theorem count_cellSkel_loop (Γ : Term sig ℕ) (m i : ℕ) (ts : List (Term sig ℕ)) (ℓ : ℕ) :
    2 ≤ (cellSkel Γ m i ts ℓ).vars.count ℓ := by
  simp only [cellSkel, vars_transpositor, vars_cellSel, vars_mux, List.map_cons, List.map_nil,
    List.map_append, List.sum_append, List.sum_cons, List.sum_nil, vars_var, add_zero,
    Multiset.count_add, Multiset.count_singleton_self]
  omega

/-- Two cells of Fig. 7 (page 86) with the same loop name never form a linear net: the hypothesis
of `cellSkel_cellSkel` forces `ℓ ≠ ℓ'`, and naming the joined loop `ℓ` in its conclusion is not a
collision of names. -/
theorem cellSkel_same_loop_not_linear (Γ Γ' : Term sig ℕ) (m i j : ℕ)
    (ts us : List (Term sig ℕ)) (ℓ : ℕ) (Δ : CNet) :
    ¬ Net.Linear (s(cellSkel Γ m i ts ℓ, cellSkel Γ' m j us ℓ) ::ₘ Δ) := by
  intro h
  have h1 := h ℓ
  have a := count_cellSkel_loop Γ m i ts ℓ
  have b := count_cellSkel_loop Γ' m j us ℓ
  simp only [Net.vars_cons, eqVars_mk, Multiset.count_add] at h1
  omega

/-- The conclusion of `cellSkel_cellSkel` (Fig. 7, page 86) is a linear net: the joined loop `ℓ`,
named on both multiplexors, is a wire between them and occurs nowhere else. -/
theorem cellSkel_cellSkel_linear (Gi Gj : List (Term sig ℕ)) (m i j : ℕ) (hGi : Gi.length = m)
    (hGj : Gj.length = m) (hi : i < m) (hj : j < m) (hpi : ∀ π ∈ Gi, π.IsPackage)
    (hpj : ∀ π ∈ Gj, π.IsPackage) (ts us : List (Term sig ℕ)) (ℓ ℓ' : ℕ) (Δ : CNet)
    (hlin : Net.Linear (s(cellSkel (menu Gi) m i ts ℓ, cellSkel (menu Gj) m j us ℓ') ::ₘ Δ)) :
    Net.Linear (s(mux (ts ++ [var ℓ]), Gj[i]'(hGj ▸ hi)) ::ₘ
        s(mux (us ++ [var ℓ]), Gi[j]'(hGi ▸ hj)) ::ₘ Δ) := by
  obtain ⟨M, hS, hE⟩ := cellSkel_cellSkel Gi Gj m i j hGi hGj hi hj hpi hpj ts us ℓ ℓ' Δ hlin
  exact hE.linear (hS.linear system_wellFormed.linear hlin)

end INet.Comb.CellSkeletonReview
