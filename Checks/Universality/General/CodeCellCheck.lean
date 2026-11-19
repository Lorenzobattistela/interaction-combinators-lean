import InteractionCombinators.Universality.General.CodeCell

/-!
# Check: the hypotheses of `codeCell_code` hold for a concrete menu (page 90)

The menu `Γ = ε & ε` of two packages (two erasers), `k = 0`, new names of the code from `K = 0`,
the identity as renaming `f`, the tree `var 100` on the principal port of `⟨α_0⟩`, one auxiliary
port carrying `var 101`, and the internal names `ℓ = 200`, `u = 201`, `w = 202`, `y = 203`,
`k₀ = 204` (so the loop of the decoder is `204, 205`). Every hypothesis of `codeCell_code` holds,
linearity included, so the theorem is not vacuous; `codeCell_code_example` applies it.
-/

namespace INet.Comb

open Term

/-- The menu `ε & ε` of page 84. -/
abbrev checkMenu : List (Term sig ℕ) := [mkEra, mkEra]

/-- The net of `codeCell_code` for the menu `ε & ε`: `!Γ` on the extra port of `⟨α_0⟩`
(Fig. 10, page 89). -/
abbrev checkNet : CNet :=
  codeCell checkMenu.length 0 (var 100) ((code 0 (menu checkMenu)).bind fun x => var x)
    [var 101] 200 201 202 203 204

/-- Both entries of the menu are packages. -/
theorem checkMenu_packages : ∀ π ∈ checkMenu, π.IsPackage := by
  intro π hπ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hπ
  rcases hπ with rfl | rfl <;> exact isPackage_mkEra

/-- The menu `ε & ε` is a package (`IsPackage.menu`, page 84). -/
theorem checkMenu_isPackage : (menu checkMenu).IsPackage :=
  IsPackage.menu _ checkMenu_packages (by simp [vars_mkEra])

/-- The menu `ε & ε` has no name, so its names are below `0`. -/
theorem checkMenu_below : (menu checkMenu).Below 0 := by
  unfold Term.Below; decide

/-- The names of `checkNet`: the decoder loop `204, 205`, and `200`, `201`, `202`, `203` twice
each; the free ports `100` and `101` once. -/
theorem checkNet_vars : Net.vars (checkNet + 0) =
    {202, 204, 204, 205, 205, 201, 202, 203, 100, 203, 201, 101, 200, 200} := by
  simp only [checkNet, codeCell, add_zero, Net.vars_cons, Net.vars_zero, eqVars_mk,
    copier, vars_autoMux, vars_decoder,
    selector_eq_cellSel, vars_cellSel, vars_cellSkel, vars_var, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  decide

/-- The net `checkNet` is linear: every name occurs at most twice. -/
theorem checkNet_linear : Net.Linear (checkNet + 0) := by
  intro x
  rw [checkNet_vars]
  by_cases hx : x ∈ ({202, 204, 204, 205, 205, 201, 202, 203, 100, 203, 201, 101, 200, 200} :
    Multiset ℕ)
  · revert x; decide
  · rw [Multiset.count_eq_zero.2 hx]; omega

/-- **`codeCell_code` applies** to the menu `ε & ε` (page 90): `!Γ` on the extra port of `⟨α_0⟩`
reduces to `[α_0]`, the cell of Fig. 10 whose menu is a renamed `ε` and whose first leaf is a
renamed copy of `!Γ`. -/
theorem codeCell_code_example :
    ∃ (g g' : ℕ → ℕ) (M : CNet), StepsE system (checkNet + 0) M ∧
      Equiv M (s(var 100, cellSkel (checkMenu[0].bind fun x => var (g x)) 2 0
        (((code 0 (menu checkMenu)).bind fun x => var (g' x)) :: [var 101]) 200) ::ₘ 0) := by
  obtain ⟨g, g', M, -, -, hS, hE⟩ := codeCell_code checkMenu checkMenu_packages
    checkMenu_isPackage 0 checkMenu_below 0 (by decide) (fun x => x)
    (fun _ _ _ _ h => h) (var 100) [var 101] 200 201 202 203 204 0 checkNet_linear
  exact ⟨g, g', M, hS, hE⟩

end INet.Comb
