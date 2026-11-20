import InteractionCombinators.Universality.General.CodeCell

/-!
# Review of `InteractionCombinators/Universality/General/CodeCell.lean` against Fig. 10 (page 89)
and page 90

Checks of the cell `⟨α_k⟩` and of the extraction `codeCell_code`, beyond `CodeCellCheck.lean`
(whose menu `ε & ε` has no names, so there the renamings `f`, `g`, `g'` act on nothing).

* `codeCell_literal` — `⟨α_1⟩` for `m = 2` and one auxiliary port, written out cell by cell: the
  port order of Fig. 10 (bottom left), and the right nesting of `M_{n_k+2}` (Fig. 4).
* `codeCell_code_linear` — the conclusion of `codeCell_code` is a linear net: the renamed menu
  entry, the renamed code and the context `Δ` share no name.
* `codeCell_code_dup` — `codeCell_code` on the menu `δ(0, 0) & γ(1, 1)`, whose code has a cut name,
  with `k = 1` (the second entry) and the renaming `f = (· + 300)`. The cell obtained carries a
  renamed `γ(a, a)`, the entry of index 1, and not the `dup` cell of index 0.
-/

namespace INet.Comb.CodeCellReview

open Term

/-- **`⟨α_1⟩` written out** (Fig. 10, bottom left, page 89), for `m = 2`, one auxiliary port
carrying `101`, the tree `99` on the extra port and `100` on the principal port:

* the extra port is the principal port of `C_2 = δ(·, ·)`; its left auxiliary port carries the
  decoder `D` (an `M_4*` whose free port is `202`), its right auxiliary port is the wire `201`;
* the free port `202` of `D` is the root of `S²_2 = M_2*(ε, 203)`, whose free port is `203`;
* `T_{1,1}` carries, from left to right, the wire `203`, the selector `S²_2` on the root of
  `M_3 = γ(201, γ(101, 200))`, and the loop `200`. The wire `201` is the first leaf of `M_3`, and
  `M_3` is nested to the right (Fig. 4). -/
theorem codeCell_literal :
    (codeCell 2 1 (var 100) (var 99) [var 101] 200 201 202 203 204 : CNet) =
      s(var 99, mkDup (muxStar [mkDup (var 204) (var 205), var 204, var 205, var 202])
          (var 201)) ::ₘ
        s(var 202, muxStar [mkEra, var 203]) ::ₘ
        s(var 100, transpositor 1 [var 203,
          muxStar [mkEra, mkCon (var 201) (mkCon (var 101) (var 200))], var 200]) ::ₘ 0 :=
  rfl

/-- **The net obtained by the extraction of page 90 is linear.** Under the hypotheses of
`codeCell_code`, the cell `[α_k]` with the renamed entry `Γ_k` and the renamed code `!Γ`, next to
the context `Δ`, is a linear net. So the renamings `g` and `g'` given by `codeCell_code` take
values that are new for each other and for `Δ`. -/
theorem codeCell_code_linear (Γs : List (Term sig ℕ)) (hp : ∀ π ∈ Γs, π.IsPackage)
    (hΓ : (menu Γs).IsPackage) (K : ℕ) (hb : (menu Γs).Below K) (k : ℕ) (hk : k < Γs.length)
    (f : ℕ → ℕ) (hf : Set.InjOn f {x | x ∈ (code K (menu Γs)).vars})
    (P : Term sig ℕ) (ts : List (Term sig ℕ)) (ℓ u w y k₀ : ℕ) (Δ : CNet)
    (hlin : Net.Linear (codeCell Γs.length k P ((code K (menu Γs)).bind fun x => var (f x)) ts
      ℓ u w y k₀ + Δ)) :
    ∃ (g g' : ℕ → ℕ), Set.InjOn g {x | x ∈ (code K (menu Γs)).vars} ∧
      Set.InjOn g' {x | x ∈ (code K (menu Γs)).vars} ∧
      Net.Linear (s(P, cellSkel (Γs[k].bind fun x => var (g x)) Γs.length k
        (((code K (menu Γs)).bind fun x => var (g' x)) :: ts) ℓ) ::ₘ Δ) := by
  obtain ⟨g, g', M, hg, hg', hS, hE⟩ :=
    codeCell_code Γs hp hΓ K hb k hk f hf P ts ℓ u w y k₀ Δ hlin
  exact ⟨g, g', hg, hg', hE.linear (hS.linear system_wellFormed.linear hlin)⟩

/-- The menu `δ(0, 0) & γ(1, 1)` (page 84): two packages, the first one a `dup` cell, so that the
code has a cut name. -/
abbrev dupMenu : List (Term sig ℕ) := [mkDup (var 0) (var 0), mkCon (var 1) (var 1)]

/-- Both entries of `dupMenu` are packages. -/
theorem dupMenu_packages : ∀ π ∈ dupMenu, π.IsPackage := by
  intro π hπ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hπ
  rcases hπ with rfl | rfl <;> (unfold Term.IsPackage; decide)

/-- The menu `δ(0, 0) & γ(1, 1)` is a package (`IsPackage.menu`, page 84). -/
theorem dupMenu_isPackage : (menu dupMenu).IsPackage :=
  IsPackage.menu _ dupMenu_packages (by decide)

/-- The names of `δ(0, 0) & γ(1, 1)` are below `2`. -/
theorem dupMenu_below : (menu dupMenu).Below 2 := by
  unfold Term.Below; decide

/-- The net of `codeCell_code` for `dupMenu`: a copy of `!Γ` renamed by `· + 300` on the extra
port of `⟨α_1⟩` (Fig. 10, page 89), with `100` on the principal port and `101` on the auxiliary
port. -/
abbrev extractNet : CNet :=
  codeCell dupMenu.length 1 (var 100) ((code 2 (menu dupMenu)).bind fun x => var (x + 300))
    [var 101] 200 201 202 203 204

/-- The names of `extractNet`: those of the renamed code (`300`, `301` and the cut name `304`, each
twice), of the decoder loop `204, 205`, of the internal wires `200`–`203`, and the free ports
`100`, `101`. -/
theorem extractNet_vars : Net.vars (extractNet + 0) =
    {304, 300, 300, 304, 301, 301, 202, 204, 205, 204, 205, 201, 202, 203, 100, 203, 201, 101,
      200, 200} := by
  decide

/-- `extractNet` is linear. -/
theorem extractNet_linear : Net.Linear (extractNet + 0) := by
  intro x
  rw [extractNet_vars]
  by_cases hx : x ∈ ({304, 300, 300, 304, 301, 301, 202, 204, 205, 204, 205, 201, 202, 203, 100,
    203, 201, 101, 200, 200} : Multiset ℕ)
  · revert x; decide
  · rw [Multiset.count_eq_zero.2 hx]; omega

/-- **`codeCell_code` on `δ(0, 0) & γ(1, 1)`, with `k = 1`** (page 90). A copy of `!Γ` renamed by
`· + 300` on the extra port of `⟨α_1⟩` reduces to the cell `[α_1]` whose menu is a renamed
`γ(a, a)` (the entry of index 1, not the `dup` cell of index 0) and whose first leaf is a renamed
copy of `!Γ`; the result is linear. -/
theorem codeCell_code_dup :
    ∃ (a : ℕ) (g' : ℕ → ℕ) (M : CNet), StepsE system (extractNet + 0) M ∧
      Equiv M (s(var 100, cellSkel (mkCon (var a) (var a)) 2 1
        (((code 2 (menu dupMenu)).bind fun x => var (g' x)) :: [var 101]) 200) ::ₘ 0) ∧
      Net.Linear (s(var 100, cellSkel (mkCon (var a) (var a)) 2 1
        (((code 2 (menu dupMenu)).bind fun x => var (g' x)) :: [var 101]) 200) ::ₘ 0) := by
  obtain ⟨g, g', M, -, -, hS, hE⟩ := codeCell_code dupMenu dupMenu_packages
    dupMenu_isPackage 2 dupMenu_below 1 (by decide) (· + 300)
    (fun _ _ _ _ h => Nat.add_right_cancel h) (var 100) [var 101] 200 201 202 203 204 0
    extractNet_linear
  have hk : (dupMenu[1].bind fun x => var (g x)) = mkCon (var (g 1)) (var (g 1)) := by
    simp only [dupMenu, List.getElem_cons_succ, List.getElem_cons_zero, mkCon, Term.bind]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hk] at hE
  exact ⟨g 1, g', M, hS, hE, hE.linear (hS.linear system_wellFormed.linear extractNet_linear)⟩

end INet.Comb.CodeCellReview
