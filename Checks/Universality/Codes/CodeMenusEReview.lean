import Checks.Universality.Codes.CodeMenusECheck

/-!
# Review of the menus of Fig. 10 for a given enumeration `e : S.Sym ≃ Fin n` (pages 89-90)

Review of `codeCellSizesE`, `codeCellMenuE`, `codeMenuSizesE` and `codeMenusE` (`CodeGamma.lean`)
against Fig. 10 (journal page 89, PDF page 21, rendered at 300 dpi) and the text of page 90.

Fig. 10 reads `Γ_i = Γ_{1,i} & ⋯ & Γ_{m,i}`, and `Γ_{i,j}` is built from `φ_{i,j}`, the side of
`α_i` in the rule `α_i`–`α_j`, under `M*_{n_i+2}`. In `[α_i]` the selector `S^i_m` meets the menu
`Γ_j` of the other cell and picks its `i`-th entry `Γ_{i,j}`, whose `M*_{n_i+2}` faces the
`M_{n_i+2}` of `[α_i]`. So the `j`-th entry of the menu of `β` must be built from the side of
`α_j` against `β`, with the arity of `α_j`.

* `getElem_codeCellMenuE` — for every `e`, the entry of `Γ_β` at the number `e α` is the package
  built from `side α β` (the side of `α` against `β`): the orientation of Fig. 10.
* `codeCellMenuE_combEnum_con`, `codeCellMenuE_combEnum_dup` — with `sideConDup` (only a side of
  `con` against `dup`), `Γ_con` is three erasers and `Γ_dup` holds `Γ_{con,dup}` at the number of
  `con`. The other orientation would put the package in `Γ_con`.
* `codeMenusE_e₁`, `codeMenusE_e₂` — with the asymmetric choice `sideAsym` (a side of `con` against
  `con` and one of `con` against `dup`) and the two numberings `combEnum` (`con, dup ↦ 0, 1`) and
  `combEnum₂` (`dup, con ↦ 0, 1`), the menus written out. The menus are listed in the order of `e`,
  and the packages inside each menu too. The name blocks follow the sizes in the order of `e`
  (`Γ_con` takes `[0, 24)` under `combEnum`, `[24, 48)` under `combEnum₂`) and do not overlap
  (`vars_codeMenusE_e₁`, `vars_codeMenusE_e₂`).
* `codeGamma_idx_ne` — the two menus do not differ only by the order of packages and names: inside
  `Γ_{i,j}`, each `⟨α_k⟩` carries the selector `S^{e α_k}_m`, so the selectors change with `e` too.
  This is harmless: `[β]` selects with the same number `e β` (`codeCell … (e β)` in
  `codeCell_code_codeMenusE`), so the whole translation is renumbered consistently.
* `sum_codeMenuSizesE`, `vars_menu_codeMenusE_indep` — the number of names of `Γ`, and so the
  names of `Γ`, do not depend on `e`.
* `codeCell_code_codeMenusE_satisfiable` — the hypotheses `hK`, `hf`, `hlin` of
  `codeCell_code_codeMenusE` hold for every `e` and `side`; with `combEnum` and `sideConDup` the
  theorem is applied and its conclusion obtained. `codeMenusE_isPackage` and
  `menu_codeMenusE_below` have no hypotheses beyond `e`, `side`, `k₀`; they are instantiated on
  `combEnum`.

Page 90 does not say in words "no order on the symbols is needed": the docstrings of
`CodeGamma.lean` paraphrase. Section 2.6 (page 86) assumes "that the alphabet can be ordered" so
that each `φ_{i,j}` uses only smaller symbols; Section 2.7 (the general case, pages 88-90) makes no
such assumption, and nothing in Fig. 10 needs one: the numbering `α_1, …, α_m` only fixes the
positions of the menus and of the selectors.
-/

namespace INet.Comb.CodeMenusEReview

open Term Rule Translation DecompositionReview ExpandedIso ExpandTrReview GammaCheck
  CodeGammaCheck CodeGammaReview CodeMenusECheck

/-! ## Orientation, for every numbering -/

section General

variable {S : Signature} {n : ℕ} (e : S.Sym ≃ Fin n)
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **The entry of `Γ_β` at the number of `α` is `Γ_{α,β}`** (Fig. 10, page 89), for every
numbering `e`: the package built from the side of `α` against `β`, on the block of `α`. -/
theorem getElem_codeCellMenuE (α β : S.Sym) (k₀ : ℕ)
    (h : (e α : ℕ) < (codeCellMenuE e side β k₀).length) :
    (codeCellMenuE e side β k₀)[(e α : ℕ)]'h =
      codeGammaOpt n (fun γ => e γ) (side α β) (k₀ + off (codeCellSizesE e side β) (e α)) := by
  simp only [codeCellMenuE, List.getElem_ofFn, Fin.eta]
  congr 2 <;> exact e.symm_apply_apply α

/-- **The number of names of `Γ` does not depend on the numbering** (pages 89-90): it is the sum
of the sizes of all the `Γ_{α,β}`. -/
theorem sum_codeMenuSizesE [Fintype S.Sym] :
    ∑ i, codeMenuSizesE e side i = ∑ β, ∑ α, codeGammaOptSize (side α β) := by
  simp only [codeMenuSizesE, codeCellSizesE]
  refine (Finset.sum_congr rfl fun i _ =>
    e.symm.sum_comp (fun α => codeGammaOptSize (side α (e.symm i)))).trans ?_
  exact e.symm.sum_comp (fun β => ∑ α, codeGammaOptSize (side α β))

/-- **The names of `Γ` do not depend on the numbering** (pages 89-90): two numberings give the
same multiset of names. -/
theorem vars_menu_codeMenusE_indep [Finite S.Sym] {n' : ℕ} (e' : S.Sym ≃ Fin n') (k₀ : ℕ) :
    (menu (codeMenusE e side k₀)).vars = (menu (codeMenusE e' side k₀)).vars := by
  have := Fintype.ofFinite S.Sym
  rw [vars_menu_codeMenusE, vars_menu_codeMenusE, sum_codeMenuSizesE, sum_codeMenuSizesE]

/-- **The hypotheses of `codeCell_code_codeMenusE` hold** (page 90), for every numbering `e`,
every choice `side`, every `k₀`, every bound `K` and every symbol `β`: with `f = id`, there are
trees and names that make the net linear. -/
theorem codeCell_code_codeMenusE_satisfiable (k₀ K : ℕ)
    (hK : k₀ + ∑ i, codeMenuSizesE e side i ≤ K) (β : S.Sym) :
    ∃ (P : Term sig ℕ) (ts : List (Term sig ℕ)) (ℓ u w y k₁ : ℕ),
      Set.InjOn id {x | x ∈ (code K (menu (codeMenusE e side k₀))).vars} ∧
      Net.Linear (codeCell (codeMenusE e side k₀).length (e β) P
        ((code K (menu (codeMenusE e side k₀))).bind fun x => var (id x)) ts ℓ u w y k₁ + 0) := by
  set c := code K (menu (codeMenusE e side k₀))
  have hb : (menu (codeMenusE e side k₀)).Below K := fun x hx =>
    (menu_codeMenusE_below e side k₀ x hx).trans_le hK
  have hc : c.IsPackage := code_isPackage K _ (menu_codeMenusE_isPackage e side k₀) hb
  have hv : (c.bind fun x => var (id x)).vars = c.vars := by
    rw [vars_bind]
    simp only [vars_var, id]
    exact (Multiset.bind_singleton c.vars id).trans (Multiset.map_id _)
  have hc' : (c.bind fun x => var (id x)).IsPackage := by
    intro x hx
    rw [hv] at hx ⊢
    exact hc x hx
  refine ⟨var (c.vars.sum + 7), [], c.vars.sum + 1, c.vars.sum + 2, c.vars.sum + 3,
    c.vars.sum + 4, c.vars.sum + 5, Set.injOn_id _, ?_⟩
  exact codeCell_linear_fresh _ _ _ hc' (c.vars.sum + 1) fun x hx =>
    Nat.lt_succ_of_le (Multiset.le_sum_of_mem (hv ▸ hx))

end General

/-! ## Orientation on `sideConDup` -/

/-- `Γ_{con,dup}` with the numbering `combEnum`, names from `k₀`. -/
abbrev gConDup (idx' : sig.Sym → ℕ) (k₀ : ℕ) : Term sig ℕ :=
  codeGamma 3 idx' ruleConDup (Equiv.swap 0 1) hs k₀

/-- **`Γ_con` is three erasers** for `sideConDup` (Fig. 10, page 89): no symbol has a side against
`con`. -/
theorem codeCellMenuE_combEnum_con :
    codeCellMenuE combEnum sideConDup .con 0 = [mkEra, mkEra, mkEra] := by
  decide

/-- **`Γ_dup` holds `Γ_{con,dup}` at the number of `con`** for `sideConDup` (Fig. 10, page 89): the
side of `con` against `dup` goes to the menu of `dup`. -/
theorem codeCellMenuE_combEnum_dup :
    codeCellMenuE combEnum sideConDup .dup 0 =
      [gConDup (fun α => combEnum α) 0, mkEra, mkEra] := by
  decide

/-! ## Two numberings -/

/-- The numbering `dup, con, era ↦ 0, 1, 2`. -/
def combEnum₂ : sig.Sym ≃ Fin 3 where
  toFun
    | .con => 1
    | .dup => 0
    | .era => 2
  invFun i := match i with
    | 0 => (Comb.dup : sig.Sym)
    | 1 => (Comb.con : sig.Sym)
    | 2 => (Comb.era : sig.Sym)
  left_inv α := by cases α <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- An asymmetric choice of sides, only to test the numbering (`side` is any function in
`codeMenusE`): the side `con`–`dup` used for `con` against `con` and for `con` against `dup`. -/
def sideAsym : ∀ α : sig.Sym, sig.Sym → Option (ExpSide sig (sig.arity α))
  | .con, .con => some ⟨2, ruleConDup, Equiv.swap 0 1, ruleConDup_linear, ruleConDup_expanded, hs⟩
  | .con, .dup => some ⟨2, ruleConDup, Equiv.swap 0 1, ruleConDup_linear, ruleConDup_expanded, hs⟩
  | _, _ => none

/-- **The menus for `combEnum`** (Fig. 10, page 89): `Γ_con` then `Γ_dup` then `Γ_era`; in each,
the package of `con` comes first. `Γ_con` has the names `[0, 24)`, `Γ_dup` the names `[24, 48)`. -/
theorem codeMenusE_e₁ :
    codeMenusE combEnum sideAsym 0 =
      [menu [gConDup (fun α => combEnum α) 0, mkEra, mkEra],
        menu [gConDup (fun α => combEnum α) 24, mkEra, mkEra],
        menu [mkEra, mkEra, mkEra]] := by
  decide

/-- **The menus for `combEnum₂`** (Fig. 10, page 89): `Γ_dup` then `Γ_con` then `Γ_era`; in each,
the package of `con` comes second. Now `Γ_dup` has the names `[0, 24)` and `Γ_con` the names
`[24, 48)`, and the selectors inside the packages use the numbers of `combEnum₂`. -/
theorem codeMenusE_e₂ :
    codeMenusE combEnum₂ sideAsym 0 =
      [menu [mkEra, gConDup (fun α => combEnum₂ α) 0, mkEra],
        menu [mkEra, gConDup (fun α => combEnum₂ α) 24, mkEra],
        menu [mkEra, mkEra, mkEra]] := by
  decide

/-- **The name blocks for `combEnum`** do not overlap and follow the sizes `24, 24, 0` (page 89). -/
theorem vars_codeMenusE_e₁ :
    (codeMenusE combEnum sideAsym 0).map Term.vars =
      [2 • Multiset.Ico 0 24, 2 • Multiset.Ico 24 48, 0] := by
  rw [codeMenusE_e₁, ← CodeGammaCheck.codeGammaSize_conDup]
  simp only [List.map_cons, List.map_nil, menu, vars_mux, List.sum_cons, List.sum_nil,
    vars_codeGamma _ _ ruleConDup_expanded ruleConDup_linear, CodeGammaCheck.codeGammaSize_conDup]
  decide

/-- **The name blocks for `combEnum₂`** do not overlap and follow the sizes `24, 24, 0`: the same
blocks as for `combEnum`, given to other symbols (page 89). -/
theorem vars_codeMenusE_e₂ :
    (codeMenusE combEnum₂ sideAsym 0).map Term.vars =
      [2 • Multiset.Ico 0 24, 2 • Multiset.Ico 24 48, 0] := by
  rw [codeMenusE_e₂, ← CodeGammaCheck.codeGammaSize_conDup]
  simp only [List.map_cons, List.map_nil, menu, vars_mux, List.sum_cons, List.sum_nil,
    vars_codeGamma _ _ ruleConDup_expanded ruleConDup_linear, CodeGammaCheck.codeGammaSize_conDup]
  decide

/-- **The selectors change with the numbering** (page 89): `Γ_{con,dup}` under `combEnum` and under
`combEnum₂`, on the same names, are different trees, because each `⟨α_k⟩` carries `S^{e α_k}_m`. -/
theorem codeGamma_idx_ne :
    gConDup (fun α => combEnum α) 0 ≠ gConDup (fun α => combEnum₂ α) 0 := by
  decide

/-! ## Instances of the theorems -/

/-- `codeMenusE_isPackage` on `combEnum` and `sideAsym`. -/
example : ∀ π ∈ codeMenusE combEnum sideAsym 0, π.IsPackage :=
  codeMenusE_isPackage combEnum sideAsym 0

/-- `menu_codeMenusE_below` on `combEnum` and `sideAsym`: the names of `Γ` are below `48`. -/
example : (menu (codeMenusE combEnum sideAsym 0)).Below 48 := by
  have h := menu_codeMenusE_below combEnum sideAsym 0
  have hs : ∑ i, codeMenuSizesE combEnum sideAsym i = 48 := by decide
  rwa [hs] at h

/-- **`codeCell_code_codeMenusE` applies** to `combEnum` and `sideConDup` (page 90): its
hypotheses hold, and the extraction gives the cell `[β]` with a copy of `Γ_β`. -/
example (β : sig.Sym) : ∃ (P : Term sig ℕ) (ts : List (Term sig ℕ)) (ℓ u w y k₁ : ℕ)
    (g g' : ℕ → ℕ) (M : CNet),
    StepsE system (codeCell (codeMenusE combEnum sideConDup 0).length (combEnum β) P
      ((code 24 (menu (codeMenusE combEnum sideConDup 0))).bind fun x => var (id x)) ts ℓ u w y
        k₁ + 0) M ∧
    Equiv M (s(P, cellSkel ((menu (codeCellMenuE combEnum sideConDup β
        (0 + off (codeMenuSizesE combEnum sideConDup) (combEnum β)))).bind fun x => var (g x))
      (codeMenusE combEnum sideConDup 0).length (combEnum β)
      (((code 24 (menu (codeMenusE combEnum sideConDup 0))).bind fun x => var (g' x)) :: ts) ℓ)
        ::ₘ 0) := by
  have hK : 0 + ∑ i, codeMenuSizesE combEnum sideConDup i ≤ 24 := by decide
  obtain ⟨P, ts, ℓ, u, w, y, k₁, hf, hlin⟩ :=
    codeCell_code_codeMenusE_satisfiable combEnum sideConDup 0 24 hK β
  obtain ⟨g, g', M, -, -, hS, hE⟩ :=
    codeCell_code_codeMenusE combEnum sideConDup 0 24 hK β id hf P ts ℓ u w y k₁ 0 hlin
  exact ⟨P, ts, ℓ, u, w, y, k₁, g, g', M, hS, hE⟩

end INet.Comb.CodeMenusEReview
