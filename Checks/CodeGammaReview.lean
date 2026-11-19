import Checks.CodeGammaCheck

/-!
# Review of `⟨φ_{i,j}⟩`, `Γ_{i,j}` and the menus of Fig. 10 (pages 89-90)

Review of `codeTerm`, `codeGamma`, `codeCellMenu` and `codeMenus` (`CodeGamma.lean`) against
Fig. 10 (journal page 89, PDF page 21, rendered at 600 dpi) and the text of page 90.

* `codeGamma_conDup` — `Γ` for the side `con`–`dup` (four cells, two middle ports, `σ = swap 0 1`),
  written out by hand: `M*_4` with the leaves `C_4`, the two trees of `⟨φ⟩` at the ports of the
  first cell, and `T_σ` on the two middle trees. Each `⟨α_k⟩` has its own block of five names, and
  its extra tree sits on `C_4` with the same wires `y`, `u` as its cell.
* `codeGamma_conDup_isPackage` — the explicit tree is a package, checked by `decide` on the tree
  itself rather than through `vars_codeGamma`: no two `⟨α_k⟩` share a name.
* `codeCell_code_codeMenus_satisfiable` — the hypotheses `hf`, `hlin` of `codeCell_code_codeMenus`
  hold for every choice `side` of expanded sides, with fresh names above the names of the code:
  the extraction of page 90 is not vacuous. `sideConDup` is such a choice with a side of four cells.

Points checked without a Lean statement:

* The leaves of `M*_{n_i+2}` in Fig. 10 are, left to right, `C_{p_{i,j}}`, the `n_i` ports on the
  side of `α_i`, `T_{σ_{i,j}}`; its root is the free port. They meet the leaves `!Γ`, the `n_i`
  ports, the loop `ℓ` of `M_{n_i+2}` in `[α_i]` (`cellSkel`), so `!Γ` reaches the copier. `codeGamma`
  is `gamma` of Fig. 6 with the copier consed in front and `codeTerm` in place of `trTerm`.
* The order of the extra trees on `C_p` is irrelevant: `copier_code` gives every leaf of a copier
  its own renamed copy of `!Γ`, whatever the leaves are, and `codeCell_code` accepts any injective
  renaming.
* `codeCellMenu β` has at index `j` the package built from `side α_j β`, as `cellMenu` of Fig. 6.
* `side` is any function: page 90 drops the ordering condition of page 86; nothing in
  `codeMenus` relates `side α β` to `side β α` or to a rule. The translation `[α]` will have to.
-/

namespace INet.Comb.CodeGammaReview

open Term Rule Translation DecompositionReview ExpandedIso ExpandTrReview GammaCheck
  CodeGammaCheck

/-! ## `Γ` for the side `con`–`dup`, by hand -/

/-- Every tree of the side `con`–`dup` has one cell, so five new names. -/
theorem codeSizes_conDup : codeSizes ruleConDup = fun _ => 5 := by
  obtain ⟨h0, h1, h2, h3⟩ := portTree_conDup
  funext q
  simp only [codeSizes]
  match q with
  | ⟨0, _⟩ => rw [show finSumFinEquiv.symm (⟨0, by omega⟩ : Fin (2 + 2)) = .inl 0 from rfl, h0]; rfl
  | ⟨1, _⟩ => rw [show finSumFinEquiv.symm (⟨1, by omega⟩ : Fin (2 + 2)) = .inl 1 from rfl, h1]; rfl
  | ⟨2, _⟩ => rw [show finSumFinEquiv.symm (⟨2, by omega⟩ : Fin (2 + 2)) = .inr 0 from rfl, h2]; rfl
  | ⟨3, _⟩ => rw [show finSumFinEquiv.symm (⟨3, by omega⟩ : Fin (2 + 2)) = .inr 1 from rfl, h3]; rfl

/-- **`Γ` of Fig. 10 for `con`–`dup`, names from `10`.** The internal wires of the side are
`10, …, 13`; the ports `l₀, l₁, m₀, m₁` take the blocks `14`, `19`, `24`, `29`. The two `dup` cells
(on `l₀`, `l₁`) become `[dup]` with the selector `S^1_3`, the two `con` cells (on `m₀`, `m₁`)
become `[con]` with `S^0_3`; the copier `C_4` carries their four extra trees, in the order of the
ports, each with the wires `y = b + 2`, `u = b + 1` of its own cell. The last leaf is
`T_σ = con` applied to the two middle trees. -/
theorem codeGamma_conDup :
    codeGamma 3 idx ruleConDup (Equiv.swap 0 1) hs 10 =
      muxStar [copier [codeExtra 3 1 16 15 17, codeExtra 3 1 21 20 22,
          codeExtra 3 0 26 25 27, codeExtra 3 0 31 30 32],
        cellSkel (var 16) 3 1 [var 15, var 10, var 11] 14,
        cellSkel (var 21) 3 1 [var 20, var 12, var 13] 19,
        mkCon (cellSkel (var 26) 3 0 [var 25, var 10, var 12] 24)
          (cellSkel (var 31) 3 0 [var 30, var 11, var 13] 29)] := by
  obtain ⟨h0, h1, h2, h3⟩ := portTreeC_conDup_eq
  have hl : portList (Equiv.swap (0 : Fin 2) 1) = [0, 1] := by decide
  have hp : pairFst (Equiv.swap (0 : Fin 2) 1) = [0] := by decide
  have hi : ruleConDup.internal = 4 := rfl
  simp only [codeGamma, codeGammaExtras, codePortExtras, codePort, codeBase, codeSizes_conDup,
    hi, transpositorPerm, hl, hp, List.ofFn_succ, List.ofFn_zero, gammaTree, List.map_cons,
    List.map_nil, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Equiv.apply_symm_apply]
  have e0 : (finSumFinEquiv.symm (0 : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = .inl 0 := rfl
  have e1 : (finSumFinEquiv.symm (1 : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = .inl 1 := rfl
  have e2 : (finSumFinEquiv.symm (2 : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = .inr 0 := rfl
  have e3 : (finSumFinEquiv.symm (Fin.succ (2 : Fin 3)) : Fin 2 ⊕ Fin 2) = .inr 1 := rfl
  rw [e0, e1, e2, e3, h0, h1, h2, h3]
  rfl

/-- **No two `⟨α_k⟩` share a name** (page 89): the tree of `codeGamma_conDup`, checked directly,
is a package. -/
theorem codeGamma_conDup_isPackage :
    (muxStar [copier [codeExtra 3 1 16 15 17, codeExtra 3 1 21 20 22,
          codeExtra 3 0 26 25 27, codeExtra 3 0 31 30 32],
        cellSkel (var 16) 3 1 [var 15, var 10, var 11] 14,
        cellSkel (var 21) 3 1 [var 20, var 12, var 13] 19,
        mkCon (cellSkel (var 26) 3 0 [var 25, var 10, var 12] 24)
          (cellSkel (var 31) 3 0 [var 30, var 11, var 13] 29)] : Term sig ℕ).IsPackage := by
  unfold Term.IsPackage
  decide

/-! ## The extraction of page 90 is not vacuous -/

/-- `⟨α_k⟩` with a package `c` on its extra port, no auxiliary port, the leaf `B + 6` on its
principal port and the fresh names `ℓ = B`, `u = B + 1`, `w = B + 2`, `y = B + 3` and the loop
`B + 4`, `B + 5` of `D` above the names of `c` is linear (Fig. 10, page 89). -/
theorem codeCell_linear_fresh (m k : ℕ) (c : Term sig ℕ) (hc : c.IsPackage) (B : ℕ)
    (hB : ∀ x ∈ c.vars, x < B) :
    Net.Linear (codeCell m k (var (B + 6)) c [] B (B + 1) (B + 2) (B + 3) (B + 4) + 0) := by
  intro x
  simp only [codeCell, add_zero, Net.vars_cons, eqVars_mk, vars_var, copier, vars_autoMux,
    vars_decoder, selector_eq_cellSel, vars_cellSel, vars_cellSkel, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Net.vars_zero, Multiset.count_add, Multiset.count_singleton,
    Multiset.insert_eq_cons, Multiset.count_cons, add_zero]
  by_cases hx : x ∈ c.vars
  · have h2 := hc x hx
    have := hB x hx
    split_ifs <;> omega
  · rw [Multiset.count_eq_zero.2 hx]
    split_ifs <;> omega

section

variable {S : Signature} [Finite S.Sym]

/-- **The hypotheses of `codeCell_code_codeMenus` hold** (page 90), for every choice `side` of
expanded sides, every `k₀`, every bound `K` and every symbol `β`: with `f = id`, there are trees
and names that make the net linear. So the extraction of page 90 is not a statement about an empty
set of nets. -/
theorem codeCell_code_codeMenus_satisfiable
    (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α))) (k₀ K : ℕ)
    (hK : k₀ + ∑ i, codeMenuSizes side i ≤ K) (β : S.Sym) :
    ∃ (P : Term sig ℕ) (ts : List (Term sig ℕ)) (ℓ u w y k₁ : ℕ),
      Set.InjOn id {x | x ∈ (code K (menu (codeMenus side k₀))).vars} ∧
      Net.Linear (codeCell (codeMenus side k₀).length (symEnum S β) P
        ((code K (menu (codeMenus side k₀))).bind fun x => var (id x)) ts ℓ u w y k₁ + 0) := by
  set c := code K (menu (codeMenus side k₀))
  have hb : (menu (codeMenus side k₀)).Below K := fun x hx =>
    (menu_codeMenus_below side k₀ x hx).trans_le hK
  have hc : c.IsPackage := code_isPackage K _ (menu_codeMenus_isPackage side k₀) hb
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

end

/-- A choice of expanded sides for the interaction combinators with a side that has cells: the
rule `con`–`dup` (four cells) for the pair `con`, `dup`, and no side elsewhere. -/
def sideConDup : ∀ α : sig.Sym, sig.Sym → Option (ExpSide sig (sig.arity α))
  | .con, .dup => some ⟨2, ruleConDup, Equiv.swap 0 1, ruleConDup_linear, ruleConDup_expanded, hs⟩
  | _, _ => none

/-- The side of `con` against `dup` in `sideConDup` has four cells. -/
example : ((sideConDup .con .dup).map fun s => Multiset.card s.φ.net.cells) = some 4 := by
  simp only [sideConDup, Option.map_some]
  exact congrArg some card_cells_conDup

/-- The extraction of page 90 applies to the `Γ` built from `sideConDup`, a side with cells. -/
example (β : sig.Sym) : ∃ (P : Term sig ℕ) (ts : List (Term sig ℕ)) (ℓ u w y k₁ : ℕ),
    Set.InjOn id
      {x | x ∈ (code (∑ i, codeMenuSizes sideConDup i) (menu (codeMenus sideConDup 0))).vars} ∧
    Net.Linear (codeCell (codeMenus sideConDup 0).length (symEnum sig β) P
      ((code (∑ i, codeMenuSizes sideConDup i) (menu (codeMenus sideConDup 0))).bind
        fun x => var (id x)) ts ℓ u w y k₁ + 0) :=
  codeCell_code_codeMenus_satisfiable sideConDup 0 _ (by omega) β

end INet.Comb.CodeGammaReview
