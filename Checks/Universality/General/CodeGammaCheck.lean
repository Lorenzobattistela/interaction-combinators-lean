import InteractionCombinators.Universality.General.CodeGamma
import Checks.Universality.RecursionFree.GammaCheck

/-!
# Checks of `⟨φ⟩` and of the package `Γ_{i,j}` of Fig. 10 (page 89)

* One `con` cell `con(7, 8)` with names from `0`: `⟨con(7, 8)⟩` is the cell `[con]` with the wire
  `2` on the menu, the wire `1` on the code, the ports `7`, `8` and the loop `0`; the one tree on
  its extra port is `C_2(D, 1)` with the loop `3`, `4` of `D` and the selector on `2`.
* The side `φ₀` without cells (`GammaCheck`): `Γ` is the `Γ` of Fig. 6 with an eraser (`C_0`) on
  the first leaf of `M*_4`.
* The rule `con`–`dup` of `system`, read as a side with four cells: `C_4` has four auxiliary
  ports, `Γ` is a package, and its names are `[10, 34)`, each twice (four internal wires and five
  names per cell).
* The same facts, and the trees at two ports, found by `decide` alone: `Γ_{i,j}` is computable.
-/

namespace INet.Comb.CodeGammaCheck

open Term Rule Translation DecompositionReview ExpandedIso ExpandTrReview GammaCheck

/-- A numbering of the three symbols. -/
def idx : sig.Sym → ℕ
  | .con => 0
  | .dup => 1
  | .era => 2

/-- One cell: `⟨con(7, 8)⟩` from `0` is `[con]` with the menu on the wire `2`, the code on the wire
`1`, and the loop `0`. -/
example : codeTerm 3 idx 0 (mkCon (var 7) (var 8) : Term sig ℕ) =
    cellSkel (var 2) 3 0 [var 1, var 7, var 8] 0 := by
  rfl

/-- One cell: the tree on its extra port is `C_2(D, 1)`, `D` with its loop `3`, `4` and the selector
`S^0_3` on the wire `2`. -/
example : codeExtras 3 idx 0 (mkCon (var 7) (var 8) : Term sig ℕ) = [codeExtra 3 0 2 1 3] := by
  rfl

/-- One cell: the names `0, …, 4`, each twice, and the ports `7`, `8` once (`vars_codeTerm_add`). -/
example : (codeTerm 3 idx 0 (mkCon (var 7) (var 8) : Term sig ℕ)).vars +
    ((codeExtras 3 idx 0 (mkCon (var 7) (var 8) : Term sig ℕ)).map Term.vars).sum =
      {7} + {8} + 2 • Multiset.Ico 0 5 := by
  have h : codeSize (mkCon (var 7) (var 8) : Term sig ℕ) = 5 := rfl
  rw [vars_codeTerm_add, h, vars_mkCon, vars_var, vars_var]

/-- The side `φ₀` without cells: `Γ` is `M*_4(ε, w₀, w₁, T_σ(w₀, w₁))` with `w₀ = 10`, `w₁ = 11`, the
eraser being the copier `C_0`. -/
theorem codeGamma_φ₀ :
    codeGamma 3 idx φ₀ (Equiv.swap 0 1) hs 10 =
      mkCon (mkCon (mkCon (mkCon (var 10) (var 11)) (var 11)) (var 10)) mkEra := by
  obtain ⟨h0, h1, h2, h3⟩ := portTreeC_φ₀
  have hl : portList (Equiv.swap (0 : Fin 2) 1) = [0, 1] := by decide
  have hp : pairFst (Equiv.swap (0 : Fin 2) 1) = [0] := by decide
  have e : ∀ p, codePortExtras 3 idx φ₀ 10 p = [] := by
    rintro (i | j)
    · revert i
      rw [Fin.forall_fin_two]
      exact ⟨by rw [codePortExtras, gammaTree, h0]; rfl, by rw [codePortExtras, gammaTree, h1]; rfl⟩
    · revert j
      rw [Fin.forall_fin_two]
      exact ⟨by rw [codePortExtras, gammaTree, h2]; rfl, by rw [codePortExtras, gammaTree, h3]; rfl⟩
  simp only [codeGamma, codeGammaExtras, e, codePort, transpositorPerm, hl, hp, List.ofFn_succ,
    List.ofFn_zero, gammaTree, h0, h1, h2, h3, List.map_cons, List.map_nil, Fin.succ_zero_eq_one]
  rfl

/-- Deliverable 3 on the side `φ₀`. -/
example : (codeGamma 3 idx φ₀ (Equiv.swap 0 1) hs 10).IsPackage :=
  codeGamma_isPackage _ _ φ₀_expanded φ₀_linear _ _ _

/-! ## The rule `con`–`dup` of `system`, as a side with four cells -/

/-- The rule `con`–`dup` has four cells. -/
theorem card_cells_conDup : Multiset.card ruleConDup.net.cells = 4 := by decide

/-- **`C_4`**: the copier of `Γ` for `con`–`dup` has one auxiliary port per cell. -/
example (k₀ : ℕ) : (codeGammaExtras 3 idx ruleConDup k₀).length = 4 := by
  rw [length_codeGammaExtras _ _ ruleConDup_expanded ruleConDup_linear, card_cells_conDup]

/-- `Γ` for `con`–`dup` is a package (deliverable 3). -/
example (k₀ : ℕ) : (codeGamma 3 idx ruleConDup (Equiv.swap 0 1) hs k₀).IsPackage :=
  codeGamma_isPackage _ _ ruleConDup_expanded ruleConDup_linear _ _ _

/-- The number of names of `Γ` for `con`–`dup`: four internal wires and five names for each of the
four cells. -/
theorem codeGammaSize_conDup : codeGammaSize ruleConDup = 24 := by
  obtain ⟨h0, h1, h2, h3⟩ := portTreeC_conDup_eq
  simp only [codeGammaSize, codeSizes]
  rw [Equiv.sum_comp finSumFinEquiv.symm (fun p => codeSize (ruleConDup.portTreeC p)),
    Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two, h0, h1, h2, h3]
  rfl

/-- The names of `Γ` for `con`–`dup` from `10`: `10, …, 33`, each twice. -/
example : (codeGamma 3 idx ruleConDup (Equiv.swap 0 1) hs 10).vars = 2 • Multiset.Ico 10 34 := by
  rw [vars_codeGamma _ _ ruleConDup_expanded ruleConDup_linear, codeGammaSize_conDup]

/-! ## `Γ_{i,j}` computes

Since `codeSizes` uses the computable `Rule.portTreeC`, the package of Fig. 10 (page 89) is
evaluated by `decide`, without the lemmas `portTreeC_conDup_eq`, `vars_codeGamma`,
`length_codeGammaExtras`. -/

/-- The number of names of `Γ` for `con`–`dup`, by evaluation alone (page 89). -/
example : codeGammaSize ruleConDup = 24 := by decide

/-- The copier `C_4` of `Γ` for `con`–`dup`, by evaluation alone (Fig. 10, page 89). -/
example : (codeGammaExtras 3 idx ruleConDup 10).length = 4 := by decide

/-- The tree of `⟨φ⟩` at the port `a₀` of `con`–`dup`, from `10`, by evaluation (Fig. 10,
page 89): the code of `dup(10, 11)` (internal wires `10, …, 13`), with its new names from
`10 + 4 = 14`. -/
example : codePort 3 idx ruleConDup 10 (.inl 0) =
    codeTerm 3 idx 14 (mkDup (var 10) (var 11) : Term sig ℕ) := by decide

/-- The tree of `⟨φ⟩` at the last middle port `b₁`, by evaluation (page 89): the code of
`con(11, 13)`, with its new names after the three blocks of five of the ports before it,
from `14 + 15 = 29`. -/
example : codePort 3 idx ruleConDup 10 (.inr 1) =
    codeTerm 3 idx 29 (mkCon (var 11) (var 13) : Term sig ℕ) := by decide

/-- The names of `Γ` for `con`–`dup` from `10`, by evaluation alone (page 89): `10, …, 33`,
each twice. -/
example : (codeGamma 3 idx ruleConDup (Equiv.swap 0 1) hs 10).vars =
    2 • Multiset.Ico 10 34 := by decide

/-- `Γ` of the side `φ₀` without cells, by evaluation alone: the tree of `codeGamma_φ₀`
(page 89). -/
example : codeGamma 3 idx φ₀ (Equiv.swap 0 1) hs 10 =
    mkCon (mkCon (mkCon (mkCon (var 10) (var 11)) (var 11)) (var 10)) mkEra := by decide

end INet.Comb.CodeGammaCheck
