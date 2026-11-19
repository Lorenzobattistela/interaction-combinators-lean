import Checks.Universality.General.CodeGammaCheck
import Checks.Universality.RecursionFree.GammaTreeCReview

/-!
# Review of `codeSizes` on the computable `Rule.portTreeC` (Fig. 10, page 89)

Lafont 1997, Section 2.7, Fig. 10, journal page 89 (PDF page 21). PR #291 changed `codeSizes φ q`
from `codeSize (φ.portTree …)` to `codeSize (φ.portTreeC …)`. Review of that change (issue #293).

## Outside the hypotheses `Expanded`, `Linear`

* `codeSizes_eq_codeSize_gammaTree`: with no hypothesis on `φ`, the new `codeSizes` at a port is
  the number of new names of the tree `gammaTree` that `codePort` codes there, so the blocks of
  names of `codeBase` always fit the trees of `codePort`. The old definition fails this on the
  non-linear side `ψdup` (`oldCodeSizes_ψdup_ne`): it reserved five names for a tree, the leaf
  `k₀`, that has none.
* The same equation `a₀ = ε` twice (`ψdup`): new `0`, old `5` (`codeSizes_ψdup`,
  `oldCodeSizes_ψdup`). Two different equations at `a₀` (`ψtwo`): new `0`, old `5` or `15`
  (`oldCodeSizes_ψtwo`). A wire `a₀ = a₁` (`ψpq`, linear, not expanded): both `0`
  (`codeSizes_ψpq`).
* The theorems about `codeGamma`, `codeGammaSize`, `codeBase` stated without `he`, `hl` are
  `codeGamma_shift`, `codeGammaOpt_shift` (`CodeShift.lean`), `codeGamma_loop`, `codeGamma_meet`
  (`CodeGammaMeet.lean`), `codeCells_meet_gamma` (`CodeCellsMeet.lean`) and `codeGamma_extract`
  (`CodeGammaExtract.lean`). All existed before #291 with the same statement and the same proof, so
  each was already true of the old definition: none was made true by the change. The last two have
  only a linearity hypothesis on the whole net, the first four none; none is vacuous for that
  reason (`codeGamma_meet` and `codeGamma_extract` are applied to linear sides in the library).

## Inside: the side `ruleD` against Fig. 10

`ruleD` (`GammaTreeCReview`): `a₀ = dup(con(w₀, w₁), ε)`, `a₁ = con(w₂, dup(w₁, w₃))`, `b₀ = w₀`,
`b₁ = con(w₃, w₂)`; six cells, a tree of depth 3 at `a₀`. `handGammaD` is the package of Fig. 10
written from the figure, `k₀ = 10`, `σ = swap 0 1`, symbols numbered `con, dup, era = 0, 1, 2`:

* How the figure is read. Bottom right of Fig. 10: the root of `M*_{n_i+2}` loops round to the
  free port of `Γ_{i,j}`; its leaves from left to right are the root of `C_{p_{i,j}}`, the `n_i`
  ports of `⟨φ_{i,j}⟩` on the side of `α_i` (the `⋯`), and a wire running down the right to the
  root of `T_{σ_{i,j}}`, whose leaves are the middle ports of `⟨φ_{i,j}⟩`. The auxiliary ports of
  `C_{p_{i,j}}` go down into the extra ports of `⟨φ_{i,j}⟩`, one per cell. Bottom left: a cell
  `⟨α_k⟩` is `[α_k]` with the wire `y` (from `S^k_m` to `T_{1,1}`) in place of the menu and the
  wire `u` (from `C_2` to `M_{n_k+2}`) in place of the code (`cellSkel`), and its extra port
  carries `C_2(D(S^k_m(y)), u)` (`codeExtra`).
* The internal wires of `ruleD` are `10, …, 13`. The new names come after, in blocks of five per
  cell (`ℓ, u, y` and the loop of `D`): the ports `a₀, a₁, b₀, b₁` in this order, each tree in
  prefix order. `a₀` has three cells (`14, 19, 24`), `a₁` two (`29, 34`), `b₀` none, `b₁` one
  (`39`). So `C_6`, and the names run up to `43`.
* `codeGamma_ruleD`: `codeGamma` is `handGammaD`, by `decide`.
* `codeGammaSize_ruleD`: `34 = 4 + 5 · 6`, the four wires of `ruleD` and five names for each of the
  six cells `⟨α_k⟩` counted on the hand-drawn package (the six auxiliary ports of `C_6`).
-/

namespace INet.Comb.CodeSizesCReview

open Term Rule Translation DecompositionReview ExpandedIso ExpandTrReview GammaCheck GammaReview
  PortTreeCReview GammaTreeCReview CodeGammaCheck

variable {S : Signature} {a k : ℕ}

/-- The definition of `codeSizes` before PR #291, through the noncomputable `Rule.portTree`
(page 89). -/
noncomputable def oldCodeSizes (φ : Rule S a k) : Fin (a + k) → ℕ :=
  fun q => codeSize (φ.portTree (finSumFinEquiv.symm q))

/-! ## The blocks fit the trees, with no hypothesis -/

/-- **The new `codeSizes` fits `codePort`** (Fig. 10, page 89): for every side `φ`, linear or not,
the number of names reserved at the port `q` is the number of new names of the tree
`gammaTree φ k₀ q` that `codePort` codes at `q`. -/
theorem codeSizes_eq_codeSize_gammaTree (φ : Rule S a k) (k₀ : ℕ) (q : Fin (a + k)) :
    codeSizes φ q = codeSize (gammaTree φ k₀ (finSumFinEquiv.symm q)) := by
  rw [gammaTree, codeSize_bind_var]
  rfl

/-! ## The same equation twice -/

/-- On `ψdup` (`a₀ = ε` twice, not linear) the new `codeSizes` is `0` (page 89). -/
theorem codeSizes_ψdup : codeSizes ψdup 0 = 0 := by decide

/-- On `ψdup` the old `codeSizes` is `5`, the names of `⟨ε⟩` (page 89). -/
theorem oldCodeSizes_ψdup : oldCodeSizes ψdup 0 = 5 := by
  have h := codeSize_bind_var (fun x => gammaName 7 x) (ψdup.portTree (.inl 0))
  rw [← oldGammaTree, oldGammaTree_ψdup] at h
  exact h.symm

/-- **The old `codeSizes` did not fit `codePort`** (page 89): on `ψdup` it reserved five names at
`a₀`, where the tree coded by `codePort` is the leaf `k₀`, with no new name. -/
theorem oldCodeSizes_ψdup_ne :
    oldCodeSizes ψdup 0 ≠ codeSize (gammaTree ψdup 7 (finSumFinEquiv.symm 0)) := by
  rw [oldCodeSizes_ψdup, ← codeSizes_eq_codeSize_gammaTree, codeSizes_ψdup]
  decide

/-- So on `ψdup` the number of names of `Γ` is `0` with the new definition and `5` with the old
one (page 89). -/
theorem codeGammaSize_ψdup :
    codeGammaSize ψdup = 0 ∧ ψdup.internal + ∑ q, oldCodeSizes ψdup q = 5 := by
  refine ⟨by decide, ?_⟩
  rw [Fin.sum_univ_one, oldCodeSizes_ψdup]
  rfl

/-! ## Two different equations at `a₀` -/

/-- On `ψtwo` (`a₀ = ε`, `a₀ = con(ε, ε)`) the new `codeSizes` is `0` and the old one is `5` or
`15`, so they differ (page 89). -/
theorem oldCodeSizes_ψtwo :
    codeSizes ψtwo 0 = 0 ∧ (oldCodeSizes ψtwo 0 = 5 ∨ oldCodeSizes ψtwo 0 = 15) := by
  refine ⟨by decide, ?_⟩
  change codeSize (ψtwo.portTree (.inl 0)) = 5 ∨ codeSize (ψtwo.portTree (.inl 0)) = 15
  rcases portTree_ψtwo with h | h <;> rw [h]
  · exact .inl rfl
  · exact .inr rfl

/-! ## A wire between two ports: linear, not expanded -/

/-- On `ψpq` (`a₀ = a₁`) the old and new `codeSizes` agree, and are `0` (page 89). -/
theorem codeSizes_ψpq (q : Fin 2) :
    codeSizes ψpq q = oldCodeSizes ψpq q ∧ codeSizes ψpq q = 0 := by
  refine ⟨by rw [codeSizes, oldCodeSizes, portTreeC_eq_portTree_of_linear ψpq_linear], ?_⟩
  revert q
  decide

/-! ## The side `ruleD` against Fig. 10 -/

/-- **`Γ` of `ruleD` drawn from Fig. 10** (page 89), `k₀ = 10`, `σ = swap 0 1`: `M*_4` whose
leaves are `C_6` on the six extra ports, `⟨φ⟩` at `a₀` and at `a₁`, and `T_σ = con` on `⟨φ⟩` at
`b₀`, `b₁`. Each cell `⟨α⟩` with block `b` is `cellSkel (var (b + 2)) 3 (idx α) (var (b + 1) :: _) b`
with extra tree `codeExtra 3 (idx α) (b + 2) (b + 1) (b + 3)`. -/
def handGammaD : Term sig ℕ :=
  muxStar
    [copier [codeExtra 3 1 16 15 17, codeExtra 3 0 21 20 22, codeExtra 3 2 26 25 27,
      codeExtra 3 0 31 30 32, codeExtra 3 1 36 35 37, codeExtra 3 0 41 40 42],
    cellSkel (var 16) 3 1
      [var 15, cellSkel (var 21) 3 0 [var 20, var 10, var 11] 19, cellSkel (var 26) 3 2 [var 25] 24]
      14,
    cellSkel (var 31) 3 0 [var 30, var 12, cellSkel (var 36) 3 1 [var 35, var 11, var 13] 34] 29,
    mkCon (var 10) (cellSkel (var 41) 3 0 [var 40, var 13, var 12] 39)]

/-- **`codeGamma` of `ruleD` is the package drawn from Fig. 10** (page 89), by evaluation. -/
theorem codeGamma_ruleD : codeGamma 3 idx ruleD (Equiv.swap 0 1) hs 10 = handGammaD := by
  decide

/-- The block sizes of `ruleD` (page 89): fifteen names at `a₀`, ten at `a₁`, none at `b₀`, five at
`b₁`. -/
theorem codeSizes_ruleD :
    codeSizes ruleD 0 = 15 ∧ codeSizes ruleD 1 = 10 ∧ codeSizes ruleD 2 = 0 ∧
      codeSizes ruleD 3 = 5 := by
  decide

/-- **The number of names of `Γ` for `ruleD`** (page 89): the four internal wires of `ruleD` and
five names for each of the six cells `⟨α_k⟩` of the hand-drawn package, which are the six
auxiliary ports of its copier `C_6`. -/
theorem codeGammaSize_ruleD :
    codeGammaSize ruleD = 34 ∧ codeGammaSize ruleD = ruleD.internal + 5 * 6 ∧
      Multiset.card ruleD.net.cells = 6 ∧ (codeGammaExtras 3 idx ruleD 10).length = 6 := by
  decide

/-- `handGammaD` is a package on the names `10, …, 43`, each twice, as `vars_codeGamma` says
(page 89). -/
example : handGammaD.vars = 2 • Multiset.Ico 10 (10 + 34) := by
  rw [← codeGamma_ruleD, vars_codeGamma _ _ ruleD_expanded ruleD_linear, codeGammaSize_ruleD.1]

end INet.Comb.CodeSizesCReview
