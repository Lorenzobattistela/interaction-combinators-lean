import Checks.Universality.RecursionFree.GammaReview
import Checks.Universality.RecursionFree.PortTreeCReview

/-!
# Review of `gammaTree` on the computable `Rule.portTreeC` (Fig. 6, page 86)

Lafont 1997, Section 2.4, Fig. 6, journal page 86 (PDF page 18). PR #285 changed `gammaTree φ k₀ p`
from `(φ.portTree p).bind …` to `(φ.portTreeC p).bind …`. Review of that change (issue #290).

## Outside the hypotheses `Expanded`, `Linear`

* Two different equations rooted at `a₀` (`PortTreeCReview.ψtwo`, not linear): the new `gammaTree`
  is the leaf `k₀`, the old one is one of the two trees (`gammaTree_ne_old_ψtwo`).
* The same equation `a₀ = ε` written twice (`ψdup`, not linear): the new `gammaTree` is the leaf
  `k₀`, the old one is `ε` (`gammaTree_ψdup`, `oldGammaTree_ψdup`). So the two definitions differ
  exactly on non-linear sides, as the docstring of `PortTreeC.lean` says.
* A wire `a₀ = a₁` between two ports (`PortTreeCReview.ψpq`, linear, not expanded): the two agree,
  and both give the leaf `k₀`, the name `gammaName` gives to ports (`gammaTree_ψpq`).
* The statements about `gammaTree` without these hypotheses are `mem_cells_gammaTree`,
  `gammaSize_eq`, `gammaSize_congr`, `gamma_congr` (`RecursionFreeTr.lean`), `gammaTree_shift`,
  `gammaSizes_eq` (`RecursionFreeFig7.lean`) and `codeGamma_extract` (`CodeGammaExtract.lean`).
  All but the first hold for any choice of trees at the ports (they only use `bind`, or relate
  `gammaTree` to constructions defined from it). The first is also true of the old definition
  (`mem_cells_oldGammaTree`). None of them has a hypothesis, so none is vacuous.

## Inside: a side with depth-2 trees, against Fig. 6

The side `ruleD` (`a = k = 2`, four internal wires):
`a₀ = dup(con(w₀, w₁), ε)`, `a₁ = con(w₂, dup(w₁, w₃))`, `b₀ = w₀`, `b₁ = con(w₃, w₂)`.
Its trees from `k₀ = 10` are computed by `decide` (`gammaTree_ruleD`), the wire `w` named `10 + w`,
and agree with `Rule.portTree` (`gammaTree_ruleD_old`). Its package under the identity translation
is the dual multiplexor `M*_3` whose last leaf is `T_σ` of the two middle trees, for `σ = swap 0 1`
(`T_σ = con`) and `σ = 1` (`T_1 = dup`), compared with the trees written by hand (`gamma_ruleD`,
`gamma_ruleD_id`) and with `muxStar` of the hand-written leaves (`gamma_ruleD_muxStar`).
-/

namespace INet.Comb.GammaTreeCReview

open Term Rule Translation DecompositionReview ExpandedIso ExpandTrReview GammaCheck GammaReview
  PortTreeCReview

variable {S : Signature} {a k : ℕ}

/-- The definition of `gammaTree` before PR #285, through the noncomputable `Rule.portTree`
(Fig. 6, page 86). -/
noncomputable def oldGammaTree (φ : Rule S a k) (k₀ : ℕ) (p : Fin a ⊕ Fin k) : Term S ℕ :=
  (φ.portTree p).bind fun x => .var (gammaName k₀ x)

/-! ## Two different equations at `a₀` -/

/-- On `ψtwo` (`a₀ = ε`, `a₀ = con(ε, ε)`), the new `gammaTree` is the leaf `k₀` (Fig. 6,
page 86). -/
theorem gammaTree_ψtwo : gammaTree ψtwo 7 (.inl 0) = var 7 := by
  decide

/-- On `ψtwo`, the old and the new `gammaTree` differ at `a₀` (Fig. 6, page 86). -/
theorem gammaTree_ne_old_ψtwo : gammaTree ψtwo 7 (.inl 0) ≠ oldGammaTree ψtwo 7 (.inl 0) := by
  rw [gammaTree_ψtwo, oldGammaTree]
  rcases portTree_ψtwo with h | h <;> rw [h] <;> simp [mkEra, mkCon, Term.bind]

/-! ## The same equation twice -/

/-- The side `a₀ = ε`, `a₀ = ε`: one equation written twice. -/
def ψdup : Rule sig 1 0 := ⟨0, s(.var (.inl 0), mkEra) ::ₘ s(.var (.inl 0), mkEra) ::ₘ 0⟩

/-- `ψdup` is not linear: `a₀` occurs twice. -/
theorem ψdup_not_linear : ¬ ψdup.Linear := fun h => absurd (h.left 0) (by decide)

/-- On `ψdup`, the new `gammaTree` is the leaf `k₀` (Fig. 6, page 86): `portTreeC` finds two
equations at `a₀` and gives up. -/
theorem gammaTree_ψdup : gammaTree ψdup 7 (.inl 0) = var 7 := by
  decide

/-- On `ψdup`, the old `gammaTree` is `ε`, the tree of either equation (Fig. 6, page 86). -/
theorem oldGammaTree_ψdup : oldGammaTree ψdup 7 (.inl 0) = mkEra := by
  have h : ψdup.portTree (.inl 0) = mkEra := by
    have hx : ∃ t, s(Term.var (port (.inl 0)), t) ∈ ψdup.net := ⟨mkEra, by decide⟩
    unfold Rule.portTree
    split_ifs
    have hs := hx.choose_spec
    generalize hx.choose = c at hs ⊢
    change s(Term.var (.inl 0), c) ∈
      (s(.var (.inl 0), mkEra) ::ₘ s(.var (.inl 0), mkEra) ::ₘ 0 :
      Net sig (Fin 1 ⊕ Fin 0 ⊕ Fin 0)) at hs
    have hm : s(Term.var (.inl 0), c) = s(.var (.inl 0), mkEra) := by
      rcases Multiset.mem_cons.1 hs with h1 | hs
      · exact h1
      rcases Multiset.mem_cons.1 hs with h1 | hs
      · exact h1
      exact absurd hs (Multiset.notMem_zero _)
    rcases Sym2.eq_iff.1 hm with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1
    · simp [mkEra] at h1
  rw [oldGammaTree, h]
  decide

/-- So the two definitions differ on `ψdup` (Fig. 6, page 86). -/
theorem gammaTree_ne_old_ψdup : gammaTree ψdup 7 (.inl 0) ≠ oldGammaTree ψdup 7 (.inl 0) := by
  rw [gammaTree_ψdup, oldGammaTree_ψdup]
  simp [mkEra]

/-! ## A wire between two ports: linear, not expanded -/

/-- On `ψpq` (`a₀ = a₁`), linear and not expanded, the old and the new `gammaTree` agree, and
both send the other port to the name `k₀` (Fig. 6, page 86). -/
theorem gammaTree_ψpq (k₀ : ℕ) (p : Fin 2 ⊕ Fin 0) :
    gammaTree ψpq k₀ p = oldGammaTree ψpq k₀ p ∧ gammaTree ψpq k₀ p = var k₀ := by
  refine ⟨by rw [gammaTree, oldGammaTree, portTreeC_eq_portTree_of_linear ψpq_linear], ?_⟩
  rcases p with i | j
  · fin_cases i
    · change (ψpq.portTreeC (.inl 0)).bind _ = _
      rw [portTreeC_ψpq.1]; rfl
    · change (ψpq.portTreeC (.inl 1)).bind _ = _
      rw [portTreeC_ψpq.2]; rfl
  · exact j.elim0

/-! ## The hypothesis-free statement, for the old definition -/

/-- `mem_cells_gammaTree` (`RecursionFreeTr.lean`), which has no hypothesis, was also true of the
old definition: the change did not make it true by accident (Fig. 6, page 86). -/
theorem mem_cells_oldGammaTree {φ : Rule S a k} {k₀ : ℕ} {p : Fin a ⊕ Fin k} {γ : S.Sym}
    (hγ : γ ∈ (oldGammaTree φ k₀ p).cells) : γ ∈ φ.net.cells := by
  rw [oldGammaTree, cells_bind] at hγ
  simp only [cells_var, Multiset.bind_zero, add_zero] at hγ
  unfold Rule.portTree at hγ
  split_ifs at hγ with h
  · exact Multiset.mem_bind.2 ⟨_, h.choose_spec, by rw [eqCells_mk]; simp [hγ]⟩
  · simp at hγ

/-- `mem_cells_gammaTree` on a non-linear side: on `ψtwo` the new tree at `a₀` has no cell, so the
statement holds trivially there, while the old tree had the cells of one equation (Fig. 6,
page 86). -/
example : (gammaTree ψtwo 7 (.inl 0)).cells = 0 := by
  rw [gammaTree_ψtwo]; rfl

/-! ## A side with trees of depth 2 -/

/-- The side `a₀ = dup(con(w₀, w₁), ε)`, `a₁ = con(w₂, dup(w₁, w₃))`, `b₀ = w₀`,
`b₁ = con(w₃, w₂)`: two ports on each group, four internal wires, two trees of depth 2. -/
abbrev ruleD : Rule sig 2 2 :=
  ⟨4, s(pl 0, mkDup (mkCon (pw 0) (pw 1)) mkEra) ::ₘ s(pl 1, mkCon (pw 2) (mkDup (pw 1) (pw 3))) ::ₘ
    s(pr 0, pw 0) ::ₘ {s(pr 1, mkCon (pw 3) (pw 2))}⟩

theorem ruleD_linear : ruleD.Linear := ⟨by decide, by decide, by decide⟩

theorem ruleD_expanded : ruleD.Expanded := by
  intro e he
  have key : ∀ e ∈ (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 4) from ruleD.net),
      e ∈ [s(pl 0, mkDup (mkCon (pw 0) (pw 1)) mkEra), s(pl 1, mkCon (pw 2) (mkDup (pw 1) (pw 3))),
        s(pr 0, pw 0), s(pr 1, mkCon (pw 3) (pw 2))] := by decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl, fun w h => (by cases h), by decide⟩

/-- **The trees of `ruleD` from `10`** (Fig. 6, page 86), by evaluation: the internal wire `w` is
named `10 + w`, the trees keep their shape. -/
theorem gammaTree_ruleD :
    gammaTree ruleD 10 (.inl 0) = mkDup (mkCon (var 10) (var 11)) mkEra ∧
      gammaTree ruleD 10 (.inl 1) = mkCon (var 12) (mkDup (var 11) (var 13)) ∧
      gammaTree ruleD 10 (.inr 0) = var 10 ∧
      gammaTree ruleD 10 (.inr 1) = mkCon (var 13) (var 12) := by
  decide

/-- On `ruleD`, expanded and linear, the old definition gives the same trees (Fig. 6,
page 86). -/
theorem gammaTree_ruleD_old (k₀ : ℕ) (p : Fin 2 ⊕ Fin 2) :
    gammaTree ruleD k₀ p = oldGammaTree ruleD k₀ p :=
  gammaTree_eq_portTree ruleD_expanded ruleD_linear k₀ p

/-- **The package of `ruleD`, `σ = swap 0 1`** (Fig. 6, page 86): `M*_3` with the trees at `a₀`,
`a₁` on its first two leaves and `T_σ = con` of the trees at `b₀`, `b₁` on its last leaf. -/
theorem gamma_ruleD :
    gamma (Translation.id sig) ruleD (Equiv.swap 0 1) hs 10 =
      mkCon (mkCon (mkCon (var 10) (mkCon (var 13) (var 12)))
        (mkCon (var 12) (mkDup (var 11) (var 13))))
        (mkDup (mkCon (var 10) (var 11)) mkEra) := by
  decide

/-- The same package, `σ = 1`: the last leaf is `T_1 = dup` of the middle trees (Fig. 6,
page 86). -/
theorem gamma_ruleD_id :
    gamma (Translation.id sig) ruleD 1 (hid 2) 10 =
      mkCon (mkCon (mkDup (var 10) (mkCon (var 13) (var 12)))
        (mkCon (var 12) (mkDup (var 11) (var 13))))
        (mkDup (mkCon (var 10) (var 11)) mkEra) := by
  decide

/-- `gamma_ruleD` is `M*_3` applied to the hand-written leaves, in the order of Fig. 6: the trees
at `a₀`, `a₁`, then the transpositor (page 86). -/
theorem gamma_ruleD_muxStar :
    gamma (Translation.id sig) ruleD (Equiv.swap 0 1) hs 10 =
      muxStar [mkDup (mkCon (var 10) (var 11)) mkEra, mkCon (var 12) (mkDup (var 11) (var 13)),
        mkCon (var 10) (mkCon (var 13) (var 12))] := by
  decide

/-- The package is one by `gamma_isPackage`, the hypotheses holding (Fig. 6, page 86). -/
example : (gamma (Translation.id sig) ruleD (Equiv.swap 0 1) hs 10).IsPackage :=
  gamma_isPackage _ ruleD_expanded ruleD_linear _ _ _

/-- Its names are `10, …, 13`, each twice, by computation (Fig. 6, page 86). -/
example : (gamma (Translation.id sig) ruleD (Equiv.swap 0 1) hs 10).vars =
    2 • Multiset.Ico 10 14 := by
  rw [gamma_ruleD]; decide

end INet.Comb.GammaTreeCReview
