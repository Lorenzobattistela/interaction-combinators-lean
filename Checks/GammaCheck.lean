import InteractionCombinators.Lafont.Gamma
import Checks.ExpandTrReview

/-!
# Checks of the package `Γ_{i,j}` (Fig. 6, page 86)

* The expanded side `l₀ = w₀, m₀ = w₀, l₁ = w₁, m₁ = w₁` (`a = k = 2`, the expanded `dup`–`dup`
  rule `dupDupExp`), the identity translation, `σ = swap 0 1`, names from `10`: `Γ` is
  `M*_3(w₀, w₁, T_σ(w₀, w₁)) = con(con(con(w₀, w₁), w₁), w₀)` with `w₀ = 10`, `w₁ = 11`
  (`gamma_dupDup`), and it is a package (`gamma_dupDup_isPackage`, by `gamma_isPackage` and by
  direct computation).
* The side `ruleConDup` (`a₀ = dup(w₀, w₁)`, `a₁ = dup(w₂, w₃)`, `b₀ = con(w₀, w₂)`,
  `b₁ = con(w₁, w₃)`) with the translation `Φrev`, which sends `con` to two cells and one internal
  wire: `Γ` is computed (`gamma_conDup`), it is a package, and its names are `[0, 6)`, each twice.
-/

namespace INet.Comb.GammaCheck

open Term Rule Translation DecompositionReview ExpandedIso ExpandTrReview

/-- Trees over the names of a side with two ports on each group and `n` internal wires. -/
abbrev V (n : ℕ) := Term sig (Fin 2 ⊕ Fin 2 ⊕ Fin n)

/-- `swap 0 1` is an involution. -/
theorem hs : Function.Involutive (Equiv.swap (0 : Fin 2) 1) := fun x => Equiv.swap_apply_self 0 1 x

/-! ## The side `l₀ = w₀, m₀ = w₀, l₁ = w₁, m₁ = w₁`, identity translation -/

/-- The expanded side of the issue, as a rule `Rule sig 2 2` with two internal wires. -/
def φ₀ : Rule sig 2 2 := ⟨2, dupDupExp⟩

theorem φ₀_linear : φ₀.Linear := dupDupExp_linear
theorem φ₀_expanded : φ₀.Expanded := dupDupExp_expanded

theorem portTree_φ₀ :
    φ₀.portTree (.inl 0) = (pw 0 : V 2) ∧ φ₀.portTree (.inl 1) = (pw 1 : V 2) ∧
      φ₀.portTree (.inr 0) = (pw 0 : V 2) ∧ φ₀.portTree (.inr 1) = (pw 1 : V 2) :=
  ⟨portTree_eq φ₀_expanded φ₀_linear (by decide),
    portTree_eq φ₀_expanded φ₀_linear (by decide),
    portTree_eq φ₀_expanded φ₀_linear (by decide),
    portTree_eq φ₀_expanded φ₀_linear (by decide)⟩

/-- The same for the computable twin `Rule.portTreeC`, which `gammaTree` uses (Fig. 6, page 86). -/
theorem portTreeC_φ₀ :
    φ₀.portTreeC (.inl 0) = (pw 0 : V 2) ∧ φ₀.portTreeC (.inl 1) = (pw 1 : V 2) ∧
      φ₀.portTreeC (.inr 0) = (pw 0 : V 2) ∧ φ₀.portTreeC (.inr 1) = (pw 1 : V 2) := by
  rw [portTreeC_eq_portTree φ₀_expanded φ₀_linear]
  exact portTree_φ₀

/-- **The package drawn by hand** (Fig. 6, page 86), for `σ = swap 0 1` and names from `10`:
`M*_3` with leaves `w₀`, `w₁` (the ports `l₀`, `l₁`) and `T_σ(w₀, w₁) = con(w₀, w₁)` (the middle
ports `m₀`, `m₁`), that is `con(con(con(10, 11), 11), 10)`. -/
theorem gamma_dupDup :
    gamma (Translation.id sig) φ₀ (Equiv.swap 0 1) hs 10 =
      mkCon (mkCon (mkCon (var 10) (var 11)) (var 11)) (var 10) := by
  obtain ⟨h0, h1, h2, h3⟩ := portTreeC_φ₀
  have hl : portList (Equiv.swap (0 : Fin 2) 1) = [0, 1] := by decide
  have hp : pairFst (Equiv.swap (0 : Fin 2) 1) = [0] := by decide
  simp only [gamma, gammaPort, trTerm_id, transpositorPerm, hl, hp, List.ofFn_succ,
    List.ofFn_zero, gammaTree, h0, h1, h2, h3, List.map_cons, List.map_nil, Fin.succ_zero_eq_one]
  rfl

/-- Deliverable 2 applies: the hypotheses `Expanded` and `Linear` hold. -/
theorem gamma_dupDup_isPackage :
    (gamma (Translation.id sig) φ₀ (Equiv.swap 0 1) hs 10).IsPackage :=
  gamma_isPackage _ φ₀_expanded φ₀_linear _ _ _

/-- The same, by direct computation on the tree drawn by hand. -/
example : (mkCon (mkCon (mkCon (var 10) (var 11)) (var 11)) (var 10) : Term sig ℕ).IsPackage := by
  intro x hx
  simp only [vars_mkCon, vars_var] at hx ⊢
  simp only [Multiset.mem_add, Multiset.mem_singleton] at hx
  rcases hx with ((rfl | rfl) | rfl) | rfl <;> decide

/-- The interval of names given by `vars_gamma`: `gammaSize = 2`, so the names are `10, 11`. -/
example : (gamma (Translation.id sig) φ₀ (Equiv.swap 0 1) hs 10).vars =
    2 • Multiset.Ico 10 12 := by
  rw [vars_gamma _ φ₀_expanded φ₀_linear]
  congr 2

/-! ## The side `con`–`dup`, translation `Φrev` -/

theorem portTree_conDup :
    ruleConDup.portTree (.inl 0) = (mkDup (pw 0) (pw 1) : V 4) ∧
      ruleConDup.portTree (.inl 1) = (mkDup (pw 2) (pw 3) : V 4) ∧
      ruleConDup.portTree (.inr 0) = (mkCon (pw 0) (pw 2) : V 4) ∧
      ruleConDup.portTree (.inr 1) = (mkCon (pw 1) (pw 3) : V 4) :=
  ⟨portTree_eq ruleConDup_expanded ruleConDup_linear (by decide),
    portTree_eq ruleConDup_expanded ruleConDup_linear (by decide),
    portTree_eq ruleConDup_expanded ruleConDup_linear (by decide),
    portTree_eq ruleConDup_expanded ruleConDup_linear (by decide)⟩

/-- The same for the computable twin `Rule.portTreeC`, which `gammaTree` uses (Fig. 6, page 86). -/
theorem portTreeC_conDup_eq :
    ruleConDup.portTreeC (.inl 0) = (mkDup (pw 0) (pw 1) : V 4) ∧
      ruleConDup.portTreeC (.inl 1) = (mkDup (pw 2) (pw 3) : V 4) ∧
      ruleConDup.portTreeC (.inr 0) = (mkCon (pw 0) (pw 2) : V 4) ∧
      ruleConDup.portTreeC (.inr 1) = (mkCon (pw 1) (pw 3) : V 4) := by
  rw [portTreeC_eq_portTree ruleConDup_expanded ruleConDup_linear]
  exact portTree_conDup

/-- Deliverable 2 on a side whose translation is not the identity: `Φrev` sends `con` to
`con(con(p₁, w), con(w, p₀))`. -/
theorem gamma_conDup_isPackage (k₀ : ℕ) :
    (gamma Φrev ruleConDup (Equiv.swap 0 1) hs k₀).IsPackage :=
  gamma_isPackage _ ruleConDup_expanded ruleConDup_linear _ _ _

/-- The size: the four internal wires of `con`–`dup`, and one wire for each of the two `con`
cells translated by `Φrev`. -/
theorem gammaSize_conDup (k₀ : ℕ) : gammaSize Φrev ruleConDup k₀ = 6 := by
  obtain ⟨h0, h1, h2, h3⟩ := portTreeC_conDup_eq
  simp only [gammaSize, gammaSizes]
  rw [Equiv.sum_comp finSumFinEquiv.symm (fun p => Φrev.size (gammaTree ruleConDup k₀ p)),
    Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [gammaTree, h0, h1, h2, h3]
  rfl

/-- **`Γ` for `con`–`dup` under `Φrev`, from `0`** (Fig. 6, page 86). The internal wires of the
side are `0, 1, 2, 3`; the two `con` trees `b₀ = con(w₀, w₂)`, `b₁ = con(w₁, w₃)` are translated
with their new wire `4`, resp. `5`, and sit in `T_σ = con(·, ·)`; the `dup` trees of `a₀`, `a₁` are
kept: `M*_3(dup(0, 1), dup(2, 3), T_σ)`. -/
theorem gamma_conDup :
    gamma Φrev ruleConDup (Equiv.swap 0 1) hs 0 =
      mkCon (mkCon
        (mkCon (mkCon (mkCon (var 2) (var 4)) (mkCon (var 4) (var 0)))
          (mkCon (mkCon (var 3) (var 5)) (mkCon (var 5) (var 1))))
        (mkDup (var 2) (var 3))) (mkDup (var 0) (var 1)) := by
  obtain ⟨h0, h1, h2, h3⟩ := portTreeC_conDup_eq
  have hl : portList (Equiv.swap (0 : Fin 2) 1) = [0, 1] := by decide
  have hp : pairFst (Equiv.swap (0 : Fin 2) 1) = [0] := by decide
  have hsz : gammaSizes Φrev ruleConDup 0 = ![0, 0, 1, 1] := by
    funext q
    have e0 : (finSumFinEquiv.symm (⟨0, by omega⟩ : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = .inl 0 := rfl
    have e1 : (finSumFinEquiv.symm (⟨1, by omega⟩ : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = .inl 1 := rfl
    have e2 : (finSumFinEquiv.symm (⟨2, by omega⟩ : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = .inr 0 := rfl
    have e3 : (finSumFinEquiv.symm (⟨3, by omega⟩ : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = .inr 1 := rfl
    fin_cases q
    · simp only [gammaSizes, gammaTree]; rw [e0, h0]; rfl
    · simp only [gammaSizes, gammaTree]; rw [e1, h1]; rfl
    · simp only [gammaSizes, gammaTree]; rw [e2, h2]; rfl
    · simp only [gammaSizes, gammaTree]; rw [e3, h3]; rfl
  simp only [gamma, gammaPort, hsz, transpositorPerm, hl, hp, List.ofFn_succ,
    List.ofFn_zero, gammaTree, h0, h1, h2, h3, List.map_cons, List.map_nil, Fin.succ_zero_eq_one]
  decide

/-- The names of this `Γ`, from `0`: `0, …, 5`, each twice. -/
example : (gamma Φrev ruleConDup (Equiv.swap 0 1) hs 0).vars =
    2 • Multiset.Ico 0 6 := by
  rw [vars_gamma _ ruleConDup_expanded ruleConDup_linear, gammaSize_conDup]

/-! ## `gammaTree` computes -/

/-- **`gammaTree` computes** (Fig. 6, page 86): the tree of `con`–`dup` at the port `a₀`, from
`10`, is `dup(10, 11)`, by evaluation alone, without `portTree_conDup`. -/
example : gammaTree ruleConDup 10 (.inl 0) = mkDup (var 10) (var 11) := by decide

/-- The same at the middle port `b₁`: `con(11, 13)`. -/
example : gammaTree ruleConDup 10 (.inr 1) = mkCon (var 11) (var 13) := by decide

/-- The package of `con`–`dup` under `Φrev` from `0` is also found by evaluation alone, without
the lemmas `portTree_conDup` and `gammaSize_conDup` used by `gamma_conDup`. -/
example :
    gamma Φrev ruleConDup (Equiv.swap 0 1) hs 0 =
      mkCon (mkCon
        (mkCon (mkCon (mkCon (var 2) (var 4)) (mkCon (var 4) (var 0)))
          (mkCon (mkCon (var 3) (var 5)) (mkCon (var 5) (var 1))))
        (mkDup (var 2) (var 3))) (mkDup (var 0) (var 1)) := by decide

end INet.Comb.GammaCheck
