import InteractionCombinators.NetLemmas
import InteractionCombinators.Lafont.Fig7End

/-!
# Checks of the end of Fig. 7 (page 86)

The side `φ₀` of `GammaCheck` (`l₀ = w₀, m₀ = w₀, l₁ = w₁, m₁ = w₁`, `a = b = k = 2`), the identity
translation and `σ = swap 0 1`, used for both `Γ_{i,j}` (names from `10`) and `Γ_{j,i}` (names from
`20`). The trees `0, 1` and `2, 3` are on the auxiliary ports of the two cells, and the loop is `5`.

* `mux_gamma_mux_gamma_dupDup` — the hypothesis of `mux_gamma_mux_gamma` holds, and the net it
  reaches is computed: `0 = 10, 1 = 11, 2 = 20, 3 = 21`, and, for the middle ports through `σ`,
  `10 = 21, 11 = 20`.
* `cellSkel_dupDup` — the same for the whole of Fig. 7, from two cells `[α₀]` with menus of one
  package each (`m = 1`).
-/

namespace INet.Comb.Fig7EndCheck

open Term Rule Translation GammaCheck

theorem gammaPort_φ₀ (k₀ : ℕ) :
    gammaPort (Translation.id sig) φ₀ k₀ (.inl 0) = var (k₀ + 0) ∧
      gammaPort (Translation.id sig) φ₀ k₀ (.inl 1) = var (k₀ + 1) ∧
      gammaPort (Translation.id sig) φ₀ k₀ (.inr 0) = var (k₀ + 0) ∧
      gammaPort (Translation.id sig) φ₀ k₀ (.inr 1) = var (k₀ + 1) := by
  obtain ⟨h0, h1, h2, h3⟩ := portTree_φ₀
  simp only [gammaPort, trTerm_id, gammaTree, h0, h1, h2, h3]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `Γ` of `φ₀` from `k₀` (as `gamma_dupDup`, for any `k₀`). -/
theorem gamma_φ₀ (k₀ : ℕ) :
    gamma (Translation.id sig) φ₀ (Equiv.swap 0 1) hs k₀ =
      mkCon (mkCon (mkCon (var (k₀ + 0)) (var (k₀ + 1))) (var (k₀ + 1))) (var (k₀ + 0)) := by
  obtain ⟨h0, h1, h2, h3⟩ := gammaPort_φ₀ k₀
  have hl : portList (Equiv.swap (0 : Fin 2) 1) = [0, 1] := by decide
  have hp : pairFst (Equiv.swap (0 : Fin 2) 1) = [0] := by decide
  simp only [gamma, transpositorPerm, hl, hp, List.ofFn_succ, List.ofFn_zero, List.map_cons,
    List.map_nil, Fin.succ_zero_eq_one, Fin.isValue, h0, h1, h2, h3]
  rfl

/-- The net of the last rows of Fig. 7 for this instance. -/
noncomputable abbrev N0 : CNet :=
  s(mux ([var 0, var 1] ++ [var 5]), gamma (Translation.id sig) φ₀ (Equiv.swap 0 1) hs 10) ::ₘ
    s(mux ([var 2, var 3] ++ [var 5]), gamma (Translation.id sig) φ₀ (Equiv.swap 0 1) hs 20) ::ₘ 0

theorem N0_linear : Net.Linear N0 := by
  apply Net.linear_of_forall_mem
  rw [N0, gamma_φ₀, gamma_φ₀]
  decide

/-- **`mux_gamma_mux_gamma` on `φ₀`** (Fig. 7, page 86): its hypothesis holds, and the net it
reaches is the six wires `0 = 10, 1 = 11, 2 = 20, 3 = 21, 10 = 21, 11 = 20`. -/
theorem mux_gamma_mux_gamma_dupDup :
    ∃ M, StepsE system N0 M ∧
      Equiv M (s(var 0, var 10) ::ₘ s(var 1, var 11) ::ₘ s(var 2, var 20) ::ₘ s(var 3, var 21) ::ₘ
        s(var 10, var 21) ::ₘ {s(var 11, var 20)}) := by
  obtain ⟨M, hS, hE⟩ := mux_gamma_mux_gamma (Translation.id sig) φ₀ φ₀ (Equiv.swap 0 1) hs 10 20
    [var 0, var 1] [var 2, var 3] rfl rfl 5 0 N0_linear
  refine ⟨M, hS, hE.trans (Equiv.of_eq ?_)⟩
  obtain ⟨a0, a1, a2, a3⟩ := gammaPort_φ₀ 10
  obtain ⟨b0, b1, b2, b3⟩ := gammaPort_φ₀ 20
  simp only [Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, Fin.isValue,
    a0, a1, a2, a3, b0, b1, b2, b3, Equiv.swap_apply_left, Equiv.swap_apply_right]
  decide

/-- **Fig. 7 on `φ₀`, from the cells** (page 86): two cells `[α₀]` with `m = 1`, menus `[Γ_{0,0}]`
from `20` and from `10`, trees `0, 1` and `2, 3`, loops `5` and `6`. The hypotheses of
`cellSkel_gamma_cellSkel_gamma` hold, and the net reaches the same six wires. -/
theorem cellSkel_dupDup :
    ∃ M, StepsE system
      (s(cellSkel (menu [gamma (Translation.id sig) φ₀ (Equiv.swap 0 1) hs 20]) 1 0
          [var 0, var 1] 5,
        cellSkel (menu [gamma (Translation.id sig) φ₀ (Equiv.swap 0 1) hs 10]) 1 0
          [var 2, var 3] 6) ::ₘ 0) M ∧
      Equiv M (s(var 0, var 10) ::ₘ s(var 1, var 11) ::ₘ s(var 2, var 20) ::ₘ s(var 3, var 21) ::ₘ
        s(var 10, var 21) ::ₘ {s(var 11, var 20)}) := by
  have hlin : Net.Linear
      (s(cellSkel (menu [gamma (Translation.id sig) φ₀ (Equiv.swap 0 1) hs 20]) 1 0
          [var 0, var 1] 5,
        cellSkel (menu [gamma (Translation.id sig) φ₀ (Equiv.swap 0 1) hs 10]) 1 0
          [var 2, var 3] 6) ::ₘ 0) := by
    apply Net.linear_of_forall_mem
    rw [gamma_φ₀, gamma_φ₀]
    decide
  have hp : ∀ k₀, ∀ π ∈ [gamma (Translation.id sig) φ₀ (Equiv.swap 0 1) hs k₀], π.IsPackage := by
    intro k₀ π hπ
    rw [List.mem_singleton.1 hπ]
    exact gamma_isPackage _ φ₀_expanded φ₀_linear _ _ _
  obtain ⟨M, hS, hE⟩ := cellSkel_gamma_cellSkel_gamma (Translation.id sig) φ₀ φ₀
    (Equiv.swap 0 1) hs 10 20 _ _ 1 0 0 rfl rfl (by omega) (by omega) (hp 20) (hp 10) rfl rfl
    [var 0, var 1] [var 2, var 3] rfl rfl 5 6 0 hlin
  refine ⟨M, hS, hE.trans (Equiv.of_eq ?_)⟩
  obtain ⟨a0, a1, a2, a3⟩ := gammaPort_φ₀ 10
  obtain ⟨b0, b1, b2, b3⟩ := gammaPort_φ₀ 20
  simp only [Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, Fin.isValue,
    a0, a1, a2, a3, b0, b1, b2, b3, Equiv.swap_apply_left, Equiv.swap_apply_right]
  decide

end INet.Comb.Fig7EndCheck
