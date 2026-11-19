import InteractionCombinators.Lafont.PlugTermTr
import Checks.PlugTrCheck

/-!
# Checks of `netTr_plug_termTr` (pages 85–86, 90)

The side `ruleConDup` (`a₀ = dup(w₀, w₁)`, `a₁ = dup(w₂, w₃)`, `b₀ = con(w₀, w₂)`,
`b₁ = con(w₁, w₃)`) for both `φ` and `ψ`, internal wires from `10` for `φ` and from `20` for `ψ`,
`σ = swap 0 1`, the names `0, 1` and `2, 3` on the ports, and the translation `Φrev`, which sends
`con(a, b)` to `con(con(b, w), con(w, a))` with one new wire `w`.

The trees are the translations of the trees of the side with new wires chosen by hand: `50`, `51`
for the two `con` trees of `φ`, `60`, `61` for those of `ψ`. They are not the trees `gammaPort`
of `netTr_plug_gamma`, which number the new wires of `φ` from `k₀ + φ.internal = 14`
(`tφ_ne_gammaPort`). The net `plugTermTarget` is linear (proved by computation), so every
hypothesis of `netTr_plug_termTr` holds.
-/

namespace INet.Comb.PlugTermTrCheck

open Term Rule Translation ExpandTrReview

/-- The trees of `ruleConDup` with internal wires from `k₀` (page 86). -/
theorem gammaTree_conDup (k₀ : ℕ) :
    gammaTree ruleConDup k₀ (.inl 0) = mkDup (var (k₀ + 0)) (var (k₀ + 1)) ∧
      gammaTree ruleConDup k₀ (.inl 1) = mkDup (var (k₀ + 2)) (var (k₀ + 3)) ∧
      gammaTree ruleConDup k₀ (.inr 0) = mkCon (var (k₀ + 0)) (var (k₀ + 2)) ∧
      gammaTree ruleConDup k₀ (.inr 1) = mkCon (var (k₀ + 1)) (var (k₀ + 3)) := by
  have h := PlugTrCheck.gammaPort_conDup k₀
  simpa only [gammaPort, trTerm_id] using h

/-- The trees chosen for `φ`: the translations by `Φrev` of the trees of `ruleConDup` with
internal wires from `10`, the new wire of the `con` tree at the middle port `l` named `50 + l`. -/
noncomputable def tφ : Fin 2 ⊕ Fin 2 → Term sig ℕ :=
  fun p => Φrev.trTerm (50 + Sum.elim (fun _ => 0) (fun l : Fin 2 => (l : ℕ)) p)
    (gammaTree ruleConDup 10 p)

/-- The trees chosen for `ψ`: internal wires from `20`, new wires `60 + l`. -/
noncomputable def tψ : Fin 2 ⊕ Fin 2 → Term sig ℕ :=
  fun p => Φrev.trTerm (60 + Sum.elim (fun _ => 0) (fun l : Fin 2 => (l : ℕ)) p)
    (gammaTree ruleConDup 20 p)

/-- The trees of `φ`, written out. -/
theorem tφ_eq :
    tφ (.inl 0) = mkDup (var 10) (var 11) ∧ tφ (.inl 1) = mkDup (var 12) (var 13) ∧
      tφ (.inr 0) = mkCon (mkCon (var 12) (var 50)) (mkCon (var 50) (var 10)) ∧
      tφ (.inr 1) = mkCon (mkCon (var 13) (var 51)) (mkCon (var 51) (var 11)) := by
  obtain ⟨h0, h1, h2, h3⟩ := gammaTree_conDup 10
  simp only [tφ, h0, h1, h2, h3, Sum.elim_inl, Sum.elim_inr]
  decide

/-- The trees of `ψ`, written out. -/
theorem tψ_eq :
    tψ (.inl 0) = mkDup (var 20) (var 21) ∧ tψ (.inl 1) = mkDup (var 22) (var 23) ∧
      tψ (.inr 0) = mkCon (mkCon (var 22) (var 60)) (mkCon (var 60) (var 20)) ∧
      tψ (.inr 1) = mkCon (mkCon (var 23) (var 61)) (mkCon (var 61) (var 21)) := by
  obtain ⟨h0, h1, h2, h3⟩ := gammaTree_conDup 20
  simp only [tψ, h0, h1, h2, h3, Sum.elim_inl, Sum.elim_inr]
  decide

/-- The trees `tφ` are not those of `netTr_plug_gamma`: at the middle port `0`, `gammaPort`
names the new wire `14`, not `50`. -/
theorem tφ_ne_gammaPort : tφ (.inr 0) ≠ gammaPort Φrev ruleConDup 10 (.inr 0) := by
  obtain ⟨h0, h1, h2, h3⟩ := GammaCheck.portTreeC_conDup_eq
  have hsz : gammaSizes Φrev ruleConDup 10 = ![0, 0, 1, 1] := by
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
  rw [tφ_eq.2.2.1]
  simp only [gammaPort, hsz, gammaTree, h2]
  decide

/-- `plugTermTarget` for this instance, written out (page 86): the middle port `0` of `φ` meets
the middle port `σ 0 = 1` of `ψ`. -/
theorem plugTermTarget_conDup :
    plugTermTarget (Equiv.swap 0 1) tφ tψ ![0, 1] ![2, 3] =
      s(var 0, mkDup (var 10) (var 11)) ::ₘ s(var 1, mkDup (var 12) (var 13)) ::ₘ
        s(var 2, mkDup (var 20) (var 21)) ::ₘ s(var 3, mkDup (var 22) (var 23)) ::ₘ
        s(mkCon (mkCon (var 12) (var 50)) (mkCon (var 50) (var 10)),
          mkCon (mkCon (var 23) (var 61)) (mkCon (var 61) (var 21))) ::ₘ
        {s(mkCon (mkCon (var 13) (var 51)) (mkCon (var 51) (var 11)),
          mkCon (mkCon (var 22) (var 60)) (mkCon (var 60) (var 20)))} := by
  obtain ⟨a0, a1, a2, a3⟩ := tφ_eq
  obtain ⟨b0, b1, b2, b3⟩ := tψ_eq
  simp only [plugTermTarget, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero,
    Fin.succ_zero_eq_one, Fin.isValue, a0, a1, a2, a3, b0, b1, b2, b3, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  decide

/-- The hypothesis `hlin` of `netTr_plug_termTr` holds for this instance. -/
theorem plugTermTarget_conDup_linear :
    Net.Linear (plugTermTarget (Equiv.swap 0 1) tφ tψ ![0, 1] ![2, 3]) := by
  rw [plugTermTarget_conDup]
  apply Net.linear_of_forall_mem
  decide

/-- **`netTr_plug_termTr` is not vacuous** (Fig. 7, page 86; Fig. 10, page 90): on the side
`ruleConDup`, with the translation `Φrev` and trees whose new wires are not those of `gammaPort`,
every hypothesis is proved, and `plugTermTarget_conDup` is, up to wires, a translation of an
instance of the plugged rule. -/
theorem netTr_plug_termTr_conDup :
    ∃ (h : Fin (Rule.plug ruleConDup ruleConDup (Equiv.swap 0 1)).internal → ℕ) (N' : CNet),
      Φrev.NetTr ((Rule.plug ruleConDup ruleConDup (Equiv.swap 0 1)).inst
        (fun i => .var (![0, 1] i)) (fun j => .var (![2, 3] j)) h) N' ∧
      Equiv N' (s(var 0, mkDup (var 10) (var 11)) ::ₘ s(var 1, mkDup (var 12) (var 13)) ::ₘ
        s(var 2, mkDup (var 20) (var 21)) ::ₘ s(var 3, mkDup (var 22) (var 23)) ::ₘ
        s(mkCon (mkCon (var 12) (var 50)) (mkCon (var 50) (var 10)),
          mkCon (mkCon (var 23) (var 61)) (mkCon (var 61) (var 21))) ::ₘ
        {s(mkCon (mkCon (var 13) (var 51)) (mkCon (var 51) (var 11)),
          mkCon (mkCon (var 22) (var 60)) (mkCon (var 60) (var 20)))}) := by
  rw [← plugTermTarget_conDup]
  exact netTr_plug_termTr Φrev ruleConDup_expanded ruleConDup_linear ruleConDup_expanded
    ruleConDup_linear _ 10 20 tφ tψ (fun p => Φrev.termTr_trTerm _ _)
    (fun q => Φrev.termTr_trTerm _ _) _ _ plugTermTarget_conDup_linear

end INet.Comb.PlugTermTrCheck
