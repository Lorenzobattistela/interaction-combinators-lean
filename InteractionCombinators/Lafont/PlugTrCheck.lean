import InteractionCombinators.Lafont.PlugTr
import InteractionCombinators.Lafont.Fig7EndCheck
import InteractionCombinators.TranslationExistsCheck

/-!
# Checks of `netTr_plug_gamma` (page 86)

The side `ruleConDup` (`a₀ = dup(w₀, w₁)`, `a₁ = dup(w₂, w₃)`, `b₀ = con(w₀, w₂)`,
`b₁ = con(w₁, w₃)`, so `a = k = 2`, with cells in every tree) used for both `φ` and `ψ`, the
identity translation, `σ = swap 0 1`, internal wires from `10` for `φ` and from `20` for `ψ`, and
the names `0, 1` and `2, 3` on the ports. `plugTarget` is the six equations
`0 = dup(10, 11)`, `1 = dup(12, 13)`, `2 = dup(20, 21)`, `3 = dup(22, 23)`,
`con(10, 12) = con(21, 23)`, `con(11, 13) = con(20, 22)`; it is linear, so every hypothesis of
`netTr_plug_gamma` holds.
-/

namespace INet.Comb.PlugTrCheck

open Term Rule Translation GammaCheck Fig7EndCheck ExpandTrReview

/-- The trees of `[ruleConDup]` under the identity translation, internal wires from `k₀`
(page 86). -/
theorem gammaPort_conDup (k₀ : ℕ) :
    gammaPort (Translation.id sig) ruleConDup k₀ (.inl 0) =
        mkDup (var (k₀ + 0)) (var (k₀ + 1)) ∧
      gammaPort (Translation.id sig) ruleConDup k₀ (.inl 1) =
        mkDup (var (k₀ + 2)) (var (k₀ + 3)) ∧
      gammaPort (Translation.id sig) ruleConDup k₀ (.inr 0) =
        mkCon (var (k₀ + 0)) (var (k₀ + 2)) ∧
      gammaPort (Translation.id sig) ruleConDup k₀ (.inr 1) =
        mkCon (var (k₀ + 1)) (var (k₀ + 3)) := by
  obtain ⟨h0, h1, h2, h3⟩ := portTree_conDup
  simp only [gammaPort, trTerm_id, gammaTree, h0, h1, h2, h3]
  -- the trees of `ruleConDup` are typed with its `internal` field (see `CLAUDE.md`)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | (erw [bind_mkDup]; congr 1) | (erw [bind_mkCon]; congr 1)

/-- `plugTarget` for this instance, written out (page 86): the middle port `0` of `φ` meets the
middle port `σ 0 = 1` of `ψ`. -/
theorem plugTarget_conDup :
    plugTarget (Translation.id sig) ruleConDup ruleConDup (Equiv.swap 0 1) 10 20 ![0, 1]
        ![2, 3] =
      s(var 0, mkDup (var 10) (var 11)) ::ₘ s(var 1, mkDup (var 12) (var 13)) ::ₘ
        s(var 2, mkDup (var 20) (var 21)) ::ₘ s(var 3, mkDup (var 22) (var 23)) ::ₘ
        s(mkCon (var 10) (var 12), mkCon (var 21) (var 23)) ::ₘ
        {s(mkCon (var 11) (var 13), mkCon (var 20) (var 22))} := by
  obtain ⟨a0, a1, a2, a3⟩ := gammaPort_conDup 10
  obtain ⟨b0, b1, b2, b3⟩ := gammaPort_conDup 20
  simp only [plugTarget, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one,
    Fin.isValue, a0, a1, a2, a3, b0, b1, b2, b3, Equiv.swap_apply_left, Equiv.swap_apply_right]
  decide

/-- The hypothesis `hlin` of `netTr_plug_gamma` holds for this instance (page 86). -/
theorem plugTarget_conDup_linear :
    Net.Linear (plugTarget (Translation.id sig) ruleConDup ruleConDup (Equiv.swap 0 1) 10 20
      ![0, 1] ![2, 3]) := by
  rw [plugTarget_conDup]
  apply Net.linear_of_forall_mem
  decide

/-- **`netTr_plug_gamma` is not vacuous** (Fig. 7, page 86): on the side `ruleConDup`, whose trees
contain cells, with `σ = swap 0 1`, every hypothesis is proved, and the net
`plugTarget_conDup` is, up to wires, a translation of an instance of the plugged rule. -/
theorem netTr_plug_conDup :
    ∃ (h : Fin (Rule.plug ruleConDup ruleConDup (Equiv.swap 0 1)).internal → ℕ) (N' : CNet),
      (Translation.id sig).NetTr ((Rule.plug ruleConDup ruleConDup (Equiv.swap 0 1)).inst
        (fun i => .var (![0, 1] i)) (fun j => .var (![2, 3] j)) h) N' ∧
      Equiv N' (s(var 0, mkDup (var 10) (var 11)) ::ₘ s(var 1, mkDup (var 12) (var 13)) ::ₘ
        s(var 2, mkDup (var 20) (var 21)) ::ₘ s(var 3, mkDup (var 22) (var 23)) ::ₘ
        s(mkCon (var 10) (var 12), mkCon (var 21) (var 23)) ::ₘ
        {s(mkCon (var 11) (var 13), mkCon (var 20) (var 22))}) := by
  rw [← plugTarget_conDup]
  exact netTr_plug_gamma _ ruleConDup_expanded ruleConDup_linear ruleConDup_expanded
    ruleConDup_linear _ 10 20 _ _ plugTarget_conDup_linear

end INet.Comb.PlugTrCheck
