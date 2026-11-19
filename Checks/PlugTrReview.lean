import InteractionCombinators.Lafont.PlugTr
import Checks.Fig7EndReview

/-!
# Review of `plugTarget` and `netTr_plug_gamma` (`PlugTr.lean`) against Fig. 7 and page 85

Lafont 1997, Section 2.4, journal pages 85–86 (PDF pages 17–18), the decomposition of a right
member as `φ_{i,j}`, `ψ_{i,j}` above the permutation box `σ_{i,j}`, and the end of Fig. 7. Review
of `Lafont/PlugTr.lean` (issue #121).

## Against the paper

* **The orientation of `σ`.** On page 85 the box `σ_{i,j}` joins the bottom wires of `φ_{i,j}` to
  those of `ψ_{i,j}`; the paper fixes no direction for it. The code reads it as "the middle wire `l`
  of `φ` meets the middle wire `σ l` of `ψ`", in both places: in `Rule.plug` through `Rule.plugR`,
  which names the middle wire `l` of `ψ` as the middle wire `σ⁻¹ l` of `φ`
  (`GammaReview.plugR_middle`), and in `plugTarget`, whose middle equations are
  `s([φ] at .inr l, [ψ] at .inr (σ l))`. The two agree for **every** permutation, involutive or not:
  `netTr_plug_gamma` is correct as stated for any `σ`. `rot_plug_net` and `rot_target` below check
  it on a 3-cycle, by computing both nets: in the plugged rule the middle wire `0` of `φ` (joined to
  its internal wire `w₀`) is the middle wire `1` of `ψ` (joined to its internal wire `w₂`), and in
  `plugTarget` the name `0` (`w₀` of `φ`) meets the name `12` (`w₂` of `ψ`).
  Involutivity is needed only upstream, by the transpositor (`mux_gamma_mux_gamma`): there `T_σ`
  against `T_σ` yields `l ↔ σ l` only because `σ = σ⁻¹`. For an involution the two readings
  `l ↔ σ l` and `l ↔ σ⁻¹ l` coincide (`Fig7EndReview.middle_symm`).
* **The order of the ports.** In `Translation.Compatible` (`Translation.lean:94`) the auxiliary
  port `i` of `αᵢ` is the name `xs i` and the port `j` of `α_j` is `ys j`, and the instance is
  `r.inst (var ∘ xs) (var ∘ ys) h`. In `plugTarget` the port `p` of `φ` gets `xs p` and the port `q`
  of `ψ` gets `ys q`, and the instance of `netTr_plug_gamma` is
  `(Rule.plug φ ψ σ).inst (var ∘ xs) (var ∘ ys) h`, the left ports of `plug` being those of `φ`
  (`Rule.plugL (.inl i) = .inl i`) and the right ports those of `ψ`
  (`Rule.plugR σ (.inl j) = .inr (.inl j)`). In Fig. 7 the leaves of `M_{nᵢ+1}` are the ports of
  `αᵢ` in order and meet the ports of `[φ_{i,j}]` in order (reviewed in `Fig7EndReview`), so the
  order is the paper's. `rot_target` shows it on `a = 1`, `b = 2`: `30` meets the tree of port `0`
  of `φ`, `31` and `32` the trees of ports `0` and `1` of `ψ`.

## Refutation attempts

* **A non-involutive `σ`** (`rot3`, the 3-cycle `0 ↦ 1 ↦ 2 ↦ 0`, `k = 3`, `a = 1`, `b = 2`):
  `rot_linear` proves the hypothesis, `rot_netTr` applies `netTr_plug_gamma`, and `rot_plug_net`,
  `rot_target` compute both sides; they pair the middle wires the same way. No defect.
* **`plugTarget` not linear** (`xs = ![30, 30]` and `ys = ![30]`): `dup_not_linear` shows that
  `plugTarget` is not linear, and `dup_no_translation` that the conclusion of `netTr_plug_gamma` is
  then **false**: a translation is linear, `Equiv` preserves linearity. So `hlin` is needed and
  can fail; it is not implied by the other hypotheses. (It also fails when the ranges
  `[k₀, k₀ + φ.internal)` and `[k₁, k₁ + ψ.internal)` overlap, or meet `xs`, `ys`.)
* **`k = 0`** (`ruleK0` on both sides, two ports joined by an internal wire): `k0_target` computes
  `plugTarget`, four equations in two components with no middle equation, and `k0_netTr` applies
  `netTr_plug_gamma`. No defect: the fresh middle names `B + l` range over `Fin 0`.

## Strength for the next step

`mux_gamma_mux_gamma_netTr` concludes `∃ M N' h, StepsE system start M ∧ Equiv M N' ∧
Φ.NetTr ((Rule.plug φ ψ σ).inst (var ∘ xs) (var ∘ ys) h) N'`, the same `xs`, `ys` as the leaves of
the multiplexors. This is the body of `Translation.Compatible` (same order of the three conjuncts,
same `StepsE`, `Equiv M N'` in that direction, the instance with `var ∘ xs`, `var ∘ ys`), with
three differences that the assembly has to bridge and that are not defects:

* the start net is rows 3–4 of Fig. 7 (two equations joined by the loop `ℓ`, empty context), not
  the single equation `s([αᵢ](xs), [α_j](ys))` of `Compatible`; rows 1–2 (the `T_{1,1}`, the
  `S_m` selection) must reach it, with `ℓ` chosen fresh, and the hypothesis `hlin` of
  `mux_gamma_mux_gamma_netTr` must be derived from the linearity in `Compatible` along those steps;
* the rule is `Rule.plug φ ψ σ` of the expanded sides, not `r`; PR #122 relates the two (a
  translation of an instance of `Rule.plug` is, up to `Equiv`, one of an instance of `r`);
* the start net has an empty context, as `Compatible` has; nothing to bridge there.

`k3_netTr` applies `mux_gamma_mux_gamma_netTr` to a concrete instance (`σ = swap 0 2`, `a = 1`,
`b = 2`), with `hlin` proved, so the theorem is not vacuous.

## Not checked

* Whether the sides `φ`, `ψ` chosen by the translation (`D.side`) make the hypotheses of
  `mux_gamma_mux_gamma_netTr` hold in the assembly: that is the assembly's job.
* `Fig7End.lean` itself (reviewed in #110).
-/

namespace INet.Comb.PlugTrReview

open Term Rule Translation DecompositionReview ExpandedIso ExpandTrReview GammaCheck GammaReview
  Fig7EndCheck Fig7EndReview

/-! ## A non-involutive `σ`: the 3-cycle on `k = 3` -/

/-- The 3-cycle `0 ↦ 1 ↦ 2 ↦ 0` on the middle wires. -/
def rot3 : Equiv.Perm (Fin 3) := ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

/-- `rot3` is not an involution. -/
theorem rot3_not_involutive : ¬ Function.Involutive rot3 := fun h => absurd (h 0) (by decide)

/-- **The plugged rule for the 3-cycle** (page 85): `Rule.plug ruleK3 ruleK3b rot3`. The middle
wires are the internal wires `0, 1, 2`, those of `ruleK3` are `3, 4, 5`, those of `ruleK3b` are
`6, 7, 8`. The middle wire `l` of `ψ` is `rot3⁻¹ l`: `ψ`'s `0, 1, 2` are `2, 0, 1`. So the wire `0`
joins `w₀` of `φ` (`3`) to `w₂` of `ψ` (`8`), `1` joins `con(5, 5)` to `7`, `2` joins `4` to `6`. -/
theorem rot_plug_net :
    (show Net sig (Fin 1 ⊕ Fin 2 ⊕ Fin 9) from (Rule.plug ruleK3 ruleK3b rot3).net) =
      s(pl 0, mkDup (pw 3) (pw 4)) ::ₘ s(pw 0, pw 3) ::ₘ s(pw 1, mkCon (pw 5) (pw 5)) ::ₘ
        s(pw 2, pw 4) ::ₘ s(pr 0, mkCon (pw 6) (pw 7)) ::ₘ s(pr 1, pw 8) ::ₘ s(pw 2, pw 6) ::ₘ
        s(pw 0, pw 8) ::ₘ {s(pw 1, pw 7)} := by
  decide

/-- **`plugTarget` for the 3-cycle** (Fig. 7, end, page 86): `ruleK3` from `0`, `ruleK3b` from
`10`, `xs = ![30]`, `ys = ![31, 32]`. The middle port `l` of `φ` meets the middle port `rot3 l` of
`ψ`: `0 = 12` (`w₀` of `φ`, `w₂` of `ψ`), `con(2, 2) = 11`, `1 = 10`, as in `rot_plug_net`. -/
theorem rot_target :
    plugTarget (Translation.id sig) ruleK3 ruleK3b rot3 0 10 ![30] ![31, 32] =
      (s(var 30, mkDup (var 0) (var 1)) ::ₘ s(var 31, mkCon (var 10) (var 11)) ::ₘ
        s(var 32, var 12) ::ₘ s(var 0, var 12) ::ₘ s(mkCon (var 2) (var 2), var 11) ::ₘ
        {s(var 1, var 10)} : CNet) := by
  obtain ⟨a0, a1, a2, a3⟩ := gammaPort_K3
  obtain ⟨b0, b1, b2, b3, b4⟩ := gammaPort_K3b
  have e0 : rot3 0 = 1 := rfl
  have e1 : rot3 1 = 2 := rfl
  have e2 : rot3 2 = 0 := rfl
  simp only [plugTarget, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one,
    Fin.isValue, Fin.succ_one_eq_two, e0, e1, e2, a0, a1, a2, a3, b0, b1, b2, b3, b4,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  decide

theorem rot_linear :
    Net.Linear (plugTarget (Translation.id sig) ruleK3 ruleK3b rot3 0 10 ![30] ![31, 32]) := by
  rw [rot_target]
  apply Net.linear_of_forall_mem
  decide

/-- **`netTr_plug_gamma` for a non-involutive `σ`** (pages 85–86): with the 3-cycle `rot3`, every
hypothesis holds and the net of `rot_target` is a translation of an instance of
`Rule.plug ruleK3 ruleK3b rot3`, the net of `rot_plug_net`. -/
theorem rot_netTr :
    ∃ (h : Fin (Rule.plug ruleK3 ruleK3b rot3).internal → ℕ) (N' : CNet),
      (Translation.id sig).NetTr ((Rule.plug ruleK3 ruleK3b rot3).inst
        (fun i => .var (![30] i)) (fun j => .var (![31, 32] j)) h) N' ∧
      Equiv N' (s(var 30, mkDup (var 0) (var 1)) ::ₘ s(var 31, mkCon (var 10) (var 11)) ::ₘ
        s(var 32, var 12) ::ₘ s(var 0, var 12) ::ₘ s(mkCon (var 2) (var 2), var 11) ::ₘ
        {s(var 1, var 10)}) := by
  obtain ⟨h, N', hN, hE⟩ := netTr_plug_gamma (Translation.id sig) ruleK3_expanded ruleK3_linear
    ruleK3b_expanded ruleK3b_linear rot3 0 10 ![30] ![31, 32] rot_linear
  exact ⟨h, N', hN, rot_target ▸ hE⟩

/-! ## `hlin` can fail, and is then needed -/

/-- `plugTarget` with the name `30` on both ports of `φ = ruleK3b` and on the port of
`ψ = ruleK3`: three occurrences of `30`. -/
noncomputable abbrev dupTarget : CNet :=
  plugTarget (Translation.id sig) ruleK3b ruleK3 (Equiv.swap 0 2) 10 0 ![30, 30] ![30]

/-- **`plugTarget` need not be linear** (page 86): with `xs = ![30, 30]` and `ys = ![30]`, the name
`30` occurs three times. All the other hypotheses of `netTr_plug_gamma` hold (`ruleK3b`, `ruleK3`
are linear and expanded). -/
theorem dup_not_linear : ¬ Net.Linear dupTarget := by
  intro h
  have h30 := h 30
  obtain ⟨a0, a1, a2, a3⟩ := gammaPort_K3
  obtain ⟨b0, b1, b2, b3, b4⟩ := gammaPort_K3b
  have e0 : Equiv.swap (0 : Fin 3) 2 0 = 2 := rfl
  have e1 : Equiv.swap (0 : Fin 3) 2 1 = 1 := rfl
  have e2 : Equiv.swap (0 : Fin 3) 2 2 = 0 := rfl
  simp only [dupTarget, plugTarget, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero,
    Fin.succ_zero_eq_one, Fin.isValue, Fin.succ_one_eq_two, e0, e1, e2, a0, a1, a2, a3, b0, b1, b2,
    b3, b4, Matrix.cons_val_zero, Matrix.cons_val_one] at h30
  revert h30
  decide

/-- **Without `hlin` the conclusion of `netTr_plug_gamma` is false** (page 86): for `dupTarget`
there is no translation of an instance of the plugged rule that is `Equiv` to it, since a
translation is linear and `Equiv` preserves linearity. -/
theorem dup_no_translation :
    ¬ ∃ (h : Fin (Rule.plug ruleK3b ruleK3 (Equiv.swap 0 2)).internal → ℕ) (N' : CNet),
      (Translation.id sig).NetTr ((Rule.plug ruleK3b ruleK3 (Equiv.swap 0 2)).inst
        (fun i => .var (![30, 30] i)) (fun j => .var (![30] j)) h) N' ∧ Equiv N' dupTarget :=
  fun ⟨_, _, hN, hE⟩ => dup_not_linear (hE.linear hN.linear)

/-! ## `k = 0`: no middle wire -/

/-- The trees of `[ruleK0]` from `k₀`: both ports are the leaf `k₀`. -/
theorem gammaPort_K0 (k₀ : ℕ) (p : Fin 2) :
    gammaPort (Translation.id sig) ruleK0 k₀ (.inl p) = var k₀ := by
  have h : ∀ p : Fin 2, ruleK0.portTreeC (.inl p) = (pw 0 : Term sig (Fin 2 ⊕ Fin 0 ⊕ Fin 1)) := by
    intro p
    fin_cases p
    · exact portTreeC_eq ruleK0_expanded ruleK0_linear (by decide)
    · exact portTreeC_eq ruleK0_expanded ruleK0_linear (by decide)
  simp only [gammaPort, trTerm_id, gammaTree, h]
  rfl

/-- **`plugTarget` with `k = 0`** (Fig. 7, page 86, with no middle wire): `ruleK0` on both sides,
from `5` and `6`. The net is two disconnected pieces, `30 = 5 = 31` and `32 = 6 = 33`. -/
theorem k0_target :
    plugTarget (Translation.id sig) ruleK0 ruleK0 1 5 6 ![30, 31] ![32, 33] =
      (s(var 30, var 5) ::ₘ s(var 31, var 5) ::ₘ s(var 32, var 6) ::ₘ {s(var 33, var 6)} : CNet) := by
  simp only [plugTarget, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, gammaPort_K0,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  decide

/-- **`netTr_plug_gamma` with `k = 0`** (pages 85–86): the two sides are not connected; the
hypotheses hold and the conclusion holds. -/
theorem k0_netTr :
    ∃ (h : Fin (Rule.plug ruleK0 ruleK0 1).internal → ℕ) (N' : CNet),
      (Translation.id sig).NetTr ((Rule.plug ruleK0 ruleK0 1).inst
        (fun i => .var (![30, 31] i)) (fun j => .var (![32, 33] j)) h) N' ∧
      Equiv N' (s(var 30, var 5) ::ₘ s(var 31, var 5) ::ₘ s(var 32, var 6) ::ₘ
        {s(var 33, var 6)}) := by
  have hlin : Net.Linear (plugTarget (Translation.id sig) ruleK0 ruleK0 1 5 6 ![30, 31]
      ![32, 33]) := by
    rw [k0_target]
    apply Net.linear_of_forall_mem
    decide
  obtain ⟨h, N', hN, hE⟩ := netTr_plug_gamma (Translation.id sig) ruleK0_expanded ruleK0_linear
    ruleK0_expanded ruleK0_linear 1 5 6 ![30, 31] ![32, 33] hlin
  exact ⟨h, N', hN, k0_target ▸ hE⟩

/-! ## The whole of `mux_gamma_mux_gamma_netTr` on a concrete instance -/

/-- **`mux_gamma_mux_gamma_netTr` is not vacuous** (Fig. 7, rows 3–4, page 86): with `ruleK3` from
`0`, `ruleK3b` from `10`, `σ = swap 0 2`, `xs = ![30]`, `ys = ![31, 32]` and the loop `35`, its
hypothesis holds and it gives a reduction to a translation of an instance of
`Rule.plug ruleK3 ruleK3b (swap 0 2)`. -/
theorem k3_netTr :
    ∃ (M N' : CNet) (h : Fin (Rule.plug ruleK3 ruleK3b (Equiv.swap 0 2)).internal → ℕ),
      StepsE system
        (s(mux (List.ofFn (fun p => (var (![30] p) : Term sig ℕ)) ++ [var 35]),
            gamma (Translation.id sig) ruleK3 (Equiv.swap 0 2) hs02 0) ::ₘ
          s(mux (List.ofFn (fun q => (var (![31, 32] q) : Term sig ℕ)) ++ [var 35]),
            gamma (Translation.id sig) ruleK3b (Equiv.swap 0 2) hs02 10) ::ₘ 0) M ∧
      Equiv M N' ∧
      (Translation.id sig).NetTr ((Rule.plug ruleK3 ruleK3b (Equiv.swap 0 2)).inst
        (fun i => .var (![30] i)) (fun j => .var (![31, 32] j)) h) N' := by
  refine mux_gamma_mux_gamma_netTr (Translation.id sig) ruleK3_expanded ruleK3_linear
    ruleK3b_expanded ruleK3b_linear (Equiv.swap 0 2) hs02 0 10 ![30] ![31, 32] 35 ?_
  apply Net.linear_of_forall_mem
  simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.succ_zero_eq_one, Fin.isValue, gamma_k3, gamma_K3b]
  decide

end INet.Comb.PlugTrReview
