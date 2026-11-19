import Checks.Universality.RecursionFree.PlugTermTrCheck
import Checks.Universality.RecursionFree.PlugTrReview
import InteractionCombinators.Universality.General.CodeGammaMeet

/-!
# Review of `plugTermTarget` and `netTr_plug_termTr` (`PlugTermTr.lean`), pages 85–86 and 90

Lafont 1997, Section 2.4, journal pages 85–86 (PDF pages 17–18: the plugged rule and the end of
Fig. 7) and page 90 (Fig. 10, where the same argument is "left to the reader"). Review of
`Lafont/PlugTermTr.lean` (issue #190). `PlugTermTrCheck` already applies `netTr_plug_termTr` with
`σ = swap 0 1`, trees renamed away from `gammaPort`, and `hlin` proved; this file adds what that
check cannot see.

## Against the paper

* **The direction of `σ`.** `plugTermTarget σ` puts the tree of `φ` at the middle port `l` against
  the tree of `ψ` at the middle port `σ l`, as `plugTarget` does (reviewed in `PlugTrReview`), and
  `Rule.plug φ ψ σ` names the middle wire `l` of `ψ` as the middle wire `σ⁻¹ l` of `φ`. The two
  agree for every permutation. A swap cannot tell `σ` from `σ⁻¹`, so the check below uses the
  3-cycle `rot3`: `rot_termTarget` computes the net with the trees of `Φrev`, and its middle
  equations pair the wires as `PlugTrReview.rot_plug_net` does (`w₀` of `φ` with `w₂` of `ψ`,
  `con(w₂, w₂)` with `w₁`, `w₁` with `w₀`). `rot_termNetTr` applies `netTr_plug_termTr` to it with
  every hypothesis proved. With `rot3⁻¹` in its place the net is a different one
  (`rot_termTarget_symm_ne`): there the tree `con(…)` of `φ` meets the left leaf `10` of the
  `con` of `ψ`, not the right leaf `11`, and the trees of a `con` cell are ordered. So the
  direction matters, and the code takes the same one in both places.
* **The convention of the next step.** `codeCells_meet_end` (`CodeGammaMeet.lean`) ends with
  `s(codePort φ … (.inr l), codePort ψ … (.inr (σ l)))`, the same `σ` as in `side α β` and
  `side β α`. That is exactly `plugTermTarget σ (codePort φ …) (codePort ψ …) xs ys`, with `xs`
  on `φ` and `ys` on `ψ`: `codeCells_meet_end_linear` states it, by `rfl` on the shape. There `σ`
  is involutive, so the order `φ`, `ψ` is also free (`Fig7EndReview.middle_symm`). Page 85 gives
  `φ_{j,i} = ψ_{i,j}` and `σ_{j,i} = σ_{i,j}⁻¹`, and then makes every `σ_{i,j}` involutive (for
  `i ≠ j` by moving the permutation into `φ_{i,j}`). So one involution for both sides, as in
  `codeCells_meet_end`, is the paper's convention.

## The hypotheses

* `hφ`, `hψ`, `hφe`, `hφl`, `hψe`, `hψl` are what the paper assumes (sides in expanded form,
  translated trees).
* **`hlin` is not implied by the others.** `TermTr` lets the new wires of an instance take any
  names, so two trees can share them. `clash_not_linear`: the trees of `ψ` take the new wire `51`
  that the tree of `φ` at the middle port `1` already uses, and `51` occurs four times. Every
  other hypothesis holds (`clash_termTr`). `clash_no_translation`: the conclusion is then false,
  since a translation is linear and `Equiv` keeps linearity. So `hlin` is needed.
* **The next step provides `hlin`.** `codeCells_meet_end_linear`: from the hypothesis of
  `codeCells_meet_end` alone, the `plugTermTarget` of its final net is linear. The proof is
  `StepsE.linear`, `Equiv.linear`, and that a summand of a linear net is linear. #188 has to
  prove `hφ`, `hψ` for the trees `codePort`; `hlin` comes for free.

## Not checked

* That the trees `codePort` translate `gammaTree` (the subject of #188).
* `k = 0` and the fresh names `B + l` are not checked again here (`PlugTrReview.k0_netTr` covers
  them for `plugTarget`, and the proof of `netTr_plug_termTr` is the same).
-/

namespace INet.Comb.PlugTermTrReview

open Term Rule Translation ExpandTrReview GammaReview Fig7EndReview PlugTrReview

/-! ## A non-involutive `σ` with trees that are not `gammaPort` -/

/-- The trees of `ruleK3` with internal wires from `0` (page 86). -/
theorem gammaTree_K3 :
    gammaTree ruleK3 0 (.inl 0) = mkDup (var 0) (var 1) ∧ gammaTree ruleK3 0 (.inr 0) = var 0 ∧
      gammaTree ruleK3 0 (.inr 1) = mkCon (var 2) (var 2) ∧
      gammaTree ruleK3 0 (.inr 2) = var 1 := by
  simpa only [gammaPort, trTerm_id] using gammaPort_K3

/-- The trees of `ruleK3b` with internal wires from `10` (page 86). -/
theorem gammaTree_K3b :
    gammaTree ruleK3b 10 (.inl 0) = mkCon (var 10) (var 11) ∧
      gammaTree ruleK3b 10 (.inl 1) = var 12 ∧ gammaTree ruleK3b 10 (.inr 0) = var 10 ∧
      gammaTree ruleK3b 10 (.inr 1) = var 12 ∧ gammaTree ruleK3b 10 (.inr 2) = var 11 := by
  simpa only [gammaPort, trTerm_id] using gammaPort_K3b

/-- The trees of `φ = ruleK3`: the translations by `Φrev` of its trees from `0`, with the new
wire `50 + l` at the middle port `l`. -/
noncomputable def tφ : Fin 1 ⊕ Fin 3 → Term sig ℕ :=
  fun p => Φrev.trTerm (50 + Sum.elim (fun _ => 0) (fun l : Fin 3 => (l : ℕ)) p)
    (gammaTree ruleK3 0 p)

/-- The trees of `ψ = ruleK3b`: from `10`, the new wire `60 + q` at the port `q`. -/
noncomputable def tψ : Fin 2 ⊕ Fin 3 → Term sig ℕ :=
  fun p => Φrev.trTerm (60 + Sum.elim (fun q : Fin 2 => (q : ℕ)) (fun _ => 0) p)
    (gammaTree ruleK3b 10 p)

/-- The trees `tφ`, written out: only the `con` at the middle port `1` gets a new wire, `51`. -/
theorem tφ_eq :
    tφ (.inl 0) = mkDup (var 0) (var 1) ∧ tφ (.inr 0) = var 0 ∧
      tφ (.inr 1) = mkCon (mkCon (var 2) (var 51)) (mkCon (var 51) (var 2)) ∧
      tφ (.inr 2) = var 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := gammaTree_K3
  simp only [tφ, h0, h1, h2, h3, Sum.elim_inl, Sum.elim_inr]
  decide

/-- The trees `tψ`, written out: only the `con` at the port `0` gets a new wire, `60`. -/
theorem tψ_eq :
    tψ (.inl 0) = mkCon (mkCon (var 11) (var 60)) (mkCon (var 60) (var 10)) ∧
      tψ (.inl 1) = var 12 ∧ tψ (.inr 0) = var 10 ∧ tψ (.inr 1) = var 12 ∧
      tψ (.inr 2) = var 11 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := gammaTree_K3b
  simp only [tψ, h0, h1, h2, h3, h4, Sum.elim_inl, Sum.elim_inr]
  decide

/-- **`plugTermTarget` for the 3-cycle** (Fig. 7, end, page 86), `xs = ![30]`, `ys = ![31, 32]`.
The middle port `l` of `φ` meets the middle port `rot3 l` of `ψ`: `0 = 12`, `con(…2…) = 11`,
`1 = 10`, the pairing of `PlugTrReview.rot_plug_net`. -/
theorem rot_termTarget :
    plugTermTarget rot3 tφ tψ ![30] ![31, 32] =
      (s(var 30, mkDup (var 0) (var 1)) ::ₘ
        s(var 31, mkCon (mkCon (var 11) (var 60)) (mkCon (var 60) (var 10))) ::ₘ
        s(var 32, var 12) ::ₘ s(var 0, var 12) ::ₘ
        s(mkCon (mkCon (var 2) (var 51)) (mkCon (var 51) (var 2)), var 11) ::ₘ
        {s(var 1, var 10)} : CNet) := by
  obtain ⟨a0, a1, a2, a3⟩ := tφ_eq
  obtain ⟨b0, b1, b2, b3, b4⟩ := tψ_eq
  have e0 : rot3 0 = 1 := rfl
  have e1 : rot3 1 = 2 := rfl
  have e2 : rot3 2 = 0 := rfl
  simp only [plugTermTarget, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero,
    Fin.succ_zero_eq_one, Fin.isValue, Fin.succ_one_eq_two, e0, e1, e2, a0, a1, a2, a3, b0, b1,
    b2, b3, b4, Matrix.cons_val_zero, Matrix.cons_val_one]
  decide

/-- The hypothesis `hlin` of `netTr_plug_termTr` holds for the 3-cycle instance (page 86). -/
theorem rot_termTarget_linear : Net.Linear (plugTermTarget rot3 tφ tψ ![30] ![31, 32]) := by
  rw [rot_termTarget]
  apply Net.linear_of_forall_mem
  decide

/-- **`netTr_plug_termTr` for a non-involutive `σ`** (pages 85–86, 90): with the 3-cycle `rot3`,
the translation `Φrev` and trees whose new wires are chosen by hand, every hypothesis is proved
and the net of `rot_termTarget` is a translation of an instance of `Rule.plug ruleK3 ruleK3b rot3`
(the net of `PlugTrReview.rot_plug_net`). -/
theorem rot_termNetTr :
    ∃ (h : Fin (Rule.plug ruleK3 ruleK3b rot3).internal → ℕ) (N' : CNet),
      Φrev.NetTr ((Rule.plug ruleK3 ruleK3b rot3).inst
        (fun i => .var (![30] i)) (fun j => .var (![31, 32] j)) h) N' ∧
      Equiv N' (s(var 30, mkDup (var 0) (var 1)) ::ₘ
        s(var 31, mkCon (mkCon (var 11) (var 60)) (mkCon (var 60) (var 10))) ::ₘ
        s(var 32, var 12) ::ₘ s(var 0, var 12) ::ₘ
        s(mkCon (mkCon (var 2) (var 51)) (mkCon (var 51) (var 2)), var 11) ::ₘ
        {s(var 1, var 10)}) := by
  rw [← rot_termTarget]
  exact netTr_plug_termTr Φrev ruleK3_expanded ruleK3_linear ruleK3b_expanded ruleK3b_linear
    rot3 0 10 tφ tψ (fun p => Φrev.termTr_trTerm _ _) (fun q => Φrev.termTr_trTerm _ _) _ _
    rot_termTarget_linear

/-- **The direction of `σ` matters** (page 85): with `rot3⁻¹` the tree `con(…2…)` of `φ` at the
middle port `1` meets `tψ (.inr 0) = 10`, the left leaf of the `con` of `ψ`, instead of the right
leaf `11`. -/
theorem rot_termTarget_symm_ne :
    plugTermTarget rot3.symm tφ tψ ![30] ![31, 32] ≠ plugTermTarget rot3 tφ tψ ![30] ![31, 32] := by
  rw [rot_termTarget]
  obtain ⟨a0, a1, a2, a3⟩ := tφ_eq
  obtain ⟨b0, b1, b2, b3, b4⟩ := tψ_eq
  have e0 : rot3.symm 0 = 2 := rfl
  have e1 : rot3.symm 1 = 0 := rfl
  have e2 : rot3.symm 2 = 1 := rfl
  simp only [plugTermTarget, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero,
    Fin.succ_zero_eq_one, Fin.isValue, Fin.succ_one_eq_two, e0, e1, e2, a0, a1, a2, a3, b0, b1,
    b2, b3, b4, Matrix.cons_val_zero, Matrix.cons_val_one]
  decide

/-! ## `hlin` is needed: two trees may share their new wires -/

/-- The trees of `ψ` with the new wire `51`, the one the tree of `φ` uses at its middle port `1`. -/
noncomputable def tψClash : Fin 2 ⊕ Fin 3 → Term sig ℕ :=
  fun p => Φrev.trTerm 51 (gammaTree ruleK3b 10 p)

/-- The trees `tψClash` are translations of the trees of `ruleK3b`: the hypothesis `hψ` holds. -/
theorem clash_termTr : ∀ q, Φrev.TermTr (gammaTree ruleK3b 10 q) (tψClash q) :=
  fun _ => Φrev.termTr_trTerm _ _

/-- **`hlin` is not implied by the other hypotheses** (page 86): the names `xs`, `ys` are distinct
and the sides are linear and expanded, but `51` occurs four times. -/
theorem clash_not_linear : ¬ Net.Linear (plugTermTarget rot3 tφ tψClash ![30] ![31, 32]) := by
  intro h
  have h51 := h 51
  obtain ⟨a0, a1, a2, a3⟩ := tφ_eq
  obtain ⟨b0, b1, b2, b3, b4⟩ := gammaTree_K3b
  have e0 : rot3 0 = 1 := rfl
  have e1 : rot3 1 = 2 := rfl
  have e2 : rot3 2 = 0 := rfl
  simp only [plugTermTarget, tψClash, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero,
    Fin.succ_zero_eq_one, Fin.isValue, Fin.succ_one_eq_two, e0, e1, e2, a0, a1, a2, a3, b0, b1,
    b2, b3, b4, Matrix.cons_val_zero, Matrix.cons_val_one] at h51
  revert h51
  decide

/-- **Without `hlin` the conclusion of `netTr_plug_termTr` is false** (page 86). -/
theorem clash_no_translation :
    ¬ ∃ (h : Fin (Rule.plug ruleK3 ruleK3b rot3).internal → ℕ) (N' : CNet),
      Φrev.NetTr ((Rule.plug ruleK3 ruleK3b rot3).inst
        (fun i => .var (![30] i)) (fun j => .var (![31, 32] j)) h) N' ∧
      Equiv N' (plugTermTarget rot3 tφ tψClash ![30] ![31, 32]) :=
  fun ⟨_, _, hN, hE⟩ => clash_not_linear (hE.linear hN.linear)

/-! ## The next step provides `hlin` -/

/-- A summand of a linear net is linear. -/
theorem linear_of_cons_cons_add {e₁ e₂ : Sym2 (Term sig ℕ)} {P Δ : CNet}
    (h : Net.Linear (e₁ ::ₘ e₂ ::ₘ (P + Δ))) : P.Linear := fun x => by
  have := h x
  simp only [Net.vars_cons, Net.vars_add, Multiset.count_add] at this
  omega

variable {S : Signature} [Finite S.Sym] (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **The end of Fig. 10 gives the hypothesis `hlin` of `netTr_plug_termTr`** (Lafont 1997,
pages 89–90): under the hypotheses of `codeCells_meet_end`, the net `plugTermTarget σ` of the
trees `codePort` of `⟨φ⟩` and `⟨ψ⟩` (with `xs` on `φ`, `ys` on `ψ`, the same `σ`) is linear, for
the bounds `K`, `K'` that `codeCells_meet_end` produces. Its final net is that net plus the two
copier equations and the context. -/
theorem codeCells_meet_end_linear (α β : S.Sym) (xs : Fin (S.arity α) → ℕ)
    (ys : Fin (S.arity β) → ℕ) (f : Fin (codeNet side α).internal → ℕ)
    (g : Fin (codeNet side β).internal → ℕ) (Δ : CNet)
    {k : ℕ} (φ : Rule S (S.arity α) k) (ψ : Rule S (S.arity β) k) (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ) (hl : φ.Linear) (he : φ.Expanded) (hl' : ψ.Linear)
    (he' : ψ.Expanded) (hs : side α β = some ⟨k, φ, σ, hl, he, hσ⟩)
    (hs' : side β α = some ⟨k, ψ, σ, hl', he', hσ⟩)
    (hlin : Net.Linear (s((codeNet side α).inst (fun i => var (xs i)) f,
      (codeNet side β).inst (fun j => var (ys j)) g) ::ₘ Δ)) :
    ∃ K K' : ℕ, Net.Linear (plugTermTarget σ
      (codePort (Nat.card S.Sym) (fun γ => symEnum S γ) φ
        (K' + (S.arity β + 1 + off (codeCellSizes side β) (symEnum S α))))
      (codePort (Nat.card S.Sym) (fun γ => symEnum S γ) ψ
        (K + (S.arity α + 1 + off (codeCellSizes side α) (symEnum S β)))) xs ys) := by
  obtain ⟨K, K', M, hS, hE⟩ := codeCells_meet_end side α β xs ys f g Δ φ ψ σ hσ hl he hl' he' hs
    hs' hlin
  refine ⟨K, K', ?_⟩
  have L := hE.linear (hS.linear system_wellFormed.linear hlin)
  unfold plugTermTarget
  exact linear_of_cons_cons_add L

end INet.Comb.PlugTermTrReview
