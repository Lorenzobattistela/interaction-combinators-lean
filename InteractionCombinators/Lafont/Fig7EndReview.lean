import InteractionCombinators.Lafont.Fig7EndCheck
import InteractionCombinators.Lafont.GammaReview

/-!
# Review of the end of Fig. 7 (`Fig7End.lean`) against rows 3 and 4 of Fig. 7 (page 86)

Lafont 1997, Section 2.4, Fig. 7, journal page 86 (PDF page 18). Review of `Lafont/Fig7End.lean`
(issue #110).

## Against the figure

* Row 3 (right): `M_{nᵢ+1}` of `[αᵢ]`, root down, faces `M*_{nᵢ+1}` of `Γ_{i,j}`, root up. The
  leaves of `M` are, left to right, the auxiliary ports of `αᵢ` and then, on the right, the loop;
  the leaves of `M*` are, left to right, the top ports of `[φ_{i,j}]` and then, on the right, the
  root of `T_{σ_{i,j}}`. `mux_muxStar` pairs leaves by position, so port `p` of `αᵢ` meets the port
  `p` of `[φ_{i,j}]`: in `mux_gamma_loop` the tree `ts[p]` meets `gammaPort … (.inl p)`. No
  reversal and no shift: `k3_reached` below has `a = 1`, `b = 2`, and the ports land at `.inl 0`,
  resp. `.inl 0`, `.inl 1`, in order.
* The loop is the last leaf of each `M_{n+1}` (`mux (ts ++ [var ℓ])`) and meets the last leaf of
  `M*`, the root of `T_σ` (`mux_gamma_loop`). The two loops of row 3 are one wire, which in row 4
  joins the roots of the two `T_σ`.
* Row 4: the two `T_σ` annihilate into the box `σ_{i,j}` between the bottom ports of `[φ_{i,j}]` and
  `[φ_{j,i}]`. The statement joins the middle port `l` of the first to the middle port `σ l` of the
  second, which is `Rule.plug` (`GammaReview.plugR_middle`). Both packages carry the same `σ`, as on
  page 86 (`σ_{j,i} = σ_{i,j}`) and in the translation (`RecursionFreeTrReview.rawSide_pair`). Since
  `σ` is involutive, `l ↔ σ l` is the same relation as `σ l ↔ l`: which side `σ` is drawn on does not
  matter (`middle_symm` below states this on the conclusion).

## Refutation attempts

* `k3_reached`: `k = 3`, `σ = swap 0 2`, `a = 1 ≠ b = 2`, a context `Δ` of one equation that uses a
  free port of the cells, every hypothesis proved, and the reached net computed: the middle ports
  `0, 1, 2` of `φ` meet the middle ports `2, 1, 0` of `ψ`.
* The dropped hypotheses (`Expanded`, `Linear` on `φ`, `ψ`): `wire_reached` applies the theorem to
  the side `ruleWire` (`a₀ = b₀`, not expanded) on both cells, with `hlin` proved. So `hlin` does
  not force the sides to be expanded, and the theorem is not vacuous there. It is still correct
  there, because it is a statement about the trees `gammaPort`, whatever they are. When a side is
  not expanded, a port leaf of `φ` is renamed `k₀` (`gammaName`); if two port leaves occur, the
  name `k₀` occurs four times and `hlin` fails, so such instances are excluded by `hlin` and not by
  a wrong conclusion.

## Fitness for the next step

The conclusion has the shape of `Rule.plug φ ψ σ`: the trees of the cell with menu `Gi` (the one
that selects `Gj[i] = Γ` of `φ`, `a` ports) meet the trees of `[φ]` at `.inl p`, those of the other
cell meet the trees of `[ψ]` at `.inl q`, and the middle trees are joined `φ l = ψ (σ l)`, which is
`plugL (.inr (.inl l)) = plugR σ (.inr (.inl (σ l)))`. This was confirmed while the review was
written: `Lafont/PlugTr.lean` (merged meanwhile) takes this conclusion as it is
(`mux_gamma_mux_gamma_ofFn`, `plugTarget`) and proves it `Equiv` to a translation of an instance of
`Rule.plug φ ψ σ` (`netTr_plug_gamma`), for linear expanded sides. What remains after that, and is
not a defect of the statement:

* `[ψ]` here is the expanded side `D.side β α`, chosen by `Rule.exists_expanded` separately for each
  side; relating `plug` of the expanded sides to `plug` of `D.dec`, and that to the rule, goes
  through `RawSide.expand_spec` and `Decomposition.Plugs`.
* The middle equations are between two translated trees; in `[plug φ ψ σ]` the middle wire is an
  internal wire between them, so the two agree up to `Equiv` (a contraction).

In the translation, `RecursionFreeData.ne` makes `σ = 1` when `α ≠ β`, and `self` makes `φ = ψ`
when `α = β`; so the instance `k3_reached` (`σ ≠ 1`, `φ ≠ ψ`) does not arise from a translation. It
tests the theorem, which is stated for all `φ`, `ψ`, `σ`.
-/

namespace INet.Comb.Fig7EndReview

open Term Rule Translation DecompositionReview ExpandedIso ExpandTrReview GammaCheck GammaReview
  Fig7EndCheck

/-! ## The direction of `σ` -/

/-- The middle equations of the conclusion of `mux_gamma_mux_gamma` (Fig. 7, row 4, page 86) are
the same whether `σ` is put on the side of `ψ` or of `φ`, since `σ` is involutive. -/
theorem middle_symm {k : ℕ} (σ : Equiv.Perm (Fin k)) (hσ : Function.Involutive σ)
    (f g : Fin k → Term sig ℕ) :
    (Finset.univ.val.map fun l : Fin k => s(f l, g (σ l))) =
      Finset.univ.val.map fun l : Fin k => s(f (σ l), g l) := by
  have e : (Finset.univ.val.map fun l : Fin k => s(f l, g (σ l))) =
      (Finset.univ.val.map σ).map fun l : Fin k => s(f l, g (σ l)) := by
    rw [Multiset.map_univ_val_equiv]
  rw [e, Multiset.map_map]
  congr 1
  funext l
  simp [hσ l]

/-! ## `k = 3`, `σ = swap 0 2`, `a = 1`, `b = 2`, a context -/

/-- `a = 2`, `k = 3`: `a₀ = con(w₀, w₁)`, `a₁ = w₂`, `b₀ = w₀`, `b₁ = w₂`, `b₂ = w₁`. -/
abbrev ruleK3b : Rule sig 2 3 :=
  ⟨3, s(pl 0, mkCon (pw 0) (pw 1)) ::ₘ s(pl 1, pw 2) ::ₘ s(pr 0, pw 0) ::ₘ s(pr 1, pw 2) ::ₘ
    {s(pr 2, pw 1)}⟩

theorem ruleK3b_linear : ruleK3b.Linear := ⟨by decide, by decide, by decide⟩

theorem ruleK3b_expanded : ruleK3b.Expanded := by
  intro e he
  have key : ∀ e ∈ (show Net sig (Fin 2 ⊕ Fin 3 ⊕ Fin 3) from ruleK3b.net),
      e ∈ [s(pl 0, mkCon (pw 0) (pw 1)), s(pl 1, pw 2), s(pr 0, pw 0), s(pr 1, pw 2),
        s(pr 2, pw 1)] := by decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl, fun w h => (by cases h), by decide⟩

/-- `swap 0 2` on `Fin 3` is an involution. -/
theorem hs02 : Function.Involutive (Equiv.swap (0 : Fin 3) 2) := Equiv.swap_apply_self 0 2

/-- The trees of `[ruleK3]` (`a = 1`), names from `0`, identity translation. -/
theorem gammaPort_K3 :
    gammaPort (Translation.id sig) ruleK3 0 (.inl 0) = mkDup (var 0) (var 1) ∧
      gammaPort (Translation.id sig) ruleK3 0 (.inr 0) = var 0 ∧
      gammaPort (Translation.id sig) ruleK3 0 (.inr 1) = mkCon (var 2) (var 2) ∧
      gammaPort (Translation.id sig) ruleK3 0 (.inr 2) = var 1 := by
  have h0 : ruleK3.portTree (.inl 0) = (mkDup (pw 0) (pw 1) : Term sig (Fin 1 ⊕ Fin 3 ⊕ Fin 3)) :=
    portTree_eq ruleK3_expanded ruleK3_linear (by decide)
  have h1 : ruleK3.portTree (.inr 0) = (pw 0 : Term sig (Fin 1 ⊕ Fin 3 ⊕ Fin 3)) :=
    portTree_eq ruleK3_expanded ruleK3_linear (by decide)
  have h2 : ruleK3.portTree (.inr 1) =
      (mkCon (pw 2) (pw 2) : Term sig (Fin 1 ⊕ Fin 3 ⊕ Fin 3)) :=
    portTree_eq ruleK3_expanded ruleK3_linear (by decide)
  have h3 : ruleK3.portTree (.inr 2) = (pw 1 : Term sig (Fin 1 ⊕ Fin 3 ⊕ Fin 3)) :=
    portTree_eq ruleK3_expanded ruleK3_linear (by decide)
  simp only [gammaPort, trTerm_id, gammaTree, h0, h1, h2, h3]
  exact ⟨by decide, rfl, by decide, rfl⟩

/-- The trees of `[ruleK3b]` (`a = 2`), names from `10`, identity translation. -/
theorem gammaPort_K3b :
    gammaPort (Translation.id sig) ruleK3b 10 (.inl 0) = mkCon (var 10) (var 11) ∧
      gammaPort (Translation.id sig) ruleK3b 10 (.inl 1) = var 12 ∧
      gammaPort (Translation.id sig) ruleK3b 10 (.inr 0) = var 10 ∧
      gammaPort (Translation.id sig) ruleK3b 10 (.inr 1) = var 12 ∧
      gammaPort (Translation.id sig) ruleK3b 10 (.inr 2) = var 11 := by
  have h0 : ruleK3b.portTree (.inl 0) =
      (mkCon (pw 0) (pw 1) : Term sig (Fin 2 ⊕ Fin 3 ⊕ Fin 3)) :=
    portTree_eq ruleK3b_expanded ruleK3b_linear (by decide)
  have h1 : ruleK3b.portTree (.inl 1) = (pw 2 : Term sig (Fin 2 ⊕ Fin 3 ⊕ Fin 3)) :=
    portTree_eq ruleK3b_expanded ruleK3b_linear (by decide)
  have h2 : ruleK3b.portTree (.inr 0) = (pw 0 : Term sig (Fin 2 ⊕ Fin 3 ⊕ Fin 3)) :=
    portTree_eq ruleK3b_expanded ruleK3b_linear (by decide)
  have h3 : ruleK3b.portTree (.inr 1) = (pw 2 : Term sig (Fin 2 ⊕ Fin 3 ⊕ Fin 3)) :=
    portTree_eq ruleK3b_expanded ruleK3b_linear (by decide)
  have h4 : ruleK3b.portTree (.inr 2) = (pw 1 : Term sig (Fin 2 ⊕ Fin 3 ⊕ Fin 3)) :=
    portTree_eq ruleK3b_expanded ruleK3b_linear (by decide)
  simp only [gammaPort, trTerm_id, gammaTree, h0, h1, h2, h3, h4]
  exact ⟨by decide, rfl, rfl, rfl, rfl⟩

/-- `Γ` of `ruleK3b` from `10`, `σ = swap 0 2`: `M*_3(con(10, 11), 12, dup(con(10, 11), 12))`. -/
theorem gamma_K3b :
    gamma (Translation.id sig) ruleK3b (Equiv.swap 0 2) hs02 10 =
      mkCon (mkCon (mkDup (mkCon (var 10) (var 11)) (var 12)) (var 12))
        (mkCon (var 10) (var 11)) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := gammaPort_K3b
  unfold gamma; rw [transpositorPerm_swap02]
  simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, Fin.isValue, h0, h1, h2, h3, h4]
  decide

/-- The net of rows 3–4 of Fig. 7 for this instance: `M_2(30, 35)` against `Γ` of `ruleK3`,
`M_3(31, 32, 35)` against `Γ` of `ruleK3b`, and the context `30 = con(33, 34)`. -/
noncomputable abbrev NK3 : CNet :=
  s(mux ([var 30] ++ [var 35]), gamma (Translation.id sig) ruleK3 (Equiv.swap 0 2) hs02 0) ::ₘ
    s(mux ([var 31, var 32] ++ [var 35]),
      gamma (Translation.id sig) ruleK3b (Equiv.swap 0 2) hs02 10) ::ₘ
    {s(var 30, mkCon (var 33) (var 34))}

theorem NK3_linear : Net.Linear NK3 := by
  apply linear_of_forall_mem
  rw [NK3, gamma_k3, gamma_K3b]
  decide

/-- **`mux_gamma_mux_gamma` with `k = 3`, `σ = swap 0 2`, `a = 1`, `b = 2` and a context**
(Fig. 7, rows 3–4, page 86): the hypothesis holds, and the net reached is
`30 = dup(0, 1)`, `31 = con(10, 11)`, `32 = 12`, the middle ports `0 ↔ 2`, `1 ↔ 1`, `2 ↔ 0`
(`0 = 11`, `con(2, 2) = 12`, `1 = 10`), and the context `30 = con(33, 34)`. -/
theorem k3_reached :
    ∃ M, StepsE system NK3 M ∧
      Equiv M (s(var 30, mkDup (var 0) (var 1)) ::ₘ s(var 31, mkCon (var 10) (var 11)) ::ₘ
        s(var 32, var 12) ::ₘ s(var 0, var 11) ::ₘ s(mkCon (var 2) (var 2), var 12) ::ₘ
        s(var 1, var 10) ::ₘ {s(var 30, mkCon (var 33) (var 34))}) := by
  obtain ⟨M, hS, hE⟩ := mux_gamma_mux_gamma (Translation.id sig) ruleK3 ruleK3b (Equiv.swap 0 2)
    hs02 0 10 [var 30] [var 31, var 32] rfl rfl 35 _ NK3_linear
  refine ⟨M, hS, hE.trans (Equiv.of_eq ?_)⟩
  obtain ⟨a0, a1, a2, a3⟩ := gammaPort_K3
  obtain ⟨b0, b1, b2, b3, b4⟩ := gammaPort_K3b
  have e0 : Equiv.swap (0 : Fin 3) 2 0 = 2 := rfl
  have e1 : Equiv.swap (0 : Fin 3) 2 1 = 1 := rfl
  have e2 : Equiv.swap (0 : Fin 3) 2 2 = 0 := rfl
  simp only [Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, Fin.isValue,
    Fin.succ_one_eq_two, e0, e1, e2, a0, a1, a2, a3, b0, b1, b2, b3, b4]
  decide

/-! ## The dropped hypotheses: a side that is not expanded -/

/-- Two cells whose packages are `Γ` of the non-expanded side `ruleWire` (`a₀ = b₀`), names from
`10` and `20`, `σ = 1`, trees `0` and `1`, loop `5`. -/
noncomputable abbrev NW : CNet :=
  s(mux ([var 0] ++ [var 5]), gamma (Translation.id sig) ruleWire 1 (hid 1) 10) ::ₘ
    s(mux ([var 1] ++ [var 5]), gamma (Translation.id sig) ruleWire 1 (hid 1) 20) ::ₘ 0

theorem NW_linear : Net.Linear NW := by
  apply linear_of_forall_mem
  rw [NW, gamma_wire, gamma_wire]
  decide

/-- **`hlin` holds for sides that are not expanded** (Fig. 7, page 86): `mux_gamma_mux_gamma`
applies to `ruleWire` on both cells, and gives `0 = 10`, `1 = 20`, `10 = 20`, that is the wire
`0 = 1` of `plug ruleWire ruleWire 1` up to contraction. -/
theorem wire_reached :
    ∃ M, StepsE system NW M ∧
      Equiv M (s(var 0, var 10) ::ₘ s(var 1, var 20) ::ₘ {s(var 10, var 20)}) := by
  obtain ⟨M, hS, hE⟩ := mux_gamma_mux_gamma (Translation.id sig) ruleWire ruleWire 1 (hid 1)
    10 20 [var 0] [var 1] rfl rfl 5 0 NW_linear
  refine ⟨M, hS, hE.trans (Equiv.of_eq ?_)⟩
  have h0 : ruleWire.portTree (.inl 0) = pr 0 :=
    portTree_of_unique (Multiset.mem_singleton_self _) fun t' h => by
      rcases Sym2.eq_iff.1 (Multiset.mem_singleton.1 h) with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · cases h
  have h1 : ruleWire.portTree (.inr 0) = pl 0 :=
    portTree_of_unique (by
      show s(pr 0, _) ∈ ({s(pl 0, pr 0)} : Multiset _)
      rw [Sym2.eq_swap]; exact Multiset.mem_singleton_self _) fun t' h => by
      rcases Sym2.eq_iff.1 (Multiset.mem_singleton.1 h) with ⟨h, -⟩ | ⟨-, h⟩
      · cases h
      · exact h
  simp only [Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Fin.isValue, gammaPort, trTerm_id,
    gammaTree, h0, h1, Equiv.Perm.coe_one, id]
  decide

end INet.Comb.Fig7EndReview
