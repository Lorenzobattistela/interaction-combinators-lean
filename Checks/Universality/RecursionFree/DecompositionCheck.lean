import InteractionCombinators.Universality.RecursionFree.DecompositionLemmas
import InteractionCombinators.Core.Combinators

/-!
# Checks of `InteractionCombinators/Universality/RecursionFree/Decomposition.lean` on the rules of
the combinators

The canonical decomposition of page 85 (PDF page 17), computed by Lean (`decide`, `rfl`) on three
rules of `Comb.system` and compared with the rules by hand.

Names in a side: `.inl i` is the port `i + 1` of the cell (ports numbered from 1, as in
`BasicCheck.lean`), `.inr (.inl l)` is the middle wire `l`, `.inr (.inr w)` an internal wire.

* `con`–`dup` (`ruleConDup`): `a = dup(w₀, w₁)`, `b = dup(w₂, w₃)`, `c = con(w₀, w₂)`,
  `d = con(w₁, w₃)`, where `a, b` are the ports of the `con` cell and `c, d` those of the `dup`
  cell. Each side keeps its two cells: `φ` is the two `dup` cells, `ψ` the two `con` cells, and
  the four wires `w₀, …, w₃` are the `k = 4` middle wires. `φ` numbers them in the order
  `w₀, w₁, w₂, w₃` (by the port at the root, then by name), `ψ` in the order `w₀, w₂, w₁, w₃`.
  So `σ` sends `0 ↦ 0`, `1 ↦ 2`, `2 ↦ 1`, `3 ↦ 3`: `w₁` is the second wire of `φ` and the third
  of `ψ`. This is the crossing of the two middle wires in the picture of the rule (Fig. 2).
* `con`–`con` (`ruleConCon`): `a = d`, `b = c`. No cell; the two equations between a port of each
  cell are the `k = 2` middle wires. `φ` is `a = 0`, `b = 1` (numbered by the port of `con` at
  their root), `ψ` is `c = 0`, `d = 1` (numbered by the port of the second `con`), and `σ` is the
  exchange: the wire `0` of `φ` (from `a`) is the wire `1` of `ψ` (to `d`).
* `era`–`con` (`ruleEraBin`): `c = ε`, `d = ε`. The eraser has no port, so `φ` is empty, `ψ` is
  the two erasers, and there is no middle wire.
-/

namespace INet.Comb.DecompositionCheck

open Term Rule

/-! ### `con`–`dup` -/

/-- `con`–`dup` has `k = 4` middle wires: the four wires created by the rule. -/
theorem conDup_k : ruleConDup.decompose.k = 4 := by decide

/-- The sides of `con`–`dup` have no internal wire. -/
theorem conDup_internal :
    ruleConDup.decompose.φ.internal = 0 ∧ ruleConDup.decompose.ψ.internal = 0 := by decide

/-- `φ` of `con`–`dup`: the two `dup` cells, on the ports of the `con` cell. -/
theorem conDup_φ : (show Net sig (Fin 2 ⊕ Fin 4 ⊕ Fin 0) from ruleConDup.decompose.φ.net) =
    s(var (.inl 0), mkDup (var (.inr (.inl 0))) (var (.inr (.inl 1)))) ::ₘ
      {s(var (.inl 1), mkDup (var (.inr (.inl 2))) (var (.inr (.inl 3))))} := by
  decide

/-- `ψ` of `con`–`dup`: the two `con` cells, on the ports of the `dup` cell. -/
theorem conDup_ψ : (show Net sig (Fin 2 ⊕ Fin 4 ⊕ Fin 0) from ruleConDup.decompose.ψ.net) =
    s(var (.inl 0), mkCon (var (.inr (.inl 0))) (var (.inr (.inl 1)))) ::ₘ
      {s(var (.inl 1), mkCon (var (.inr (.inl 2))) (var (.inr (.inl 3))))} := by
  decide

/-- `σ` of `con`–`dup` exchanges the middle wires `1` and `2`. -/
theorem conDup_σ :
    (List.finRange ruleConDup.decompose.k).map (fun l => (ruleConDup.decompose.σ l).val) =
      [0, 2, 1, 3] := by
  decide

/-! ### `con`–`con` -/

/-- `con`–`con` has `k = 2` middle wires: its two equations between a port of each cell. -/
theorem conCon_k : ruleConCon.decompose.k = 2 := by decide

/-- `φ` of `con`–`con`: no cell, each port of the first cell on a middle wire. -/
theorem conCon_φ : (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0) from ruleConCon.decompose.φ.net) =
    s(var (.inl 0), var (.inr (.inl 0))) ::ₘ {s(var (.inl 1), var (.inr (.inl 1)))} := by
  decide

/-- `ψ` of `con`–`con`: no cell, each port of the second cell on a middle wire. -/
theorem conCon_ψ : (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0) from ruleConCon.decompose.ψ.net) =
    s(var (.inl 0), var (.inr (.inl 0))) ::ₘ {s(var (.inl 1), var (.inr (.inl 1)))} := by
  decide

/-- `σ` of `con`–`con` is the exchange. -/
theorem conCon_σ :
    (List.finRange ruleConCon.decompose.k).map (fun l => (ruleConCon.decompose.σ l).val) =
      [1, 0] := by
  decide

/-! ### `era`–`con` -/

/-- `era`–`con` has no middle wire. -/
theorem eraBin_k : ruleEraBin.decompose.k = 0 := by decide

/-- `φ` of `era`–`con` is empty: the eraser has no port. -/
theorem eraBin_φ : ruleEraBin.decompose.φ.net = 0 := by decide

/-- `ψ` of `era`–`con` is the two erasers. -/
theorem eraBin_ψ : (show Net sig (Fin 2 ⊕ Fin 0 ⊕ Fin 0) from ruleEraBin.decompose.ψ.net) =
    s(var (.inl 0), mkEra) ::ₘ {s(var (.inl 1), mkEra)} := by
  decide

/-! ### The general results on these rules -/

/-- The cells of `con`–`dup` are split two and two, as `decompose_cells_left` says. -/
theorem conDup_cells : ruleConDup.decompose.φ.net.cells = {Comb.dup, Comb.dup} ∧
    ruleConDup.decompose.ψ.net.cells = {Comb.con, Comb.con} := by
  decide

/-- Plugging the decomposition of `con`–`dup` gives back the rule (`plug_decompose`). -/
theorem conDup_plug : ∃ ι : Fin ruleConDup.internal →
    Fin (Rule.plug ruleConDup.decompose.φ ruleConDup.decompose.ψ ruleConDup.decompose.σ).internal,
    Function.Injective ι ∧
      Equiv (Rule.plug ruleConDup.decompose.φ ruleConDup.decompose.ψ ruleConDup.decompose.σ).net
        (ruleConDup.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) :=
  ruleConDup.plug_decompose ruleConDup_linear

end INet.Comb.DecompositionCheck
