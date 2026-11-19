import InteractionCombinators.Lafont.SimulationStrict
import InteractionCombinators.Combinators

/-!
# Checks of `L > 0` for a strict translation (page 81)

The hypotheses of `Translation.CompatibleWithin.pos` hold for the identity translation of the
combinators: it is strict, the combinators are well-formed, and it is compatible within `1` and
`1`, hence within `0` and `1`. From the bound `0`, `pos` gives back the bound `1`. The
hypotheses of `Translation.not_equiv_pair_of_strict` hold for the `con`–`con` rule with the
names `0, 1` and `2, 3`.
-/

namespace INet.SimulationStrictCheck

open Term Comb

/-- The identity translation is strict: every symbol is translated to a cell (Lafont 1997,
page 80). -/
theorem id_strict (S : Signature) : (Translation.id S).Strict := fun _ _ h => by
  cases h

/-- A translation compatible within `L` and `M` is compatible within any smaller `L`
(Lafont 1997, page 81). -/
theorem compatibleWithin_mono {S S' : Signature} {Φ : Translation S S'} {I : System S}
    {I' : System S'} {L L' M : ℕ} (hL : L' ≤ L) (h : Φ.CompatibleWithin I I' L M) :
    Φ.CompatibleWithin I I' L' M := by
  intro α β r hr xs ys f g hl
  obtain ⟨M₁, N', h₁, ⟨k, hk, hM, hs⟩, hE, hT⟩ := h α β r hr xs ys f g hl
  exact ⟨M₁, N', h₁, ⟨k, hL.trans hk, hM, hs⟩, hE, hT⟩

/-- The identity translation of the combinators, compatible within `0` and `1`, is compatible
within `1` and `1` by `pos` (Lafont 1997, page 81): the hypotheses of `pos` can hold. -/
example : (Translation.id sig).CompatibleWithin system system 1 1 :=
  (compatibleWithin_mono (Nat.zero_le 1)
    (Translation.id_compatibleWithin system system_wellFormed)).pos (id_strict sig)
    system_wellFormed system_wellFormed.linear

/-- The `con`–`con` pair with the names `0, 1` and `2, 3` is not the same graph as a translation
of its right member (Lafont 1997, page 81): the hypotheses of `not_equiv_pair_of_strict` can
hold. -/
example {r : Rule sig (sig.arity Comb.con) (sig.arity Comb.con)}
    (hr : system.rule Comb.con Comb.con = some r) {h : Fin r.internal → ℕ} {N' : Net sig ℕ}
    (hT : (Translation.id sig).NetTr
      (r.inst (fun i => .var (i : ℕ)) (fun j => .var (sig.arity Comb.con + j)) h) N') :
    ¬ Equiv (s(((Translation.id sig).net Comb.con).inst (fun i => .var (i : ℕ)) Fin.elim0,
      ((Translation.id sig).net Comb.con).inst (fun j => .var (sig.arity Comb.con + j))
        Fin.elim0) ::ₘ (0 : Net sig ℕ)) N' :=
  Translation.not_equiv_pair_of_strict (id_strict sig) system_wellFormed hr
    (fun a b e => Fin.ext e) (fun a b e => Fin.ext (Nat.add_left_cancel e))
    (fun a b e => by have := a.isLt; omega) Fin.elim0 Fin.elim0 hT

end INet.SimulationStrictCheck
