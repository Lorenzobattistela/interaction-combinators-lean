import InteractionCombinators.Lafont.Transpositor

/-!
# Checks of `Lafont/Transpositor.lean` against the paper

A review (issue 38) compared `pairCon`, `transpositor`, `swapPairs` and `transpositor_transpositor`
with Lafont 1997, page 83 (PDF page 15): the picture of the property of `T_{p,q}` and the picture
of its implementation. This file records the cases worked by hand as statements that Lean checks.

Ports are numbered as in `BasicCheck.lean` and `AutoMuxCheck.lean`: on a cell drawn with its
principal port down, the left auxiliary port is 1 and the right one is 2; `mkCon a b` has `a` on
port 1. Both copies of `T_{p,q}` in the picture of page 83 are drawn with their principal port down,
so both are numbered `1, …, 2p + q` from left to right, as for `T_n`.

* `transpositor_shape_two_one`, `transpositor_one_zero`, `transpositor_zero`, `transpositor_nil` —
  the trees: `γ` cells on the first `2p` ports, `T_{0,q} = T_q`, `T_{p,q}` with `p + q = 0` is `ε`.
* `transpositor_transpositor_two_one` — the property for `p = 2`, `q = 1`, by hand: two `δδ` and
  two `γγ` steps, without `transpositor_transpositor`; `transpositor_transpositor_two_one'` gets
  the same from the general theorem, and `transpositor_figure_two_one` is the closed net.
* `transpositor_transpositor_zero` — for `p = 0`, the identity wiring, as `autoMux_autoMux`.
* `dupPair_dupPair` — with `δ` in place of `γ` (page 83: "`δ` is not suitable") the ports are
  joined `i` to `i`, which is not `ι_{p,q}`.
* `pairCon_min`, `swapPairs_min`, `transpositor_min` — the missing hypothesis `2p ≤ length` is
  harmless: `transpositor p ts` is `T_{p', q'}` with `p' = min p (length / 2)`, and
  `2p' + q' = length`; `swapPairs` is cut down the same way.
-/

namespace INet.Comb.TranspositorCheck

open Term

variable (t₁ t₂ t₃ t₄ t₅ u₁ u₂ u₃ u₄ u₅ : Term sig ℕ) (Δ : CNet)

/-- `T_{2,1}` (page 83): the autodual multiplexor `T_3` (a `dup` with a `dup` on its port 2, Fig. 5)
whose first two auxiliary ports carry a `con` each, on ports `1, 2` and `3, 4`; port 5 is free. -/
theorem transpositor_shape_two_one :
    transpositor 2 [t₁, t₂, t₃, t₄, t₅] = mkDup (mkCon t₁ t₂) (mkDup (mkCon t₃ t₄) t₅) :=
  rfl

/-- `T_{1,0}` (page 83) is one `con`: `T_1` is a wire carrying the `γ` cell. -/
theorem transpositor_one_zero : transpositor 1 [t₁, t₂] = mkCon t₁ t₂ := rfl

/-- `T_{0,q}` (page 83) is the autodual multiplexor `T_q`. -/
theorem transpositor_zero (ts : List (Term sig ℕ)) : transpositor 0 ts = autoMux ts := rfl

/-- `T_{p,q}` with no port (page 83, `p + q = 0`) is `T_0 = ε` of Fig. 5, whatever `p` is given. -/
theorem transpositor_nil (p : ℕ) : transpositor p ([] : List (Term sig ℕ)) = mkEra := by
  cases p <;> rfl

/-- `ι_{2,1}` (page 83) exchanges 1 with 2 and 3 with 4, and fixes 5. -/
theorem swapPairs_two_one : swapPairs 2 [t₁, t₂, t₃, t₄, t₅] = [t₂, t₁, t₄, t₃, t₅] := rfl

/-- The property of the transpositor (page 83) for `p = 2`, `q = 1`, by hand: `δδ` (the
multiplexors meet), `γγ` on ports 1, 2, `δδ`, `γγ` on ports 3, 4. Port `i` of the left copy is
joined to port `ι_{2,1}(i)` of the right one: `1–2`, `2–1`, `3–4`, `4–3`, `5–5`. -/
theorem transpositor_transpositor_two_one :
    Red (s(transpositor 2 [t₁, t₂, t₃, t₄, t₅], transpositor 2 [u₁, u₂, u₃, u₄, u₅]) ::ₘ Δ)
      (s(t₁, u₂) ::ₘ s(t₂, u₁) ::ₘ s(t₃, u₄) ::ₘ s(t₄, u₃) ::ₘ s(t₅, u₅) ::ₘ Δ) := by
  rw [transpositor_shape_two_one, transpositor_shape_two_one]
  refine Relation.ReflTransGen.head (step_dup_dup _ _ _ _ Δ) ?_
  refine Relation.ReflTransGen.head (step_con_con t₁ t₂ u₁ u₂ _) ?_
  have h : Red (s(mkDup (mkCon t₃ t₄) t₅, mkDup (mkCon u₃ u₄) u₅) ::ₘ
      s(t₁, u₂) ::ₘ s(t₂, u₁) ::ₘ Δ)
      (s(t₃, u₄) ::ₘ s(t₄, u₃) ::ₘ s(t₅, u₅) ::ₘ s(t₁, u₂) ::ₘ s(t₂, u₁) ::ₘ Δ) :=
    Relation.ReflTransGen.head (step_dup_dup _ _ _ _ _)
      (Steps.single (step_con_con t₃ t₄ u₃ u₄ _))
  refine Steps.cast h ?_ ?_ <;> ms

/-- `transpositor_transpositor` gives the same result as the computation by hand for `p = 2`,
`q = 1` (page 83). -/
theorem transpositor_transpositor_two_one' :
    Red (s(transpositor 2 [t₁, t₂, t₃, t₄, t₅], transpositor 2 [u₁, u₂, u₃, u₄, u₅]) ::ₘ Δ)
      (s(t₁, u₂) ::ₘ s(t₂, u₁) ::ₘ s(t₃, u₄) ::ₘ s(t₄, u₃) ::ₘ s(t₅, u₅) ::ₘ Δ) := by
  have h := transpositor_transpositor 2 [t₁, t₂, t₃, t₄, t₅] [u₁, u₂, u₃, u₄, u₅] Δ rfl
  refine h.cast rfl ?_
  simp only [swapPairs, List.zipWith_cons_cons, List.zipWith_nil_right, ← Multiset.cons_coe,
    Multiset.coe_nil]
  ms

/-- The picture of page 83 for `p = 2`, `q = 1`, on free ports: `T_{2,1}` on ports `0, …, 4`
against `T_{2,1}` on ports `5, …, 9`, alone, reduces to `0–6`, `1–5`, `2–8`, `3–7`, `4–9`. The
hypotheses of `transpositor_transpositor` hold here, so it is not vacuous. -/
theorem transpositor_figure_two_one :
    Red {s(transpositor 2 [var 0, var 1, var 2, var 3, var 4],
          transpositor 2 [var 5, var 6, var 7, var 8, var 9])}
      (s(var 0, var 6) ::ₘ s(var 1, var 5) ::ₘ s(var 2, var 8) ::ₘ s(var 3, var 7) ::ₘ
        {s(var 4, var 9)}) :=
  transpositor_transpositor_two_one _ _ _ _ _ _ _ _ _ _ 0

/-- The property for `p = 0` (page 83): `T_{0,q} = T_q`, and two copies reduce to the identity
wiring, as in `autoMux_autoMux`. -/
theorem transpositor_transpositor_zero :
    Red {s(transpositor 0 [var 0, var 1, var 2], transpositor 0 [var 3, var 4, var 5])}
      (s(var 0, var 3) ::ₘ s(var 1, var 4) ::ₘ {s(var 2, var 5)}) := by
  have h := transpositor_transpositor 0 [var 0, var 1, var 2] [var 3, var 4, var 5] 0 rfl
  refine h.cast rfl ?_
  simp only [swapPairs, List.zipWith_cons_cons, List.zipWith_nil_right, ← Multiset.cons_coe,
    Multiset.coe_nil, add_zero]
  rfl

/-- "`δ` is not suitable" (page 83): with a `dup` in place of the `con` of `T_{1,0}`, the two
copies join port 1 to port 1 and port 2 to port 2, which is the identity and not `ι_{1,0}`. -/
theorem dupPair_dupPair :
    Step system (s(mkDup t₁ t₂, mkDup u₁ u₂) ::ₘ Δ) (s(t₁, u₁) ::ₘ s(t₂, u₂) ::ₘ Δ) :=
  step_dup_dup t₁ t₂ u₁ u₂ Δ

/-- `pairCon p` only pairs what it can: it is `pairCon p'` with `p' = min p (length / 2)`, and
`2p' ≤ length`. -/
theorem pairCon_min : ∀ (p : ℕ) (ts : List (Term sig ℕ)),
    pairCon p ts = pairCon (min p (ts.length / 2)) ts
  | 0, _ => by simp [pairCon]
  | _ + 1, [] => by simp [pairCon]
  | _ + 1, [_] => by simp [pairCon]
  | p + 1, t :: t' :: ts => by
    have h : min (p + 1) ((t :: t' :: ts).length / 2) = min p (ts.length / 2) + 1 := by
      simp only [List.length_cons]; omega
    rw [h, pairCon, pairCon, pairCon_min p ts]

/-- `swapPairs p` is cut down in the same way as `pairCon p`. -/
theorem swapPairs_min {α : Type*} : ∀ (p : ℕ) (l : List α),
    swapPairs p l = swapPairs (min p (l.length / 2)) l
  | 0, _ => by simp [swapPairs]
  | _ + 1, [] => by simp [swapPairs]
  | _ + 1, [_] => by simp [swapPairs]
  | p + 1, t :: t' :: l => by
    have h : min (p + 1) ((t :: t' :: l).length / 2) = min p (l.length / 2) + 1 := by
      simp only [List.length_cons]; omega
    rw [h, swapPairs, swapPairs, swapPairs_min p l]

/-- The missing hypothesis `2p ≤ length` is harmless (page 83): on `n` ports, `transpositor p` is
`T_{p', q'}` with `p' = min p (n / 2)` and `q' = n - 2p'`, which the paper defines, and
`transpositor_transpositor` for `p` is its instance for `p'` (by `swapPairs_min`). -/
theorem transpositor_min (p : ℕ) (ts : List (Term sig ℕ)) :
    transpositor p ts = transpositor (min p (ts.length / 2)) ts ∧
      2 * min p (ts.length / 2) ≤ ts.length := by
  refine ⟨by rw [transpositor, transpositor, pairCon_min], by omega⟩

/-- An instance of `transpositor_min`: `T` with `p = 3` on three ports is `T_{1,1}`. -/
example : transpositor 3 [t₁, t₂, t₃] = transpositor 1 [t₁, t₂, t₃] := rfl

end INet.Comb.TranspositorCheck
