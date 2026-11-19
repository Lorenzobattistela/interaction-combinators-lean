import InteractionCombinators.Translations.SimulationE
import InteractionCombinators.Core.Combinators

/-!
# A check of `Translation.CompatibleWithin.stepsEN`

Lafont 1997, Proposition 4, page 81. The hypotheses of `Translation.CompatibleWithin.stepsEN` hold
on a source reduction that needs a wire substitution before its interaction:

* `cutLong` is a `con` and a `dup` whose principal ports are joined by the named wire `8`. It has
  no literal interaction (`not_step_cutLong`): every equation has a name on one side.
* It is the same graph as `cut`, the two cells plugged directly (`equiv_cutLong_cut`), and `cut`
  reduces to `cutResult` by the `con`–`dup` rule. So `StepE system cutLong cutResult`.
* The identity translation of the combinators is within `L = M = 1` (`id_compatibleWithin`), and
  `cutLong` is its own translation. The theorem then gives a reduction of `cutLong` in exactly one
  interaction to a net that is the same graph as a translation of `cutResult`.
-/

namespace INet.SimulationECheck

open Term Comb

/-- A `con` and a `dup` whose principal ports are joined by the wire `8`. -/
def cutLong : CNet :=
  s(var 8, mkCon (var 0) (var 1)) ::ₘ s(var 8, mkDup (var 2) (var 3)) ::ₘ 0

/-- The same two cells plugged directly by their principal ports. -/
def cut : CNet := s(mkCon (var 0) (var 1), mkDup (var 2) (var 3)) ::ₘ 0

/-- The result of the `con`–`dup` interaction of `cut`, with new wires `4`, `5`, `6`, `7`. -/
def cutResult : CNet :=
  s(var 0, mkDup (var 4) (var 5)) ::ₘ s(var 1, mkDup (var 6) (var 7)) ::ₘ
    s(var 2, mkCon (var 4) (var 6)) ::ₘ s(var 3, mkCon (var 5) (var 7)) ::ₘ 0

/-- `cutLong` is linear: the wire `8` occurs twice, every other name once. -/
theorem cutLong_linear : cutLong.Linear := by
  intro y
  simp [cutLong, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- `cutLong` has no literal interaction: each of its equations has a name on one side, and an
interaction needs two cells on the two sides of one equation (page 72). -/
theorem not_step_cutLong (M : CNet) : ¬ Step system cutLong M := by
  intro h
  generalize hN : cutLong = N at h
  obtain ⟨α, β, rl, -, as, bs, Δ, -, -, -⟩ := h
  have hm : s(Term.app α as, Term.app β bs) ∈ cutLong := hN ▸ Multiset.mem_cons_self _ _
  simp [cutLong] at hm

/-- `cutLong` and `cut` are the same graph: substituting the wire `8` (page 72). -/
theorem equiv_cutLong_cut : Equiv cutLong cut := by
  have h := Wire.mk (S := sig) 8 (mkCon (var 0) (var 1)) (var 8) (mkDup (var 2) (var 3)) 0
    cutLong_linear (by simp)
  have e : (mkDup (var 2) (var 3)).subst 8 (mkCon (var 0) (var 1)) = mkDup (var 2) (var 3) :=
    Term.subst_of_notMem (by simp)
  rw [subst_var_self, e] at h
  exact h.equiv

/-- One interaction up to wires, and not a literal one: `cutLong` reduces to `cutResult`. -/
theorem stepE_cutLong : StepE system cutLong cutResult := by
  refine ⟨cut, equiv_cutLong_cut, ?_⟩
  exact step_con_dup (var 0) (var 1) (var 2) (var 3) 0 4 5 6 7 (by decide) (by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> simp)

/-- `Translation.CompatibleWithin.stepsEN` applied to the identity translation of the combinators
and the reduction up to wires `stepE_cutLong`, which has no literal counterpart
(`not_step_cutLong`). The hypotheses hold, and the conclusion is a reduction in exactly one
interaction (Lafont 1997, Proposition 4, page 81, with `L = M = 1`). -/
example : ∃ n' M₁ M', StepsEN system n' cutLong M₁ ∧ 1 * 1 ≤ n' ∧ n' ≤ 1 * 1 ∧
    Equiv M₁ M' ∧ (Translation.id sig).NetTr cutResult M' :=
  Translation.CompatibleWithin.stepsEN system_wellFormed.linear system_wellFormed.linear
    (Translation.id_compatibleWithin system system_wellFormed) (StepsEN.single stepE_cutLong)
    ⟨Multiset.rel_refl_of_refl_on fun e _ => Translation.eqTr_id e, cutLong_linear⟩

/-- The same with `Translation.Compatible.stepsE`, on the identity translation. -/
example : ∃ M₁ M', StepsE system cutLong M₁ ∧ Equiv M₁ M' ∧
    (Translation.id sig).NetTr cutResult M' :=
  Translation.Compatible.stepsE system_wellFormed.linear system_wellFormed.linear
    (Translation.id_compatible system system_wellFormed)
    (Relation.ReflTransGen.single stepE_cutLong)
    ⟨Multiset.rel_refl_of_refl_on fun e _ => Translation.eqTr_id e, cutLong_linear⟩

end INet.SimulationECheck
