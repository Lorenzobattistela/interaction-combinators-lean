import InteractionCombinators.Lafont.RecursionFreeTerminates

/-!
# Checks of `Lafont/RecursionFreeTerminates.lean` (page 86)

* The two theorems apply to the example of page 87, the combinators without `con`–`dup`
  (`systemNoConDup_recursionFree`).
* A concrete interaction `era`–`con` of that system: the measure goes from `{0, 1}` to `{0, 0}`,
  which `measure_step` sees as a decrease in the Dershowitz–Manna order. So the measure is not
  constant and the step relation is not empty.
* For the full system `Comb.system` the hypothesis fails (`system_not_recursionFree`), and the
  conclusion fails too: Fig. 3 (page 82) is a net that reduces to itself in four steps. Fig. 3 is
  not formalized in the library. It would need four concrete `StepE` (`con`–`dup`, `era`–`dup`,
  `era`–`con`, `era`–`era`, the only multiset of interactions that gives back the cells it
  consumed), each with an `Equiv` proof of the intermediate net, more than the 50 lines this
  check was allowed for it. It is left for a separate issue.
-/

namespace INet.Comb

open Term

/-- **Page 86, applied to page 87.** There is no infinite sequence of interactions in the
combinators without `con`–`dup`. -/
theorem systemNoConDup_step_wellFounded :
    WellFounded (fun N' N => Step systemNoConDup N N') :=
  systemNoConDup_recursionFree.step_wellFounded

/-- **Page 86, applied to page 87.** There is no infinite sequence of interactions up to `Equiv`
in the combinators without `con`–`dup`. -/
theorem systemNoConDup_stepE_wellFounded :
    WellFounded (fun N' N => StepE systemNoConDup N N') :=
  systemNoConDup_recursionFree.stepE_wellFounded

/-- No sequence of nets has an interaction of `systemNoConDup` from each to the next (page 86). -/
theorem systemNoConDup_not_step_seq (N : ℕ → Net sig ℕ) :
    ¬ ∀ n, Step systemNoConDup (N n) (N (n + 1)) :=
  systemNoConDup_recursionFree.not_step_seq N

/-- The full system of combinators is not recursion-free (page 87), so the theorems of page 86
do not apply to it. -/
theorem system_hypothesis_fails : ¬ system.RecursionFree := system_not_recursionFree

/-- An eraser against a `con` cell whose auxiliary ports are the free ports `0` and `1`. -/
def eraConNet : Net sig ℕ := s(mkEra, mkCon (var 0) (var 1)) ::ₘ 0

/-- What `eraConNet` reduces to: an eraser on each port. -/
def eraConResult : Net sig ℕ :=
  ruleEraBin.inst (S := sig) (a := sig.arity Comb.era) (b := sig.arity Comb.con) ![]
    ![var 0, var 1] Fin.elim0 + 0

/-- The interaction `era`–`con` of `eraConNet` in `systemNoConDup`. -/
theorem eraConNet_step : Step systemNoConDup eraConNet eraConResult := by
  unfold eraConNet eraConResult mkEra mkCon
  refine @Step.mk sig systemNoConDup Comb.era Comb.con ruleEraBin rfl ![] ![var 0, var 1] 0
    (fun i => i.elim0) ?_ ?_ <;>
    intro i <;> exact i.elim0

/-- The measure of `eraConNet` is `{era, con} = {0, 1}`. -/
theorem eraConNet_measure :
    recursionFreeDataNoConDup.measure eraConNet = {0, 1} := by decide

/-- The measure of the result is `{era, era} = {0, 0}`. -/
theorem eraConResult_measure :
    recursionFreeDataNoConDup.measure eraConResult = {0, 0} := by decide

/-- `measure_step` on the concrete interaction: `{0, 0}` is below `{0, 1}`. -/
theorem eraConNet_measure_lt :
    Multiset.IsDershowitzMannaLT ({0, 0} : Multiset ℕ) {0, 1} := by
  rw [← eraConNet_measure, ← eraConResult_measure]
  exact recursionFreeDataNoConDup.measure_step eraConNet_step

end INet.Comb
