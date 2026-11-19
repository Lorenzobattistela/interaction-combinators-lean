import Checks.SimulationInvertibleCheck
import InteractionCombinators.Lafont.NormalFormE

/-!
# Checks of `NormalFormE.lean` (pages 73-74)

The hypotheses of `StepsEN.normal_of_stepsEN` and `StepsEN.normal_unique` can hold with a
reduction of positive length: the `con`–`con` pair `con(0, 1) = con(2, 3)` of the combinators is
linear, and reduces in one interaction up to wires to a net without a cut
(`SimulationInvertibleCheck.conPair_stepE_not_hasCut`), which is irreducible. The pair itself is
not irreducible.
-/

namespace INet.NormalFormECheck

open Term Comb

/-- The pair `con(0, 1) = con(2, 3)`. -/
abbrev conPair : Net sig ℕ := PairStepE.pairNet (Comb.con : sig.Sym) Comb.con ![0, 1] ![2, 3]

/-- The pair is linear (Lafont 1997, page 71). -/
theorem conPair_linear : conPair.Linear := by
  have hv : Net.vars conPair = {0, 1, 2, 3} := by decide
  intro y
  rw [hv]
  simp [Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- The pair is not irreducible (Lafont 1997, page 73). -/
theorem conPair_not_normal : ¬ StepE.Normal system conPair := by
  obtain ⟨K, hs, -⟩ := SimulationInvertibleCheck.conPair_stepE_not_hasCut
  exact fun h => h K hs

/-- **The hypotheses of the consequence of Proposition 1 can hold** (Lafont 1997, pages 73-74):
the linear `con`–`con` pair reduces in one step up to wires to an irreducible net `P`, and then
every reduction of the pair to an irreducible net has length `1` and ends at the same graph as
`P`. -/
theorem conPair_normal :
    ∃ P, StepsEN system 1 conPair P ∧ StepE.Normal system P ∧
      ∀ m Q, StepsEN system m conPair Q → StepE.Normal system Q → m = 1 ∧ Equiv P Q := by
  obtain ⟨K, hs, hK⟩ := SimulationInvertibleCheck.conPair_stepE_not_hasCut
  have hP : StepE.Normal system K := StepE.Normal.of_not_hasCut hK
  exact ⟨K, StepsEN.single hs, hP, fun m Q ht hQ =>
    StepsEN.normal_unique system_wellFormed conPair_linear hP hQ (StepsEN.single hs) ht⟩

/-- Every reduction of the pair has at most one step, by `StepsEN.le_of_normal`. -/
example (k : ℕ) (Q : Net sig ℕ) (h : StepsEN system k conPair Q) : k ≤ 1 := by
  obtain ⟨K, hs, hK⟩ := SimulationInvertibleCheck.conPair_stepE_not_hasCut
  exact StepsEN.le_of_normal system_wellFormed conPair_linear (StepE.Normal.of_not_hasCut hK)
    (StepsEN.single hs) h

end INet.NormalFormECheck
