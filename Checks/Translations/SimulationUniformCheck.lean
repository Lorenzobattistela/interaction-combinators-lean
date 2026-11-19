import InteractionCombinators.Translations.SimulationUniform

/-!
# Checks for the uniform bounds of page 81

`Translation.Compatible.exists_compatibleWithin` and `Comb.codeTranslation_compatibleWithin`
(`Lafont/SimulationUniform.lean`) applied to the translation of Fig. 10 of the combinators into
themselves. That translation is not the identity: `[γ]`, `[δ]`, `[ε]` are the trees of Fig. 10,
and each rule of Fig. 2 is simulated by the reduction of Fig. 7, not by one interaction.
-/

namespace INet.Comb.SimulationUniformCheck

/-- **Deliverable 2, applied** (Lafont 1997, page 81): the translation of Fig. 10 of the
combinators into themselves has uniform bounds `L`, `M`. The hypotheses are the well-formedness of
the combinators (`system_wellFormed`, Fig. 2) and the compatibility of the translation
(`codeTranslation_compatible`). -/
example : ∃ L M, (codeTranslation system_wellFormed.decData.side).CompatibleWithin system system
    L M :=
  (system_wellFormed.decData.codeTranslation_compatible system_wellFormed).exists_compatibleWithin
    system_wellFormed system_wellFormed.linear

/-- **Deliverable 3, applied** (Lafont 1997, pages 81 and 90): Theorem 1 with step counts, for the
combinators themselves with their own decomposition data. -/
example : ∃ L M, 0 < L ∧
    (codeTranslation system_wellFormed.decData.side).CompatibleWithin system system L M :=
  codeTranslation_compatibleWithin system_wellFormed system_wellFormed.decData

/-- With the bounds, Proposition 4 counts the steps: `n` interactions of the combinators are
simulated by `n'` interactions of their translation, `L n ≤ n' ≤ M n`, with `L > 0`. -/
example {n : ℕ} {N M₀ : CNet} {N' : CNet} (h : StepsN system n N M₀)
    (hT : (codeTranslation system_wellFormed.decData.side).NetTr N N') :
    ∃ L M, 0 < L ∧ ∃ n' M₁ M', StepsEN system n' N' M₁ ∧ L * n ≤ n' ∧ n' ≤ M * n ∧
      Equiv M₁ M' ∧ (codeTranslation system_wellFormed.decData.side).NetTr M₀ M' := by
  obtain ⟨L, M, hL, hLM⟩ :=
    codeTranslation_compatibleWithin system_wellFormed system_wellFormed.decData
  exact ⟨L, M, hL, hLM.steps system_wellFormed.linear system_wellFormed.linear h hT⟩

end INet.Comb.SimulationUniformCheck
