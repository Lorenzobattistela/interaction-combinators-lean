import InteractionCombinators.Lafont.TranslationCompCompatible
import InteractionCombinators.Lafont.CodeCompatibleReview
import InteractionCombinators.Lafont.RecursionFreeCompatibleReview

/-!
# Checks of `Translation.Compatible.comp` (page 80)

`Compatible.comp` is applied to translations that are not the identity, so its hypotheses are
shown to hold:

* the translation `D.translation` of Fig. 6 of the recursion-free system `tsys` into the
  combinators (Section 2.4, pages 85–87), followed by the translation `codeTranslation` of the
  combinators into themselves (Theorem 1, pages 88–90);
* `codeTranslation` followed by itself.

For the first composite, the rule `b`–`c` of `tsys` gives an actual reduction
(`comp_bc_reduces`), with names for which the linearity hypothesis holds
(`Translation.exists_linear_pair`).
-/

namespace INet.Comb.TranslationCompCompatibleCheck

open INet INet.Comb INet.Comb.RecursionFreeCompatibleReview

/-- The translation of Theorem 1 of the combinators into themselves (pages 88–90). -/
noncomputable abbrev codeΦ : Translation sig sig := codeTranslation system_wellFormed.decData.side

/-- `codeΦ` is a translation of interaction systems from the combinators to themselves. -/
theorem codeΦ_compatible : codeΦ.Compatible system system :=
  system_wellFormed.decData.codeTranslation_compatible system_wellFormed

/-- **The translation of Fig. 6 followed by that of Theorem 1 is compatible** (page 80). The
recursion-free system `tsys` (pages 85–87) is translated into the combinators by
`tdata.translation`, and the combinators into themselves by `codeTranslation`; the composite translates `tsys` into the
combinators. The rules of the combinators are linear. -/
theorem comp_tsys_compatible : (codeΦ.comp tdata.translation).Compatible tsys system :=
  Translation.Compatible.comp system_wellFormed.linear system_wellFormed.linear
    (tdata.translation_compatible tsys_wellFormed) codeΦ_compatible

/-- **The translation of Theorem 1 followed by itself is compatible** (page 80). -/
theorem comp_code_code_compatible : (codeΦ.comp codeΦ).Compatible system system :=
  Translation.Compatible.comp system_wellFormed.linear system_wellFormed.linear
    codeΦ_compatible codeΦ_compatible

/-- **The composite gives an actual reduction** (page 80). For the rule `b`–`c` of `tsys`, there
are names for which the pair `Ψ(Φ(b)) — Ψ(Φ(c))` is linear, and it reduces up to wires to a net
equivalent to a translation by the composite of the right-hand side. -/
theorem comp_bc_reduces : ∃ (xs : Fin 1 → ℕ) (ys : Fin 1 → ℕ)
    (f : Fin ((codeΦ.comp tdata.translation).net TSym.b).internal → ℕ)
    (g : Fin ((codeΦ.comp tdata.translation).net TSym.c).internal → ℕ)
    (M N' : Net sig ℕ) (h : Fin ruleBC.internal → ℕ),
    StepsE system {s(((codeΦ.comp tdata.translation).net TSym.b).inst (fun i => .var (xs i)) f,
      ((codeΦ.comp tdata.translation).net TSym.c).inst (fun j => .var (ys j)) g)} M ∧
    Equiv M N' ∧
    (codeΦ.comp tdata.translation).NetTr
      (ruleBC.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N' := by
  obtain ⟨xs, ys, f, g, hlin⟩ :=
    (codeΦ.comp tdata.translation).exists_linear_pair TSym.b TSym.c
  obtain ⟨M, N', h, hS, hE, hN⟩ := comp_tsys_compatible TSym.b TSym.c ruleBC rfl xs ys f g hlin
  exact ⟨xs, ys, f, g, M, N', h, hS, hE, hN⟩

end INet.Comb.TranslationCompCompatibleCheck
