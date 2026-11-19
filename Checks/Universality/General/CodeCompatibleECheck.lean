import Checks.Universality.General.CodeGammaExtractECheck
import InteractionCombinators.Universality.General.CodeCompatibleSides

/-!
# Check: `codeCells_plugE` and compatibility at `combEnum` (Fig. 10, pages 89–90)

Lafont 1997, Fig. 10 (journal page 89, PDF page 21) and page 90. The theorems `codeCells_plugE`,
`codeTranslationE_compatible_of_sides`, `System.DecData.codeTranslationE_compatible` and
`codeTranslationE_strict` are applied to the interaction combinators themselves, with the symbols
numbered by hand, `con, dup, era ↦ 0, 1, 2` (`combEnum`, from `CodeMenusECheck`), without
`symEnum`.

* `plugE_conDup_concrete` — `codeCells_plugE` at `combEnum` and `sideConDupSym` (from
  `CodeGammaExtractECheck`; `sideConDup` has no side of `dup` against `con`, so the hypotheses
  `hs`, `hs'` could never both hold for it) on the concrete net `netConDupE`, whose linearity is
  proved: its hypotheses are met.
* `compatibleE_system` — for any decomposition data of the combinator system, the translation of
  Fig. 10 with the numbering `combEnum` is compatible; such data exist (`decData_nonempty`).
* `strictCompatibleE_system` — a strict and compatible translation of the combinator system into
  itself, built with `combEnum`: the form Stage B.5 needs.
-/

namespace INet.Comb.CodeCompatibleECheck

open Term Translation CodeGammaReview CodeMenusECheck CodeGammaExtractCheck
  CodeGammaExtractECheck ExpandTrReview RecursionFreeFig7Check

/-- **`codeCells_plugE` at `combEnum` and `sideConDupSym`, `[con]` against `[dup]`** (Fig. 10,
pages 89–90): with any names on the ports and wires, in a linear context, the two cells reduce up
to wires to `plugTermTarget (swap 0 1) tφ tψ xs ys` beside the context, where `tφ`, `tψ` are
translations by `codeTranslationE combEnum sideConDupSym` of the trees of the side `ruleConDup`. -/
theorem plugE_conDup (xs : Fin (sig.arity (Comb.con : sig.Sym)) → ℕ)
    (ys : Fin (sig.arity (Comb.dup : sig.Sym)) → ℕ)
    (f : Fin (codeNetE combEnum sideConDupSym (Comb.con : sig.Sym)).internal → ℕ)
    (g : Fin (codeNetE combEnum sideConDupSym (Comb.dup : sig.Sym)).internal → ℕ) (Δ : CNet)
    (hlin : Net.Linear (s((codeNetE combEnum sideConDupSym (Comb.con : sig.Sym)).inst
        (fun i => var (xs i)) f,
      (codeNetE combEnum sideConDupSym (Comb.dup : sig.Sym)).inst (fun j => var (ys j)) g) ::ₘ
        Δ)) :
    ∃ (k₀ k₁ : ℕ) (M : CNet) (tφ : Fin (sig.arity (Comb.con : sig.Sym)) ⊕ Fin 2 → Term sig ℕ)
      (tψ : Fin (sig.arity (Comb.dup : sig.Sym)) ⊕ Fin 2 → Term sig ℕ),
      StepsE system (s((codeNetE combEnum sideConDupSym (Comb.con : sig.Sym)).inst
          (fun i => var (xs i)) f,
        (codeNetE combEnum sideConDupSym (Comb.dup : sig.Sym)).inst (fun j => var (ys j)) g) ::ₘ
          Δ) M ∧
      Equiv M (plugTermTarget (Equiv.swap 0 1) tφ tψ xs ys + Δ) ∧
      (∀ p, (codeTranslationE combEnum sideConDupSym).TermTr (gammaTree ruleConDup k₀ p) (tφ p)) ∧
      (∀ q, (codeTranslationE combEnum sideConDupSym).TermTr (gammaTree ruleConDup k₁ q)
        (tψ q)) :=
  codeCells_plugE combEnum sideConDupSym Comb.con Comb.dup xs ys f g Δ ruleConDup ruleConDup
    (Equiv.swap 0 1) GammaCheck.hs ruleConDup_linear ruleConDup_expanded ruleConDup_linear
    ruleConDup_expanded rfl rfl hlin

/-- **`codeCells_plugE` applies to a concrete net** (Fig. 10, pages 89–90): `[con]` against
`[dup]` at `combEnum` and `sideConDupSym`, ports `0, 1` and `2, 3`, internal wires from `4`, with
the linearity hypothesis proved (`linear_netConDupE`), reduces to a net `Equiv` to
`plugTermTarget (swap 0 1) tφ tψ` on these ports; here the translated trees are left abstract. -/
theorem plugE_conDup_concrete :
    ∃ (k₀ k₁ : ℕ) (M : CNet) (tφ : Fin (sig.arity (Comb.con : sig.Sym)) ⊕ Fin 2 → Term sig ℕ)
      (tψ : Fin (sig.arity (Comb.dup : sig.Sym)) ⊕ Fin 2 → Term sig ℕ),
      StepsE system netConDupE M ∧
      Equiv M (plugTermTarget (Equiv.swap 0 1) tφ tψ zeroOne twoThree + 0) ∧
      (∀ p, (codeTranslationE combEnum sideConDupSym).TermTr (gammaTree ruleConDup k₀ p) (tφ p)) ∧
      (∀ q, (codeTranslationE combEnum sideConDupSym).TermTr (gammaTree ruleConDup k₁ q)
        (tψ q)) :=
  plugE_conDup zeroOne twoThree fromFour
    (afterFour (codeNetE combEnum sideConDupSym (Comb.con : sig.Sym)).internal) 0 linear_netConDupE

/-- The combinator system has decomposition data (`System.exists_decData`, page 86), so the
hypothesis of `compatibleE_system` can be met. -/
theorem decData_nonempty : Nonempty (System.DecData (system : System sig)) :=
  System.exists_decData system_wellFormed

/-- **The translation of Fig. 10 numbered by `combEnum` is compatible** (Fig. 10, pages 89–90,
page 90): for any decomposition data `D` of the combinator system,
`codeTranslationE combEnum D.side` is compatible with the system. -/
theorem compatibleE_system (D : System.DecData (system : System sig)) :
    (codeTranslationE combEnum D.side).Compatible system system :=
  System.DecData.codeTranslationE_compatible combEnum system_wellFormed D

/-- **`codeTranslationE_compatible_of_sides` at `combEnum`** (Fig. 10, pages 89–90): the same
for the sides of any decomposition data, through `System.DecData.sidesPlug`. -/
theorem compatibleE_of_sides_system (D : System.DecData (system : System sig)) :
    (codeTranslationE combEnum D.side).Compatible system system :=
  codeTranslationE_compatible_of_sides combEnum (D.sidesPlug system_wellFormed)

/-- **A strict compatible translation numbered by hand** (definition page 80, Fig. 10 pages
89–90): the combinator system has a translation into itself that is strict and compatible,
the translation of Fig. 10 with the numbering `combEnum`. -/
theorem strictCompatibleE_system :
    ∃ T : Translation sig sig, T.Strict ∧ T.Compatible system system := by
  obtain ⟨D⟩ := decData_nonempty
  exact ⟨codeTranslationE combEnum D.side, codeTranslationE_strict combEnum D.side,
    compatibleE_system D⟩

/-- `codeTranslationE_strict` at `combEnum` and the hand-written sides `sideConDupSym`. -/
example : (codeTranslationE combEnum sideConDupSym).Strict :=
  codeTranslationE_strict combEnum sideConDupSym

end INet.Comb.CodeCompatibleECheck
