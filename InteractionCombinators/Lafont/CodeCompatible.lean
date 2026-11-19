import InteractionCombinators.Lafont.CodeCompatibleSides

/-!
# The translation of Fig. 10 is compatible, and Theorem 1 in strict form (pages 88–90)

Lafont 1997, Section 2.7, Fig. 10 (journal page 89, PDF page 21) and page 90, where the analogue of
Fig. 7 is "left to the reader"; Theorem 1, stated page 82, proved pages 82–90.

* `System.DecData.codeTranslation_compatible` — the translation of Fig. 10 built from the sides of
  any decomposition data `D` is a translation of interaction systems (`Translation.Compatible`):
  the sides `D.side` plug back into the rules (`System.DecData.sidesPlug`), and the translation
  of any such sides is compatible (`codeTranslation_compatible_of_sides`,
  `CodeCompatibleSides.lean`).
* `universal_strict'` — **Theorem 1 in strict form**: every well-formed interaction system over a
  finite alphabet has a strict translation into the interaction combinators.
* `universal'` — **Theorem 1**.

The two theorems are primed because `Universality.lean` states the unprimed names as the target.
-/

namespace INet.Comb

open Term

/-- **The translation of Fig. 10 is compatible with reduction** (Lafont 1997, Section 2.7, Fig. 10,
pages 89–90, the analogue of Fig. 7, pages 85–86). For every rule `α`–`β` of a well-formed system
and any decomposition data `D`, the cells `[α]` and `[β]` of Fig. 10 plugged by their roots reduce,
up to wires (`StepsE system`), to a translation of an instance of the rule. -/
theorem _root_.INet.System.DecData.codeTranslation_compatible {S : Signature} [Finite S.Sym]
    {I : System S} (hI : I.WellFormed) (D : I.DecData) :
    (codeTranslation D.side).Compatible I system :=
  codeTranslation_compatible_of_sides (D.sidesPlug hI)

/-- **Theorem 1, strict form** (Lafont 1997, stated page 82, proved pages 82–90). Every
well-formed interaction system over a finite alphabet has a strict translation into the
interaction combinators: the translation of Fig. 10 for decomposition data given by
`System.exists_decData` is strict (`codeTranslation_strict`) and compatible
(`System.DecData.codeTranslation_compatible`). This is the statement `universal_strict` of `Universality.lean`. -/
theorem universal_strict' : StrictlyUniversal system := by
  intro S _ I hI
  obtain ⟨D⟩ := System.exists_decData hI
  exact ⟨codeTranslation D.side, codeTranslation_strict _, D.codeTranslation_compatible hI⟩

/-- **Theorem 1** (Lafont 1997, stated page 82, proved pages 82–90). Any interaction system can
be translated into the system of interaction combinators; it follows from the strict form
`universal_strict'`. This is the statement `universal` of `Universality.lean`. -/
theorem universal' : Universal system :=
  universal_strict'.universal

end INet.Comb
