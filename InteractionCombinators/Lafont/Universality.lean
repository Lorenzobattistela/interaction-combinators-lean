import InteractionCombinators.Lafont.CodeCompatible

/-!
# Lafont, "Interaction Combinators" (1997): Theorem 1

The target of this project, proved. The statements are those fixed before any proof was written;
the proofs are `universal'` and `universal_strict'` of `Lafont/CodeCompatible.lean`, by the
translation of Fig. 10.
-/

namespace INet.Comb

/-- **Theorem 1** (Lafont 1997, stated on page 82; its proof ends on page 90). Any interaction system can be translated into the system
of interaction combinators. -/
theorem universal : Universal system :=
  universal'

/-- The form of Theorem 1 this project aimed at: the translation is strict. It implies `universal`
by `StrictlyUniversal.universal`. Lafont's translation has a cell at the root of every symbol
(Fig. 6 and Fig. 10), so it is strict. -/
theorem universal_strict : StrictlyUniversal system :=
  universal_strict'

end INet.Comb
