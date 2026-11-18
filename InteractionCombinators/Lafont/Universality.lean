import InteractionCombinators.Combinators
import InteractionCombinators.Translation

/-!
# Lafont, "Interaction Combinators" (1997): Theorem 1

The target of this project. The statement is checked by Lean; the proof is not yet written, and
`proof_wanted` adds no axiom.
-/

namespace INet.Comb

/-- **Theorem 1** (Lafont 1997). Any interaction system can be translated into the system of
interaction combinators. -/
proof_wanted universal : Universal system

/-- The form of Theorem 1 this project aims at: the translation is strict. It implies `universal`
by `StrictlyUniversal.universal`. Lafont's translation has a cell at the root of every symbol
(Fig. 6 and Fig. 10), so it should be strict. -/
proof_wanted universal_strict : StrictlyUniversal system

end INet.Comb
