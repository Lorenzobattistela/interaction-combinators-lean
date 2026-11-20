/-- **Theorem 1, with a strict translation**: no symbol is translated into a single wire. This is
the target of the project, `StrictlyUniversal system`, unfolded. Lafont's translation (Fig. 10,
page 89) has a cell at the root of the translation of every symbol, so it is strict; by
Proposition 4 every step of `I` then costs at least one step of the combinators.

Library: `INet.Comb.universal_strict` in `InteractionCombinators/Universality/Theorem1.lean`. -/
theorem theorem_1_strict
    -- an interaction system with finitely many symbols
    (S : Signature)
    [Finite S.Sym]
    (I : System S)
    (hI : I.WellFormed) :
    -- some translation into the combinators is strict
    ∃ Φ : Translation S sig, Φ.Strict ∧
      -- and simulates every rule of `I`
      Φ.Compatible I system
