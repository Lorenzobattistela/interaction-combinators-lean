/-- A strictly universal interaction system: every interaction system over a finite alphabet has a
strict translation into it. Strictness excludes translations that erase cells by turning them into
wires, so every interaction of the source costs at least one interaction of the target. -/
def StrictlyUniversal
    -- the system, over the signature `S'`
    (I' : System S') :
    Prop :=
  ∀
    -- for every signature `S`
    (S : Signature)
    -- with finitely many symbols,
    [Finite S.Sym]
    -- and every system `I` over `S`
    (I : System S),
    -- that is an interaction system in the sense of Lafont,
    I.WellFormed →
    -- there is a translation `Φ` of the symbols of `S` into principal nets over `S'`
    ∃ Φ : Translation S S',
      -- that translates no symbol to a single wire,
      Φ.Strict ∧
      -- and that is a translation of the interaction system `I` into `I'`
      Φ.Compatible I I'
