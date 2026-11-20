theorem theorem_1_strict
    (S : Signature)
    [Finite S.Sym]
    (I : System S)
    (hI : I.WellFormed) :
    ∃ Φ : Translation S sig, Φ.Strict ∧
      Φ.Compatible I system
