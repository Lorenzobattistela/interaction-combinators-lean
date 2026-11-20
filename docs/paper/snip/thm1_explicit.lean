theorem theorem_1_explicit
    {I : System S}
    {n : ℕ}
    (e : S.Sym ≃ Fin n)
    {side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α))}
    (hside : I.SidesPlug side) :
    (codeTranslationE e side).Strict ∧
    (codeTranslationE e side).Compatible I system
