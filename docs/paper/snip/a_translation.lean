/-- A translation of the symbols of `S` into principal nets over `S'`. -/
structure Translation (S S' : Signature) where
  /-- The principal net that stands for a symbol. -/
  net : (α : S.Sym) → PNet S' (S.arity α)

/-- A translation is strict when no symbol is translated to a single wire. -/
def Strict
    (Φ : Translation S S') :
    Prop :=
  -- the principal net of every symbol has a cell at its root
  ∀ α, (Φ.net α).Strict
