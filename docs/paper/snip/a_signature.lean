/-- Symbols, each with the number of its auxiliary ports. Every cell also has one principal
port. -/
structure Signature where
  /-- The symbols. -/
  Sym : Type
  /-- The number of auxiliary ports of a symbol. -/
  arity : Sym → ℕ

/-- A tree of cells with leaves named in `ν`. The root of `app α ts` is the principal port of an
`α` cell whose `i`-th auxiliary port is plugged into the root of `ts i`. -/
inductive Term (S : Signature) (ν : Type) : Type
  -- a leaf: the end of the wire named `x`
  | var : ν → Term S ν
  -- a cell of symbol `α`, with one tree for each of its auxiliary ports
  | app : (α : S.Sym) → (Fin (S.arity α) → Term S ν) → Term S ν
