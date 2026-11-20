structure Signature where
  Sym : Type
  arity : Sym → ℕ

inductive Term (S : Signature) (ν : Type) : Type
  | var : ν → Term S ν
  | app : (α : S.Sym) → (Fin (S.arity α) → Term S ν) → Term S ν
