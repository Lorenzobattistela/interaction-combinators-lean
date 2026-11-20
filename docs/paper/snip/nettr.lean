inductive TermTr (Φ : Translation S S') : Term S ℕ → Term S' ℕ → Prop
  | var
      (x : ℕ) :
      TermTr Φ (.var x) (.var x)
  | app
      (α : S.Sym)
      (ts : Fin (S.arity α) → Term S ℕ)
      (ts' : Fin (S.arity α) → Term S' ℕ)
      (f : Fin (Φ.net α).internal → ℕ)
      (h : ∀ i, TermTr Φ (ts i) (ts' i)) :
      TermTr Φ (.app α ts) ((Φ.net α).inst ts' f)

structure NetTr (Φ : Translation S S') (N : Net S ℕ) (N' : Net S' ℕ) : Prop where
  rel : Multiset.Rel Φ.EqTr N N'
  linear : N'.Linear
