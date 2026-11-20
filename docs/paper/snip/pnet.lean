structure PNet (S : Signature) (n : ℕ) where
  internal : ℕ
  tree : Term S (Fin n ⊕ Fin internal)
  port_count : ∀ i, tree.vars.count (.inl i) = 1
  internal_count : ∀ w, tree.vars.count (.inr w) = 2

def inst
    (p : PNet S n)
    (args : Fin n → Term S ℕ)
    (f : Fin p.internal → ℕ) :
    Term S ℕ :=
  p.tree.bind (Sum.elim args fun w => Term.var (f w))
