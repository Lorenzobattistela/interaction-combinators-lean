structure Rule (S : Signature) (a b : ℕ) where
  internal : ℕ
  net : Net S (Fin a ⊕ Fin b ⊕ Fin internal)

def Rule.inst
    {a b : ℕ}
    (r : Rule S a b)
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    (f : Fin r.internal → ℕ) :
    Net S ℕ :=
  r.net.bind (Sum.elim as (Sum.elim bs fun i => Term.var (f i)))
