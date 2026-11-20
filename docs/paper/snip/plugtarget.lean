noncomputable def plugTermTarget
    {a b k : ℕ}
    (σ : Equiv.Perm (Fin k))
    (tφ : Fin a ⊕ Fin k → Term sig ℕ)
    (tψ : Fin b ⊕ Fin k → Term sig ℕ)
    (xs : Fin a → ℕ)
    (ys : Fin b → ℕ) :
    CNet :=
  (Finset.univ.val.map fun p : Fin a => s(var (xs p), tφ (.inl p))) +
    (Finset.univ.val.map fun q : Fin b => s(var (ys q), tψ (.inl q))) +
    (Finset.univ.val.map fun l : Fin k => s(tφ (.inr l), tψ (.inr (σ l))))
