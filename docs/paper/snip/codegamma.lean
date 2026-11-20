def codeGamma
    (φ : Rule S a k)
    (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ)
    (k₀ : ℕ) :
    Term sig ℕ :=
  muxStar (copier (codeGammaExtras m idx φ k₀) ::
    (List.ofFn (fun i => codePort m idx φ k₀ (.inl i)) ++
      [transpositorPerm σ hσ (fun j => codePort m idx φ k₀ (.inr j))]))
