theorem codeCells_plugE
    (α β : S.Sym)
    (xs : Fin (S.arity α) → ℕ)
    (ys : Fin (S.arity β) → ℕ)
    (f : Fin (codeNetE e side α).internal → ℕ)
    (g : Fin (codeNetE e side β).internal → ℕ)
    (Δ : CNet)
    {k : ℕ}
    (φ : Rule S (S.arity α) k)
    (ψ : Rule S (S.arity β) k)
    (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ)
    (hl : φ.Linear)
    (he : φ.Expanded)
    (hl' : ψ.Linear)
    (he' : ψ.Expanded)
    (hs : side α β = some ⟨k, φ, σ, hl, he, hσ⟩)
    (hs' : side β α = some ⟨k, ψ, σ, hl', he', hσ⟩)
    (hlin : Net.Linear (s((codeNetE e side α).inst (fun i => var (xs i)) f,
      (codeNetE e side β).inst (fun j => var (ys j)) g) ::ₘ Δ)) :
    ∃ (k₀ k₁ : ℕ) (M : CNet) (tφ : Fin (S.arity α) ⊕ Fin k → Term sig ℕ)
      (tψ : Fin (S.arity β) ⊕ Fin k → Term sig ℕ),
      StepsE system (s((codeNetE e side α).inst (fun i => var (xs i)) f,
        (codeNetE e side β).inst (fun j => var (ys j)) g) ::ₘ Δ) M ∧
      Equiv M (plugTermTarget σ tφ tψ xs ys + Δ) ∧
      (∀ p, (codeTranslationE e side).TermTr (gammaTree φ k₀ p) (tφ p)) ∧
      (∀ q, (codeTranslationE e side).TermTr (gammaTree ψ k₁ q) (tψ q))
