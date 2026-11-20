def System.SidesPlug
    {S : Signature}
    (I : System S)
    (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α))) :
    Prop :=
  ∀ {α β : S.Sym} {r : Rule S (S.arity α) (S.arity β)}, I.rule α β = some r →
    ∃ (k : ℕ) (φ : Rule S (S.arity α) k) (ψ : Rule S (S.arity β) k) (σ : Equiv.Perm (Fin k))
      (hσ : Function.Involutive σ) (hl : φ.Linear) (he : φ.Expanded)
      (hl' : ψ.Linear) (he' : ψ.Expanded),
      side α β = some ⟨k, φ, σ, hl, he, hσ⟩ ∧
      side β α = some ⟨k, ψ, σ, hl', he', hσ⟩ ∧
      (⟨k, φ, ψ, σ⟩ : Decomposition S (S.arity α) (S.arity β)).Plugs r
