theorem decoder_property
    (π : Term sig ℕ)
    (hπ : π.IsPackage)
    (k w k₀ : ℕ)
    (Δ : CNet)
    (hlin : Net.Linear (s(var w, π) ::ₘ Δ))
    (hb : Net.Below k (s(var w, π) ::ₘ Δ))
    (hk₀ : (decomp k π).k ≤ k₀) :
    ∃ M, StepsE system (s(code k π, decoder w k₀) ::ₘ Δ) M ∧
      Equiv M (s(var w, π) ::ₘ Δ)
