def codeCell
    (m k : ℕ)
    (P x : Term sig ℕ)
    (ts : List (Term sig ℕ))
    (ℓ u w y k₀ : ℕ) :
    CNet :=
  s(x, copier [decoder w k₀, var u]) ::ₘ s(var w, selector m k y) ::ₘ
    s(P, cellSkel (var y) m k (var u :: ts) ℓ) ::ₘ 0
