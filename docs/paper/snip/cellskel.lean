def cellSel
    (m i : ℕ)
    (t : Term sig ℕ) :
    Term sig ℕ :=
  muxStar (List.replicate i mkEra ++ t :: List.replicate (m - i - 1) mkEra)

def cellSkel
    (Γ : Term sig ℕ)
    (m i : ℕ)
    (ts : List (Term sig ℕ))
    (ℓ : ℕ) :
    Term sig ℕ :=
  transpositor 1 [Γ, cellSel m i (mux (ts ++ [var ℓ])), var ℓ]
