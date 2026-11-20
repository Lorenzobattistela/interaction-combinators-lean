def menu
    (πs : List (Term sig ℕ)) :
    Term sig ℕ :=
  mux πs

def selector
    (n i x : ℕ) :
    Term sig ℕ :=
  muxStar (List.replicate i mkEra ++ var x :: List.replicate (n - i - 1) mkEra)
