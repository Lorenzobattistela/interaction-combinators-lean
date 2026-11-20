theorem proposition_1
    {I : System S}
    (hI : I.WellFormed)
    {N P P' : Net S ℕ}
    (hN : N.Linear)
    (h : StepE I N P)
    (h' : StepE I N P') :
    Equiv P P' ∨
    ∃ Q Q', StepE I P Q ∧ StepE I P' Q' ∧
      Equiv Q Q'
