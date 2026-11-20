theorem normal_form_unique
    {I : System S}
    (hI : I.WellFormed)
    {N P Q : Net S ℕ}
    (hN : N.Linear)
    {n m : ℕ}
    (hP : StepE.Normal I P)
    (hs : StepsEN I n N P)
    (hQ : StepE.Normal I Q)
    (ht : StepsEN I m N Q) :
    m = n ∧
    Equiv P Q
