theorem proposition_4_bounds
    {I : System S}
    {I' : System S'}
    (hI : LinearRules I)
    (hI' : LinearRules I')
    {Φ : Translation S S'}
    {L U : ℕ}
    (hΦ : Φ.CompatibleWithin I I' L U)
    {n : ℕ}
    {N M : Net S ℕ}
    {N' : Net S' ℕ}
    (h : StepsEN I n N M)
    (hT : Φ.NetTr N N') :
    ∃ n' M₁ M', StepsEN I' n' N' M₁ ∧
      L * n ≤ n' ∧
      n' ≤ U * n ∧
      Equiv M₁ M' ∧
      Φ.NetTr M M'
