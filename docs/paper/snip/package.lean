def Term.IsPackage
    {S : Signature}
    (π : Term S ℕ) :
    Prop :=
  ∀ x ∈ π.vars, π.vars.count x = 2
