def Decomposition.Plugs
    {a b : ℕ}
    (D : Decomposition S a b)
    (r : Rule S a b) :
    Prop :=
  ∃ ι : Fin r.internal → Fin (Rule.plug D.φ D.ψ D.σ).internal,
    Function.Injective ι ∧
    Equiv (Rule.plug D.φ D.ψ D.σ).net (r.net.bind fun x => var (Sum.map id (Sum.map id ι) x))
