structure System.WellFormed (I : System S) : Prop where
  linear : ∀ α β r, I.rule α β = some r → r.Linear
  reduced : ∀ α β r, I.rule α β = some r → r.Reduced
  unique : ∀ α β, α ≠ β → (I.rule α β).isSome → I.rule β α = none
  symm :
    ∀ α r, I.rule α α = some r →
      ∃ π : _root_.Equiv.Perm (Fin r.internal),
        Equiv r.swap.net (r.net.bind fun x => Term.var (Sum.map id (Sum.map id π) x))
