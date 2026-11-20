def Reduced
    (r : Rule S a b) :
    Prop :=
  ∀ e ∈ r.net,
    ∃ p t,
      e = s(Term.var p, t) ∧
      ∀ w, p ≠ .inr (.inr w)
