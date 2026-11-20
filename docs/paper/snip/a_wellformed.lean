/-- An interaction system in the sense of Lafont: rules are linear and reduced, and can be applied
without ambiguity. -/
structure System.WellFormed (I : System S) : Prop where
  /-- Every rule is linear. -/
  linear : ∀ α β r, I.rule α β = some r → r.Linear
  /-- Every right-hand side is a reduced net. -/
  reduced : ∀ α β r, I.rule α β = some r → r.Reduced
  /-- A rule given for `α`, `β` excludes another rule for `β`, `α`. -/
  unique : ∀ α β, α ≠ β → (I.rule α β).isSome → I.rule β α = none
  /-- A rule of a symbol with itself is symmetric: read from the other cell it is the same graph
  (Lafont 1997, page 73), that is, the same net up to wires and up to a permutation of its
  internal wires. The permutation is needed because the internal wires of a rule are named by
  `Fin r.internal`, which leaves no spare name through which `Equiv` could exchange two of them. -/
  symm :
    -- for every rule `r` of a symbol `α` with itself,
    ∀ α r, I.rule α α = some r →
      -- there is a permutation `π` of the wires created by the rule such that
      ∃ π : _root_.Equiv.Perm (Fin r.internal),
        -- the rule read from the other cell is, up to wires, the rule with its wires permuted
        Equiv r.swap.net (r.net.bind fun x => Term.var (Sum.map id (Sum.map id π) x))
