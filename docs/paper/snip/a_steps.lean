/-- Reduction in any number of interactions. -/
abbrev Steps
    (I : System S) :
    Net S ℕ → Net S ℕ → Prop :=
  Relation.ReflTransGen (Step I)

/-- One interaction up to wires: the net is first rewritten into an equivalent one, then two
cells interact. This lets two cells interact when their principal ports are joined by a named
wire, as in `x = α(…)`, `x = β(…)`, which is an active pair of the graph. -/
def StepE
    -- the system
    (I : System S)
    -- the net one starts from, and the net one arrives at
    (N M : Net S ℕ) :
    Prop :=
  -- there is a net `N'` such that
  ∃ N',
    -- `N'` is the same graph as `N`,
    Equiv N N' ∧
    -- and one interaction leads from `N'` to `M`
    Step I N' M

/-- Reduction up to wires, in any number of interactions. -/
abbrev StepsE
    (I : System S) :
    Net S ℕ → Net S ℕ → Prop :=
  Relation.ReflTransGen (StepE I)
