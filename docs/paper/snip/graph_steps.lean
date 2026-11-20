theorem step_is_interaction
    {I : System S}
    (hI : LinearRules I)
    {N M : Net S ℕ}
    (hN : N.Linear)
    (h : StepE I N M)
    {G : Graph S ℕ}
    (hG : N.HasGraph G) :
    ∃ H H', Graph.Interact I G H ∧
      M.HasGraph H' ∧
      H.Iso H'

theorem interaction_is_step
    {I : System S}
    (hI : LinearRules I)
    {N : Net S ℕ}
    (hN : N.Linear)
    {G H : Graph S ℕ}
    (hG : N.HasGraph G)
    (h : Graph.Interact I G H) :
    ∃ M H', StepE I N M ∧
      M.HasGraph H' ∧
      H.Iso H'
