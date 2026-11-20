abbrev Net (S : Signature) (ν : Type) := Multiset (Sym2 (Term S ν))

def Linear
    [DecidableEq ν]
    (N : Net S ν) :
    Prop :=
  ∀ x, N.vars.count x ≤ 2
