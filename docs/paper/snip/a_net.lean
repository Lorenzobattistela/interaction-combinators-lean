/-- A net: a multiset of unordered equations between trees. -/
abbrev Net (S : Signature) (ν : Type) := Multiset (Sym2 (Term S ν))

/-- Every name occurs at most twice: once at each end of a wire, or once for a free port. -/
def Linear
    [DecidableEq ν]
    (N : Net S ν) :
    Prop :=
  ∀ x, N.vars.count x ≤ 2
