/-- The right-hand side of an interaction rule. Its names are the `a` auxiliary ports of the first
cell, the `b` auxiliary ports of the second, and `internal` new wires. -/
structure Rule (S : Signature) (a b : ℕ) where
  /-- The number of wires created by the rule. -/
  internal : ℕ
  /-- The net that replaces the two cells. -/
  net : Net S (Fin a ⊕ Fin b ⊕ Fin internal)

/-- The right-hand side of a rule, with trees plugged into the auxiliary ports and the internal
wires named by `f`. -/
def Rule.inst
    -- the rule, between a cell with `a` auxiliary ports and a cell with `b`
    {a b : ℕ}
    (r : Rule S a b)
    -- the trees plugged into the auxiliary ports of the first cell
    (as : Fin a → Term S ℕ)
    -- the trees plugged into the auxiliary ports of the second cell
    (bs : Fin b → Term S ℕ)
    -- the names given to the wires created by the rule
    (f : Fin r.internal → ℕ) :
    Net S ℕ :=
  r.net.bind (Sum.elim as (Sum.elim bs fun i => Term.var (f i)))

/-- In the right-hand side of a rule, every auxiliary port of the two cells occurs exactly once and
every internal wire exactly twice. -/
structure Linear (r : Rule S a b) : Prop where
  -- every auxiliary port of the first cell occurs exactly once
  left : ∀ i, r.net.vars.count (.inl i) = 1
  -- every auxiliary port of the second cell occurs exactly once
  right : ∀ j, r.net.vars.count (.inr (.inl j)) = 1
  -- every wire created by the rule has exactly two ends
  internal : ∀ w, r.net.vars.count (.inr (.inr w)) = 2

/-- The right-hand side is a reduced net, written as trees rooted at the auxiliary ports: every
equation has an auxiliary port on one side. Together with linearity this excludes pairs of cells
plugged by their principal ports, vicious circles and cyclic wires. -/
def Reduced
    (r : Rule S a b) :
    Prop :=
  -- for every equation `e` of the right-hand side,
  ∀ e ∈ r.net,
    -- there are a name `p` and a tree `t` such that
    ∃ p t,
      -- the equation is `p = t`,
      e = s(Term.var p, t) ∧
      -- and `p` is an auxiliary port of one of the two cells, not a wire created by the rule
      ∀ w, p ≠ .inr (.inr w)

/-- The same rule read from the other cell: the two groups of auxiliary ports are exchanged. -/
def swap
    (r : Rule S a b) :
    Rule S b a where
  -- the same number of wires is created
  internal := r.internal
  -- the ports of the first cell become those of the second and conversely; the wires are kept
  net := r.net.bind fun p =>
    Term.var (Sum.elim (fun i => .inr (.inl i)) (Sum.elim .inl fun w => .inr (.inr w)) p)
