/-- A principal net of arity `n`: a tree over the `n` auxiliary ports and some internal wires.
The root of the tree is the root of the net. -/
structure PNet (S : Signature) (n : ℕ) where
  /-- The number of internal wires. -/
  internal : ℕ
  /-- The tree: its leaves are auxiliary ports or ends of internal wires. -/
  tree : Term S (Fin n ⊕ Fin internal)
  /-- Every auxiliary port occurs exactly once. -/
  port_count : ∀ i, tree.vars.count (.inl i) = 1
  /-- Every internal wire has exactly two ends. -/
  internal_count : ∀ w, tree.vars.count (.inr w) = 2

/-- An instance of a principal net: trees plugged into the auxiliary ports, and the internal wires
named by `f`. -/
def inst
    -- the principal net
    (p : PNet S n)
    -- the trees plugged into its auxiliary ports
    (args : Fin n → Term S ℕ)
    -- the names given to its internal wires
    (f : Fin p.internal → ℕ) :
    Term S ℕ :=
  p.tree.bind (Sum.elim args fun w => Term.var (f w))

/-- A principal net is strict when it is not a single wire: its root is the principal port of a
cell. -/
def Strict
    (p : PNet S n) :
    Prop :=
  -- the tree is not a leaf
  ∀ x, p.tree ≠ Term.var x
