/-- The three combinators. -/
inductive Comb : Type
  -- the constructor, Lafont's `γ`
  | con
  -- the duplicator, Lafont's `δ`
  | dup
  -- the eraser, Lafont's `ε`
  | era
  deriving DecidableEq

/-- The signature of the combinators: `con` and `dup` have two auxiliary ports, `era` none. -/
def sig : Signature where
  Sym := Comb
  arity
    | con => 2
    | dup => 2
    | era => 0

/-- A `con` cell with trees on its auxiliary ports (Lafont's `γ`). -/
def mkCon
    -- the trees on the left and on the right auxiliary port
    (a b : Term sig ν) :
    Term sig ν :=
  .app Comb.con ![a, b]

/-- A `dup` cell with trees on its auxiliary ports (Lafont's `δ`). -/
def mkDup
    -- the trees on the left and on the right auxiliary port
    (a b : Term sig ν) :
    Term sig ν :=
  .app Comb.dup ![a, b]

/-- An `era` cell (Lafont's `ε`). -/
def mkEra : Term sig ν :=
  .app Comb.era ![]
