/-- `con`–`con` annihilation: the auxiliary ports are exchanged. -/
def ruleConCon : Rule sig 2 2 :=
  -- no new wire; left port to right port, right port to left port
  ⟨0, s(l 0, r 1) ::ₘ {s(l 1, r 0)}⟩

/-- `dup`–`dup` annihilation: the auxiliary ports are joined in order. -/
def ruleDupDup : Rule sig 2 2 :=
  -- no new wire; left port to left port, right port to right port
  ⟨0, s(l 0, r 0) ::ₘ {s(l 1, r 1)}⟩

/-- `era`–`era` annihilation: nothing is left. -/
def ruleEraEra : Rule sig 0 0 :=
  -- no new wire, and the empty net
  ⟨0, 0⟩

/-- `era`–`con` and `era`–`dup` commutation: an eraser on each auxiliary port. -/
def ruleEraBin : Rule sig 0 2 :=
  -- no new wire; one `era` on each auxiliary port of the second cell
  ⟨0, s(mkEra, r 0) ::ₘ {s(mkEra, r 1)}⟩

/-- `con`–`dup` commutation: each cell is copied and four wires are created. -/
def ruleConDup : Rule sig 2 2 :=
  -- four new wires; a `dup` on each auxiliary port of the `con`, a `con` on each auxiliary port
  -- of the `dup`; the wire `w 0` joins the left `dup` to the left `con`, `w 1` the left `dup` to
  -- the right `con`, `w 2` the right `dup` to the left `con`, `w 3` the right `dup` to the right
  -- `con`
  ⟨4, s(l 0, mkDup (w 0) (w 1)) ::ₘ s(l 1, mkDup (w 2) (w 3)) ::ₘ
    s(r 0, mkCon (w 0) (w 2)) ::ₘ {s(r 1, mkCon (w 1) (w 3))}⟩

/-- Lafont's system of interaction combinators. -/
def system : System sig where
  rule
    -- the three annihilations
    | con, con => some ruleConCon
    | dup, dup => some ruleDupDup
    | era, era => some ruleEraEra
    -- the three commutations
    | era, con => some ruleEraBin
    | era, dup => some ruleEraBin
    | con, dup => some ruleConDup
    -- the same pairs in the other order have no rule of their own: an equation is unordered
    | _, _ => none
