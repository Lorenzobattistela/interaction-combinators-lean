/-- `t'` is a translation of the tree `t`: names are kept, and every cell is replaced by an
instance of the principal net of its symbol. -/
inductive TermTr (Φ : Translation S S') : Term S ℕ → Term S' ℕ → Prop
  -- a leaf is translated to itself
  | var
      (x : ℕ) :
      TermTr Φ (.var x) (.var x)
  -- a cell is translated to an instance of the principal net of its symbol
  | app
      -- the symbol of the cell
      (α : S.Sym)
      -- the trees on its auxiliary ports
      (ts : Fin (S.arity α) → Term S ℕ)
      -- their translations
      (ts' : Fin (S.arity α) → Term S' ℕ)
      -- the names given to the internal wires of this instance: any names
      (f : Fin (Φ.net α).internal → ℕ)
      -- each `ts' i` is a translation of `ts i`
      (h : ∀ i, TermTr Φ (ts i) (ts' i)) :
      -- the instance has the translated trees plugged into its auxiliary ports
      TermTr Φ (.app α ts) ((Φ.net α).inst ts' f)

/-- `e'` is a translation of the equation `e`. -/
def EqTr
    -- the translation
    (Φ : Translation S S')
    -- the equation over `S`
    (e : Sym2 (Term S ℕ))
    -- the equation over `S'`
    (e' : Sym2 (Term S' ℕ)) :
    Prop :=
  -- there are trees `a`, `b` over `S` and `a'`, `b'` over `S'` such that
  ∃ a b a' b',
    -- `e` is the equation `a = b`,
    e = s(a, b) ∧
    -- `e'` is the equation `a' = b'`,
    e' = s(a', b') ∧
    -- `a'` is a translation of `a`,
    Φ.TermTr a a' ∧
    -- and `b'` is a translation of `b`
    Φ.TermTr b b'

/-- `N'` is a translation of the net `N`: equation by equation, and linear. Linearity forces the
internal wires of the instances to have names that are new and pairwise distinct. -/
structure NetTr (Φ : Translation S S') (N : Net S ℕ) (N' : Net S' ℕ) : Prop where
  /-- The equations of `N'` are translations of those of `N`. -/
  rel : Multiset.Rel Φ.EqTr N N'
  /-- The translated net is linear. -/
  linear : N'.Linear
