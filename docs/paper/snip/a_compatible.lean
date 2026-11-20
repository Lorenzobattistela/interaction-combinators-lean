/-- A translation of interaction systems (Lafont, Section 1.7): for every rule, the translations of
the two cells, plugged by their roots, reduce to a translation of the right-hand side. The
auxiliary ports of the two cells are the names `xs` and `ys`. Reduction is up to wires
(`StepsE`): cells whose principal ports are joined by a named wire may interact. -/
def Compatible
    -- the translation: a principal net over `S'` for each symbol of `S`
    (Φ : Translation S S')
    -- the system that is translated, over `S`
    (I : System S)
    -- the system it is translated into, over `S'`
    (I' : System S') :
    Prop :=
  -- for all symbols `α`, `β` of `S` and every net `r` such that
  ∀ (α β : S.Sym) (r : Rule S (S.arity α) (S.arity β)),
    -- `r` is the right-hand side of the rule of `I` for an `α` cell against a `β` cell,
    I.rule α β = some r →
    ∀
      -- for all names `xs` of the auxiliary ports of the `α` cell,
      (xs : Fin (S.arity α) → ℕ)
      -- all names `ys` of the auxiliary ports of the `β` cell,
      (ys : Fin (S.arity β) → ℕ)
      -- all names `f` of the internal wires of the translation of `α`,
      (f : Fin (Φ.net α).internal → ℕ)
      -- and all names `g` of the internal wires of the translation of `β`,
      (g : Fin (Φ.net β).internal → ℕ),
      -- if the translation of `α` plugged by its root into the root of the translation of `β`
      -- is a linear net, that is, if no name among `xs`, `ys`, `f`, `g` occurs more than twice,
      Net.Linear ({s((Φ.net α).inst (fun i => .var (xs i)) f,
        (Φ.net β).inst (fun j => .var (ys j)) g)} : Net S' ℕ) →
      -- then there are two nets `M`, `N'` over `S'`, and names `h` for the wires created by the
      -- rule, such that
      ∃ (M N' : Net S' ℕ) (h : Fin r.internal → ℕ),
        -- in `I'`, the two translations plugged by their roots reduce, up to wires, to `M`,
        StepsE I' {s((Φ.net α).inst (fun i => .var (xs i)) f,
          (Φ.net β).inst (fun j => .var (ys j)) g)} M ∧
        -- `M` is the same graph as `N'`,
        Equiv M N' ∧
        -- and `N'` is a translation of the right-hand side of the rule, taken with the same
        -- names `xs` and `ys` on the auxiliary ports of the two cells and with `h` on its wires
        Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N'
