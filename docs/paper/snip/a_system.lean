/-- An interaction system: at most one rule for each pair of symbols. An equation is unordered, so
a rule given for `α`, `β` also applies to `β`, `α`. -/
structure System (S : Signature) where
  /-- The rule for a pair of symbols, if any. -/
  rule : (α β : S.Sym) → Option (Rule S (S.arity α) (S.arity β))

/-- One interaction: two cells plugged by their principal ports are replaced by the right-hand
side of their rule. The wires the rule creates get names not used in the net. -/
inductive Step (I : System S) : Net S ℕ → Net S ℕ → Prop
  | mk
      -- the symbols of the two cells, and the rule of the system for them
      (α β : S.Sym)
      (r : Rule S (S.arity α) (S.arity β))
      (hr : I.rule α β = some r)
      -- the trees on the auxiliary ports of the first cell
      (as : Fin (S.arity α) → Term S ℕ)
      -- the trees on the auxiliary ports of the second cell
      (bs : Fin (S.arity β) → Term S ℕ)
      -- the rest of the net
      (Δ : Net S ℕ)
      -- the names given to the wires created by the rule: pairwise distinct,
      (f : Fin r.internal → ℕ)
      (hf : Function.Injective f)
      -- and not used in the net one starts from
      (hfresh : ∀ i, f i ∉ Net.vars (s(Term.app α as, Term.app β bs) ::ₘ Δ)) :
      -- the equation between the two cells is replaced by the right-hand side of the rule
      Step I (s(Term.app α as, Term.app β bs) ::ₘ Δ) (r.inst as bs f + Δ)
