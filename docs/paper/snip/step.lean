inductive Step (I : System S) : Net S ℕ → Net S ℕ → Prop
  | mk
      (α β : S.Sym)
      (r : Rule S (S.arity α) (S.arity β))
      (hr : I.rule α β = some r)
      (as : Fin (S.arity α) → Term S ℕ)
      (bs : Fin (S.arity β) → Term S ℕ)
      (Δ : Net S ℕ)
      (f : Fin r.internal → ℕ)
      (hf : Function.Injective f)
      (hfresh : ∀ i, f i ∉ Net.vars (s(Term.app α as, Term.app β bs) ::ₘ Δ)) :
      Step I (s(Term.app α as, Term.app β bs) ::ₘ Δ) (r.inst as bs f + Δ)

def StepE
    (I : System S)
    (N M : Net S ℕ) :
    Prop :=
  ∃ N',
    Equiv N N' ∧
    Step I N' M
