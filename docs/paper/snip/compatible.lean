def Compatible
    (Φ : Translation S S')
    (I : System S)
    (I' : System S') :
    Prop :=
  ∀ (α β : S.Sym) (r : Rule S (S.arity α) (S.arity β)),
    I.rule α β = some r →
    ∀
      (xs : Fin (S.arity α) → ℕ)
      (ys : Fin (S.arity β) → ℕ)
      (f : Fin (Φ.net α).internal → ℕ)
      (g : Fin (Φ.net β).internal → ℕ),
      Net.Linear ({s((Φ.net α).inst (fun i => .var (xs i)) f,
        (Φ.net β).inst (fun j => .var (ys j)) g)} : Net S' ℕ) →
      ∃ (M N' : Net S' ℕ) (h : Fin r.internal → ℕ),
        StepsE I' {s((Φ.net α).inst (fun i => .var (xs i)) f,
          (Φ.net β).inst (fun j => .var (ys j)) g)} M ∧
        Equiv M N' ∧
        Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N'
