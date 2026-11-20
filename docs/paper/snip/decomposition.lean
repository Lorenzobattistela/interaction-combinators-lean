structure Decomposition
    (S : Signature)
    (a b : ℕ) where
  k : ℕ
  φ : Rule S a k
  ψ : Rule S b k
  σ : Equiv.Perm (Fin k)

def plug
    (φ : Rule S a k)
    (ψ : Rule S b k)
    (σ : Equiv.Perm (Fin k)) :
    Rule S a b where
  internal := k + φ.internal + ψ.internal
  net := φ.net.bind (fun x => var (plugL x)) + ψ.net.bind (fun x => var (plugR σ x))
