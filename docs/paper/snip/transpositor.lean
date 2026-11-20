def pairCon :
    ℕ →
    List (Term sig ℕ) →
    List (Term sig ℕ)
  | 0, ts => ts
  | p + 1, t :: t' :: ts => mkCon t t' :: pairCon p ts
  | _ + 1, ts => ts

def transpositor
    (p : ℕ)
    (ts : List (Term sig ℕ)) :
    Term sig ℕ :=
  autoMux (pairCon p ts)
