def mux :
    List (Term sig ℕ) →
    Term sig ℕ
  | [] => mkEra
  | [t] => t
  | t :: t' :: ts => mkCon t (mux (t' :: ts))

def muxStar :
    List (Term sig ℕ) →
    Term sig ℕ
  | [] => mkEra
  | [u] => u
  | u :: u' :: us => mkCon (muxStar (u' :: us)) u
