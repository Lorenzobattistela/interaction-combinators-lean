def autoMux :
    List (Term sig ℕ) →
    Term sig ℕ
  | [] => mkEra
  | [t] => t
  | t :: t' :: ts => mkDup t (autoMux (t' :: ts))
