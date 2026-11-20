def codeTreeE
    (α : S.Sym) :
    Term sig ℕ :=
  cellSkel (menu (codeCellMenuE e side α (S.arity α + 1))) n (e α)
    (code (codeKeyE e side α) (menu (codeMenusE e side (codeMenuBaseE e side α))) ::
      List.ofFn fun j : Fin (S.arity α) => var (j : ℕ)) (S.arity α)
