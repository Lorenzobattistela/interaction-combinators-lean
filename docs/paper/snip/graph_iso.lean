def Iso
    (G H : Graph S ν) :
    Prop :=
  ∃ σ : ℕ → ℕ,
    Set.InjOn σ {c | c ∈ G.cells.map Prod.fst} ∧
    H.cells = G.cells.map (Prod.map σ id) ∧
    H.wires = G.wires.map (Sym2.map (End.mapCell σ)) ∧
    H.loops = G.loops
