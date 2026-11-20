theorem equiv_iff_graph_iso
    {N M : Net S ℕ}
    (hN : N.Linear)
    (hM : M.Linear)
    {G G' : Graph S ℕ}
    (hG : N.HasGraph G)
    (hG' : M.HasGraph G') :
    Equiv N M ↔ G.Iso G'
