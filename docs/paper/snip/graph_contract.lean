inductive Contract : Graph S ν → Graph S ν → Prop
  | join
      (x : ν)
      (p q : End ν)
      (C : Multiset (ℕ × S.Sym))
      (W : Multiset (Sym2 (End ν)))
      (n : ℕ) :
      Contract ⟨C, s(.name x, p) ::ₘ s(.name x, q) ::ₘ W, n⟩ ⟨C, s(p, q) ::ₘ W, n⟩
  | loop
      (x : ν)
      (C : Multiset (ℕ × S.Sym))
      (W : Multiset (Sym2 (End ν)))
      (n : ℕ) :
      Contract ⟨C, s(.name x, .name x) ::ₘ W, n⟩ ⟨C, W, n + 1⟩

def Net.HasGraph
    [DecidableEq ν]
    (N : Net S ν)
    (G : Graph S ν) :
    Prop :=
  ∃ (L : List (Term S ν × Term S ν)) (k : ℕ),
    N = Net.ofList L ∧
    Relation.ReflTransGen Graph.Contract (Graph.raw k L) G ∧
    ∀ x, G.ends.count (.name x) ≤ 1
