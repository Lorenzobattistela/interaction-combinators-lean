inductive End (ν : Type) : Type
  | port (c i : ℕ)
  | name (x : ν)
  deriving DecidableEq

structure Graph (S : Signature) (ν : Type) where
  cells : Multiset (ℕ × S.Sym)
  wires : Multiset (Sym2 (End ν))
  loops : ℕ

structure WF [DecidableEq ν] (G : Graph S ν) : Prop where
  nodup : (G.cells.map Prod.fst).Nodup
  port : ∀ c α, (c, α) ∈ G.cells → ∀ i ≤ S.arity α, G.ends.count (.port c i) = 1
  cell : ∀ c i, End.port c i ∈ G.ends → ∃ α, (c, α) ∈ G.cells ∧ i ≤ S.arity α
  name : ∀ x, G.ends.count (.name x) ≤ 1
