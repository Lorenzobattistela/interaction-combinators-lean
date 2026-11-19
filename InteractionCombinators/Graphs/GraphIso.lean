import InteractionCombinators.Graphs.GraphContractUnique

/-!
# The graph of a linear net is unique up to isomorphism

Lafont 1997, Section 1.1, page 71: a net is a graph, and a text of it is not unique. The equations
can be listed in any order, each written either way round, and the cells numbered from anywhere.
This file shows that all these texts give the same graph up to `Graph.Iso` (PLAN.md Stage C,
statement 2).

* `Graph.Iso.refl`, `Graph.Iso.trans`, `Graph.Iso.count_name` (the names, hence the free ports,
  are kept), `Graph.Iso.contract` and `Graph.Iso.contracts` (a contraction of one graph is a
  contraction of an isomorphic graph).
* `Graph.raw_shift_iso` — numbering the cells from another `k` gives an isomorphic raw graph.
* `Graph.raw_swap_iso`, `Graph.raw_flip_iso` — exchanging two blocks of equations, or the two
  sides of an equation, gives an isomorphic raw graph.
* `Graph.raw_iso_of_ofList_eq` — two lists of equations that are texts of one net have
  isomorphic raw graphs.
* `Net.Linear.hasGraph_iso` — two graphs of a linear net are isomorphic.
-/

namespace INet

variable {S : Signature} {ν : Type}

namespace End

theorem mapCell_id : mapCell (ν := ν) id = id := by
  funext e; cases e <;> rfl

theorem mapCell_comp (σ τ : ℕ → ℕ) : mapCell (ν := ν) τ ∘ mapCell σ = mapCell (τ ∘ σ) := by
  funext e; cases e <;> rfl

end End

namespace Graph

/-! ## Basic properties of `Iso` -/

/-- **A graph is isomorphic to itself** (Lafont 1997, page 71). -/
theorem Iso.refl (G : Graph S ν) : G.Iso G :=
  ⟨id, Set.injOn_id _, by simp, by simp [End.mapCell_id], rfl⟩

/-- **Isomorphisms compose** (Lafont 1997, page 71). -/
theorem Iso.trans {G H K : Graph S ν} (h₁ : G.Iso H) (h₂ : H.Iso K) : G.Iso K := by
  obtain ⟨σ, hσ, hc, hw, hl⟩ := h₁
  obtain ⟨τ, hτ, hc', hw', hl'⟩ := h₂
  refine ⟨τ ∘ σ, fun a ha b hb e => hσ ha hb (hτ ?_ ?_ e), ?_, ?_, hl'.trans hl⟩
  · change σ a ∈ H.cells.map Prod.fst
    rw [hc, Multiset.map_map]
    exact Multiset.mem_map.2 (by
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 ha
      exact ⟨p, hp, rfl⟩)
  · change σ b ∈ H.cells.map Prod.fst
    rw [hc, Multiset.map_map]
    exact Multiset.mem_map.2 (by
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hb
      exact ⟨p, hp, rfl⟩)
  · rw [hc', hc, Multiset.map_map, Prod.map_comp_map]
    rfl
  · rw [hw', hw, Multiset.map_map, <- Sym2.map_comp, End.mapCell_comp]

/-- The ends of an isomorphic graph are the ends renamed. -/
theorem Iso.ends_eq {G H : Graph S ν} {σ : ℕ → ℕ}
    (hw : H.wires = G.wires.map (Sym2.map (End.mapCell σ))) :
    H.ends = G.ends.map (End.mapCell σ) := by
  rw [ends_eq_bind, ends_eq_bind, hw, Multiset.bind_map, Multiset.map_bind]
  congr 1
  funext e
  induction e using Sym2.ind with
  | _ p q => simp [Multiset.insert_eq_cons]

/-- **An isomorphism keeps the names** (Lafont 1997, page 71): a name ends as many wires in two
isomorphic graphs. In particular the free ports are the same. -/
theorem Iso.count_name [DecidableEq ν] {G H : Graph S ν} (h : G.Iso H) (x : ν) :
    H.ends.count (.name x) = G.ends.count (.name x) := by
  obtain ⟨σ, -, -, hw, -⟩ := h
  rw [Iso.ends_eq hw, Multiset.count_map, Multiset.count_eq_card_filter_eq]
  congr 1
  apply Multiset.filter_congr
  intro e _
  cases e <;> simp [End.mapCell]

/-- **A contraction of a graph is a contraction of an isomorphic graph** (Lafont 1997, page 71):
if `G` and `G'` are isomorphic and `G` contracts to `H`, then `G'` contracts to a graph
isomorphic to `H`. -/
theorem Iso.contract {G G' H : Graph S ν} (hi : G.Iso G') (h : Contract G H) :
    ∃ H', Contract G' H' ∧ H.Iso H' := by
  obtain ⟨σ, hσ, hc, hw, hl⟩ := hi
  cases h with
  | join x p q C W n =>
    refine ⟨⟨G'.cells, s(End.mapCell σ p, End.mapCell σ q) ::ₘ
      W.map (Sym2.map (End.mapCell σ)), G'.loops⟩, ?_, σ, hσ, hc, by simp, hl⟩
    rw [contract_iff]
    refine ⟨rfl, x, 0, ?_, rfl⟩
    rw [hw]
    simpa [End.mapCell] using EraseName.join (x := x) (End.mapCell σ p) (End.mapCell σ q)
      (W.map (Sym2.map (End.mapCell σ)))
  | loop x C W n =>
    refine ⟨⟨G'.cells, W.map (Sym2.map (End.mapCell σ)), G'.loops + 1⟩, ?_, σ, hσ, hc, rfl,
      by simp [hl]⟩
    rw [contract_iff]
    refine ⟨rfl, x, 1, ?_, rfl⟩
    rw [hw]
    simpa [End.mapCell] using EraseName.loop (x := x) (W.map (Sym2.map (End.mapCell σ)))

/-- **Contractions of a graph are contractions of an isomorphic graph** (Lafont 1997, page 71). -/
theorem Iso.contracts {G G' H : Graph S ν} (hi : G.Iso G')
    (h : Relation.ReflTransGen Contract G H) :
    ∃ H', Relation.ReflTransGen Contract G' H' ∧ H.Iso H' := by
  induction h with
  | refl => exact ⟨G', .refl, hi⟩
  | tail _ s ih =>
    obtain ⟨K', hK', iK⟩ := ih
    obtain ⟨H', s', iH⟩ := iK.contract s
    exact ⟨H', .tail hK' s', iH⟩

end Graph

/-! ## Renumbering the cells of a tree -/

private theorem map_finsum' {ι α β : Type} (s : Finset ι) (g : ι → Multiset α)
    (f : α → β) : (∑ i ∈ s, g i).map f = ∑ i ∈ s, (g i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

namespace Term

/-- The numbers of the cells of a tree numbered from `k` lie in `[k, k + t.size)`. -/
theorem mem_rawCells_range {t : Term S ν} {k : ℕ} {p : ℕ × S.Sym} (hp : p ∈ t.rawCells k) :
    k ≤ p.1 ∧ p.1 < k + t.size := by
  have h := Multiset.mem_map_of_mem Prod.fst hp
  rw [rawCells_fst, Multiset.mem_Ico] at h
  exact h

private theorem childBase_shift {n : ℕ} (k k' : ℕ) (ts : Fin n → Term S ν) (i : Fin n) :
    childBase k' ts i + k = childBase k ts i + k' := by
  unfold childBase; omega

private theorem mem_rawCells_child {α : S.Sym} {ts : Fin (S.arity α) → Term S ν} {k : ℕ}
    {i : Fin (S.arity α)} {p : ℕ × S.Sym} (hp : p ∈ (ts i).rawCells (childBase k ts i)) :
    p ∈ (app α ts).rawCells k :=
  Multiset.mem_cons_of_mem (Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, hp⟩)

/-- **Renumbering the cells of a tree** (Lafont 1997, page 71): a renaming that moves each cell of
`t` numbered from `k` by `k' - k` carries the cells of `t` numbered from `k` to those numbered
from `k'`. The shift is written `σ c + k = c + k'`, which makes sense for `k' < k` too. -/
theorem rawCells_map_shift (σ : ℕ → ℕ) (t : Term S ν) (k k' : ℕ)
    (h : ∀ p ∈ t.rawCells k, σ p.1 + k = p.1 + k') :
    (t.rawCells k).map (Prod.map σ id) = t.rawCells k' := by
  induction t generalizing k k' with
  | var x => rfl
  | app α ts ih =>
    have h0 : σ k = k' := by
      have := h (k, α) (Multiset.mem_cons_self _ _); simp only at this; omega
    simp only [rawCells, Multiset.map_cons, map_finsum', Prod.map, h0, id]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ih i _ _ fun p hp => ?_
    have := h p (mem_rawCells_child hp)
    have := childBase_shift k k' ts i
    omega

/-- The root of a renumbered tree (Lafont 1997, page 71). -/
theorem rootEnd_map_shift (σ : ℕ → ℕ) (t : Term S ν) (k k' : ℕ)
    (h : ∀ p ∈ t.rawCells k, σ p.1 + k = p.1 + k') :
    End.mapCell σ (t.rootEnd k) = t.rootEnd k' := by
  cases t with
  | var x => rfl
  | app α ts =>
    have := h (k, α) (Multiset.mem_cons_self _ _)
    simp only at this
    change End.port (σ k) 0 = End.port k' 0
    congr 1; omega

/-- **The inner wires of a renumbered tree** (Lafont 1997, page 71). -/
theorem rawWires_map_shift (σ : ℕ → ℕ) (t : Term S ν) (k k' : ℕ)
    (h : ∀ p ∈ t.rawCells k, σ p.1 + k = p.1 + k') :
    (t.rawWires k).map (Sym2.map (End.mapCell σ)) = t.rawWires k' := by
  induction t generalizing k k' with
  | var x => rfl
  | app α ts ih =>
    have h0 : σ k = k' := by
      have := h (k, α) (Multiset.mem_cons_self _ _); simp only at this; omega
    have hi : ∀ i : Fin (S.arity α), ∀ p ∈ (ts i).rawCells (childBase k ts i),
        σ p.1 + childBase k ts i = p.1 + childBase k' ts i := fun i p hp => by
      have := h p (mem_rawCells_child hp)
      have := childBase_shift k k' ts i
      omega
    simp only [rawWires, map_finsum', Multiset.map_cons, Sym2.map_mk]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ih i _ _ (hi i), rootEnd_map_shift σ _ _ _ (hi i)]
    simp [End.mapCell, h0]

end Term

namespace Graph

/-! ## Renumbering the cells of a raw graph -/

/-- The numbers of the cells of `raw k L` lie in `[k, k + rawSize L)`. -/
theorem mem_raw_cells_range {k : ℕ} {L : List (Term S ν × Term S ν)} {p : ℕ × S.Sym}
    (hp : p ∈ (raw k L).cells) : k ≤ p.1 ∧ p.1 < k + rawSize L := by
  have h := Multiset.mem_map_of_mem Prod.fst hp
  rw [raw_cells_fst, Multiset.mem_Ico] at h
  exact h

/-- **Renumbering the cells of a raw graph** (Lafont 1997, page 71): a renaming that moves each
cell of `raw k L` by `k' - k` carries its cells and wires to those of `raw k' L`. -/
theorem raw_map_shift (σ : ℕ → ℕ) (L : List (Term S ν × Term S ν)) (k k' : ℕ)
    (h : ∀ p ∈ (raw k L).cells, σ p.1 + k = p.1 + k') :
    (raw k L).cells.map (Prod.map σ id) = (raw k' L).cells ∧
      (raw k L).wires.map (Sym2.map (End.mapCell σ)) = (raw k' L).wires := by
  induction L generalizing k k' with
  | nil => exact ⟨rfl, rfl⟩
  | cons e L ih =>
    obtain ⟨a, b⟩ := e
    have ha : ∀ p ∈ a.rawCells k, σ p.1 + k = p.1 + k' := fun p hp =>
      h p (Multiset.mem_add.2 (.inl (Multiset.mem_add.2 (.inl hp))))
    have hb : ∀ p ∈ b.rawCells (k + a.size), σ p.1 + (k + a.size) = p.1 + (k' + a.size) :=
      fun p hp => by
        have := h p (Multiset.mem_add.2 (.inl (Multiset.mem_add.2 (.inr hp)))); omega
    have hL : ∀ p ∈ (raw (k + a.size + b.size) L).cells,
        σ p.1 + (k + a.size + b.size) = p.1 + (k' + a.size + b.size) :=
      fun p hp => by have := h p (Multiset.mem_add.2 (.inr hp)); omega
    obtain ⟨ic, iw⟩ := ih _ _ hL
    refine ⟨?_, ?_⟩
    · simp only [raw, Multiset.map_add, ic, Term.rawCells_map_shift σ a _ _ ha,
        Term.rawCells_map_shift σ b _ _ hb]
    · simp only [raw, Multiset.map_cons, Multiset.map_add, iw, Sym2.map_mk,
        Term.rawWires_map_shift σ a _ _ ha, Term.rawWires_map_shift σ b _ _ hb,
        Term.rootEnd_map_shift σ a _ _ ha, Term.rootEnd_map_shift σ b _ _ hb]

/-- A renaming that moves each cell of `raw k L` by `k' - k` is an isomorphism onto
`raw k' L` (Lafont 1997, page 71). -/
theorem raw_iso_of_shift (σ : ℕ → ℕ) (L : List (Term S ν × Term S ν)) (k k' : ℕ)
    (h : ∀ p ∈ (raw k L).cells, σ p.1 + k = p.1 + k') : (raw k L).Iso (raw k' L) := by
  obtain ⟨ic, iw⟩ := raw_map_shift σ L k k' h
  refine ⟨σ, fun a ha b hb e => ?_, ic.symm, iw.symm, by rw [raw_loops, raw_loops]⟩
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 ha
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hb
  have := h p hp
  have := h q hq
  omega

/-- **The numbering of the cells does not matter** (Lafont 1997, page 71): numbering the cells
of a list of equations from `k` or from `k'` gives isomorphic raw graphs. -/
theorem raw_shift_iso (L : List (Term S ν × Term S ν)) (k k' : ℕ) :
    (raw k L).Iso (raw k' L) :=
  raw_iso_of_shift (fun c => c + k' - k) L k k' fun p hp => by
    have := (mem_raw_cells_range hp).1
    omega

/-! ## Unions of graphs -/

/-- The union of two graphs: their cells, their wires and their cyclic wires side by side. -/
def union (G H : Graph S ν) : Graph S ν :=
  ⟨G.cells + H.cells, G.wires + H.wires, G.loops + H.loops⟩

theorem union_comm (G H : Graph S ν) : G.union H = H.union G := by
  simp only [union, add_comm]

/-- The number of cells of two lists of equations. -/
theorem rawSize_append (A B : List (Term S ν × Term S ν)) :
    rawSize (A ++ B) = rawSize A + rawSize B := by
  simp [rawSize]

/-- **The raw graph of two lists of equations** (Lafont 1997, page 71) is the union of their raw
graphs, the cells of the second numbered after those of the first. -/
theorem raw_append (k : ℕ) (A B : List (Term S ν × Term S ν)) :
    raw k (A ++ B) = (raw k A).union (raw (k + rawSize A) B) := by
  induction A generalizing k with
  | nil => simp [raw, union, rawSize]
  | cons e A ih =>
    obtain ⟨a, b⟩ := e
    have hs : k + rawSize ((a, b) :: A) = k + a.size + b.size + rawSize A := by
      simp [rawSize]; omega
    rw [hs, List.cons_append]
    simp only [raw, ih, union, add_assoc, Multiset.cons_add]

/-- A cell number of `raw k L` is in `[k, k + rawSize L)`. -/
theorem mem_raw_fst {k : ℕ} {L : List (Term S ν × Term S ν)} {c : ℕ} :
    c ∈ (raw k L).cells.map Prod.fst ↔ k ≤ c ∧ c < k + rawSize L := by
  rw [raw_cells_fst, Multiset.mem_Ico]

/-- Every port at an end of a wire of `raw k L` is a port of one of its cells. -/
theorem raw_portsIn (k : ℕ) (L : List (Term S ν × Term S ν)) (c i : ℕ)
    (h : End.port c i ∈ (raw k L).ends) : c ∈ (raw k L).cells.map Prod.fst := by
  obtain ⟨α, hα, -⟩ := raw_cell k L c i h
  exact Multiset.mem_map.2 ⟨_, hα, rfl⟩

/-- Two renamings that agree on the cells of the ports at the ends of some wires rename these
wires alike. -/
private theorem map_wires_congr {W : Multiset (Sym2 (End ν))} {ρ σ : ℕ → ℕ}
    (h : ∀ c i, End.port c i ∈ W.bind wireEnds → ρ c = σ c) :
    W.map (Sym2.map (End.mapCell ρ)) = W.map (Sym2.map (End.mapCell σ)) := by
  apply Multiset.map_congr rfl
  intro e he
  induction e using Sym2.ind with
  | _ p q =>
    have key : ∀ r ∈ ({p, q} : Multiset (End ν)), End.mapCell ρ r = End.mapCell σ r := by
      intro r hr
      cases r with
      | name x => rfl
      | port c i =>
        change End.port (ρ c) i = End.port (σ c) i
        rw [h c i (Multiset.mem_bind.2 ⟨_, he, by rwa [wireEnds_mk]⟩)]
    simp only [Sym2.map_mk]
    rw [key p (by simp), key q (by simp)]

private theorem mem_fst_of_cells {C C' : Multiset (ℕ × S.Sym)} {σ : ℕ → ℕ}
    (hc : C' = C.map (Prod.map σ id)) {c : ℕ} (h : c ∈ C.map Prod.fst) :
    σ c ∈ C'.map Prod.fst := by
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 h
  rw [hc, Multiset.map_map]
  exact Multiset.mem_map.2 ⟨p, hp, rfl⟩

/-- **Isomorphisms of disjoint graphs make an isomorphism of their union** (Lafont 1997,
page 71), when the wires of each graph end only at its own cells and the cells of the two graphs,
and of their images, have different numbers. -/
theorem Iso.union {G G' H H' : Graph S ν} (hG : G.Iso G') (hH : H.Iso H')
    (pG : ∀ c i, End.port c i ∈ G.ends → c ∈ G.cells.map Prod.fst)
    (pH : ∀ c i, End.port c i ∈ H.ends → c ∈ H.cells.map Prod.fst)
    (d : ∀ c ∈ G.cells.map Prod.fst, c ∉ H.cells.map Prod.fst)
    (d' : ∀ c ∈ G'.cells.map Prod.fst, c ∉ H'.cells.map Prod.fst) :
    (G.union H).Iso (G'.union H') := by
  classical
  obtain ⟨σ, hσ, hc, hw, hl⟩ := hG
  obtain ⟨τ, hτ, hc', hw', hl'⟩ := hH
  let ρ : ℕ → ℕ := fun c => if c ∈ G.cells.map Prod.fst then σ c else τ c
  have eG : ∀ c ∈ G.cells.map Prod.fst, ρ c = σ c := fun c h => by
    simp only [ρ]; split_ifs
    rfl
  have eH : ∀ c ∈ H.cells.map Prod.fst, ρ c = τ c := fun c h => by
    simp only [ρ]; split_ifs with h'
    · exact absurd h (d c h')
    · rfl
  refine ⟨ρ, ?_, ?_, ?_, by
    change G'.loops + H'.loops = G.loops + H.loops
    rw [hl, hl']⟩
  · intro a ha b hb e
    change a ∈ (G.cells + H.cells).map Prod.fst at ha
    change b ∈ (G.cells + H.cells).map Prod.fst at hb
    rw [Multiset.map_add, Multiset.mem_add] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [eG a ha, eG b hb] at e
      exact hσ ha hb e
    · rw [eG a ha, eH b hb] at e
      exact absurd (by rw [e]; exact mem_fst_of_cells hc' hb) (d' _ (mem_fst_of_cells hc ha))
    · rw [eH a ha, eG b hb] at e
      exact absurd (by rw [← e]; exact mem_fst_of_cells hc' ha) (d' _ (mem_fst_of_cells hc hb))
    · rw [eH a ha, eH b hb] at e
      exact hτ ha hb e
  · change G'.cells + H'.cells = (G.cells + H.cells).map _
    rw [Multiset.map_add, hc, hc']
    congr 1 <;> refine Multiset.map_congr rfl fun p hp => Prod.ext ?_ rfl
    · exact (eG _ (Multiset.mem_map_of_mem _ hp)).symm
    · exact (eH _ (Multiset.mem_map_of_mem _ hp)).symm
  · change G'.wires + H'.wires = (G.wires + H.wires).map _
    rw [Multiset.map_add, hw, hw', map_wires_congr (W := G.wires) (fun c i h => eG c (pG c i h)),
      map_wires_congr (W := H.wires) (fun c i h => eH c (pH c i h))]

/-! ## Changing the text -/

/-- **Equations can be replaced block by block** (Lafont 1997, page 71): isomorphic raw graphs
of a first block and of the rest give isomorphic raw graphs of the whole list, when the first
blocks have the same number of cells. -/
theorem raw_append_iso {k : ℕ} {A A' B B' : List (Term S ν × Term S ν)}
    (hA : (raw k A).Iso (raw k A')) (hB : (raw (k + rawSize A) B).Iso (raw (k + rawSize A) B'))
    (hs : rawSize A = rawSize A') : (raw k (A ++ B)).Iso (raw k (A' ++ B')) := by
  rw [raw_append, raw_append, ← hs]
  refine hA.union hB (raw_portsIn _ _) (raw_portsIn _ _) ?_ ?_ <;>
  · intro c h h'
    rw [mem_raw_fst] at h h'
    omega

/-- **The order of two blocks of equations does not matter** (Lafont 1997, page 71). -/
theorem raw_swap_iso (k : ℕ) (A B : List (Term S ν × Term S ν)) :
    (raw k (A ++ B)).Iso (raw k (B ++ A)) := by
  rw [raw_append, raw_append, union_comm (raw k B)]
  refine (raw_shift_iso A k (k + rawSize B)).union (raw_shift_iso B (k + rawSize A) k)
    (raw_portsIn _ _) (raw_portsIn _ _) ?_ ?_ <;>
  · intro c h h'
    rw [mem_raw_fst] at h h'
    omega

/-- **The orientation of an equation does not matter** (Lafont 1997, page 71): `a = b` and
`b = a` have isomorphic raw graphs. -/
theorem raw_flip_iso (k : ℕ) (a b : Term S ν) : (raw k [(a, b)]).Iso (raw k [(b, a)]) := by
  let σ : ℕ → ℕ := fun c => if c < k + a.size then c + b.size else c - a.size
  have ha : ∀ p ∈ a.rawCells k, σ p.1 + k = p.1 + (k + b.size) := fun p hp => by
    have := Term.mem_rawCells_range hp
    simp only [σ]; split_ifs <;> omega
  have hb : ∀ p ∈ b.rawCells (k + a.size), σ p.1 + (k + a.size) = p.1 + k := fun p hp => by
    have := Term.mem_rawCells_range hp
    simp only [σ]; split_ifs <;> omega
  refine ⟨σ, ?_, ?_, ?_, rfl⟩
  · intro c hc d hd e
    have hc' : c ∈ (raw k [(a, b)]).cells.map Prod.fst := hc
    have hd' : d ∈ (raw k [(a, b)]).cells.map Prod.fst := hd
    rw [mem_raw_fst] at hc' hd'
    simp only [rawSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hc' hd'
    simp only [σ] at e
    split_ifs at e <;> omega
  · simp only [raw, Multiset.map_add, Term.rawCells_map_shift σ a _ _ ha,
      Term.rawCells_map_shift σ b _ _ hb, add_zero]
    exact add_comm _ _
  · simp only [raw, Multiset.map_cons, Multiset.map_add, Sym2.map_mk,
      Term.rawWires_map_shift σ a _ _ ha, Term.rawWires_map_shift σ b _ _ hb,
      Term.rootEnd_map_shift σ a _ _ ha, Term.rootEnd_map_shift σ b _ _ hb, add_zero]
    congr 1
    · exact Sym2.eq_swap
    · exact add_comm _ _

/-- **Two texts of one net, as lists of equations up to permutation and orientation, have
isomorphic raw graphs** (Lafont 1997, page 71), the cells numbered from any `k` and `k'`. -/
theorem raw_iso_of_perm (L L' : List (Term S ν × Term S ν))
    (h : (L.map fun e => s(e.1, e.2)).Perm (L'.map fun e => s(e.1, e.2))) (k k' : ℕ) :
    (raw k L).Iso (raw k' L') := by
  induction L generalizing L' k k' with
  | nil =>
    obtain rfl : L' = [] := by simpa using h.symm
    exact Iso.refl _
  | cons e L ih =>
    obtain ⟨a, b⟩ := e
    have hm : s(a, b) ∈ L'.map fun e => s(e.1, e.2) := h.subset (List.mem_cons_self ..)
    obtain ⟨⟨c, d⟩, he', hee⟩ := List.mem_map.1 hm
    obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem he'
    simp only at hee
    have hp : (L.map fun e => s(e.1, e.2)).Perm ((L₁ ++ L₂).map fun e => s(e.1, e.2)) := by
      have h2 := h
      simp only [List.map_cons, List.map_append, hee] at h2
      rw [List.map_append]
      exact (h2.trans List.perm_middle).cons_inv
    have stepA : (raw k ((a, b) :: L)).Iso (raw k ((a, b) :: (L₁ ++ L₂))) :=
      raw_append_iso (A := [(a, b)]) (A' := [(a, b)]) (Iso.refl _) (ih _ hp _ _) rfl
    have stepB : (raw k ((a, b) :: (L₁ ++ L₂))).Iso (raw k ((c, d) :: (L₁ ++ L₂))) := by
      rcases Sym2.eq_iff.1 hee with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
        exact Iso.refl _
      · rw [h1, h2]
        exact raw_append_iso (A := [(a, b)]) (A' := [(b, a)]) (raw_flip_iso k a b) (Iso.refl _)
          (by simp [rawSize, add_comm])
    have stepC : (raw k ((c, d) :: (L₁ ++ L₂))).Iso (raw k (L₁ ++ (c, d) :: L₂)) := by
      rw [show (c, d) :: (L₁ ++ L₂) = ([(c, d)] ++ L₁) ++ L₂ by simp,
        show L₁ ++ (c, d) :: L₂ = (L₁ ++ [(c, d)]) ++ L₂ by simp]
      exact raw_append_iso (raw_swap_iso _ _ _) (Iso.refl _)
        (by simp only [rawSize_append]; exact add_comm _ _)
    exact ((stepA.trans stepB).trans stepC).trans (raw_shift_iso _ k k')

/-- **The raw graph does not depend on the text** (Lafont 1997, page 71; PLAN.md Stage C,
statement 2): two lists of equations that are texts of one net have isomorphic raw graphs, the
cells numbered from any `k` and `k'`. -/
theorem raw_iso_of_ofList_eq {L L' : List (Term S ν × Term S ν)}
    (h : Net.ofList L = Net.ofList L') (k k' : ℕ) : (raw k L).Iso (raw k' L') :=
  raw_iso_of_perm L L' (Multiset.coe_eq_coe.1 h) k k'

end Graph

/-- **The graph of a linear net is unique up to isomorphism** (Lafont 1997, page 71; PLAN.md
Stage C, statement 2): two graphs of a linear net, read off any two of its texts with the cells
numbered from anywhere and the names erased in any order, are isomorphic. -/
theorem Net.Linear.hasGraph_iso [DecidableEq ν] {N : Net S ν} (hN : N.Linear)
    {G G' : Graph S ν} (h : N.HasGraph G) (h' : N.HasGraph G') : G.Iso G' := by
  obtain ⟨L, k, hL, hc, hn⟩ := h
  obtain ⟨L', k', hL', hc', hn'⟩ := h'
  obtain ⟨H, hH, iH⟩ := (Graph.raw_iso_of_ofList_eq (hL.symm.trans hL') k k').contracts hc
  have nH : ∀ x, H.ends.count (.name x) ≤ 1 := fun x => (iH.count_name x).trans_le (hn x)
  rwa [Graph.contracts_unique (Graph.raw_count_name_le_two k' L' (hL' ▸ hN)) hH hc' nH hn']
    at iH

end INet
