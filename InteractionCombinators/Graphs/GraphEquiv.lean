import InteractionCombinators.Graphs.GraphIso

/-!
# Equivalent linear nets have isomorphic graphs

Lafont 1997, Section 1.1, page 71: a net is a graph, and the texts `x = t, …` with `x` occurring
again elsewhere, and the same text with `t` plugged into that other occurrence, are the same
graph. This file proves the direction "`Equiv` implies `Iso`" of PLAN.md Stage C, statement 3.

* `Graph.Iso.symm` — an isomorphism can be reversed, when the wires of the graph end only at its
  own cells.
* `Term.raw_subst` — plugging `t` into the occurrence of `x` in `a` renumbers the cells of `a`
  and of `t` and joins the wire of `x` to the root of `t`.
* `Graph.raw_wire_contract` — the raw graph of `x = t, a = b, Δ` contracts, by erasing `x`, to a
  graph isomorphic to the raw graph of `a[t/x] = b, Δ`.
* `Wire.hasGraph_iso` — a wire substitution keeps the graph up to `Iso`.
* `Net.Linear.equiv_hasGraph_iso` — equivalent linear nets have isomorphic graphs.
-/

namespace INet

variable {S : Signature} {ν : Type}

/-! ## Reversing an isomorphism -/

namespace Graph

private theorem map_wires_congr' {W : Multiset (Sym2 (End ν))} {ρ σ : ℕ → ℕ}
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

/-- **An isomorphism can be reversed** (Lafont 1997, page 71), when every port at an end of a wire
of `G` is a port of a cell of `G`. This holds for well-formed graphs and for raw graphs. -/
theorem Iso.symm {G H : Graph S ν} (h : G.Iso H)
    (hG : ∀ c i, End.port c i ∈ G.ends → c ∈ G.cells.map Prod.fst) : H.Iso G := by
  obtain ⟨σ, hσ, hc, hw, hl⟩ := h
  let s : Set ℕ := {c | c ∈ G.cells.map Prod.fst}
  let τ := Function.invFunOn σ s
  have hτ : ∀ c ∈ s, τ (σ c) = c := fun c hc => hσ.leftInvOn_invFunOn hc
  refine ⟨τ, ?_, ?_, ?_, hl.symm⟩
  · intro a ha b hb e
    change a ∈ H.cells.map Prod.fst at ha
    change b ∈ H.cells.map Prod.fst at hb
    rw [hc, Multiset.map_map] at ha hb
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 ha
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hb
    have hp' : p.1 ∈ s := Multiset.mem_map_of_mem _ hp
    have hq' : q.1 ∈ s := Multiset.mem_map_of_mem _ hq
    change τ (σ p.1) = τ (σ q.1) at e
    rw [hτ _ hp', hτ _ hq'] at e
    change σ p.1 = σ q.1
    rw [e]
  · rw [hc, Multiset.map_map]
    conv_lhs => rw [← Multiset.map_id G.cells]
    refine Multiset.map_congr rfl fun p hp => ?_
    simp only [Function.comp_apply, Prod.map, id]
    rw [hτ _ (Multiset.mem_map_of_mem _ hp)]
  · rw [hw, Multiset.map_map, ← Sym2.map_comp, End.mapCell_comp]
    rw [map_wires_congr' (ρ := τ ∘ σ) (σ := id) fun c i hm => hτ c (hG c i hm),
      End.mapCell_id, Sym2.map_id, Multiset.map_id]

/-- The wires of a well-formed graph end only at its cells. -/
theorem WF.portsIn [DecidableEq ν] {G : Graph S ν} (h : G.WF) (c i : ℕ)
    (hm : End.port c i ∈ G.ends) : c ∈ G.cells.map Prod.fst := by
  obtain ⟨α, hα, -⟩ := h.cell c i hm
  exact Multiset.mem_map.2 ⟨_, hα, rfl⟩

end Graph

/-! ## Plugging an end into a name -/

variable [DecidableEq ν]

namespace End

/-- Replace the name `x` by the end `r`. -/
def substName (x : ν) (r : End ν) : End ν → End ν
  | port c i => port c i
  | name y => if y = x then r else name y

@[simp] theorem substName_port (x : ν) (r : End ν) (c i : ℕ) :
    substName x r (port c i) = port c i := rfl

@[simp] theorem substName_self (x : ν) (r : End ν) : substName x r (name x) = r := by
  simp [substName]

theorem substName_of_ne {x : ν} (r : End ν) {e : End ν} (h : e ≠ name x) : substName x r e = e := by
  cases e with
  | port c i => rfl
  | name y =>
    have : y ≠ x := fun h' => h (h' ▸ rfl)
    simp [substName, this]

end End

namespace Graph

/-- Wires that do not end at the name `x` are kept when `x` is replaced. -/
theorem map_substName_of_count {W : Multiset (Sym2 (End ν))} {x : ν} (r : End ν)
    (h : (W.bind wireEnds).count (.name x) = 0) :
    W.map (Sym2.map (End.substName x r)) = W := by
  conv_rhs => rw [← Multiset.map_id W]
  refine Multiset.map_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | _ p q =>
    have hn : End.name x ∉ W.bind wireEnds := Multiset.count_eq_zero.1 h
    have hp : p ≠ .name x := fun e => hn (Multiset.mem_bind.2 ⟨_, he, by simp [e]⟩)
    have hq : q ≠ .name x := fun e => hn (Multiset.mem_bind.2 ⟨_, he, by simp [e]⟩)
    simp [End.substName_of_ne r hp, End.substName_of_ne r hq]

/-- **Erasing a name joins its two wires** (Lafont 1997, page 71): if `x` ends the wire to `r`
and exactly one other wire, contracting `x` replaces `x` by `r` in the other wire. -/
theorem contract_substName (C : Multiset (ℕ × S.Sym)) (W : Multiset (Sym2 (End ν))) (n : ℕ)
    (x : ν) (r : End ν) (hW : (W.bind wireEnds).count (.name x) = 1) :
    Contract ⟨C, s(.name x, r) ::ₘ W, n⟩ ⟨C, W.map (Sym2.map (End.substName x r)), n⟩ := by
  have hm : End.name x ∈ W.bind wireEnds := Multiset.count_pos.1 (by omega)
  obtain ⟨e, he, hxe⟩ := Multiset.mem_bind.1 hm
  induction e using Sym2.ind with
  | _ p q =>
    obtain ⟨W₀, rfl⟩ := Multiset.exists_cons_of_mem he
    have hpq : s(p, q) = s(.name x, if p = .name x then q else p) := by
      rw [wireEnds_mk] at hxe
      split_ifs with h
      · rw [h]
      · have : q = .name x := by simpa [Multiset.insert_eq_cons, Ne.symm h, eq_comm] using hxe
        rw [this, Sym2.eq_swap]
    rw [hpq] at hW ⊢
    set q' := if p = .name x then q else p
    rw [Multiset.cons_bind, wireEnds_mk, Multiset.count_add] at hW
    have hq' : q' ≠ .name x := by
      intro e
      rw [e] at hW
      simp [Multiset.insert_eq_cons] at hW
      omega
    have h0 : (W₀.bind wireEnds).count (.name x) = 0 := by
      simp [Multiset.insert_eq_cons, Ne.symm hq'] at hW
      exact Multiset.count_eq_zero.2 (by simpa using hW)
    rw [Multiset.map_cons, map_substName_of_count r h0, Sym2.map_mk, End.substName_self,
      End.substName_of_ne r hq']
    exact Contract.join x r q' C W₀ n

end Graph

/-! ## Sums over the subtrees -/

private theorem map_finsum'' {ι α β : Type} (s : Finset ι) (g : ι → Multiset α)
    (f : α → β) : (∑ i ∈ s, g i).map f = ∑ i ∈ s, (g i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private theorem sum_ite_lt_add_le {n : ℕ} (f : Fin n → ℕ) (j : Fin n) (P : Fin n → Prop)
    [DecidablePred P] (hP : ∀ l, l ≤ j → P l) :
    (∑ l, if l < j then f l else 0) + f j ≤ ∑ l, if P l then f l else 0 := by
  have : f j = ∑ l, if l = j then f l else 0 := by simp
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases h1 : l < j
  · have h2 : l ≠ j := ne_of_lt h1
    simp [h1, h2, hP l h1.le]
  · by_cases h2 : l = j
    · subst h2; simp [hP l le_rfl]
    · simp [h1, h2]

private theorem exists_eq_one_of_sum {n : ℕ} (f : Fin n → ℕ) (h : ∑ i, f i = 1) :
    ∃ i, f i = 1 ∧ ∀ j, j ≠ i → f j = 0 := by
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h ▸ one_ne_zero : ∑ i, f i ≠ 0)
  have e := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
  rw [h] at e
  refine ⟨i, by omega, fun j hj => ?_⟩
  have h0 : ∑ l ∈ Finset.univ.erase i, f l = 0 := by omega
  exact (Finset.sum_eq_zero_iff.1 h0) j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)

private theorem sum_update_add {β : Type} {n : ℕ} (F G : Fin n → Multiset β) (X : Multiset β)
    (i : Fin n) (hi : F i + X = G i) (hj : ∀ j, j ≠ i → F j = G j) :
    ∑ j, F j + X = ∑ j, G j := by
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ i),
    ← Finset.add_sum_erase _ G (Finset.mem_univ i),
    ← hi, Finset.sum_congr rfl fun j hj' => hj j (Finset.ne_of_mem_erase hj')]
  abel

/-! ## Plugging a tree into a name -/

namespace Term

/-- The number of cells of `r.subst x t`: one copy of `t` for each occurrence of `x`. -/
theorem size_subst (r : Term S ν) (x : ν) (t : Term S ν) :
    (r.subst x t).size = r.size + r.vars.count x * t.size := by
  induction r with
  | var y =>
    by_cases h : y = x
    · subst h; simp [subst, size]
    · simp [subst, size, h, Ne.symm h]
  | app α ts ih =>
    change (app α fun i => (ts i).subst x t).size = _
    simp only [size, ih, vars_app, Multiset.count_sum', Finset.sum_add_distrib, Finset.sum_mul]
    ring

/-- The name `x` ends as many wires of a tree, its root included, as it has occurrences. -/
theorem count_name_ends (t : Term S ν) (k : ℕ) (x : ν) :
    (t.rootEnd k ::ₘ (t.rawWires k).bind Graph.wireEnds).count (.name x) = t.vars.count x := by
  rw [rootEnd_cons_rawWires, Multiset.count_add, Multiset.count_eq_zero.2, zero_add,
    Multiset.count_map_eq_count' _ _ (fun _ _ h => End.name.inj h)]
  simp [Graph.cellPorts]

theorem count_name_rawWires_of_notMem {t : Term S ν} {x : ν} (h : x ∉ t.vars) (k : ℕ) :
    ((t.rawWires k).bind Graph.wireEnds).count (.name x) = 0 := by
  have := count_name_ends t k x
  rw [Multiset.count_eq_zero.2 h, Multiset.count_cons] at this
  omega

theorem rootEnd_ne_of_notMem {t : Term S ν} {x : ν} (h : x ∉ t.vars) (k : ℕ) :
    t.rootEnd k ≠ .name x := fun e => by
  have := count_name_ends t k x
  rw [Multiset.count_eq_zero.2 h, e, Multiset.count_cons_self] at this
  omega

/-- A tree without `x` is kept when `x` is replaced in its wires. -/
theorem rawWires_substName_of_notMem {t : Term S ν} {x : ν} (h : x ∉ t.vars) (k : ℕ)
    (r : End ν) : (t.rawWires k).map (Sym2.map (End.substName x r)) = t.rawWires k :=
  Graph.map_substName_of_count r (count_name_rawWires_of_notMem h k)

omit [DecidableEq ν] in
private theorem childBase_eq {n : ℕ} (k : ℕ) (ts : Fin n → Term S ν) (i : Fin n) :
    childBase k ts i = k + childBase 0 ts i := by unfold childBase; omega

omit [DecidableEq ν] in
private theorem one_le_childBase {n : ℕ} (ts : Fin n → Term S ν) (i : Fin n) :
    1 ≤ childBase 0 ts i := by unfold childBase; omega

omit [DecidableEq ν] in
private theorem childBase_add_size_le {n : ℕ} (k : ℕ) (ts : Fin n → Term S ν) {i j : Fin n}
    (h : j < i) : childBase k ts j + (ts j).size ≤ childBase k ts i := by
  unfold childBase
  have := sum_ite_lt_add_le (fun l => (ts l).size) j (· < i) (fun l hl => lt_of_le_of_lt hl h)
  beta_reduce at this
  omega

omit [DecidableEq ν] in
private theorem childBase_add_size_le_size {α : S.Sym} (k : ℕ)
    (ts : Fin (S.arity α) → Term S ν) (i : Fin (S.arity α)) :
    childBase k ts i + (ts i).size ≤ k + (app α ts).size := by
  unfold childBase
  have := sum_ite_lt_add_le (fun l => (ts l).size) i (fun _ => True) (fun _ _ => trivial)
  simp only [ite_true] at this
  simp only [size]
  omega

omit [DecidableEq ν] in
private theorem childBase_subst {n : ℕ} (k : ℕ) (ts ts' : Fin n → Term S ν) (i : Fin n) (d : ℕ)
    (hs : ∀ l, (ts' l).size = (ts l).size + if l = i then d else 0) (j : Fin n) :
    childBase k ts' j = childBase k ts j + if i < j then d else 0 := by
  unfold childBase
  have : (∑ l, if l < j then (ts' l).size else 0) =
      (∑ l, if l < j then (ts l).size else 0) +
        ∑ l, if l = i then (if i < j then d else 0) else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hs l]
    by_cases h1 : l = i
    · subst h1
      by_cases h2 : l < j <;> simp [h2]
    · by_cases h2 : l < j <;> simp [h1, h2]
  rw [this, Fintype.sum_ite_eq']
  omega

/-- **Plugging a tree into a name** (Lafont 1997, page 71). Let `x` occur once in `a`, and let `p`
be the number of cells of `a` before that occurrence in prefix order. Number the cells of `a` from
`k` and those of `t` from `m`. A renaming `σ` that keeps the `p` first cells of `a` in place (up to
the shift from `k` to `k'`), moves the others of `a` by the size of `t`, and puts the cells of `t`
after the `p` first ones, carries the cells of `a` and `t` to those of `a.subst x t` numbered
from `k'`. It carries the inner wires of `a`, with the name `x` replaced by the root of `t`, and
the inner wires of `t`, to the inner wires of `a.subst x t`; and the root of `a` to its root. -/
theorem raw_subst (x : ν) (t : Term S ν) (a : Term S ν) (ha : a.vars.count x = 1) :
    ∃ p, p ≤ a.size ∧ ∀ (σ : ℕ → ℕ) (k k' m : ℕ),
      (∀ c, k ≤ c → c < k + p → σ c + k = c + k') →
      (∀ c, k + p ≤ c → c < k + a.size → σ c + k = c + k' + t.size) →
      (∀ c, m ≤ c → c < m + t.size → σ c + m = c + k' + p) →
      (a.rawCells k).map (Prod.map σ id) + (t.rawCells m).map (Prod.map σ id) =
          (a.subst x t).rawCells k' ∧
        (a.rawWires k).map (Sym2.map (End.mapCell σ ∘ End.substName x (t.rootEnd m))) +
          (t.rawWires m).map (Sym2.map (End.mapCell σ)) = (a.subst x t).rawWires k' ∧
        End.mapCell σ (End.substName x (t.rootEnd m) (a.rootEnd k)) =
          (a.subst x t).rootEnd k' := by
  induction a with
  | var y =>
    have hy : y = x := by
      by_contra h
      simp [Ne.symm h] at ha
    subst hy
    refine ⟨0, Nat.zero_le _, fun σ k k' m _ _ h3 => ?_⟩
    have h3' : ∀ q ∈ t.rawCells m, σ q.1 + m = q.1 + k' := fun q hq => by
      have := mem_rawCells_range hq
      have := h3 q.1 this.1 this.2
      omega
    have e : (var y : Term S ν).subst y t = t := by simp [subst]
    rw [e]
    refine ⟨?_, ?_, ?_⟩
    · simp only [rawCells, Multiset.map_zero, zero_add]
      exact rawCells_map_shift σ t m k' h3'
    · simp only [rawWires, Multiset.map_zero, zero_add]
      exact rawWires_map_shift σ t m k' h3'
    · simp only [rootEnd, End.substName_self]
      exact rootEnd_map_shift σ t m k' h3'
  | app α ts ih =>
    rw [vars_app, Multiset.count_sum'] at ha
    obtain ⟨i, hi, h0⟩ := exists_eq_one_of_sum (fun j => (ts j).vars.count x) ha
    obtain ⟨pi, hpi, H⟩ := ih i hi
    let ts' : Fin (S.arity α) → Term S ν := fun j => (ts j).subst x t
    have e : (app α ts).subst x t = app α ts' := rfl
    have hnot : ∀ j, j ≠ i → x ∉ (ts j).vars := fun j hj => Multiset.count_eq_zero.1 (h0 j hj)
    have hts' : ∀ j, j ≠ i → ts' j = ts j := fun j hj => subst_of_notMem (hnot j hj)
    have hs : ∀ l, (ts' l).size = (ts l).size + if l = i then t.size else 0 := by
      intro l
      simp only [ts', size_subst]
      by_cases hl : l = i
      · subst hl; simp [hi]
      · simp [hl, h0 l hl]
    have hcb : ∀ k j, childBase k ts' j = childBase k ts j + if i < j then t.size else 0 :=
      fun k j => childBase_subst k ts ts' i t.size hs j
    have hB := one_le_childBase ts i
    refine ⟨childBase 0 ts i + pi, ?_, fun σ k k' m h1 h2 h3 => ?_⟩
    · have := childBase_add_size_le_size (α := α) 0 ts i
      omega
    have hk : σ k = k' := by have := h1 k le_rfl (by omega); omega
    have ek := childBase_eq k ts i
    have ek' := childBase_eq k' ts i
    have hsz := childBase_add_size_le_size (α := α) k ts i
    have hcbi : childBase k' ts' i = childBase k' ts i := by simp [hcb]
    obtain ⟨Hc, Hw, Hr⟩ := H σ (childBase k ts i) (childBase k' ts' i) m
      (fun c hc hc' => by have := h1 c (by omega) (by omega); omega)
      (fun c hc hc' => by have := h2 c (by omega) (by omega); omega)
      (fun c hc hc' => by have := h3 c hc hc'; omega)
    have hshift : ∀ j, j ≠ i → ∀ q ∈ (ts j).rawCells (childBase k ts j),
        σ q.1 + childBase k ts j = q.1 + childBase k' ts' j := by
      intro j hj q hq
      have hq' := mem_rawCells_range hq
      have ej := childBase_eq k ts j
      have ej' := childBase_eq k' ts j
      rcases lt_or_gt_of_ne hj with hlt | hlt
      · have hle := childBase_add_size_le k ts hlt
        have : ¬ i < j := not_lt.2 hlt.le
        simp only [hcb, this, ↓reduceIte, add_zero]
        have := h1 q.1 (by omega) (by omega)
        omega
      · have hle := childBase_add_size_le k ts hlt
        have hsj := childBase_add_size_le_size (α := α) k ts j
        simp only [hcb, hlt, ↓reduceIte]
        have := h2 q.1 (by omega) (by omega)
        omega
    rw [e]
    refine ⟨?_, ?_, ?_⟩
    · simp only [rawCells, Multiset.map_cons, map_finsum'', Multiset.cons_add]
      simp only [Prod.map, hk, id]
      congr 1
      refine sum_update_add _ _ _ i Hc fun j hj => ?_
      rw [hts' j hj]
      exact rawCells_map_shift σ (ts j) _ _ (hshift j hj)
    · have hf : ∀ j : Fin (S.arity α),
          Sym2.map (End.mapCell σ ∘ End.substName x (t.rootEnd m))
            s(End.port k ((j : ℕ) + 1), (ts j).rootEnd (childBase k ts j)) =
          s(End.port k' ((j : ℕ) + 1),
            End.mapCell σ (End.substName x (t.rootEnd m) ((ts j).rootEnd (childBase k ts j)))) := by
        intro j
        simp [End.mapCell, hk]
      simp only [rawWires, map_finsum'', Multiset.map_cons, hf]
      refine sum_update_add _ _ _ i ?_ fun j hj => ?_
      · rw [Multiset.cons_add, Hr, Hw]
      · rw [hts' j hj, End.substName_of_ne _ (rootEnd_ne_of_notMem (hnot j hj) _),
          rootEnd_map_shift σ _ _ _ (hshift j hj), Sym2.map_comp, ← Multiset.map_map,
          rawWires_substName_of_notMem (hnot j hj), rawWires_map_shift σ _ _ _ (hshift j hj)]
    · simp [rootEnd, End.mapCell, hk]

end Term

/-! ## The raw graph of one wire substitution -/

namespace Graph

/-- Wires of a raw graph whose text does not contain `x` are kept when `x` is replaced. -/
theorem raw_wires_substName_of_notMem {x : ν} (k : ℕ) (L : List (Term S ν × Term S ν))
    (h : x ∉ (Net.ofList L).vars) (r : End ν) :
    (raw k L).wires.map (Sym2.map (End.substName x r)) = (raw k L).wires :=
  map_substName_of_count r (by
    rw [← ends_eq_bind, raw_count_name]; exact Multiset.count_eq_zero.2 h)

/-- **One wire substitution on the raw graph** (Lafont 1997, page 71). Let `x` occur once in `a`
and nowhere in `t`, `b` and the rest `L`. The raw graph of `x = t, a = b, L` contracts, by erasing
`x`, to a graph isomorphic to the raw graph of `a[t/x] = b, L`. The cells of `t` move from their
own block into the middle of the block of `a`. -/
theorem raw_wire_contract (k : ℕ) (x : ν) (t a b : Term S ν) (L : List (Term S ν × Term S ν))
    (ha : a.vars.count x = 1) (hb : x ∉ b.vars) (ht : x ∉ t.vars)
    (hL : x ∉ (Net.ofList L).vars) :
    ∃ H, Contract (raw k ((.var x, t) :: (a, b) :: L)) H ∧
      H.Iso (raw k ((a.subst x t, b) :: L)) := by
  obtain ⟨p, hp, hsub⟩ := Term.raw_subst x t a ha
  set G1 := raw (k + t.size) ((a, b) :: L) with hG1
  set GL := raw (k + t.size + a.size + b.size) L with hGL
  have e1 : raw k ((.var x, t) :: (a, b) :: L) =
      ⟨0 + t.rawCells k + G1.cells, s(.name x, t.rootEnd k) ::ₘ (0 + t.rawWires k + G1.wires),
        G1.loops⟩ :=
    rfl
  have hW : ((0 + t.rawWires k + G1.wires).bind wireEnds).count (.name x) = 1 := by
    rw [Multiset.add_bind, Multiset.add_bind, Multiset.zero_bind, zero_add, Multiset.count_add,
      Term.count_name_rawWires_of_notMem ht, zero_add, ← ends_eq_bind, hG1, raw_count_name,
      Net.ofList_cons, Net.vars_cons, eqVars_mk, Multiset.count_add, Multiset.count_add, ha,
      Multiset.count_eq_zero.2 hb, Multiset.count_eq_zero.2 hL]
  refine ⟨_, e1 ▸ contract_substName _ _ G1.loops x (t.rootEnd k) hW, ?_⟩
  have hsz := Term.size_subst a x t
  rw [ha, one_mul] at hsz
  let σ : ℕ → ℕ := fun c =>
    if c < k + t.size then c + p else if c < k + t.size + p then c - t.size else c
  obtain ⟨Hc, Hw, Hr⟩ := hsub σ (k + t.size) k k
    (fun c h h' => by simp only [σ]; split_ifs <;> omega)
    (fun c h h' => by simp only [σ]; split_ifs <;> omega)
    (fun c _ h' => by simp only [σ, h', ↓reduceIte]; omega)
  have hid : ∀ c, k + t.size + a.size ≤ c → σ c = c := fun c h => by
    simp only [σ]; split_ifs <;> omega
  have hbs : ∀ q ∈ b.rawCells (k + t.size + a.size),
      σ q.1 + (k + t.size + a.size) = q.1 + (k + (a.subst x t).size) := fun q hq => by
    have := Term.mem_rawCells_range hq
    rw [hid _ this.1]; omega
  have hLs : ∀ q ∈ GL.cells,
      σ q.1 + (k + t.size + a.size + b.size) = q.1 + (k + (a.subst x t).size + b.size) :=
    fun q hq => by
      have := mem_raw_cells_range hq
      rw [hid _ (by omega)]; omega
  obtain ⟨cL, wL⟩ := raw_map_shift σ L _ _ hLs
  have hbr : b.rootEnd (k + t.size + a.size) ≠ .name x := Term.rootEnd_ne_of_notMem hb _
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · intro c hc d hd e
    have hc' : c ∈ (raw k ((.var x, t) :: (a, b) :: L)).cells.map Prod.fst := hc
    have hd' : d ∈ (raw k ((.var x, t) :: (a, b) :: L)).cells.map Prod.fst := hd
    rw [mem_raw_fst] at hc' hd'
    simp only [σ] at e
    split_ifs at e <;> omega
  · change (a.subst x t).rawCells k + b.rawCells (k + (a.subst x t).size) +
      (raw (k + (a.subst x t).size + b.size) L).cells = _
    rw [← cL, ← Term.rawCells_map_shift σ b _ _ hbs, ← Hc]
    change _ = (0 + t.rawCells k + (a.rawCells (k + t.size) + b.rawCells (k + t.size + a.size) +
      GL.cells)).map _
    simp only [Multiset.map_add, zero_add]
    abel
  · change s((a.subst x t).rootEnd k, b.rootEnd (k + (a.subst x t).size)) ::ₘ
      ((a.subst x t).rawWires k + b.rawWires (k + (a.subst x t).size) +
        (raw (k + (a.subst x t).size + b.size) L).wires) = _
    have hA : ((a.rawWires (k + t.size)).map (Sym2.map (End.substName x (t.rootEnd k)))).map
        (Sym2.map (End.mapCell σ)) =
        (a.rawWires (k + t.size)).map
          (Sym2.map (End.mapCell σ ∘ End.substName x (t.rootEnd k))) := by
      rw [Multiset.map_map, Sym2.map_comp]
    rw [← wL, ← Term.rawWires_map_shift σ b _ _ hbs, ← Term.rootEnd_map_shift σ b _ _ hbs,
      ← Hw, ← Hr]
    change _ = ((0 + t.rawWires k + (s(a.rootEnd (k + t.size), b.rootEnd (k + t.size + a.size)) ::ₘ
      (a.rawWires (k + t.size) + b.rawWires (k + t.size + a.size) + GL.wires))).map _).map _
    simp only [Multiset.map_add, zero_add, Multiset.map_cons, Sym2.map_mk,
      End.substName_of_ne _ hbr, Term.rawWires_substName_of_notMem ht,
      Term.rawWires_substName_of_notMem hb, hA]
    eta_reduce
    rw [show GL.wires.map (Sym2.map (End.substName x (t.rootEnd k))) = GL.wires from
      raw_wires_substName_of_notMem _ _ hL _, Multiset.add_cons]
    congr 1
    abel
  · change (raw k ((a.subst x t, b) :: L)).loops = G1.loops
    rw [raw_loops, raw_loops]

omit [DecidableEq ν] in
/-- The wires of a graph reached by contraction from a raw graph end only at its cells. -/
theorem contracts_raw_portsIn {k : ℕ} {L : List (Term S ν × Term S ν)} {H : Graph S ν}
    (h : Relation.ReflTransGen Contract (raw k L) H) (c i : ℕ) (hm : End.port c i ∈ H.ends) :
    c ∈ H.cells.map Prod.fst := by
  rw [contracts_cells_eq h]
  exact raw_portsIn k L c i (Multiset.mem_of_le (contracts_ends_le h) hm)

end Graph

/-! ## Wire substitution and equivalence -/

/-- A wire substitution keeps the graph, in the case where the name `x` occurs in the left side
`a` of the equation `a = b`. -/
private theorem wire_hasGraph_iso_left {x : ν} {t a b : Term S ν} {Δ : Net S ν}
    (hlin : Net.Linear (s(.var x, t) ::ₘ s(a, b) ::ₘ Δ)) (ha : a.vars.count x = 1)
    (hb : x ∉ b.vars) (ht : x ∉ t.vars) (hΔ : x ∉ Δ.vars) {G G' : Graph S ν}
    (hG : Net.HasGraph (s(.var x, t) ::ₘ s(a, b) ::ₘ Δ) G)
    (hG' : Net.HasGraph (s(a.subst x t, b) ::ₘ Δ) G') : G.Iso G' := by
  obtain ⟨LΔ, rfl⟩ := Net.exists_ofList Δ
  have eN : s(.var x, t) ::ₘ s(a, b) ::ₘ Net.ofList LΔ =
      Net.ofList ((Term.var x, t) :: (a, b) :: LΔ) := rfl
  have eM : s(a.subst x t, b) ::ₘ Net.ofList LΔ = Net.ofList ((a.subst x t, b) :: LΔ) := rfl
  have wf' := hG'.wf
  obtain ⟨H, hc, hi⟩ := Graph.raw_wire_contract 0 x t a b LΔ ha hb ht hΔ
  obtain ⟨L0, k0, hL0, c0, n0⟩ := hG
  obtain ⟨L1, k1, hL1, c1, n1⟩ := hG'
  obtain ⟨G₁, c₁, i₁⟩ := (Graph.raw_iso_of_ofList_eq (hL0.symm.trans eN) k0 0).contracts c0
  have hHp := Graph.contracts_raw_portsIn (.single hc)
  obtain ⟨G₂, c₂, i₂⟩ :=
    ((Graph.raw_iso_of_ofList_eq (hL1.symm.trans eM) k1 0).trans (hi.symm hHp)).contracts c1
  have n₁ : ∀ y, G₁.ends.count (.name y) ≤ 1 := fun y => (i₁.count_name y).trans_le (n0 y)
  have n₂ : ∀ y, G₂.ends.count (.name y) ≤ 1 := fun y => (i₂.count_name y).trans_le (n1 y)
  have e := Graph.contracts_unique (Graph.raw_count_name_le_two 0 _ (eN ▸ hlin)) c₁
    (.head hc c₂) n₁ n₂
  rw [e] at i₁
  exact i₁.trans (i₂.symm wf'.portsIn)

/-- **A wire substitution keeps the graph** (Lafont 1997, Section 1.1, page 71; PLAN.md Stage C,
statement 3): if `N` becomes `M` by plugging `t` into the other end of the wire `x` of an
equation `x = t`, every graph of `N` is isomorphic to every graph of `M`. The linearity of `N`
is part of `Wire`. -/
theorem Wire.hasGraph_iso {N M : Net S ν} (h : Wire N M) {G G' : Graph S ν}
    (hG : N.HasGraph G) (hG' : M.HasGraph G') : G.Iso G' := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hxl := hlin x
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hxl
  have hx1 : 1 ≤ (a.vars + b.vars).count x := Multiset.one_le_count_iff_mem.2 hx
  rw [Multiset.count_add] at hx1
  have ht : x ∉ t.vars := Multiset.count_eq_zero.1 (by omega)
  have hΔ : x ∉ Δ.vars := Multiset.count_eq_zero.1 (by omega)
  by_cases ha : a.vars.count x = 1
  · have hb : x ∉ b.vars := Multiset.count_eq_zero.1 (by omega)
    rw [Term.subst_of_notMem hb] at hG'
    exact wire_hasGraph_iso_left hlin ha hb ht hΔ hG hG'
  · have hb : b.vars.count x = 1 := by omega
    have ha' : x ∉ a.vars := Multiset.count_eq_zero.1 (by omega)
    rw [Term.subst_of_notMem ha', Sym2.eq_swap (a := a)] at hG'
    rw [Sym2.eq_swap (a := a)] at hG hlin
    exact wire_hasGraph_iso_left hlin hb ha' ht hΔ hG hG'

/-- **Equivalent linear nets have isomorphic graphs** (Lafont 1997, Section 1.1, page 71; PLAN.md
Stage C, statement 3, the direction from `Equiv` to `Iso`): if `N` is linear and `Equiv N M`,
every graph of `N` is isomorphic to every graph of `M`. Linearity is needed: a text that is not
linear can have two graphs that are not isomorphic (`threeText_two_graphs`). -/
theorem Net.Linear.equiv_hasGraph_iso {N M : Net S ν} (hN : N.Linear) (h : Equiv N M)
    {G G' : Graph S ν} (hG : N.HasGraph G) (hG' : M.HasGraph G') : G.Iso G' := by
  induction h generalizing G G' with
  | rel _ _ h => exact h.hasGraph_iso hG hG'
  | refl => exact hN.hasGraph_iso hG hG'
  | symm A B hAB ih =>
    exact (ih ((Equiv.linear_iff hAB).2 hN) hG' hG).symm hG'.wf.portsIn
  | trans A B C hAB _ ih₁ ih₂ =>
    obtain ⟨GB, hGB, -⟩ := Net.exists_graph B
    exact (ih₁ hN hG hGB).trans (ih₂ (Equiv.linear hAB hN) hGB hG')

end INet
