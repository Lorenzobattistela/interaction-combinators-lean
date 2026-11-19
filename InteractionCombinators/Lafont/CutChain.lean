import InteractionCombinators.Lafont.Cut

/-!
# A translation reflects cuts (Proposition 3, page 80)

Lafont 1997, page 80, first point of the proof of Proposition 3: "if `Φ(N)` contains a cut, so
does `N`".

`Net.HasCut` speaks of every net equivalent to `N`, which is not a statement one can follow
through a translation. This file gives a description of a cut on the text itself: a chain of
wires written out,

  `a = x₁, x₁ = x₂, …, xₖ = b`   with `a` and `b` cells   (`Net.ChainCut`),

and shows that it is the same as a cut up to wires for a linear net (`Net.hasCut_iff_chainCut`).
The hard direction is that a wire substitution, in either direction, keeps a written chain
(`Cut.Wire.chainCut`, `Cut.Wire.chainCut_symm`): it shortens the chain, lengthens it, or plugs a
tree into one of its two cells.

The chain of `Φ(N)` is then followed back in `N` (`Cut.walk`): it starts at a cell of `N`, goes
through the same names, and ends at a cell of `N`, possibly before the end of the chain of `Φ(N)`.
-/

namespace INet

variable {S S' : Signature}

open Term

/-- A tree whose root is the principal port of a cell. -/
def Term.IsCell (t : Term S ℕ) : Prop := ∃ α ts, t = Term.app α ts

namespace Cut

theorem not_isCell_var (y : ℕ) : ¬ (Term.var y : Term S ℕ).IsCell := by
  rintro ⟨α, ts, h⟩
  cases h

theorem isCell_subst {t : Term S ℕ} (h : t.IsCell) (x : ℕ) (u : Term S ℕ) :
    (t.subst x u).IsCell := by
  obtain ⟨α, ts, rfl⟩ := h
  exact ⟨α, _, rfl⟩

@[simp] theorem subst_var_self (x : ℕ) (t : Term S ℕ) : (Term.var x).subst x t = t := by
  simp [Term.subst]

theorem subst_var_ne {x y : ℕ} (h : y ≠ x) (t : Term S ℕ) :
    (Term.var y : Term S ℕ).subst x t = Term.var y := by
  simp [Term.subst, h]

/-! ## Plugging a tree into one name of a net -/

/-- Plug the tree `t` into the name `x`, in every equation of a net. -/
def sub (N : Net S ℕ) (x : ℕ) (t : Term S ℕ) : Net S ℕ := N.map (Sym2.map fun r => r.subst x t)

@[simp] theorem sub_cons (a b : Term S ℕ) (N : Net S ℕ) (x : ℕ) (t : Term S ℕ) :
    sub (s(a, b) ::ₘ N) x t = s(a.subst x t, b.subst x t) ::ₘ sub N x t := by
  simp [sub]

@[simp] theorem sub_singleton (a b : Term S ℕ) (x : ℕ) (t : Term S ℕ) :
    sub ({s(a, b)} : Net S ℕ) x t = {s(a.subst x t, b.subst x t)} := by
  simp [sub]

@[simp] theorem sub_add (N M : Net S ℕ) (x : ℕ) (t : Term S ℕ) :
    sub (N + M) x t = sub N x t + sub M x t := by
  simp [sub]

theorem sub_of_notMem {N : Net S ℕ} {x : ℕ} (t : Term S ℕ) (h : x ∉ N.vars) : sub N x t = N := by
  conv_rhs => rw [← Multiset.map_id N]
  refine Multiset.map_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | _ a b =>
    have hab : x ∉ a.vars + b.vars := fun hx =>
      h (Multiset.mem_bind.2 ⟨_, he, by simpa using hx⟩)
    rw [Multiset.mem_add, not_or] at hab
    simp [Term.subst_of_notMem hab.1, Term.subst_of_notMem hab.2]

/-! ## Chains of wires -/

/-- The chain of wires `a = x₁, x₁ = x₂, …, xₖ = b`; with no name, the equation `a = b`. -/
def chain (a : Term S ℕ) : List ℕ → Term S ℕ → Net S ℕ
  | [], b => {s(a, b)}
  | y :: ys, b => s(a, var y) ::ₘ chain (var y) ys b

@[simp] theorem chain_nil (a b : Term S ℕ) : chain a [] b = {s(a, b)} := rfl

@[simp] theorem chain_cons (a b : Term S ℕ) (y : ℕ) (ys : List ℕ) :
    chain a (y :: ys) b = s(a, var y) ::ₘ chain (var y) ys b := rfl

/-- The names of a chain: those of its two ends, and each name of the list twice. -/
theorem count_vars_chain (b : Term S ℕ) (z : ℕ) :
    ∀ (a : Term S ℕ) (xs : List ℕ),
      (chain a xs b).vars.count z = a.vars.count z + b.vars.count z + 2 * xs.count z
  | a, [] => by simp
  | a, y :: ys => by
    rw [chain_cons, Net.vars_cons, Multiset.count_add, count_vars_chain b z (var y) ys]
    simp only [eqVars_mk, vars_var, Multiset.count_add, Multiset.count_singleton, List.count_cons,
      beq_iff_eq]
    split_ifs <;> omega

/-- Plugging a tree into a name that is not a link of the chain plugs it into the two ends. -/
theorem sub_chain {x : ℕ} {t : Term S ℕ} (b : Term S ℕ) :
    ∀ (a : Term S ℕ) (xs : List ℕ), x ∉ xs →
      sub (chain a xs b) x t = chain (a.subst x t) xs (b.subst x t)
  | a, [], _ => by simp
  | a, y :: ys, h => by
    have hy : y ≠ x := fun e => h (e ▸ List.mem_cons_self ..)
    have := sub_chain (t := t) b (var y) ys (fun hm => h (List.mem_cons_of_mem _ hm))
    rw [chain_cons, sub_cons, this, subst_var_ne hy, chain_cons]

/-- **A chain is one wire** (Lafont 1997, Section 1.2, page 71). In a linear net, the chain
`a = x₁, …, xₖ = b` is the same graph as the equation `a = b`. -/
theorem equiv_chain (b : Term S ℕ) :
    ∀ (a : Term S ℕ) (xs : List ℕ) (D : Net S ℕ), (chain a xs b + D).Linear →
      Equiv (chain a xs b + D) (s(a, b) ::ₘ D)
  | a, [], D, _ => Equiv.of_eq (by simp)
  | a, y :: ys, D, hlin => by
    have e : chain a (y :: ys) b + D = chain (var y) ys b + (s(a, var y) ::ₘ D) := by
      rw [chain_cons, Multiset.cons_add, Multiset.add_cons]
    rw [e] at hlin ⊢
    have E := equiv_chain b (var y) ys _ hlin
    have hlin' := E.linear hlin
    have hc := hlin' y
    simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
      Multiset.count_singleton_self] at hc
    have ha : y ∉ a.vars := Multiset.count_eq_zero.1 (by omega)
    have W := Wire.mk y b a (var y) D hlin' (by simp)
    refine E.trans (W.equiv.trans (Equiv.of_eq ?_))
    rw [Term.subst_of_notMem ha, subst_var_self]

end Cut

open Cut

namespace Net

/-- A cut written out on the text: a chain of wires `a = x₁, x₁ = x₂, …, xₖ = b` between two
cells `a` and `b` (Lafont 1997, page 80). With no name it is an equation `a = b` between two
cells. -/
def ChainCut (N : Net S ℕ) : Prop :=
  ∃ a b xs D, Term.IsCell a ∧ Term.IsCell b ∧ N = chain a xs b + D

theorem ChainCut.add_right {N : Net S ℕ} (h : N.ChainCut) (D' : Net S ℕ) : (N + D').ChainCut := by
  obtain ⟨a, b, xs, D, ha, hb, rfl⟩ := h
  exact ⟨a, b, xs, D + D', ha, hb, by rw [add_assoc]⟩

/-- An equation between two cells is a written cut. -/
theorem chainCut_of_mem {N : Net S ℕ} {α β : S.Sym} {ts : Fin (S.arity α) → Term S ℕ}
    {us : Fin (S.arity β) → Term S ℕ} (h : s(Term.app α ts, Term.app β us) ∈ N) : N.ChainCut := by
  obtain ⟨D, rfl⟩ := Multiset.exists_cons_of_mem h
  exact ⟨_, _, [], D, ⟨α, ts, rfl⟩, ⟨β, us, rfl⟩, by simp⟩

/-- A written cut of a linear net is a cut (Lafont 1997, page 80): the chain is contracted to an
equation between the two cells (`Cut.equiv_chain`). -/
theorem ChainCut.hasCut {N : Net S ℕ} (h : N.ChainCut) (hN : N.Linear) : N.HasCut := by
  obtain ⟨a, b, xs, D, ⟨α, ts, rfl⟩, ⟨β, us, rfl⟩, rfl⟩ := h
  exact (hasCut_of_mem (Multiset.mem_cons_self _ _)).of_equiv (equiv_chain _ _ xs D hN).symm

end Net

namespace Cut

/-! ## A wire substitution keeps a written cut -/

/-- An equation `x = t` of a chain between two trees that are not the name `x` is a link: `x` is
one of the names of the chain. -/
theorem mem_chain_var {x : ℕ} {t b : Term S ℕ} (hb : b.IsCell) :
    ∀ (a : Term S ℕ) (xs : List ℕ), a ≠ var x → s(var x, t) ∈ chain a xs b → x ∈ xs
  | a, [], ha, h => by
    rw [chain_nil, Multiset.mem_singleton] at h
    rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h2, -⟩
    · exact absurd h1.symm ha
    · exact (not_isCell_var x (h2 ▸ hb)).elim
  | a, y :: ys, ha, h => by
    rw [chain_cons, Multiset.mem_cons] at h
    by_cases hxy : x = y
    · exact hxy ▸ List.mem_cons_self ..
    rcases h with h | h
    · rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1.symm ha
      · cases h1; exact absurd rfl hxy
    · exact List.mem_cons_of_mem _
        (mem_chain_var hb (var y) ys (fun e => hxy (Term.var.inj e).symm) h)

/-- A chain that starts at the name `x`, with `x` nowhere else, starts with the equation `x = t`;
the rest of the chain makes a chain from any `a`, starting with `a = t`. -/
theorem chain_var_head {x : ℕ} {t b : Term S ℕ} (hb : x ∉ b.vars) (a : Term S ℕ) :
    ∀ (ys : List ℕ) (cs : Net S ℕ), x ∉ ys → chain (var x) ys b = s(var x, t) ::ₘ cs →
      chain a ys b = s(a, t) ::ₘ cs ∧ x ∉ Net.vars cs
  | [], cs, _, h => by
    rw [chain_nil, Multiset.singleton_eq_cons_iff] at h
    obtain ⟨h1, rfl⟩ := h
    rcases Sym2.eq_iff.1 h1 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨by simp, by simp⟩
    · exact absurd (by simp) hb
  | z :: zs, cs, hx, h => by
    have hxz : x ≠ z := fun e => hx (e ▸ List.mem_cons_self ..)
    have hxzs : x ∉ zs := fun hm => hx (List.mem_cons_of_mem _ hm)
    have hnot : x ∉ Net.vars (chain (var z) zs b) := by
      intro hm
      have := Multiset.one_le_count_iff_mem.2 hm
      rw [count_vars_chain] at this
      simp [hxz, Multiset.count_eq_zero.2 hb,
        List.count_eq_zero.2 hxzs] at this
    rw [chain_cons, Multiset.cons_eq_cons] at h
    rcases h with ⟨h1, rfl⟩ | ⟨-, cs', h1, -⟩
    · rcases Sym2.eq_iff.1 h1 with ⟨-, rfl⟩ | ⟨-, h2⟩
      · exact ⟨rfl, hnot⟩
      · cases h2; exact absurd rfl hxz
    · exact absurd (h1 ▸ Multiset.mem_bind.2 ⟨_, Multiset.mem_cons_self _ _, by simp⟩) hnot

/-- **Contracting a link of a chain.** If `x = t` is a link of a chain whose name `x` occurs once
in the list and nowhere else, plugging `t` into `x` in the rest of the chain gives the chain
without `x`. -/
theorem sub_contract {x : ℕ} {t b : Term S ℕ} (hb : x ∉ b.vars) :
    ∀ (a : Term S ℕ) (xs : List ℕ) (C : Net S ℕ), x ∉ a.vars → xs.count x = 1 →
      chain a xs b = s(var x, t) ::ₘ C → sub C x t = chain a (xs.erase x) b
  | a, [], _, _, h1, _ => by simp at h1
  | a, y :: ys, C, ha, h1, h => by
    rw [chain_cons, Multiset.cons_eq_cons] at h
    rcases h with ⟨h2, rfl⟩ | ⟨-, cs, h2, rfl⟩
    · rcases Sym2.eq_iff.1 h2 with ⟨rfl, -⟩ | ⟨rfl, h3⟩
      · exact absurd (by simp) ha
      · cases h3
        have hys : x ∉ ys := by
          rw [List.count_cons_self] at h1
          exact List.count_eq_zero.1 (by omega)
        rw [sub_chain b (var x) ys hys, subst_var_self, Term.subst_of_notMem hb,
          List.erase_cons_head]
    · by_cases hyx : y = x
      · subst hyx
        have hys : y ∉ ys := by
          rw [List.count_cons_self] at h1
          exact List.count_eq_zero.1 (by omega)
        obtain ⟨e, hcs⟩ := chain_var_head hb a ys cs hys h2
        rw [sub_cons, sub_of_notMem t hcs, Term.subst_of_notMem ha, subst_var_self,
          List.erase_cons_head, e]
      · have h1' : ys.count x = 1 := by simpa [List.count_cons, hyx] using h1
        have IH := sub_contract hb (var y) ys cs (by simp [Ne.symm hyx]) h1' h2
        rw [sub_cons, IH, Term.subst_of_notMem ha, subst_var_ne hyx,
          List.erase_cons_tail (by simpa using hyx), chain_cons]

/-- **Inserting a link in a chain.** Replacing an equation `t = c` of a chain by `x = t, x = c`
gives a chain. -/
theorem chain_insert {x : ℕ} {t c : Term S ℕ} (b : Term S ℕ) :
    ∀ (a : Term S ℕ) (xs : List ℕ) (C : Net S ℕ), chain a xs b = s(t, c) ::ₘ C →
      ∃ xs', s(var x, t) ::ₘ s(var x, c) ::ₘ C = chain a xs' b
  | a, [], C, h => by
    rw [chain_nil, Multiset.singleton_eq_cons_iff] at h
    obtain ⟨h1, rfl⟩ := h
    refine ⟨[x], ?_⟩
    rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [Sym2.eq_swap]
    · simp only [chain_cons, chain_nil]
      rw [Multiset.cons_swap, Sym2.eq_swap (a := var x) (b := a)]
      rfl
  | a, y :: ys, C, h => by
    rw [chain_cons, Multiset.cons_eq_cons] at h
    rcases h with ⟨h1, rfl⟩ | ⟨-, cs, h2, rfl⟩
    · refine ⟨x :: y :: ys, ?_⟩
      rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [chain_cons]
        rw [Sym2.eq_swap (a := var x) (b := a)]
      · simp only [chain_cons]
        rw [Multiset.cons_swap, Sym2.eq_swap (a := var x) (b := a)]
    · obtain ⟨xs', e⟩ := chain_insert b (var y) ys cs h2
      refine ⟨y :: xs', ?_⟩
      rw [chain_cons, ← e, Multiset.cons_swap (s(var x, c)), Multiset.cons_swap (s(var x, t))]

/-- **Changing a cell at an end of a chain.** If an equation `c = b₀` of a chain has a cell `c`
on one side, it is an end of the chain, and the cell can be replaced by any tree `a'`. The new
chain starts at `a` unless the old one started at the cell `c`. -/
theorem chain_replace_end {c a' b₀ : Term S ℕ} (hc : c.IsCell) :
    ∀ (a b : Term S ℕ) (xs : List ℕ) (C : Net S ℕ), chain a xs b = s(c, b₀) ::ₘ C →
      ∃ a₁ b₁, s(a', b₀) ::ₘ C = chain a₁ xs b₁ ∧ (a₁ = a ∨ (a₁ = a' ∧ a.IsCell)) ∧
        (b₁ = b ∨ b₁ = a')
  | a, b, [], C, h => by
    rw [chain_nil, Multiset.singleton_eq_cons_iff] at h
    obtain ⟨h1, rfl⟩ := h
    rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨a', _, by simp, Or.inr ⟨rfl, hc⟩, Or.inl rfl⟩
    · exact ⟨_, a', by simp [Sym2.eq_swap], Or.inl rfl, Or.inr rfl⟩
  | a, b, y :: ys, C, h => by
    rw [chain_cons, Multiset.cons_eq_cons] at h
    rcases h with ⟨h1, rfl⟩ | ⟨-, cs, h2, rfl⟩
    · rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨-, rfl⟩
      · exact ⟨a', b, rfl, Or.inr ⟨rfl, hc⟩, Or.inl rfl⟩
      · exact absurd hc (not_isCell_var y)
    · obtain ⟨a₂, b₂, e, ha₂, hb₂⟩ := chain_replace_end hc (var y) b ys cs h2
      have ha₂' : a₂ = var y := ha₂.resolve_right fun h => not_isCell_var y h.2
      subst ha₂'
      refine ⟨a, b₂, ?_, Or.inl rfl, hb₂⟩
      rw [Multiset.cons_swap, e, chain_cons]

/-- **A wire substitution keeps a written cut** (Lafont 1997, page 80). If the wire `x = t` is a
link of the chain, the chain gets shorter; otherwise `t` is plugged into the rest of the net and
the chain keeps its links. -/
theorem Wire.chainCut {N M : Net S ℕ} (h : Wire N M) (hc : N.ChainCut) : M.ChainCut := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hcx := hlin x
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hcx
  have hx1 : 1 ≤ (a.vars + b.vars).count x := Multiset.one_le_count_iff_mem.2 hx
  rw [Multiset.count_add] at hx1
  have ht : x ∉ t.vars := Multiset.count_eq_zero.1 (by omega)
  have hΔ : x ∉ Net.vars Δ := Multiset.count_eq_zero.1 (by omega)
  have hM : s(a.subst x t, b.subst x t) ::ₘ Δ = sub (s(a, b) ::ₘ Δ) x t := by
    rw [sub_cons, sub_of_notMem t hΔ]
  rw [hM]
  obtain ⟨A, B, xs, D, hA, hB, hN⟩ := hc
  have hlin' := hlin x
  rw [hN, Net.vars_add, Multiset.count_add, count_vars_chain] at hlin'
  have hW : s(var x, t) ∈ chain A xs B + D := hN ▸ Multiset.mem_cons_self _ _
  rcases Multiset.mem_add.1 hW with hWc | hWD
  · obtain ⟨C, hC⟩ := Multiset.exists_cons_of_mem hWc
    rw [hC, Multiset.cons_add] at hN
    rw [(Multiset.cons_inj_right _).1 hN]
    have hxs : x ∈ xs := mem_chain_var hB A xs (fun e => not_isCell_var x (e ▸ hA)) hWc
    have h1 := List.count_pos_iff.2 hxs
    have hD : x ∉ Net.vars D := Multiset.count_eq_zero.1 (by omega)
    have hAx : x ∉ A.vars := Multiset.count_eq_zero.1 (by omega)
    have hBx : x ∉ B.vars := Multiset.count_eq_zero.1 (by omega)
    rw [sub_add, sub_of_notMem t hD, sub_contract hBx A xs C hAx (by omega) hC]
    exact ⟨A, B, _, D, hA, hB, rfl⟩
  · obtain ⟨D₁, rfl⟩ := Multiset.exists_cons_of_mem hWD
    rw [Multiset.add_cons] at hN
    rw [(Multiset.cons_inj_right _).1 hN]
    have hD1 : 1 ≤ (Net.vars (s(var x, t) ::ₘ D₁)).count x := by
      rw [Net.vars_cons, eqVars_mk, Multiset.count_add, Term.vars_var, Multiset.count_add,
        Multiset.count_singleton_self]
      omega
    have hxs : x ∉ xs := fun hm => by
      have := List.count_pos_iff.2 hm
      omega
    rw [sub_add, sub_chain B A xs hxs]
    exact ⟨_, _, xs, _, isCell_subst hA x t, isCell_subst hB x t, rfl⟩

/-- A wire substitution undone keeps a written cut, when `x` occurs in the left side `a` of the
equation it was plugged into. -/
theorem chainCut_unsub {x : ℕ} {t a b : Term S ℕ} {Δ : Net S ℕ} (hxa : x ∈ a.vars)
    (hc : Net.ChainCut (s(a.subst x t, b) ::ₘ Δ)) :
    Net.ChainCut (s(var x, t) ::ₘ s(a, b) ::ₘ Δ) := by
  obtain ⟨A, B, xs, D, hA, hB, hN⟩ := hc
  have hT : s(a.subst x t, b) ∈ chain A xs B + D := hN ▸ Multiset.mem_cons_self _ _
  rcases Multiset.mem_add.1 hT with hTc | hTD
  · obtain ⟨C, hC⟩ := Multiset.exists_cons_of_mem hTc
    rw [hC, Multiset.cons_add] at hN
    rw [(Multiset.cons_inj_right _).1 hN]
    cases a with
    | var y =>
      have hy : y = x := by simpa [eq_comm] using hxa
      subst hy
      rw [subst_var_self] at hC
      obtain ⟨xs', e⟩ := chain_insert (x := y) B A xs C hC
      refine ⟨A, B, xs', D, hA, hB, ?_⟩
      rw [← Multiset.cons_add, ← Multiset.cons_add, e]
    | app α ts =>
      obtain ⟨A₁, B₁, e, hA₁, hB₁⟩ :=
        chain_replace_end (a' := Term.app α ts) (isCell_subst ⟨α, ts, rfl⟩ x t) A B xs C hC
      refine ⟨A₁, B₁, xs, s(var x, t) ::ₘ D, ?_, ?_, ?_⟩
      · rcases hA₁ with rfl | ⟨rfl, -⟩
        · exact hA
        · exact ⟨α, ts, rfl⟩
      · rcases hB₁ with rfl | rfl
        · exact hB
        · exact ⟨α, ts, rfl⟩
      · rw [Multiset.add_cons, ← Multiset.cons_add, e]
  · obtain ⟨D₁, rfl⟩ := Multiset.exists_cons_of_mem hTD
    rw [Multiset.add_cons] at hN
    rw [(Multiset.cons_inj_right _).1 hN]
    refine ⟨A, B, xs, s(var x, t) ::ₘ s(a, b) ::ₘ D₁, hA, hB, ?_⟩
    rw [Multiset.add_cons, Multiset.add_cons]

/-- **A wire substitution undone keeps a written cut** (Lafont 1997, page 80). If `M` is `N` with
the wire `x = t` contracted and `M` has a written cut, so has `N`: the chain gets a new link `x`,
or one of its two cells is the cell into which `t` was plugged. -/
theorem Wire.chainCut_symm {N M : Net S ℕ} (h : Wire N M) (hc : M.ChainCut) : N.ChainCut := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hcx := hlin x
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hcx
  rcases Multiset.mem_add.1 hx with hxa | hxb
  · have hb : x ∉ b.vars := by
      have := Multiset.one_le_count_iff_mem.2 hxa
      exact Multiset.count_eq_zero.1 (by omega)
    rw [Term.subst_of_notMem hb] at hc
    exact chainCut_unsub hxa hc
  · have ha : x ∉ a.vars := by
      have := Multiset.one_le_count_iff_mem.2 hxb
      exact Multiset.count_eq_zero.1 (by omega)
    rw [Term.subst_of_notMem ha, Sym2.eq_swap] at hc
    rw [Sym2.eq_swap (a := a)]
    exact chainCut_unsub hxb hc

/-- Equivalent nets have a written cut together. -/
theorem Equiv.chainCut_iff {N M : Net S ℕ} (h : Equiv N M) : N.ChainCut ↔ M.ChainCut := by
  induction h with
  | rel _ _ h => exact ⟨Wire.chainCut h, Wire.chainCut_symm h⟩
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end Cut

namespace Net

/-- A cut up to wires is written out in the net itself (Lafont 1997, page 80): a chain of wires
`a = x₁, …, xₖ = b` between two cells. No linearity is needed. -/
theorem HasCut.chainCut {N : Net S ℕ} (h : N.HasCut) : N.ChainCut := by
  obtain ⟨N', hE, α, β, ts, us, hm⟩ := h
  exact (Cut.Equiv.chainCut_iff hE).2 (chainCut_of_mem hm)

/-- **A cut up to wires is a chain of wires** (Lafont 1997, page 80). For a linear net, a cut of
the graph is the same as a chain `a = x₁, x₁ = x₂, …, xₖ = b` between two cells `a`, `b` among the
equations of the net. -/
theorem hasCut_iff_chainCut {N : Net S ℕ} (hN : N.Linear) : N.HasCut ↔ N.ChainCut :=
  ⟨HasCut.chainCut, fun h => h.hasCut hN⟩

end Net

namespace Cut

variable {Φ : Translation S S'}

theorem TermTr.isCell {t : Term S ℕ} {t' : Term S' ℕ} (h : Φ.TermTr t t') (h' : t'.IsCell) :
    t.IsCell := by
  cases h with
  | var x => exact absurd h' (not_isCell_var x)
  | app α ts ts' f _ => exact ⟨α, ts, rfl⟩

theorem TermTr.var_var {x y : ℕ} (h : Φ.TermTr (Term.var y) (Term.var x)) : y = x := by
  cases h
  rfl

/-- The equations that translate to `a' = b'` are the `a = b` with `a` translating to `a'` and
`b` to `b'`. -/
theorem EqTr.inv {e : Sym2 (Term S ℕ)} {a' b' : Term S' ℕ} (h : Φ.EqTr e s(a', b')) :
    ∃ a b, e = s(a, b) ∧ Φ.TermTr a a' ∧ Φ.TermTr b b' := by
  obtain ⟨a, b, c', d', rfl, he, ha, hb⟩ := h
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨a, b, rfl, ha, hb⟩
  · exact ⟨b, a, Sym2.eq_swap, hb, ha⟩

/-- **Following a chain back through a translation.** If the equations `C` translate a chain
`a' = x₁, …, xₖ = b'` whose end `b'` is a cell, then either `C` already has a written cut, or `C`
has a chain `a = x₁, …, xⱼ = y` with `a` translating `a'` and `y` a cell, `j ≤ k`.

Each link `xᵢ = xᵢ₊₁` of the translation comes from an equation `xᵢ = u` of `C` with `u`
translating to the name `xᵢ₊₁`. Either `u` is the name `xᵢ₊₁` and the chain goes on, or `u` is a
cell whose translation is a single wire from its root to an auxiliary port: then the chain of `C`
ends at the principal port of that cell. -/
theorem walk : ∀ (xs : List ℕ) (a' b' : Term S' ℕ) (C : Net S ℕ),
    Multiset.Rel Φ.EqTr C (chain a' xs b') → b'.IsCell →
      C.ChainCut ∨ ∃ a ys y D, C = chain a ys y + D ∧ Φ.TermTr a a' ∧ y.IsCell
  | [], a', b', C, h, hb' => by
    rw [chain_nil, ← Multiset.cons_zero, Multiset.rel_cons_right] at h
    obtain ⟨e, C₀, he, h0, rfl⟩ := h
    rw [Multiset.rel_zero_right] at h0
    subst h0
    obtain ⟨a, b, rfl, ha, hb⟩ := EqTr.inv he
    exact Or.inr ⟨a, [], b, 0, by simp, ha, TermTr.isCell hb hb'⟩
  | z :: zs, a', b', C, h, hb' => by
    rw [chain_cons, Multiset.rel_cons_right] at h
    obtain ⟨e, C₀, he, h0, rfl⟩ := h
    obtain ⟨a, y, rfl, ha, hy⟩ := EqTr.inv he
    cases y with
    | app γ vs =>
      exact Or.inr ⟨a, [], Term.app γ vs, C₀, by simp, ha, ⟨γ, vs, rfl⟩⟩
    | var w =>
      have hw := TermTr.var_var hy
      subst hw
      rcases walk zs (var w) b' C₀ h0 hb' with hcc | ⟨a₀, ys, y₀, D₀, rfl, ha₀, hy₀⟩
      · have := hcc.add_right {s(a, var w)}
        rw [add_comm, Multiset.singleton_add] at this
        exact Or.inl this
      · cases a₀ with
        | var v =>
          have hv := TermTr.var_var ha₀
          subst hv
          exact Or.inr ⟨a, v :: ys, y₀, D₀, by rw [chain_cons, Multiset.cons_add], ha, hy₀⟩
        | app γ vs =>
          refine Or.inl ⟨Term.app γ vs, y₀, ys, s(a, var w) ::ₘ D₀, ⟨γ, vs, rfl⟩, hy₀, ?_⟩
          rw [Multiset.add_cons]

/-- A translation keeps every name: each name occurs in the translation at least as often as in
the source net. -/
theorem rel_count_le {N : Net S ℕ} {N' : Net S' ℕ} (h : Multiset.Rel Φ.EqTr N N') (y : ℕ) :
    N.vars.count y ≤ N'.vars.count y := by
  induction h with
  | zero => simp
  | cons he _ ih =>
    obtain ⟨a, b, a', b', rfl, rfl, ha, hb⟩ := he
    simp only [Net.vars_cons, eqVars_mk, Multiset.count_add]
    have := ha.count_le y
    have := hb.count_le y
    omega

end Cut

/-- **A translation reflects cuts** (Lafont 1997, Proposition 3, first point of the proof,
page 80): if `N'` translates `N` and `N'` has a cut, so has `N`. No strictness is needed.

The cut of `N'` is a chain `a' = x₁, …, xₖ = b'` between two cells (`Net.hasCut_iff_chainCut`).
The internal wires of an instance join two leaves, so they are never links of the chain. The chain
is followed in `N` from the cell that translates to `a'` (`Cut.walk`): it goes through the same
names `x₁, x₂, …` and ends at the principal port of a cell of `N`. That cell is the one that
translates to `b'`, or an earlier one whose translation is a wire from its root to an auxiliary
port: the chain of `N'` passes through such a cell, the chain of `N` stops at it. -/
theorem Translation.NetTr.hasCut_reflect {Φ : Translation S S'} {N : Net S ℕ} {N' : Net S' ℕ}
    (h : Φ.NetTr N N') (hc : N'.HasCut) : N.HasCut := by
  refine Net.ChainCut.hasCut ?_ h.linear_source
  obtain ⟨A', B', xs, D', hA', hB', hN'⟩ := hc.chainCut
  have hrel := h.rel
  rw [hN'] at hrel
  obtain ⟨C, D, hC, -, rfl⟩ := Multiset.rel_add_right.1 hrel
  rcases Cut.walk xs A' B' C hC hB' with hcc | ⟨a, ys, y, D₀, rfl, ha, hy⟩
  · exact hcc.add_right D
  · exact ⟨a, y, ys, D₀ + D, Cut.TermTr.isCell ha hA', hy, add_assoc _ _ _⟩

end INet
