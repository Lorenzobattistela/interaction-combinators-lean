import InteractionCombinators.Lafont.Vicious
import InteractionCombinators.Combinators

/-!
# Review of cuts, vicious circles and reduced nets against pages 79–80

Witnesses for the review of `Net.HasCut`, `Net.HasVicious` and `Net.IsReduced` (Lafont 1997,
pages 79–80), on nets of combinators, whose cells have two auxiliary ports.

* `circle3` — a vicious circle of length 3 spread over four equations, one of them a wire written
  the other way round. No equation of the net is `x = t` with `x` a leaf of `t`
  (`circle3_not_literal`), and `Net.HasVicious` still sees it (`circle3_hasVicious`).
* `auxCycle` — two cells whose auxiliary ports are joined to each other, a cycle through
  auxiliary ports only. It is reduced (`auxCycle_isReduced`).
* `mixedCycle` — two cells, the principal port of `dup` on an auxiliary port of `con`, and an
  auxiliary port of `dup` on the other auxiliary port of `con`: a cycle that is half principal,
  half auxiliary, and not a vicious circle. It is reduced (`mixedCycle_isReduced`).
* `circle2` — the same two cells, closed by principal ports: a vicious circle of length 2, not
  reduced (`circle2_not_isReduced`).

The general fact used to refute circles is `IsCircle.head_leaf`: in a written vicious circle the
name on the left of every equation is a leaf of a tree of the circle.
-/

namespace INet.ViciousReview

open Term Comb Vicious

variable {S : Signature}

/-! ## A necessary condition for a written circle -/

/-- In a written vicious circle (Lafont 1997, page 79) every equation is `x = t` with `x` a leaf of
a tree of the circle: the principal port at the root of `t` goes into an auxiliary port of the
next cell of the circle. -/
theorem IsCircle.head_leaf {K : Net S ℕ} (h : IsCircle K) {e : Sym2 (Term S ℕ)} (he : e ∈ K) :
    ∃ x t, e = s(var x, t) ∧ ∃ x' t', s(var x', t') ∈ K ∧ x ∈ t'.vars := by
  obtain ⟨x, y, t, C, rfl, hy, hC, hK⟩ := h.rotate he
  by_cases hC0 : C = 0
  · subst hC0
    have := hC.eq_of_zero
    subst this
    exact ⟨y, t, rfl, y, t, hK ▸ Multiset.mem_cons_self _ _, hy⟩
  · obtain ⟨x₁, t₁, C₁, hz, -, rfl⟩ := hC.snoc hC0
    exact ⟨x, t, rfl, x₁, t₁,
      hK ▸ Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _), hz⟩

/-- Two multisets of two elements that are equal have the same elements, in some order. -/
theorem pair_eq_cons_cons {α : Type*} {e₁ e₂ f₁ f₂ : α} {D : Multiset α}
    (h : e₁ ::ₘ {e₂} = f₁ ::ₘ f₂ ::ₘ D) : (f₁ = e₁ ∧ f₂ = e₂) ∨ (f₁ = e₂ ∧ f₂ = e₁) := by
  rcases Multiset.cons_eq_cons.1 h with ⟨h1, h2⟩ | ⟨-, cs, h2, h3⟩
  · exact Or.inl ⟨h1.symm, (Multiset.singleton_eq_cons_iff _).1 h2 |>.1.symm⟩
  · obtain ⟨h4, rfl⟩ := (Multiset.singleton_eq_cons_iff _).1 h2
    exact Or.inr ⟨h4.symm, ((Multiset.singleton_eq_cons_iff _).1 h3.symm).1.symm⟩

/-! ## A vicious circle spread over several equations is caught -/

/-- `x₀ = con(x₁, x₅), x₂ = x₁, x₂ = dup(x₆, x₃), x₃ = con(x₇, x₀)`: the principal port of each
cell on an auxiliary port of the next, `con → dup` through the wire `x₁ — x₂`. -/
def circle3 : Net sig ℕ :=
  s(var 0, mkCon (var 1) (var 5)) ::ₘ s(var 2, var 1) ::ₘ s(var 2, mkDup (var 6) (var 3)) ::ₘ
    {s(var 3, mkCon (var 7) (var 0))}

/-- `circle3` is linear. -/
theorem circle3_linear : circle3.Linear := by
  intro y
  simp only [circle3, Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_var, vars_mkCon,
    vars_mkDup, Multiset.count_add, Multiset.count_singleton]
  split_ifs <;> omega

/-- No equation of `circle3` is literally a vicious circle `x = t` with `x` a leaf of `t`. -/
theorem circle3_not_literal :
    ¬ ∃ (x : ℕ) (t : Term sig ℕ), x ∈ t.vars ∧ s(var x, t) ∈ circle3 := by
  rintro ⟨x, t, hx, hm⟩
  simp only [circle3, Multiset.mem_cons, Multiset.mem_singleton,
    Sym2.eq_iff, var.injEq] at hm
  rcases hm with (⟨rfl, rfl⟩ | ⟨h, -⟩) | (⟨rfl, rfl⟩ | ⟨h, rfl⟩) | (⟨rfl, rfl⟩ | ⟨h, -⟩) |
      (⟨rfl, rfl⟩ | ⟨h, -⟩) <;>
    first | (simp at hx; done) | simp [mkCon, mkDup] at h | (subst h; simp at hx)

/-- **A vicious circle of length 3 over four equations is a vicious circle** (Lafont 1997,
page 79): `Net.HasVicious` contracts the wire and the three equations of `circle3` into one
equation `x = t` with `x` a leaf of `t`. -/
theorem circle3_hasVicious : circle3.HasVicious := by
  refine Net.ChainVicious.hasVicious ⟨circle3, 0, ⟨0, 1, mkCon (var 1) (var 5),
    s(var 1, var 2) ::ₘ s(var 2, mkDup (var 6) (var 3)) ::ₘ {s(var 3, mkCon (var 7) (var 0))},
    by simp, .cons (by simp) (.cons (by simp) (.cons (by simp) (.nil 0))), ?_⟩, by simp⟩
    circle3_linear
  rw [circle3, Sym2.eq_swap (a := var 2) (b := var 1)]

/-! ## A cycle through auxiliary ports is not a vicious circle -/

/-- `x₀ = con(x₂, x₃), x₁ = dup(x₂, x₃)`: the auxiliary ports of `con` joined to those of `dup`,
the principal ports free. -/
def auxCycle : Net sig ℕ :=
  s(var 0, mkCon (var 2) (var 3)) ::ₘ {s(var 1, mkDup (var 2) (var 3))}

/-- `auxCycle` is linear. -/
theorem auxCycle_linear : auxCycle.Linear := by
  intro y
  simp only [auxCycle, Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_var, vars_mkCon,
    vars_mkDup, Multiset.count_add, Multiset.count_singleton]
  split_ifs <;> omega

/-- `x₀ = con(x₁, x₂), x₁ = dup(x₂, x₃)`: the principal port of `dup` on the first auxiliary port
of `con`, the first auxiliary port of `dup` on the second auxiliary port of `con`. -/
def mixedCycle : Net sig ℕ :=
  s(var 0, mkCon (var 1) (var 2)) ::ₘ {s(var 1, mkDup (var 2) (var 3))}

/-- `mixedCycle` is linear. -/
theorem mixedCycle_linear : mixedCycle.Linear := by
  intro y
  simp only [mixedCycle, Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_var, vars_mkCon,
    vars_mkDup, Multiset.count_add, Multiset.count_singleton]
  split_ifs <;> omega

/-- An equation `x = t` of a net `x₀ = con(a, b), x₁ = dup(c, d)` is one of the two. -/
theorem mem_pair {x : ℕ} {t : Term sig ℕ} {a b c d : Term sig ℕ}
    (hm : s(var x, t) ∈ s(var 0, mkCon a b) ::ₘ ({s(var 1, mkDup c d)} : Net sig ℕ)) :
    (x = 0 ∧ t = mkCon a b) ∨ (x = 1 ∧ t = mkDup c d) := by
  simp only [Multiset.mem_cons, Multiset.mem_singleton, Sym2.eq_iff, var.injEq] at hm
  rcases hm with (h | ⟨h, -⟩) | (h | ⟨h, -⟩)
  · exact Or.inl h
  · simp [mkCon] at h
  · exact Or.inr h
  · simp [mkDup] at h

/-- A net `x₀ = con(a, b), x₁ = dup(c, d)` has no written cut: no equation joins two cells, none
is a wire between two names, and the two equations do not share their name `x₀`, `x₁`. -/
theorem pair_not_chainCut {a b c d : Term sig ℕ} :
    ¬ Net.ChainCut (s(var 0, mkCon a b) ::ₘ ({s(var 1, mkDup c d)} : Net sig ℕ)) := by
  rintro ⟨a', b', xs, D, ha, hb, h⟩
  match xs, h with
  | [], h =>
    have hm : s(a', b') ∈ s(var 0, mkCon a b) ::ₘ ({s(var 1, mkDup c d)} : Net sig ℕ) := by
      rw [h]; simp
    simp only [Multiset.mem_cons, Multiset.mem_singleton, Sym2.eq_iff] at hm
    rcases hm with (⟨rfl, -⟩ | ⟨-, rfl⟩) | (⟨rfl, -⟩ | ⟨-, rfl⟩) <;>
      first | exact Cut.not_isCell_var _ ha | exact Cut.not_isCell_var _ hb
  | [y], h =>
    rw [Cut.chain_cons, Cut.chain_nil, Multiset.cons_add, Multiset.singleton_add] at h
    rcases pair_eq_cons_cons h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Sym2.eq_iff, var.injEq] at h1 h2 <;>
      rcases h1 with ⟨rfl, -⟩ | ⟨-, h1⟩ <;>
      first
        | exact Cut.not_isCell_var _ ha
        | (rcases h2 with ⟨h2, -⟩ | ⟨-, rfl⟩
           · omega
           · exact Cut.not_isCell_var _ hb)
  | y :: z :: zs, h =>
    have hm : s(var y, var z) ∈ s(var 0, mkCon a b) ::ₘ ({s(var 1, mkDup c d)} : Net sig ℕ) := by
      rw [h, Cut.chain_cons, Cut.chain_cons]; simp
    simp only [Multiset.mem_cons, Multiset.mem_singleton, Sym2.eq_iff, var.injEq] at hm
    rcases hm with (⟨-, h⟩ | ⟨h, -⟩) | (⟨-, h⟩ | ⟨h, -⟩) <;> simp [mkCon, mkDup] at h

/-- **Two cells joined by their auxiliary ports form a reduced net** (Lafont 1997, page 79):
`auxCycle` has no cut and no vicious circle, although its two cells form a cycle. The names
`x₀`, `x₁` on the left are leaves of no tree, so no equation can be in a circle
(`IsCircle.head_leaf`). -/
theorem auxCycle_isReduced : auxCycle.IsReduced := by
  refine ⟨fun hc => pair_not_chainCut ((Net.hasCut_iff_chainCut auxCycle_linear).1 hc),
    fun hv => ?_⟩
  obtain ⟨K, D, hK, h⟩ := hv.chainVicious
  obtain ⟨x, y, t, C, hy, hC, rfl⟩ := hK
  have hsub : ∀ e ∈ s(var x, t) ::ₘ C, e ∈ auxCycle := fun e he => h ▸ Multiset.mem_add.2 (.inl he)
  obtain ⟨x₀, t₀, he, x', t', hm', hx⟩ :=
    IsCircle.head_leaf ⟨x, y, t, C, hy, hC, rfl⟩ (Multiset.mem_cons_self _ _)
  have hm₀ := hsub _ (Multiset.mem_cons_self _ _)
  rw [he] at hm₀
  rcases mem_pair hm₀ with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    rcases mem_pair (hsub _ hm') with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp at hx

/-- **A cycle half principal, half auxiliary, is not a vicious circle** (Lafont 1997, page 79):
`mixedCycle` is reduced. Its principal path `dup → con` stops at the free port `x₀`. -/
theorem mixedCycle_isReduced : mixedCycle.IsReduced := by
  refine ⟨fun hc => pair_not_chainCut ((Net.hasCut_iff_chainCut mixedCycle_linear).1 hc),
    fun hv => ?_⟩
  obtain ⟨K, D, hK, h⟩ := hv.chainVicious
  have hsub : ∀ e ∈ K, e ∈ mixedCycle := fun e he => h ▸ Multiset.mem_add.2 (.inl he)
  -- the equation `x₀ = con(x₁, x₂)` is in no circle: `x₀` is a leaf of no tree
  have h0 : s(var 0, mkCon (var 1) (var 2)) ∉ K := by
    intro he
    obtain ⟨x₀, t₀, he', x', t', hm', hx⟩ := IsCircle.head_leaf hK he
    have hx₀ : x₀ = 0 := by
      rcases Sym2.eq_iff.1 he' with ⟨h1, -⟩ | ⟨-, h1⟩
      · exact (var.inj h1).symm
      · simp [mkCon] at h1
    subst hx₀
    rcases mem_pair (hsub _ hm') with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp at hx
  obtain ⟨x, y, t, C, hy, hC, rfl⟩ := hK
  obtain ⟨x₀, t₀, he, x', t', hm', hx⟩ :=
    IsCircle.head_leaf ⟨x, y, t, C, hy, hC, rfl⟩ (Multiset.mem_cons_self _ _)
  rcases mem_pair (hsub _ hm') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h0 hm'
  · have hm₀ := hsub _ (Multiset.mem_cons_self _ _)
    rw [he] at hm₀
    rcases mem_pair hm₀ with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp at hx

/-! ## A net that is not reduced -/

/-- `x₀ = con(x₁, x₂), x₁ = dup(x₃, x₀)`: the principal port of `dup` on an auxiliary port of
`con`, and that of `con` on an auxiliary port of `dup`. -/
def circle2 : Net sig ℕ :=
  s(var 0, mkCon (var 1) (var 2)) ::ₘ {s(var 1, mkDup (var 3) (var 0))}

/-- `circle2` is linear. -/
theorem circle2_linear : circle2.Linear := by
  intro y
  simp only [circle2, Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_var, vars_mkCon,
    vars_mkDup, Multiset.count_add, Multiset.count_singleton]
  split_ifs <;> omega

/-- **Two cells in a vicious circle of length 2 are not a reduced net** (Lafont 1997, page 79).
`circle2` has no cut, but a vicious circle. -/
theorem circle2_not_isReduced : ¬ circle2.HasCut ∧ circle2.HasVicious ∧ ¬ circle2.IsReduced := by
  have hv : circle2.HasVicious :=
    Net.ChainVicious.hasVicious ⟨circle2, 0, ⟨0, 1, mkCon (var 1) (var 2),
      {s(var 1, mkDup (var 3) (var 0))}, by simp, .cons (by simp) (.nil 0), rfl⟩, by simp⟩
      circle2_linear
  exact ⟨fun hc => pair_not_chainCut ((Net.hasCut_iff_chainCut circle2_linear).1 hc), hv,
    fun h => h.2 hv⟩

end INet.ViciousReview
