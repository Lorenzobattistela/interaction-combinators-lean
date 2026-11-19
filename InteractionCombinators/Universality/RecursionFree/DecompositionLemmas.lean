import InteractionCombinators.Universality.RecursionFree.Decomposition
import InteractionCombinators.Core.Combinators
import InteractionCombinators.Text.RenameMany
import InteractionCombinators.Text.Instance

/-!
# General lemmas first proved in the review of the decomposition (page 85)

These lemmas were proved in `DecompositionCheck.lean` and `DecompositionReview.lean` and are used
by library files. They keep their names, including the namespaces `Comb.DecompositionCheck` and
`Comb.DecompositionReview`.

* `Comb.DecompositionCheck.termDecEq` — decidable equality of trees, and the instances that let
  `decide` compare nets of the combinators.
* `Equiv.sol_iff` — nets that are the same graph have the same solutions on their free ports
  (an invariant of `Equiv`, explained in `DecompositionReview.lean`).
* `Comb.DecompositionReview.pl`, `pr`, `pw` — the names of a rule written as trees.
* `Comb.DecompositionReview.equiv_wire_of_eq` — one wire substitution between two nets given as
  texts.
-/

namespace INet.Comb.DecompositionCheck

open Term Rule

/-- Equality of trees is decidable when equality of symbols and of names is: compare the
symbols, then the subtrees. Only used to let `decide` compare nets in this file. -/
def termDecEq {S : Signature} [DecidableEq S.Sym] {ν : Type} [DecidableEq ν] :
    (t u : Term S ν) → Decidable (t = u)
  | .var x, .var y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse fun e => h (by cases e; rfl)
  | .var _, .app _ _ => isFalse fun e => by cases e
  | .app _ _, .var _ => isFalse fun e => by cases e
  | .app α ts, .app β us =>
    if h : α = β then by
      subst h
      exact
        haveI : ∀ i, Decidable (ts i = us i) := fun i => termDecEq (ts i) (us i)
        if h' : ∀ i, ts i = us i then isTrue (congrArg _ (funext h'))
        else isFalse fun e => by cases e; exact h' fun _ => rfl
    else isFalse fun e => by cases e; exact h rfl

instance : DecidableEq sig.Sym := inferInstanceAs (DecidableEq Comb)

instance {ν : Type} [DecidableEq ν] : DecidableEq (Term sig ν) := termDecEq

end INet.Comb.DecompositionCheck

namespace INet

variable {S : Signature} {ν μ : Type}

open Term

/-! ### Solutions of a net -/

/-- `s` solves the net `N`: the two sides of every equation become the same tree when each name
`x` is replaced by `s x`. -/
def Net.Solves (s : ν → Term S μ) (N : Net S ν) : Prop :=
  ∀ e ∈ N, Sym2.lift ⟨fun u v => u.bind s = v.bind s, fun _ _ => propext eq_comm⟩ e

/-- A solution of `u = v` and of `N` is a solution of the net `u = v, N`. -/
theorem Net.solves_cons {s : ν → Term S μ} {u v : Term S ν} {N : Net S ν} :
    Net.Solves s (s(u, v) ::ₘ N) ↔ u.bind s = v.bind s ∧ Net.Solves s N := by
  simp [Net.Solves]

variable [DecidableEq ν]

/-- Plugging into a substituted tree is plugging into the tree, with `x` sent to the image of the
tree substituted for it. -/
theorem Term.bind_subst_update (s : ν → Term S μ) (a : Term S ν) (x : ν) (t : Term S ν) :
    (a.subst x t).bind s = a.bind (Function.update s x (t.bind s)) := by
  unfold Term.subst
  rw [Term.bind_bind]
  refine Term.bind_congr fun y _ => ?_
  by_cases h : y = x
  · subst h; simp
  · simp [h]

/-- The values on the free ports of `N` that extend to a solution of `N`. -/
def Net.Sol (N : Net S ν) (s : ν → Term S μ) : Prop :=
  ∃ s', Net.Solves s' N ∧ ∀ p, N.vars.count p = 1 → s' p = s p

/-- A wire substitution does not change the values on the free ports that extend to a solution:
the eliminated wire `x` takes the value of the tree plugged into it. -/
theorem Wire.sol_iff {N M : Net S ν} (h : Wire N M) (s : ν → Term S μ) :
    N.Sol s ↔ M.Sol s := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hfree := (Wire.mk x t a b Δ hlin hx).free_iff
  have hc := hlin x
  have hx1 := Multiset.one_le_count_iff_mem.2 hx
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hc hx1
  have ht : x ∉ t.vars := fun h => by
    have := Multiset.one_le_count_iff_mem.2 h; omega
  have hΔ : x ∉ Δ.vars := fun h => by
    have := Multiset.one_le_count_iff_mem.2 h; omega
  constructor
  · rintro ⟨s', hs, hp⟩
    rw [Net.solves_cons, Net.solves_cons] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    have hu : Function.update s' x (t.bind s') = s' := by
      rw [Function.update_eq_self_iff]; exact h1.symm
    refine ⟨s', Net.solves_cons.2 ⟨?_, h3⟩, fun p hp1 => hp p ((hfree p).2 hp1)⟩
    rw [Term.bind_subst_update, Term.bind_subst_update, hu]
    exact h2
  · rintro ⟨s', hs, hp⟩
    rw [Net.solves_cons] at hs
    obtain ⟨h2, h3⟩ := hs
    set s'' := Function.update s' x (t.bind s')
    have hts : t.bind s'' = t.bind s' :=
      Term.bind_congr fun y hy => Function.update_of_ne (fun e => ht (by rw [← e]; exact hy)) _ _
    refine ⟨s'', ?_, fun p hp1 => ?_⟩
    · rw [Net.solves_cons, Net.solves_cons]
      refine ⟨by simp [s'', hts],
        by rwa [Term.bind_subst_update, Term.bind_subst_update] at h2, ?_⟩
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have hv : ∀ y ∈ u.vars + v.vars, y ≠ x := fun y hy e => hΔ (e ▸ Multiset.mem_bind.2
          ⟨s(u, v), he, by simpa using hy⟩)
        have key := h3 _ he
        simp only [Sym2.lift_mk] at key ⊢
        rw [Term.bind_congr (g := s') fun y hy =>
            Function.update_of_ne (hv y (Multiset.mem_add.2 (Or.inl hy))) _ _,
          Term.bind_congr (f := s'') (g := s') fun y hy =>
            Function.update_of_ne (hv y (Multiset.mem_add.2 (Or.inr hy))) _ _]
        exact key
    · have hpx : p ≠ x := by
        rintro rfl
        simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
          Multiset.count_singleton_self] at hp1
        omega
      rw [show s'' p = s' p from Function.update_of_ne hpx _ _]
      exact hp p ((hfree p).1 hp1)

/-- Nets that are the same graph have the same solutions on their free ports. -/
theorem Equiv.sol_iff {N M : Net S ν} (h : Equiv N M) (s : ν → Term S μ) :
    N.Sol s ↔ M.Sol s := by
  induction h with
  | rel _ _ h => exact h.sol_iff s
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end INet

namespace INet.Comb.DecompositionReview

open Term Rule

/-- A port of the first cell. -/
abbrev pl {a b m : ℕ} (i : Fin a) : Term sig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inl i)
/-- A port of the second cell (in a side: a middle wire). -/
abbrev pr {a b m : ℕ} (j : Fin b) : Term sig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inr (.inl j))
/-- An internal wire. -/
abbrev pw {a b m : ℕ} (w : Fin m) : Term sig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inr (.inr w))

/-- One wire substitution between two nets given as texts. -/
theorem equiv_wire_of_eq {ν : Type} [DecidableEq ν] {N M : Net sig ν} (x : ν) (t a b : Term sig ν)
    (Δ : Net sig ν) (hlin : Net.Linear (s(var x, t) ::ₘ s(a, b) ::ₘ Δ)) (hx : x ∈ a.vars + b.vars)
    (hN : N = s(var x, t) ::ₘ s(a, b) ::ₘ Δ) (hM : M = s(a.subst x t, b.subst x t) ::ₘ Δ) :
    Equiv N M := by
  rw [hN, hM]
  exact (Wire.mk x t a b Δ hlin hx).equiv

end INet.Comb.DecompositionReview
