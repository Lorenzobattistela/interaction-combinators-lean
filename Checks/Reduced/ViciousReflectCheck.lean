import InteractionCombinators.Reduced.ViciousReflect
import Checks.Reduced.ViciousCheck

/-!
# Checks of the third point of Proposition 3 and of Proposition 3 (page 80)

The setting of `Checks/Reduced/ViciousCheck.lean`: a symbol `o` with no auxiliary port, a symbol `w`
with one, and the non-strict translation `Φ` that keeps `o` and turns `w` into a wire (it is not the
identity: `CutCheck.not_strict`).

* `Translation.NetTr.hasVicious_reflect` is not vacuous: the circle of length 2
  `x₀ = w(x₁), x₁ = w(x₀)` (`ViciousCheck.loop2`, two equations) translates to the circle of wires
  `x₀ = x₁, x₁ = x₀`, and the theorem gives back a vicious circle of `loop2`. The other branch is
  excluded: `loop2` has no cut.
* `Translation.NetTr.isReduced` is not vacuous: the tree `w(o)` on the free port `x₀` is reduced,
  and
  so is its translation `x₀ = o`.
-/

namespace INet.ViciousReflectCheck

open Term CutCheck ViciousCheck

@[simp] theorem var_ne_w (x : ℕ) (t : Term sig ℕ) : (var x : Term sig ℕ) ≠ w t := fun h => by
  cases h

@[simp] theorem w_ne_var (x : ℕ) (t : Term sig ℕ) : w t ≠ (var x : Term sig ℕ) := fun h => by
  cases h

/-- The number of equations of a chain of wires. -/
theorem card_chain (a b : Term sig ℕ) :
    ∀ xs : List ℕ, Multiset.card (Cut.chain a xs b) = xs.length + 1
  | [] => by simp
  | y :: ys => by
    rw [Cut.chain_cons, Multiset.card_cons, card_chain (var y) b ys, List.length_cons]

/-! ## A circle of two equations, followed back -/

/-- `x₀ = x₁, x₁ = x₀`: a vicious circle made of two wires. -/
def wires2 : Net sig ℕ := s(var 0, var 1) ::ₘ {s(var 1, var 0)}

theorem wires2_linear : wires2.Linear := by
  intro y
  simp only [wires2, Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_var,
    Multiset.count_add, Multiset.count_singleton]
  split_ifs <;> omega

/-- `x₀ = x₁, x₁ = x₀` has a vicious circle (page 79), written with its two equations. -/
theorem wires2_hasVicious : wires2.HasVicious :=
  Net.ChainVicious.hasVicious ⟨wires2, 0, ⟨0, 1, var 1, {s(var 1, var 0)}, by simp,
    .cons (by simp) (.nil 0), rfl⟩, by simp⟩ wires2_linear

/-- `Φ` translates `x₀ = w(x₁), x₁ = w(x₀)` to `x₀ = x₁, x₁ = x₀`. -/
theorem netTr_loop2 : Φ.NetTr loop2 wires2 := by
  have ha : ∀ k : ℕ, Φ.TermTr (w (var k)) (var k) := fun k =>
    Translation.TermTr.app (Φ := Φ) true (fun _ => var k) (fun _ => var k) (fun _ => 0)
      fun _ => .var k
  exact ⟨Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, .var 0, ha 1⟩
    (Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, .var 1, ha 0⟩ Multiset.Rel.zero), wires2_linear⟩

/-- `x₀ = w(x₁), x₁ = w(x₀)` has no cut (page 79): each equation joins a cell to a name, and the
two equations do not make a chain between the principal ports of two cells. -/
theorem loop2_not_hasCut : ¬ loop2.HasCut := by
  intro hc
  obtain ⟨a, b, xs, D, ha, hb, h⟩ := hc.chainCut
  have hcard := congrArg Multiset.card h
  rw [Multiset.card_add, card_chain] at hcard
  have h2 : Multiset.card loop2 = 2 := rfl
  rcases xs with _ | ⟨y, _ | ⟨y', ys⟩⟩
  · have hm : s(a, b) ∈ loop2 := by rw [h]; simp
    simp only [loop2, Multiset.mem_cons, Multiset.mem_singleton, Sym2.eq_iff] at hm
    rcases hm with (⟨rfl, -⟩ | ⟨-, rfl⟩) | (⟨rfl, -⟩ | ⟨-, rfl⟩)
    · exact Cut.not_isCell_var _ ha
    · exact Cut.not_isCell_var _ hb
    · exact Cut.not_isCell_var _ ha
    · exact Cut.not_isCell_var _ hb
  · have hD : D = 0 := Multiset.card_eq_zero.1 (by simp at hcard; omega)
    subst hD
    have h1 : s(a, var y) ∈ loop2 := by rw [h]; simp
    have h3 : s(var y, b) ∈ loop2 := by rw [h]; simp
    have h4 : s(var 1, w (var 0)) ∈ Cut.chain a [y] b + 0 := by rw [← h]; simp [loop2]
    have h5 : s(var 0, w (var 1)) ∈ Cut.chain a [y] b + 0 := by rw [← h]; simp [loop2]
    simp only [loop2, Multiset.mem_cons, Multiset.mem_singleton, Sym2.eq_iff, var_ne_w,
      and_false, false_or] at h1 h3
    rcases h1 with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;> rcases h3 with ⟨h3, rfl⟩ | ⟨h3, rfl⟩ <;>
      simp_all
  · simp at hcard
    omega

/-- **The third point of Proposition 3, on a circle of two equations** (page 80): `Φ` turns the
circle `x₀ = w(x₁), x₁ = w(x₀)` into the circle of wires `x₀ = x₁, x₁ = x₀`, and
`Translation.NetTr.hasVicious_reflect` gives back a vicious circle of the source. -/
theorem loop2_hasVicious_reflect : loop2.HasVicious :=
  (netTr_loop2.hasVicious_reflect wires2_hasVicious).resolve_right loop2_not_hasCut

/-! ## A reduced net and its translation -/

/-- `Φ` translates `x₀ = w(o)` to `x₀ = o`. -/
theorem netTr_tree : Φ.NetTr {s(var 0, w o)} tgt := by
  have ho : Φ.TermTr o o :=
    Translation.TermTr.app (Φ := Φ) false _ (Fin.elim0 : Fin 0 → Term sig ℕ) (fun _ => 0)
      fun i => i.elim0
  have ha : Φ.TermTr (w o) o :=
    Translation.TermTr.app (Φ := Φ) true (fun _ => o) (fun _ => o) (fun _ => 0) fun _ => ho
  refine ⟨Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, .var 0, ha⟩ Multiset.Rel.zero, fun y => ?_⟩
  simp only [tgt, Net.vars_singleton, eqVars_mk, vars_o, vars_var, Multiset.count_add,
    Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- **Proposition 3 on a tree** (page 80): the tree `w(o)` on the free port `x₀` is reduced, so its
translation `x₀ = o` is reduced (`Translation.NetTr.isReduced`). -/
theorem tgt_isReduced : tgt.IsReduced :=
  netTr_tree.isReduced (Net.isReduced_tree (by simp))

end INet.ViciousReflectCheck
