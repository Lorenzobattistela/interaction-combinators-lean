import InteractionCombinators.Lafont.GraphEquiv
import InteractionCombinators.Combinators
import InteractionCombinators.Lafont.DecompositionLemmas

/-!
# Check of `Lafont/GraphEquiv.lean`

Lafont 1997, Section 1.1, page 71. Names `x, y, z, w, u = 0, 1, 2, 3, 4`.

* One wire: `x = con(y, z), w = dup(x, u)` becomes `w = dup(con(y, z), u)` (`wire1`). Both nets
  are linear and have graphs (`Net.exists_graph`), so `Wire.hasGraph_iso` applies to actual graphs
  (`wire1_iso`).
* Two wires: `x = con(y, z), u = era, w = dup(x, u)` becomes `w = dup(con(y, z), era)` by
  plugging `x` and then `u` (`equiv2`). `Net.Linear.equiv_hasGraph_iso` applies to its graphs
  (`equiv2_iso`).
-/

namespace INet.GraphEquivCheck

open Comb

/-- A net over `ℕ` is linear if its names that occur occur at most twice; this form is decidable. -/
theorem linear_of_mem {N : Net sig ℕ} (h : ∀ x ∈ N.vars, N.vars.count x ≤ 2) : N.Linear := by
  intro x
  by_cases hx : x ∈ N.vars
  · exact h x hx
  · rw [Multiset.count_eq_zero.2 hx]; omega

/-- `x = con(y, z), w = dup(x, u)`. -/
def net1 : Net sig ℕ :=
  s(.var 0, mkCon (.var 1) (.var 2)) ::ₘ s(.var 3, mkDup (.var 0) (.var 4)) ::ₘ 0

/-- `w = dup(con(y, z), u)`. -/
def net1' : Net sig ℕ := s(.var 3, mkDup (mkCon (.var 1) (.var 2)) (.var 4)) ::ₘ 0

theorem net1_linear : net1.Linear := linear_of_mem (by decide)

/-- One wire substitution, plugging `con(y, z)` into `x` (page 71). -/
theorem wire1 : Wire net1 net1' :=
  Wire.cast (Wire.mk 0 (mkCon (.var 1) (.var 2)) (.var 3) (mkDup (.var 0) (.var 4)) 0
    net1_linear (by decide)) rfl (by decide)

/-- `Wire.hasGraph_iso` on actual graphs of the two nets (page 71). -/
theorem wire1_iso : ∃ G G' : Graph sig ℕ, net1.HasGraph G ∧ net1'.HasGraph G' ∧ G.Iso G' := by
  obtain ⟨G, hG, -⟩ := Net.exists_graph net1
  obtain ⟨G', hG', -⟩ := Net.exists_graph net1'
  exact ⟨G, G', hG, hG', wire1.hasGraph_iso hG hG'⟩

/-- `x = con(y, z), u = era, w = dup(x, u)`. -/
def net2 : Net sig ℕ :=
  s(.var 0, mkCon (.var 1) (.var 2)) ::ₘ s(.var 4, mkEra) ::ₘ
    s(.var 3, mkDup (.var 0) (.var 4)) ::ₘ 0

/-- `w = dup(con(y, z), u), u = era`: after plugging `x`. -/
def net2a : Net sig ℕ :=
  s(.var 3, mkDup (mkCon (.var 1) (.var 2)) (.var 4)) ::ₘ s(.var 4, mkEra) ::ₘ 0

/-- `w = dup(con(y, z), era)`: after plugging `u`. -/
def net2b : Net sig ℕ := s(.var 3, mkDup (mkCon (.var 1) (.var 2)) mkEra) ::ₘ 0

theorem net2_linear : net2.Linear := linear_of_mem (by decide)

/-- The first wire: plug `con(y, z)` into `x`. -/
theorem wire2a : Wire net2 net2a := by
  have e : net2 = s(.var 0, mkCon (.var 1) (.var 2)) ::ₘ s(.var 3, mkDup (.var 0) (.var 4)) ::ₘ
      s(.var 4, mkEra) ::ₘ 0 := Multiset.cons_swap _ _ _ |> congrArg _
  rw [e]
  refine Wire.cast (Wire.mk 0 (mkCon (.var 1) (.var 2)) (.var 3) (mkDup (.var 0) (.var 4)) _
    (e ▸ net2_linear) (by decide)) rfl (by decide)

/-- The second wire: plug `era` into `u`. -/
theorem wire2b : Wire net2a net2b := by
  have hl : net2a.Linear := wire2a.linear_right
  have e : net2a = s(.var 4, mkEra) ::ₘ s(.var 3, mkDup (mkCon (.var 1) (.var 2)) (.var 4)) ::ₘ 0 :=
    Multiset.cons_swap _ _ _
  rw [e] at hl ⊢
  exact Wire.cast (Wire.mk 4 mkEra (.var 3) (mkDup (mkCon (.var 1) (.var 2)) (.var 4)) 0 hl
    (by decide)) rfl (by decide)

/-- `net2` and `net2b` are equivalent by two wire substitutions. -/
theorem equiv2 : Equiv net2 net2b := wire2a.equiv.trans wire2b.equiv

/-- `Net.Linear.equiv_hasGraph_iso` on actual graphs of the two nets (page 71). -/
theorem equiv2_iso : ∃ G G' : Graph sig ℕ, net2.HasGraph G ∧ net2b.HasGraph G' ∧ G.Iso G' := by
  obtain ⟨G, hG, -⟩ := Net.exists_graph net2
  obtain ⟨G', hG', -⟩ := Net.exists_graph net2b
  exact ⟨G, G', hG, hG', net2_linear.equiv_hasGraph_iso equiv2 hG hG'⟩

/-- The two nets are different texts: the equivalence is not equality. -/
theorem net2_ne_net2b : net2 ≠ net2b := fun h => by
  have := congrArg Multiset.card h
  simp [net2, net2b] at this

end INet.GraphEquivCheck
