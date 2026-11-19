import InteractionCombinators.Lafont.ReducedDecompUnique
import Checks.ReducedDecompReview

/-!
# Checks for Proposition 2, uniqueness (page 79)

* `pendant_not_normal`, `merged_normal` — `0 = 7, 2 = con(7, 3)` (the net `pendant` of the
  review) is in the form `Net.IsTreesOnWiring` but not in the normal form
  `Net.IsTreesOnWiringN`, because of the equation `0 = 7` with `7` internal: the new condition is
  not vacuous. One wire substitution contracts it to `2 = con(0, 3)` (`merged`), which is in
  normal form; `Net.IsReduced.exists_treesOnWiringN` applies to it.
* `renamed_unique` — `0 = con(2, 2)` and `0 = con(5, 5)` are in normal form and equivalent;
  `Net.IsTreesOnWiringN.unique` applies, and the renaming it gives sends `2` to `5`. So the
  conclusion cannot be strengthened to equality of the nets.
-/

namespace INet.ReducedDecompUniqueCheck

open Term Comb ReducedDecompReview

/-! ## `pendant`, contracted to its normal form -/

/-- `pendant` (`0 = 7, 2 = con(7, 3)`) is in the form `Net.IsTreesOnWiring` and **not** in the
normal form: `0 = 7` hangs the free port `0` on the internal name `7` (page 79). -/
theorem pendant_not_normal : pendant.IsTreesOnWiring ∧ ¬ pendant.IsTreesOnWiringN := by
  refine ⟨pendant_form, fun h => ?_⟩
  have := h.2 0 7 (by simp [pendant])
  simp [pendant] at this

/-- `merged` (`2 = con(0, 3)`) is in normal form. -/
theorem merged_normal : merged.IsTreesOnWiringN := by
  refine ⟨merged_form, fun x y h => ?_⟩
  simp [merged, mkCon] at h

/-- **`pendant`, contracted to its normal form** (page 79): `pendant` is equivalent to `merged`,
which is in normal form. -/
theorem pendant_to_normal : Equiv pendant merged ∧ merged.IsTreesOnWiringN :=
  ⟨pendant_wire.equiv, merged_normal⟩

/-- **Non-vacuity of Proposition 2, existence in normal form**: the hypotheses hold for `pendant`,
a linear reduced net not in normal form. -/
theorem pendant_exists_normal : ∃ M, Equiv pendant M ∧ M.IsTreesOnWiringN :=
  Net.IsReduced.exists_treesOnWiringN pendant_linear pendant_form.isReduced

/-! ## Two normal forms that differ by a renaming of the wiring -/

/-- `0 = con(2, 2)`: a `con` cell whose auxiliary ports are joined by the wire `2`. -/
def renamedA : Net sig ℕ := s(var 0, mkCon (var 2) (var 2)) ::ₘ 0

/-- `0 = con(5, 5)`: the same graph, the wire named `5`. -/
def renamedB : Net sig ℕ := s(var 0, mkCon (var 5) (var 5)) ::ₘ 0

/-- `renamedA` is linear. -/
theorem renamedA_linear : renamedA.Linear := by
  intro y
  simp only [renamedA, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_mkCon,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- `renamedB` is linear. -/
theorem renamedB_linear : renamedB.Linear := by
  intro y
  simp only [renamedB, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_mkCon,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- `renamedA` is in normal form. -/
theorem renamedA_normal : renamedA.IsTreesOnWiringN := by
  refine ⟨fun e he => ?_, fun x y h => ?_⟩
  · simp only [renamedA, Multiset.mem_cons, Multiset.notMem_zero, or_false] at he
    subst he
    exact ⟨0, _, rfl, by simp [renamedA]⟩
  · simp [renamedA, mkCon] at h

/-- `renamedB` is in normal form. -/
theorem renamedB_normal : renamedB.IsTreesOnWiringN := by
  refine ⟨fun e he => ?_, fun x y h => ?_⟩
  · simp only [renamedB, Multiset.mem_cons, Multiset.notMem_zero, or_false] at he
    subst he
    exact ⟨0, _, rfl, by simp [renamedB]⟩
  · simp [renamedB, mkCon] at h

/-- `renamedA` and `renamedB` are different texts. -/
theorem renamedA_ne_renamedB : renamedA ≠ renamedB := by
  intro h
  have := congrArg (fun N : Net sig ℕ => N.vars.count 2) h
  simp [renamedA, renamedB] at this

/-- **Proposition 2, uniqueness, applied** (page 79): `renamedA` and `renamedB` are equivalent
nets in normal form, so `Net.IsTreesOnWiringN.unique` gives a renaming `ρ` of the wiring, which
fixes the free port `0` and sends the wire `2` to `5`. -/
theorem renamed_unique : ∃ ρ : ℕ → ℕ, ρ 0 = 0 ∧ ρ 2 = 5 ∧
    renamedB = renamedA.bind (fun x => var (ρ x)) := by
  obtain ⟨ρ, hfix, -, hb⟩ := Net.IsTreesOnWiringN.unique renamedA_linear renamedB_linear
    renamedA_normal renamedB_normal renamedA_equiv_renamedB
  have h0 : ρ 0 = 0 := hfix 0 (by simp [renamedA])
  refine ⟨ρ, h0, ?_, hb⟩
  have h5 := congrArg (fun N : Net sig ℕ => N.vars.count 5) hb
  simp only [Net.vars_bind] at h5
  by_contra h2
  simp [renamedA, renamedB, vars_mkCon, h0, Ne.symm h2] at h5

end INet.ReducedDecompUniqueCheck
