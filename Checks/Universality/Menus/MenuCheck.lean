import InteractionCombinators.Universality.Menus.Menu
import Checks.Universality.Menus.PackageCheck

/-!
# Checks of `InteractionCombinators/Universality/Menus/Menu.lean` against the paper

A review (issue 36) compared `menu`, `selector`, `menu_selector` and `IsPackage.menu` with Lafont
1997, page 84 (and pages 82–83 for `M_n`, `M_n*`). This file records the cases worked by hand, as
statements that Lean checks.

Ports are numbered as in `BasicCheck.lean`: on a cell drawn with its principal port up, the left
auxiliary port is 2 and the right one is 1; `mkCon a b` has `a` on port 1 and `b` on port 2.
The selector `Sⁱₙ` of page 84 is `M_n*` drawn with its principal port up, with `i - 1` erasers to
the left of its free wire and `n - i` to the right; Lafont counts `i` from 1. The code counts from
0, so `selector n i x` should be `S^{i+1}_n`: `i` erasers on the left, `n - i - 1` on the right.

* `selector_shapes` — the three selectors of arity 3, as trees. Read with the numbering above, the
  free wire is at position 1, 2, 3 from the left for `i = 0, 1, 2`: `selector 3 i` is `S^{i+1}_3`.
* `menu_selector_wires` — the multiplexor step alone, on free leaves: the free port of
  `selector 3 2` faces the third tree of the menu, not the first (no reversal).
* `menu_selector_three` — `menu_selector` for `n = 3`, `i = 2`, three distinct packages: it
  extracts the third one, `dup(1, 1)`. Its hypotheses hold, so the theorem is not vacuous for
  `n ≥ 3`. `menu_selector_three_first` does the same for `i = 0`.
* `menu_selector_needs_isPackage` — without `IsPackage` the conclusion fails: a free wire on a
  non-selected port of the menu stays free.
* `menu_selector_needs_linear` — without linearity the conclusion fails.
* `steps_count_of_mem`, `menu_selector_not_red` — literal reduction `Red` does not suffice:
  erasing a package with an internal wire needs a wire substitution, hence `StepsE`.
* `menu_nil`, `menu_singleton`, `not_isPackage_menu_shared`, `isPackage_menu_three` — a menu of
  zero packages is `ε`, of one package is that package; the disjointness hypothesis of
  `IsPackage.menu` cannot be dropped; it holds for the three packages above.
-/

namespace INet.Comb.MenuCheck

open Term

/-! ## Indexing -/

/-- The selectors `S¹₃`, `S²₃`, `S³₃` of page 84 are `selector 3 0`, `selector 3 1`, `selector 3 2`.
With the principal port up (port 2 left, port 1 right), `con(con(x, ε), ε)` reads `ε, ε, x` from
left to right, `con(con(ε, x), ε)` reads `ε, x, ε`, and `con(con(ε, ε), x)` reads `x, ε, ε`. -/
theorem selector_shapes (x : ℕ) :
    (selector 3 0 x : Term sig ℕ) = mkCon (mkCon mkEra mkEra) (var x) ∧
      (selector 3 1 x : Term sig ℕ) = mkCon (mkCon mkEra (var x)) mkEra ∧
      (selector 3 2 x : Term sig ℕ) = mkCon (mkCon (var x) mkEra) mkEra :=
  ⟨rfl, rfl, rfl⟩

/-- Page 84, the multiplexor step of `menu_selector` on free leaves: `M_3` with leaves `10, 11, 12`
against `selector 3 2` with free port `2` joins `12` (the third leaf) to `2`, and the other two
leaves to erasers. -/
theorem menu_selector_wires :
    Red {s(menu [var 10, var 11, var 12], selector 3 2 2)}
      (s(var 10, mkEra) ::ₘ s(var 11, mkEra) ::ₘ {s(var 12, var 2)}) := by
  have h := mux_muxStar [var 10, var 11, var 12] [mkEra, mkEra, var 2] 0 rfl
  refine h.cast rfl ?_
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, ← Multiset.cons_coe,
    Multiset.coe_nil, add_zero]
  rfl

/-- The package `dup(x, x)`. -/
theorem isPackage_mkDup_var (x : ℕ) : (mkDup (var x) (var x) : Term sig ℕ).IsPackage := by
  intro y hy
  simp only [vars_mkDup, vars_var, Multiset.mem_add, Multiset.mem_singleton, or_self] at hy
  subst hy
  simp

/-- Three distinct packages: `ε`, `con(0, 0)`, `dup(1, 1)`. -/
abbrev three : List (Term sig ℕ) := [mkEra, mkCon (var 0) (var 0), mkDup (var 1) (var 1)]

theorem isPackage_three : ∀ π ∈ three, π.IsPackage := by
  intro π hπ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hπ
  rcases hπ with rfl | rfl | rfl
  · exact isPackage_mkEra
  · exact isPackage_mkCon_var 0
  · exact isPackage_mkDup_var 1

theorem linear_three (i : ℕ) (hi : i < 3) :
    Net.Linear ({s(menu three, selector three.length i 2)} : CNet) := by
  intro y
  interval_cases i <;>
  · simp only [three, menu, selector, List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.replicate, List.nil_append, List.cons_append, mux, muxStar,
      Net.vars_singleton, eqVars_mk, vars_mkEra, vars_mkCon, vars_mkDup, vars_var,
      zero_add, add_zero, Multiset.count_add, Multiset.count_singleton]
    split_ifs <;> omega

/-- `menu_selector` (page 84) for `n = 3`, `i = 2` (Lafont's `S³₃`): the menu `ε & γ(0,0) & δ(1,1)`
against `selector 3 2` extracts the third package `δ(1, 1)`. -/
theorem menu_selector_three :
    StepsE system {s(menu three, selector 3 2 2)} {s(mkDup (var 1) (var 1), var 2)} := by
  have h := menu_selector three 2 (by simp) 2 isPackage_three 0 (linear_three 2 (by omega))
  simpa using h

/-- `menu_selector` for `n = 3`, `i = 0` (Lafont's `S¹₃`): the same menu gives the first package
`ε`. -/
theorem menu_selector_three_first :
    StepsE system {s(menu three, selector 3 0 2)} {s(mkEra, var 2)} := by
  have h := menu_selector three 0 (by simp) 2 isPackage_three 0 (linear_three 0 (by omega))
  simpa using h

/-! ## The hypotheses of `menu_selector` are needed -/

/-- Without `IsPackage` the conclusion of `menu_selector` is false: the menu `0 & ε` (a free wire
on the first port) against `S²₂` with free port `1` is linear, but the free port `0` stays free, so
the net does not reduce to `ε – 1`. -/
theorem menu_selector_needs_isPackage :
    ({s(menu [var 0, mkEra], selector 2 1 1)} : CNet).Linear ∧
      ¬ StepsE system {s(menu [var 0, mkEra], selector 2 1 1)} {s(mkEra, var 1)} := by
  refine ⟨fun y => ?_, fun h => ?_⟩
  · simp only [menu, selector, Nat.reduceSub, List.replicate, List.nil_append, List.cons_append,
      mux, muxStar, Net.vars_singleton, eqVars_mk, vars_mkEra, vars_mkCon, vars_var, add_zero,
      Multiset.count_add, Multiset.count_singleton]
    split_ifs <;> omega
  · have := PackageCheck.stepsE_free h (y := 0) (by
      simp [menu, selector, mux, muxStar, List.replicate])
    simp at this

/-- Without linearity the conclusion of `menu_selector` is false: with the menu `γ(0,0) & ε`, the
selector `S²₂` and a context that also uses `0`, the name `0` has three ends, a number that
reduction keeps, while the conclusion has only one. -/
theorem menu_selector_needs_linear :
    ¬ StepsE system (s(menu [mkCon (var 0) (var 0), mkEra], selector 2 1 1) ::ₘ {s(mkEra, var 0)})
      (s(mkEra, var 1) ::ₘ {s(mkEra, var 0)}) := by
  intro h
  have := PackageCheck.stepsE_count_of_three_le h (y := 0) (by
    simp [menu, selector, mux, muxStar, List.replicate])
  simp [menu, selector, mux, muxStar, List.replicate] at this

/-- Literal reduction keeps the number of occurrences of a name already in the net. -/
theorem steps_count_of_mem {N M : CNet} (h : Steps system N M) {y : ℕ} (hy : y ∈ N.vars) :
    M.vars.count y = N.vars.count y := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    rw [PackageCheck.step_count_of_mem hs (Multiset.one_le_count_iff_mem.1 (by
      rw [ih]; exact Multiset.one_le_count_iff_mem.2 hy)), ih]

/-- `StepsE` cannot be replaced by `Red` in `menu_selector`: the menu `γ(0,0) & ε` against `S²₂`
does not reach `ε – 1` by literal interactions, since they keep the two ends of the internal wire
`0`. Up to wires it does (`menu_selector`): the two erasers left on `0` meet after a wire
substitution. -/
theorem menu_selector_not_red :
    ¬ Red {s(menu [mkCon (var 0) (var 0), mkEra], selector 2 1 1)} {s(mkEra, var 1)} := by
  intro h
  have := steps_count_of_mem h (y := 0) (by simp [menu, selector, mux, muxStar, List.replicate])
  simp [menu, selector, mux, muxStar, List.replicate] at this

/-! ## A menu is a package -/

/-- A menu of no package is `M_0 = ε`, and a menu of one package is that package (`M_1` is a
wire). -/
theorem menu_nil_singleton (π : Term sig ℕ) : menu [] = (mkEra : Term sig ℕ) ∧ menu [π] = π :=
  ⟨rfl, rfl⟩

/-- The disjointness hypothesis of `IsPackage.menu` cannot be dropped: the menu of two copies of the
package `γ(0, 0)` uses the wire `0` four times. In the paper the packages are separate nets, so
their wires are distinct; in the text they must be given distinct names. -/
theorem not_isPackage_menu_shared :
    ¬ (menu [mkCon (var 0) (var 0), mkCon (var 0) (var 0)] : Term sig ℕ).IsPackage :=
  PackageCheck.not_isPackage_mkCon_shared

/-- `IsPackage.menu` applies to the three packages `ε`, `γ(0, 0)`, `δ(1, 1)`. -/
theorem isPackage_menu_three : (menu three).IsPackage := by
  refine IsPackage.menu three isPackage_three ?_
  simp only [three, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.Pairwise.nil, forall_eq, vars_mkEra, vars_mkCon, vars_mkDup, vars_var,
    Multiset.mem_add, Multiset.mem_singleton, or_self, IsEmpty.forall_iff, implies_true, and_true,
    true_and, Multiset.notMem_zero]
  omega

end INet.Comb.MenuCheck
