import InteractionCombinators.Lafont.Package

/-!
# Checks of `Lafont/Package.lean` against the paper

A review (issue 22) compared `Term.IsPackage`, `erase_wiring` and `erase_package` with Lafont
1997, pages 79, 80, 84 and 85. This file records what was checked, as statements that Lean checks.

* `isPackage_iff_one_free` — the definition. A tree `π`, with its root on the name `r`, is a
  linear net whose only free port is `r` exactly when `π.IsPackage` and `r ∉ π.vars`. So
  `IsPackage` says "one free port, the root" (page 80), no more and no less, for nets written as
  one tree.
* `not_isPackage_var` — a bare wire is not a package: it has two free ports.
* `not_step_tree` — a net written as one tree has no active pair (page 79: trees are reduced).
* `equiv_package_wiring` — a package drawn as a tree `τ` and a separate wiring `ω` (page 80) is
  the same graph as the one-tree form used by `IsPackage`.
* `not_isPackage_mkCon_shared` — the disjointness hypothesis of `IsPackage.mkCon` is needed.
* `stepsE_free`, `stepsE_count_of_three_le` — two invariants of `StepsE`: a free port stays a free
  port, and a name occurring three times or more keeps its number of occurrences.
* `erase_wiring_needs_linear`, `erase_package_needs_linear` — without linearity the conclusions of
  `erase_wiring` and `erase_package` are false.
* `erase_package_needs_isPackage_var`, `erase_package_needs_isPackage_con` — an eraser on a tree
  with free leaves does not vanish.
* `erase_package_crossing`, `erase_wiring_two` — instances with a non-empty context, both kinds of
  binary cell and crossed wires.
-/

namespace INet.Comb.PackageCheck

open Term

/-! ## The definition of a package -/

/-- Page 80: "a reduced net with only one free port is called a package". For a net written as
one tree `π` whose root is plugged into the name `r`, being linear with `r` as its only free port
is the same as `π.IsPackage` and `r ∉ π.vars`. -/
theorem isPackage_iff_one_free (π : Term sig ℕ) (r : ℕ) :
    (({s(var r, π)} : CNet).Linear ∧ ∀ y, ({s(var r, π)} : CNet).vars.count y = 1 ↔ y = r) ↔
      π.IsPackage ∧ r ∉ π.vars := by
  have hc : ∀ y, ({s(var r, π)} : CNet).vars.count y =
      (if y = r then 1 else 0) + π.vars.count y := by
    intro y
    simp only [Net.vars_singleton, eqVars_mk, vars_var, Multiset.count_add,
      Multiset.count_singleton]
  constructor
  · rintro ⟨hl, hf⟩
    have hr : r ∉ π.vars := by
      have := (hf r).2 rfl
      simp only [hc, ite_true] at this
      exact Multiset.count_eq_zero.1 (by omega)
    refine ⟨fun x hx => ?_, hr⟩
    have hxr : x ≠ r := fun h => hr (h ▸ hx)
    have h1 := hl x
    have h2 := (hf x).not.2 hxr
    have h3 := Multiset.one_le_count_iff_mem.2 hx
    simp only [hc, hxr, ite_false] at h1 h2
    omega
  · rintro ⟨hπ, hr⟩
    have hy : ∀ y, y ≠ r → π.vars.count y = 0 ∨ π.vars.count y = 2 := by
      intro y _
      by_cases hm : y ∈ π.vars
      · exact Or.inr (hπ y hm)
      · exact Or.inl (Multiset.count_eq_zero.2 hm)
    have hr0 := Multiset.count_eq_zero.2 hr
    refine ⟨fun y => ?_, fun y => ?_⟩
    · rw [hc]
      by_cases h : y = r
      · subst h; simp [hr0]
      · simp only [h, ite_false]; rcases hy y h with h' | h' <;> omega
    · rw [hc]
      by_cases h : y = r
      · subst h; simp [hr0]
      · simp only [h, ite_false, iff_false]; rcases hy y h with h' | h' <;> omega

/-- A wire is not a package (page 80): the net `var x` has two free ports, and Proposition 2 with
one free port gives a tree whose leaves are paired, which a single wire is not. -/
theorem not_isPackage_var (x : ℕ) : ¬ (var x : Term sig ℕ).IsPackage := by
  intro h
  simpa using h x (by simp)

/-- A package is not a bare name. -/
theorem IsPackage.ne_var {π : Term sig ℕ} (hπ : π.IsPackage) (x : ℕ) : π ≠ var x := by
  rintro rfl
  exact not_isPackage_var x hπ

/-- A net written as one tree has no active pair, so no literal interaction (page 79: "trees and
wirings are typical examples of reduced nets"). -/
theorem not_step_tree (π : Term sig ℕ) (r : ℕ) (M : CNet) : ¬ Step system {s(var r, π)} M := by
  intro h
  generalize hN : ({s(var r, π)} : CNet) = N at h
  obtain ⟨α, β, rl, -, as, bs, Δ, -, -, -⟩ := h
  have hm : s(Term.app α as, Term.app β bs) ∈ ({s(var r, π)} : CNet) :=
    hN ▸ Multiset.mem_cons_self _ _
  rw [Multiset.mem_singleton, Sym2.eq_iff] at hm
  rcases hm with ⟨h, -⟩ | ⟨-, h⟩ <;> cases h

/-- The decomposition of page 80, drawn with the wiring `ω` apart from the tree `τ`: a `con` with
its auxiliary ports on `0` and `1`, and the wire `0 – 1`. It is the same graph as the one-tree
form `con(1, 1)` used by `IsPackage`. -/
theorem equiv_package_wiring :
    Equiv (s(var 0, var 1) ::ₘ {s(var 9, mkCon (var 0) (var 1))} : CNet)
      {s(var 9, mkCon (var 1) (var 1))} := by
  refine (wire_con_left (x := 0) (t := var 1) (r := var 9) (c := var 1) (Δ := 0) ?_).equiv
  intro y
  simp only [Net.vars_cons, Net.vars_zero, eqVars_mk, vars_mkCon, vars_var, add_zero,
    Multiset.count_add, Multiset.count_singleton]
  split_ifs <;> omega

/-- The disjointness hypothesis of `IsPackage.mkCon` is needed: two copies of the package
`con(0, 0)` on the ports of a `con` share the wire `0`, which then has four ends. -/
theorem not_isPackage_mkCon_shared :
    ¬ (mkCon (mkCon (var 0) (var 0)) (mkCon (var 0) (var 0)) : Term sig ℕ).IsPackage := by
  intro h
  have := h 0 (by simp)
  simp at this

/-! ## Two invariants of reduction up to wires -/

/-- A literal interaction does not change the number of occurrences of a name already in the
net: the rule is linear, and the wires it creates have new names. -/
theorem step_count_of_mem {N M : CNet} (h : Step system N M) {y : ℕ} (hy : y ∈ N.vars) :
    M.vars.count y = N.vars.count y := by
  obtain ⟨α, β, r, hr, as, bs, Δ, f, -, hfresh⟩ := h
  have hsum : ∑ w, (if y = f w then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun w _ => by
      have := hfresh w
      have hne : y ≠ f w := fun h => this (h ▸ hy)
      simp [hne]
  simp only [Net.vars_cons, Net.vars_add, eqVars_mk, Term.vars_app, Multiset.count_add,
    Multiset.count_sum']
  rw [Rule.count_vars_inst r (system_wellFormed.linear _ _ _ hr), hsum]
  ring

/-- A net that is not linear is equivalent only to itself: every wire substitution needs a linear
net. -/
theorem equiv_eq_of_not_linear {N M : CNet} (h : Equiv N M) (hN : ¬ N.Linear) : N = M := by
  induction h with
  | rel _ _ h => exact absurd h.linear_left hN
  | refl => rfl
  | symm a b hab ih =>
    exact (ih fun ha => hN ((Equiv.linear_iff hab).1 ha)).symm
  | trans a b c _ _ ih ih' =>
    obtain rfl := ih hN
    exact ih' hN

/-- One interaction up to wires keeps a free port free. -/
theorem stepE_free {N M : CNet} (h : StepE system N M) {y : ℕ} (hy : N.vars.count y = 1) :
    M.vars.count y = 1 := by
  obtain ⟨N', he, hs⟩ := h
  have h' := (he.free_iff y).1 hy
  rw [step_count_of_mem hs (Multiset.one_le_count_iff_mem.1 (by omega)), h']

/-- Reduction up to wires keeps a free port free. -/
theorem stepsE_free {N M : CNet} (h : StepsE system N M) {y : ℕ} (hy : N.vars.count y = 1) :
    M.vars.count y = 1 := by
  induction h with
  | refl => exact hy
  | tail _ hs ih => exact stepE_free hs ih

/-- In a net where a name occurs three times or more, an interaction up to wires does not change
its number of occurrences: no wire substitution applies, and the interaction keeps old names. -/
theorem stepE_count_of_three_le {N M : CNet} (h : StepE system N M) {y : ℕ}
    (hy : 3 ≤ N.vars.count y) : M.vars.count y = N.vars.count y := by
  obtain ⟨N', he, hs⟩ := h
  obtain rfl := equiv_eq_of_not_linear he (fun hl => by have := hl y; omega)
  exact step_count_of_mem hs (Multiset.one_le_count_iff_mem.1 (by omega))

/-- Reduction up to wires does not change the number of occurrences of a name occurring three
times or more. -/
theorem stepsE_count_of_three_le {N M : CNet} (h : StepsE system N M) {y : ℕ}
    (hy : 3 ≤ N.vars.count y) : M.vars.count y = N.vars.count y := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [stepE_count_of_three_le hs (by omega), ih]

/-! ## The hypotheses of `erase_wiring` and `erase_package` are needed -/

/-- `erase_wiring` (Lemma 2 (ii), page 85) without linearity is false: with `D = {0}` and the
context `Δ = {ε – 0}`, the name `0` has three ends and the net does not reduce to `Δ`. -/
theorem erase_wiring_needs_linear :
    ¬ StepsE system (({0} + {0} : Multiset ℕ).map (fun x => s(mkEra, Term.var x)) +
      {s(mkEra, var 0)}) {s(mkEra, var 0)} := by
  intro h
  have := stepsE_count_of_three_le h (y := 0) (by simp)
  simp at this

/-- `erase_package` (page 84) without linearity is false: the package `con(0, 0)` plugged into an
eraser, next to a context that also uses the name `0`, does not reduce to the context. -/
theorem erase_package_needs_linear :
    ¬ StepsE system (s(mkEra, mkCon (var 0) (var 0)) ::ₘ {s(mkEra, var 0)}) {s(mkEra, var 0)} := by
  intro h
  have := stepsE_count_of_three_le h (y := 0) (by simp)
  simp at this

/-- `erase_package` without `IsPackage` is false: an eraser on a free wire is irreducible, even
up to wires, since the free port `0` stays free. The net is linear. -/
theorem erase_package_needs_isPackage_var :
    ({s(mkEra, var 0)} : CNet).Linear ∧ ¬ StepsE system {s(mkEra, var 0)} 0 := by
  refine ⟨fun y => ?_, fun h => ?_⟩
  · simp only [Net.vars_singleton, eqVars_mk, vars_mkEra, vars_var, zero_add,
      Multiset.count_singleton]
    split_ifs <;> omega
  · have := stepsE_free h (y := 0) (by simp)
    simp at this

/-- `erase_package` without `IsPackage` is false for a tree with two free leaves: an eraser on
`con(0, 1)` leaves erasers on the free ports `0` and `1`. -/
theorem erase_package_needs_isPackage_con :
    ({s(mkEra, mkCon (var 0) (var 1))} : CNet).Linear ∧
      ¬ StepsE system {s(mkEra, mkCon (var 0) (var 1))} 0 := by
  refine ⟨fun y => ?_, fun h => ?_⟩
  · simp only [Net.vars_singleton, eqVars_mk, vars_mkEra, vars_mkCon, vars_var, zero_add,
      Multiset.count_add, Multiset.count_singleton]
    split_ifs <;> omega
  · have := stepsE_free h (y := 0) (by simp)
    simp at this

/-! ## Instances -/

/-- `erase_package` (page 84) on a package with both kinds of binary cell and crossed wires,
`dup(con(0, 1), con(1, 0))`, next to a non-empty context. -/
theorem erase_package_crossing :
    StepsE system
      (s(mkEra, mkDup (mkCon (var 0) (var 1)) (mkCon (var 1) (var 0))) ::ₘ {s(var 2, var 3)})
      {s(var 2, var 3)} := by
  refine erase_package _ ?_ _ ?_
  · intro x hx
    simp only [vars_mkDup, vars_mkCon, vars_var, Multiset.mem_add, Multiset.mem_singleton] at hx
    simp only [vars_mkDup, vars_mkCon, vars_var, Multiset.count_add, Multiset.count_singleton]
    rcases hx with ((rfl | rfl) | (rfl | rfl)) <;> simp
  · intro y
    simp only [Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_mkEra, vars_mkDup, vars_mkCon,
      vars_var, zero_add, Multiset.count_add, Multiset.count_singleton]
    split_ifs <;> omega

/-- `erase_wiring` (Lemma 2 (ii), page 85) on a wiring of two wires `0` and `1`, next to a
non-empty context. -/
theorem erase_wiring_two :
    StepsE system (({0, 1} + {0, 1} : Multiset ℕ).map (fun x => s(mkEra, Term.var x)) +
      {s(var 2, var 3)}) {s(var 2, var 3)} := by
  refine erase_wiring _ _ ?_
  intro y
  simp only [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.map_cons, Multiset.map_add,
    Multiset.map_singleton, Net.vars_cons, Net.vars_add, Net.vars_singleton, eqVars_mk,
    vars_mkEra, vars_var, zero_add, Multiset.count_add, Multiset.count_singleton]
  split_ifs <;> omega

end INet.Comb.PackageCheck
