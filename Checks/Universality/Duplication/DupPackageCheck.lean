import InteractionCombinators.Text.NetLemmas
import InteractionCombinators.Universality.Duplication.DupPackage
import Checks.Universality.Menus.PackageCheck

/-!
# Checks of `dup_package` against the paper

`dup_package` (`Lafont/DupPackage.lean`) is the corollary of Lemma 3 on page 87: a package `π`
without `dup`, plugged into the principal port of a `dup`, reduces to two copies of `π`. These
checks test the statement.

* `dup_package_separate` — the two copies are separate graphs. The statement only asks that `f`
  and `g` be injective on the names of `π`; it does not say that the images of `f` and `g` are
  disjoint, nor that they avoid the names of `u`, `v` and `Δ`. This follows anyway: reduction and
  equivalence keep linearity, so the right-hand side is linear, and in a package every name occurs
  twice. The injectivity of `f` and `g` follows the same way, so the two `Set.InjOn` of the
  statement are redundant.
* `dup_package_two_wires`, `dup_package_era` — the hypotheses hold on a package with two crossed
  wires next to a context that shares names with `u` and `v`, and on `ε`.
* `dup_package_needs_isPackage` — without `IsPackage` the conclusion is false: the free ports are
  an invariant of reduction (`stepsE_free_iff`), and a copy of a tree with a free leaf has a free
  port too many.

That `DupFree` is needed is shown in `Checks/DupDupCheck.lean` (`dup_package_needs_dupFree`), on
the paper's example `π = dup(0, 0)` (page 87: "δ cannot duplicate δ").
-/

namespace INet.Comb.DupPackageCheck

open Term PackageCheck

/-! ## Counting the names of a renamed tree -/

/-- The names of a tree renamed by `f` are the images of its names. -/
theorem vars_rename (π : Term sig ℕ) (f : ℕ → ℕ) :
    (π.bind fun x => var (f x)).vars = π.vars.map f := by
  rw [Term.vars_bind]
  simp [Multiset.bind_singleton]

/-- Renaming by any function does not lower the number of occurrences of a name. -/
theorem count_le_count_map (s : Multiset ℕ) (f : ℕ → ℕ) (x : ℕ) :
    s.count x ≤ (s.map f).count (f x) := by
  rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
  exact Multiset.card_le_card (Multiset.monotone_filter_right s fun a h => h ▸ rfl)

/-- Renaming two distinct names to the same name adds up their occurrences. -/
theorem count_add_le_count_map (s : Multiset ℕ) (f : ℕ → ℕ) {x x' : ℕ} (hne : x ≠ x')
    (hf : f x = f x') : s.count x + s.count x' ≤ (s.map f).count (f x) := by
  conv_rhs => rw [← Multiset.filter_add_not (· = x) s]
  rw [Multiset.map_add, Multiset.count_add, Multiset.filter_eq', Multiset.map_replicate,
    Multiset.count_replicate_self]
  have h := count_le_count_map (s.filter fun a => ¬ a = x) f x'
  rw [Multiset.count_filter_of_pos (p := fun a => ¬ a = x) hne.symm, ← hf] at h
  omega

/-! ## The two copies are separate -/

/-- The conclusion of `dup_package` (page 87) forces the two copies to be separate graphs, each
the same graph as `π`. In the right-hand side, `f` is injective on the names of `π`, and so is
`g`; no name of the first copy is a name of the second; and no name of either copy is a name of
`u`, `v` or `Δ`. The argument: reduction and equivalence keep linearity, so the right-hand side
has each name at most twice, while every name `x` of the package `π` occurs twice in it, so
`f x` occurs at least twice in the first copy and `g x` at least twice in the second. -/
theorem dup_package_separate (π : Term sig ℕ) (hπ : π.IsPackage) (u v : Term sig ℕ) (Δ : CNet)
    (hlin : Net.Linear (s(mkDup u v, π) ::ₘ Δ)) (f g : ℕ → ℕ) (N : CNet)
    (hS : StepsE system (s(mkDup u v, π) ::ₘ Δ) N)
    (hE : Equiv N (s(u, π.bind (fun x => var (f x))) ::ₘ
      s(v, π.bind (fun x => var (g x))) ::ₘ Δ)) :
    Set.InjOn f {x | x ∈ π.vars} ∧ Set.InjOn g {x | x ∈ π.vars} ∧
      (∀ x ∈ π.vars, ∀ x' ∈ π.vars, f x ≠ g x') ∧
      (∀ x ∈ π.vars, f x ∉ u.vars ∧ f x ∉ v.vars ∧ f x ∉ Δ.vars) ∧
      (∀ x ∈ π.vars, g x ∉ u.vars ∧ g x ∉ v.vars ∧ g x ∉ Δ.vars) := by
  have hR := hE.linear (hS.linear system_wellFormed.linear hlin)
  have hc : ∀ y, (u.vars.count y + (π.vars.map f).count y) +
      ((v.vars.count y + (π.vars.map g).count y) + Δ.vars.count y) ≤ 2 := fun y => by
    have := hR y
    simpa only [Net.vars_cons, eqVars_mk, vars_rename, Multiset.count_add] using this
  have h2 : ∀ x ∈ π.vars, π.vars.count x = 2 := hπ
  have hf2 : ∀ x ∈ π.vars, 2 ≤ (π.vars.map f).count (f x) := fun x hx =>
    h2 x hx ▸ count_le_count_map _ f x
  have hg2 : ∀ x ∈ π.vars, 2 ≤ (π.vars.map g).count (g x) := fun x hx =>
    h2 x hx ▸ count_le_count_map _ g x
  have pos : ∀ {s : Multiset ℕ} {y : ℕ}, y ∈ s → 1 ≤ s.count y := fun h =>
    Multiset.one_le_count_iff_mem.2 h
  refine ⟨fun x hx x' hx' h => ?_, fun x hx x' hx' h => ?_, fun x hx x' hx' h => ?_,
    fun x hx => ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩,
    fun x hx => ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩⟩
  · by_contra hne
    have := count_add_le_count_map π.vars f hne h
    have := hc (f x)
    rw [h2 x hx, h2 x' hx'] at *
    omega
  · by_contra hne
    have := count_add_le_count_map π.vars g hne h
    have := hc (g x)
    rw [h2 x hx, h2 x' hx'] at *
    omega
  · have := hf2 x hx
    have := hg2 x' hx'
    have := hc (f x)
    rw [← h] at *
    omega
  all_goals first
    | (have := hf2 x hx; have := pos h; have := hc (f x); omega)
    | (have := hg2 x hx; have := pos h; have := hc (g x); omega)

/-! ## The hypotheses can hold -/

/-- `dup_package` (page 87) applies to the package `con(con(0, 1), con(1, 0))`, with two crossed
wires, next to a context `con(3, 4) – 2` that shares the names `2` and `3` with the auxiliary
trees `u = 2` and `v = 3`. The copies are separate: the wires of the first copy are not those of
the second, nor names of the context. -/
theorem dup_package_two_wires :
    ∃ (f g : ℕ → ℕ) (N : CNet),
      StepsE system (s(mkDup (var 2) (var 3), mkCon (mkCon (var 0) (var 1)) (mkCon (var 1) (var 0)))
        ::ₘ {s(var 2, mkCon (var 3) (var 4))}) N ∧
      Equiv N (s(var 2, mkCon (mkCon (var (f 0)) (var (f 1))) (mkCon (var (f 1)) (var (f 0)))) ::ₘ
        s(var 3, mkCon (mkCon (var (g 0)) (var (g 1))) (mkCon (var (g 1)) (var (g 0)))) ::ₘ
        {s(var 2, mkCon (var 3) (var 4))}) ∧
      f 0 ≠ f 1 ∧ g 0 ≠ g 1 ∧ (∀ x ∈ ({0, 1} : Finset ℕ), ∀ x' ∈ ({0, 1} : Finset ℕ), f x ≠ g x') ∧
      (∀ x ∈ ({0, 1} : Finset ℕ), f x ∉ ({2, 3, 4} : Finset ℕ) ∧ g x ∉ ({2, 3, 4} : Finset ℕ)) := by
  set π : Term sig ℕ := mkCon (mkCon (var 0) (var 1)) (mkCon (var 1) (var 0)) with hπdef
  have hπ : π.IsPackage := by unfold Term.IsPackage; decide
  have hd : DupFree π := by simp [hπdef, DupFree]
  have hlin : Net.Linear (s(mkDup (var 2) (var 3), π) ::ₘ {s(var 2, mkCon (var 3) (var 4))}) :=
    Net.linear_of_forall_mem (by decide)
  obtain ⟨f, g, N, -, -, hS, hE⟩ := dup_package π hπ hd (var 2) (var 3) _ hlin
  obtain ⟨hif, hig, hfg, hfu, hgu⟩ := dup_package_separate π hπ _ _ _ hlin f g N hS hE
  have m0 : (0 : ℕ) ∈ π.vars := by decide
  have m1 : (1 : ℕ) ∈ π.vars := by decide
  have mem : ∀ x ∈ ({0, 1} : Finset ℕ), x ∈ π.vars := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    exacts [m0, m1]
  refine ⟨f, g, N, hS, by simpa [hπdef] using hE, fun h => absurd (hif m0 m1 h) (by decide),
    fun h => absurd (hig m0 m1 h) (by decide),
    fun x hx x' hx' => hfg x (mem x hx) x' (mem x' hx'), fun x hx => ⟨?_, ?_⟩⟩
  · obtain ⟨h1, h2, h3⟩ := hfu x (mem x hx)
    simp only [vars_var, Multiset.mem_singleton, Net.vars_singleton, eqVars_mk, vars_mkCon,
      Multiset.mem_add] at h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · obtain ⟨h1, h2, h3⟩ := hgu x (mem x hx)
    simp only [vars_var, Multiset.mem_singleton, Net.vars_singleton, eqVars_mk, vars_mkCon,
      Multiset.mem_add] at h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

/-- `dup_package` (page 87) on `ε`, a package with no wire: a `dup` plugged into an eraser leaves
an eraser on each auxiliary tree, whatever the trees and the context. -/
theorem dup_package_era (u v : Term sig ℕ) (Δ : CNet)
    (hlin : Net.Linear (s(mkDup u v, mkEra) ::ₘ Δ)) :
    ∃ N, StepsE system (s(mkDup u v, mkEra) ::ₘ Δ) N ∧
      Equiv N (s(u, mkEra) ::ₘ s(v, mkEra) ::ₘ Δ) := by
  obtain ⟨f, g, N, -, -, hS, hE⟩ :=
    dup_package mkEra isPackage_mkEra (by simp [mkEra, DupFree]) u v Δ hlin
  exact ⟨N, hS, by simpa using hE⟩

/-! ## `IsPackage` is needed -/

/-- An interaction never creates a free port: a name that occurs once after it occurred once
before. The rule is linear, so the names it adds occur twice. -/
theorem step_free_of {N M : CNet} (h : Step system N M) {y : ℕ} (hy : M.vars.count y = 1) :
    N.vars.count y = 1 := by
  obtain ⟨α, β, r, hr, as, bs, Δ, f, -, -⟩ := h
  simp only [Net.vars_cons, Net.vars_add, eqVars_mk, Term.vars_app, Multiset.count_add,
    Multiset.count_sum'] at hy ⊢
  rw [Rule.count_vars_inst r (system_wellFormed.linear _ _ _ hr)] at hy
  omega

/-- Reduction up to wires keeps the free ports, in both directions. -/
theorem stepsE_free_iff {N M : CNet} (h : StepsE system N M) (y : ℕ) :
    N.vars.count y = 1 ↔ M.vars.count y = 1 := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨K, he, hk⟩ := hs
    exact ih.trans ⟨fun h => (stepE_free ⟨K, he, hk⟩ h),
      fun h => (he.free_iff y).2 (step_free_of hk h)⟩

/-- `dup_package` (page 87) without `IsPackage` is false. The tree `con(0, ε)` has no `dup`, and
the net `dup(1, 2) – con(0, ε)` is linear, with free ports `0`, `1` and `2`. Two copies
`1 – con(f 0, ε)` and `2 – con(g 0, ε)` have four leaves `1, 2, f 0, g 0`: for the free ports to
be exactly `0`, `1`, `2`, as reduction requires, one of `f 0`, `g 0` must be `0` and the other
would be a fourth free port. -/
theorem dup_package_needs_isPackage :
    ¬ (mkCon (var 0) mkEra : Term sig ℕ).IsPackage ∧ DupFree (mkCon (var 0) mkEra : Term sig ℕ) ∧
      Net.Linear ({s(mkDup (var 1) (var 2), mkCon (var 0) mkEra)} : CNet) ∧
      ¬ ∃ (f g : ℕ → ℕ) (N : CNet),
        StepsE system {s(mkDup (var 1) (var 2), mkCon (var 0) mkEra)} N ∧
        Equiv N (s(var 1, (mkCon (var 0) mkEra : Term sig ℕ).bind (fun x => var (f x))) ::ₘ
          {s(var 2, (mkCon (var 0) mkEra : Term sig ℕ).bind (fun x => var (g x)))}) := by
  refine ⟨fun h => ?_, by simp [mkEra, DupFree], ?_, ?_⟩
  · have := h 0 (by simp)
    simp at this
  · intro y
    simp only [Net.vars_singleton, eqVars_mk, vars_mkDup, vars_mkCon, vars_mkEra, vars_var,
      add_zero, Multiset.count_add, Multiset.count_singleton]
    split_ifs <;> omega
  rintro ⟨f, g, N, hS, hE⟩
  -- the free ports before and after: `y` occurs once in the start iff `y ∈ {0, 1, 2}`, and
  -- once in the copies iff it is one of `1, f 0, 2, g 0` exactly once
  have H : ∀ y, ((if y = 1 then 1 else 0) + (if y = 2 then 1 else 0) +
      (if y = 0 then 1 else 0) = 1) ↔
      ((if y = 1 then 1 else 0) + (if y = f 0 then 1 else 0) +
        ((if y = 2 then 1 else 0) + (if y = g 0 then 1 else 0)) = 1) := fun y => by
    have := (stepsE_free_iff hS y).trans (hE.free_iff y)
    simpa only [Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_mkDup, vars_mkCon, vars_mkEra,
      bind_mkCon, bind_mkEra, bind_var, vars_var, add_zero, Multiset.count_add,
      Multiset.count_singleton] using this
  generalize f 0 = a at H
  generalize g 0 = b at H
  have H0 := H 0
  have H1 := H 1
  have H2 := H 2
  have Ha := H a
  have Hb := H b
  by_cases a0 : a = 0 <;> by_cases b0 : b = 0 <;> by_cases a1 : a = 1 <;> by_cases b1 : b = 1 <;>
    by_cases a2 : a = 2 <;> by_cases b2 : b = 2
  all_goals simp_all
  all_goals omega

end INet.Comb.DupPackageCheck
