import InteractionCombinators.Universality.Codes.Copier
import Checks.Universality.Duplication.DupPackageCheck

/-!
# Checks of the copier `C_n` against the paper

`copier` and `copier_package` (`InteractionCombinators/Universality/Codes/Copier.lean`) are the
copier of page 88, first picture of Section 2.6: a package without `dup` plugged into the root of
`C_n` reduces to `n` copies, one on each auxiliary port. These checks test the definition and the
statement.

* `copier_nil`, `copier_one`, `copier_three`, `vars_copier` — the shape of `C_n`: `era` for
  `n = 0`, a wire for `n = 1`, `dup` cells nested to the right otherwise, with the `n` auxiliary
  ports in the order of the list and no other name: a principal net of arity `n`.
* `copier_package_separate`, `copier_package_pairwise` — the copies are separate graphs. The
  statement only asks that each `f_i` be injective on the names of `π`. It follows anyway that
  the names of copy `i` occur neither in another copy, nor in any `u_j`, nor in `Δ`: reduction and
  equivalence keep linearity, and every name of a package occurs twice in it.
* `copier_package_zero` — for `n = 0` the package is erased.
* `copier_package_three` — the hypotheses hold for `n = 3`, a package with two crossed wires and a
  context that shares names with the auxiliary trees.

Not shown here: that `DupFree` is needed (see `DupPackageCheck.lean` for why this is out of reach).
-/

namespace INet.Comb.CopierCheck

open Term DupPackageCheck

/-! ## The shape of `C_n` -/

/-- `C_0` is an eraser (page 88, with Fig. 5 of page 83). -/
theorem copier_nil : (copier [] : Term sig ℕ) = mkEra := rfl

/-- `C_1` is a wire: the tree on its only auxiliary port is plugged into the package directly. -/
theorem copier_one (u : Term sig ℕ) : copier [u] = u := rfl

/-- `C_3` is two `dup` cells, the upper one on the right auxiliary port of the lower one, as `M_n`
is nested in Fig. 4 (page 83); the auxiliary ports read left to right. -/
theorem copier_three (a b c : Term sig ℕ) : copier [a, b, c] = mkDup a (mkDup b c) := rfl

/-- `C_n` is a principal net of arity `n` (page 88): plugged into `n` distinct free ports, its
names are exactly those ports, in order; its cells carry no other name. -/
theorem vars_copier (l : List ℕ) : (copier (l.map var) : Term sig ℕ).vars = l := by
  rw [copier, vars_autoMux, List.map_map]
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-! ## The copies are separate -/

/-- In a linear net, the names of a renamed copy of a package occur nowhere else: not in the tree
it is plugged into, not in the rest of the net. Every name `x` of the package occurs twice in it,
so `f x` occurs at least twice in the copy. -/
theorem copy_isolated {π : Term sig ℕ} (hπ : π.IsPackage) (f : ℕ → ℕ) (u : Term sig ℕ) (R : CNet)
    (hlin : Net.Linear (s(u, π.bind fun x => var (f x)) ::ₘ R)) {x : ℕ} (hx : x ∈ π.vars) :
    f x ∉ u.vars ∧ f x ∉ R.vars := by
  have hc := hlin (f x)
  simp only [Net.vars_cons, eqVars_mk, vars_rename, Multiset.count_add] at hc
  have h2 : 2 ≤ (π.vars.map f).count (f x) := hπ x hx ▸ count_le_count_map _ f x
  constructor <;> intro h <;> have := Multiset.one_le_count_iff_mem.2 h <;> omega

/-- The conclusion of `copier_package` (page 88) forces the copies to be separate graphs: a name
of copy `i` is not a name of `u_i`, of `Δ`, of another `u_j`, or of another copy `j`. -/
theorem copier_package_separate (π : Term sig ℕ) (hπ : π.IsPackage) (us : List (Term sig ℕ))
    (Δ : CNet) (hlin : Net.Linear (s(copier us, π) ::ₘ Δ)) (fs : List (ℕ → ℕ)) (N : CNet)
    (hlen : fs.length = us.length) (hS : StepsE system (s(copier us, π) ::ₘ Δ) N)
    (hE : Equiv N ((List.zipWith (fun u f => s(u, π.bind (fun x => var (f x)))) us fs : CNet) + Δ))
    (i : ℕ) (hi : i < us.length) (x : ℕ) (hx : x ∈ π.vars) :
    fs[i] x ∉ us[i].vars ∧ fs[i] x ∉ Δ.vars ∧ ∀ (j : ℕ) (hj : j < us.length), j ≠ i →
      fs[i] x ∉ us[j].vars ∧ ∀ x' ∈ π.vars, fs[i] x ≠ fs[j] x' := by
  have hR := hE.linear (hS.linear system_wellFormed.linear hlin)
  set Z := List.zipWith (fun u f => s(u, π.bind (fun x => var (f x)))) us fs with hZ
  have hZl : Z.length = us.length := by simp [hZ, hlen]
  have hZi : ∀ k (hk : k < us.length), Z[k]'(hZl ▸ hk) =
      s(us[k], π.bind (fun x => var (fs[k] x))) := fun k hk => by
    simp [hZ, List.getElem_zipWith]
  have hsplit : (Z : CNet) = Z[i]'(hZl ▸ hi) ::ₘ (Z.eraseIdx i : CNet) :=
    Multiset.coe_eq_coe.2 (List.getElem_cons_eraseIdx_perm _).symm
  rw [hsplit, Multiset.cons_add, hZi i hi] at hR
  obtain ⟨hu, hrest⟩ := copy_isolated hπ _ _ _ hR hx
  rw [Net.vars_add, Multiset.mem_add, not_or] at hrest
  refine ⟨hu, hrest.2, fun j hj hji => ?_⟩
  have hmem : Z[j]'(hZl ▸ hj) ∈ Z.eraseIdx i :=
    List.mem_eraseIdx_iff_getElem.2 ⟨j, hZl ▸ hj, hji, rfl⟩
  obtain ⟨r, hr⟩ := Multiset.exists_cons_of_mem (s := (Z.eraseIdx i : CNet)) hmem
  have h := hrest.1
  rw [hr, Net.vars_cons, hZi j hj, eqVars_mk, vars_rename] at h
  simp only [Multiset.mem_add, not_or] at h
  exact ⟨h.1.1, fun x' hx' he => h.1.2 (he ▸ Multiset.mem_map_of_mem _ hx')⟩

/-- The same as `copier_package_separate`, as a statement about the list of renamings: two
distinct copies have no name in common. -/
theorem copier_package_pairwise (π : Term sig ℕ) (hπ : π.IsPackage) (us : List (Term sig ℕ))
    (Δ : CNet) (hlin : Net.Linear (s(copier us, π) ::ₘ Δ)) (fs : List (ℕ → ℕ)) (N : CNet)
    (hlen : fs.length = us.length) (hS : StepsE system (s(copier us, π) ::ₘ Δ) N)
    (hE : Equiv N ((List.zipWith (fun u f => s(u, π.bind (fun x => var (f x)))) us fs : CNet) + Δ)) :
    fs.Pairwise (fun f g => ∀ x ∈ π.vars, ∀ x' ∈ π.vars, f x ≠ g x') := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij x hx x' hx'
  exact ((copier_package_separate π hπ us Δ hlin fs N hlen hS hE i (hlen ▸ hi) x hx).2.2 j
    (hlen ▸ hj) (Nat.ne_of_gt hij)).2 x' hx'

/-! ## `n = 0` and a non-vacuity check -/

/-- `copier_package` for `n = 0` (page 88, with the corollary of Lemma 2, page 84): a package
plugged into `C_0` is erased, whatever the context. -/
theorem copier_package_zero (π : Term sig ℕ) (hπ : π.IsPackage) (hd : DupFree π) (Δ : CNet)
    (hlin : Net.Linear (s(copier [], π) ::ₘ Δ)) :
    ∃ N, StepsE system (s(mkEra, π) ::ₘ Δ) N ∧ Equiv N Δ := by
  obtain ⟨fs, N, -, -, hS, hE⟩ := copier_package π hπ hd [] Δ hlin
  exact ⟨N, hS, by simpa using hE⟩

/-- `copier_package` (page 88) applies to `C_3`, the package `con(con(0, 1), con(1, 0))` with two
crossed wires, and the context `2 – con(3, 4)`, which shares all its names with the auxiliary
trees `2`, `3`, `4`. The three copies are separate, and none uses a name of the context. -/
theorem copier_package_three :
    ∃ (fs : List (ℕ → ℕ)) (N : CNet), fs.length = 3 ∧
      StepsE system (s(copier [var 2, var 3, var 4],
        mkCon (mkCon (var 0) (var 1)) (mkCon (var 1) (var 0))) ::ₘ
        {s(var 2, mkCon (var 3) (var 4))}) N ∧
      Equiv N ((List.zipWith (fun u f => s(u, mkCon (mkCon (var (f 0)) (var (f 1)))
        (mkCon (var (f 1)) (var (f 0))))) [var 2, var 3, var 4] fs : CNet) +
        {s(var 2, mkCon (var 3) (var 4))}) ∧
      fs.Pairwise (fun f g => ∀ x ∈ ({0, 1} : Finset ℕ), ∀ x' ∈ ({0, 1} : Finset ℕ), f x ≠ g x') ∧
      (∀ f ∈ fs, f 0 ≠ f 1 ∧ ∀ x ∈ ({0, 1} : Finset ℕ), f x ∉ ({2, 3, 4} : Finset ℕ)) := by
  set π : Term sig ℕ := mkCon (mkCon (var 0) (var 1)) (mkCon (var 1) (var 0)) with hπdef
  have hπ : π.IsPackage := by unfold Term.IsPackage; decide
  have hd : DupFree π := by simp [hπdef, DupFree]
  set us : List (Term sig ℕ) := [var 2, var 3, var 4]
  set Δ : CNet := {s(var 2, mkCon (var 3) (var 4))}
  have hlin : Net.Linear (s(copier us, π) ::ₘ Δ) := by
    intro y
    simp only [us, Δ, hπdef, copier, autoMux, Net.vars_cons, Net.vars_singleton, eqVars_mk,
      vars_mkDup, vars_mkCon, vars_var, Multiset.count_add, Multiset.count_singleton]
    split_ifs <;> omega
  obtain ⟨fs, N, hlen, hinj, hS, hE⟩ := copier_package π hπ hd us Δ hlin
  have mem : ∀ x ∈ ({0, 1} : Finset ℕ), x ∈ π.vars := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> decide
  refine ⟨fs, N, hlen, hS, by simpa [hπdef] using hE,
    (copier_package_pairwise π hπ us Δ hlin fs N hlen hS hE).imp
      fun h x hx x' hx' => h x (mem x hx) x' (mem x' hx'), fun f hf => ⟨?_, fun x hx => ?_⟩⟩
  · exact fun h => absurd (hinj f hf (mem 0 (by simp)) (mem 1 (by simp)) h) (by decide)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
  have hi' : i < us.length := hlen ▸ hi
  obtain ⟨h1, h2, h3⟩ := copier_package_separate π hπ us Δ hlin fs N hlen hS hE i hi' x (mem x hx)
  have hΔ : ∀ y, y ∈ Δ.vars ↔ y = 2 ∨ y = 3 ∨ y = 4 := fun y => by
    simp only [Δ, Net.vars_singleton, eqVars_mk, vars_mkCon, vars_var, Multiset.mem_add,
      Multiset.mem_singleton]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rw [hΔ] at h2
  exact h2
