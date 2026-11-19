import InteractionCombinators.Universality.Menus.Package

/-!
# Lafont, "Interaction Combinators" (1997): menus and selectors (page 84)

* `menu` — the menu `π₁ & ⋯ & πₙ`: the multiplexor `M_n` with the package `πᵢ` on its `i`-th
  auxiliary port.
* `selector` — the selector `Sⁱₙ`: the dual multiplexor `M_n*` with an eraser on every auxiliary
  port but the `i`-th, which is the free port of the selector.
* `menu_selector` — the menu plugged into `Sⁱₙ` reduces to `πᵢ` on the free port of the selector.
* `IsPackage.menu` — a menu of packages with pairwise disjoint names is a package.

Indices are counted from 0.
-/

namespace INet.Comb

open Term

/-- The menu `π₁ & ⋯ & πₙ` (Lafont, page 84): the multiplexor `M_n` with `πᵢ` on its `i`-th
auxiliary port. -/
def menu (πs : List (Term sig ℕ)) : Term sig ℕ := mux πs

/-- The selector `Sⁱₙ` (Lafont, page 84), with free port `x`: `M_n*` with `ε` on every auxiliary
port but the `i`-th (counted from 0), which is the wire `x`. -/
def selector (n i x : ℕ) : Term sig ℕ :=
  muxStar (List.replicate i mkEra ++ var x :: List.replicate (n - i - 1) mkEra)

/-- Plugging a list of trees into a list of copies of `e` gives the equations `s(t, e)`. -/
theorem zipWith_replicate (ts : List (Term sig ℕ)) (e : Term sig ℕ) :
    List.zipWith (fun t u => s(t, u)) ts (List.replicate ts.length e) =
      ts.map (fun t => s(t, e)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [List.replicate_succ, ih]

/-- The equations produced by the multiplexor property against the auxiliary ports of the
selector `Sⁱₙ` (page 84): `πᵢ` meets the free port `x`, every other `πⱼ` meets an eraser. -/
theorem zipWith_selector (πs : List (Term sig ℕ)) (i : ℕ) (hi : i < πs.length) (x : ℕ) :
    ((List.zipWith (fun t u => s(t, u)) πs
        (List.replicate i mkEra ++ var x :: List.replicate (πs.length - i - 1) mkEra) :
          List (Sym2 (Term sig ℕ))) : CNet) =
      s(πs[i], var x) ::ₘ (((πs.eraseIdx i).map (fun π => s(π, mkEra)) :
        List (Sym2 (Term sig ℕ))) : CNet) := by
  induction πs generalizing i with
  | nil => simp at hi
  | cons π ps ih =>
    cases i with
    | zero =>
      simp only [List.replicate_zero, List.nil_append, List.length_cons, Nat.add_sub_cancel,
        Nat.sub_zero, List.zipWith_cons_cons, zipWith_replicate, List.getElem_cons_zero,
        List.eraseIdx_cons_zero, ← Multiset.cons_coe]
    | succ k =>
      have hk : k < ps.length := by simpa using hi
      have hlen : (π :: ps).length - (k + 1) - 1 = ps.length - k - 1 := by simp
      rw [hlen, List.replicate_succ, List.cons_append, List.zipWith_cons_cons,
        ← Multiset.cons_coe, ih k hk, List.getElem_cons_succ, List.eraseIdx_cons_succ,
        List.map_cons, ← Multiset.cons_coe, Multiset.cons_swap]

/-- A list of packages, each plugged into an eraser, reduces to the empty net (page 84, the
corollary of Lemma 2 applied to each package in turn). -/
theorem erase_packages (ps : List (Term sig ℕ)) (hp : ∀ π ∈ ps, π.IsPackage) (Δ : CNet)
    (hlin : Net.Linear (((ps.map (fun π => s(π, mkEra)) : List (Sym2 (Term sig ℕ))) : CNet) + Δ)) :
    StepsE system (((ps.map (fun π => s(π, mkEra)) : List (Sym2 (Term sig ℕ))) : CNet) + Δ) Δ := by
  induction ps with
  | nil => simpa using Relation.ReflTransGen.refl
  | cons π ps ih =>
    have e : (((π :: ps).map (fun π => s(π, mkEra)) : List (Sym2 (Term sig ℕ))) : CNet) + Δ =
        s(mkEra, π) ::ₘ ((((ps.map (fun π => s(π, mkEra)) : List (Sym2 (Term sig ℕ))) : CNet)
          + Δ)) := by
      rw [List.map_cons, ← Multiset.cons_coe, Multiset.cons_add, Sym2.eq_swap]
    rw [e] at hlin ⊢
    have hrest := linear_of_add (N := {s(mkEra, π)})
      (hlin.cast (by rw [Multiset.singleton_add]))
    exact (erase_package π (hp π (by simp)) _ hlin).trans
      (ih (fun π' h => hp π' (by simp [h])) hrest)

/-- Lafont's property of menus and selectors (page 84): the menu `π₁ & ⋯ & πₙ` plugged into the
selector `Sⁱₙ` reduces to `πᵢ` on the free port `x` of the selector. The multiplexor property
(`mux_muxStar`) connects each `πⱼ` to the `j`-th auxiliary port of `Sⁱₙ`, then every package but
`πᵢ` is erased (`erase_package`). -/
theorem menu_selector (πs : List (Term sig ℕ)) (i : ℕ) (hi : i < πs.length) (x : ℕ)
    (hπ : ∀ π ∈ πs, π.IsPackage) (Δ : CNet)
    (hlin : Net.Linear (s(menu πs, selector πs.length i x) ::ₘ Δ)) :
    StepsE system (s(menu πs, selector πs.length i x) ::ₘ Δ) (s(πs[i], var x) ::ₘ Δ) := by
  have hlen : πs.length =
      (List.replicate i mkEra ++ var x :: List.replicate (πs.length - i - 1) mkEra).length := by
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega
  have h1 := mux_muxStar πs _ Δ hlen
  rw [zipWith_selector πs i hi x] at h1
  have e : s(πs[i], var x) ::ₘ (((πs.eraseIdx i).map (fun π => s(π, mkEra)) :
        List (Sym2 (Term sig ℕ))) : CNet) + Δ =
      (((πs.eraseIdx i).map (fun π => s(π, mkEra)) : List (Sym2 (Term sig ℕ))) : CNet) +
        (s(πs[i], var x) ::ₘ Δ) := by
    rw [Multiset.cons_add, Multiset.add_cons]
  rw [e] at h1
  refine h1.stepsE.trans (erase_packages _ ?_ _ (h1.linear system_wellFormed.linear hlin))
  intro π hmem
  exact hπ π (List.mem_of_mem_eraseIdx hmem)

/-- Every name of a multiplexor `M_n` is a name of one of the trees on its auxiliary ports. -/
theorem mem_vars_mux : ∀ (ts : List (Term sig ℕ)) {x : ℕ}, x ∈ (mux ts).vars → ∃ t ∈ ts, x ∈ t.vars
  | [], x, h => by simp [mux] at h
  | [t], x, h => ⟨t, by simp, by simpa [mux] using h⟩
  | t :: t' :: ts, x, h => by
    rw [mux, vars_mkCon, Multiset.mem_add] at h
    rcases h with h | h
    · exact ⟨t, by simp, h⟩
    · obtain ⟨u, hu, hx⟩ := mem_vars_mux (t' :: ts) h
      exact ⟨u, List.mem_cons_of_mem _ hu, hx⟩

/-- A menu of packages is a package (page 84), when the packages have pairwise disjoint names.
Disjointness is stated as `List.Pairwise`: of two packages in the list, no name of the first
occurs in the second. For `πs = []` the menu is an eraser. -/
theorem IsPackage.menu : ∀ (πs : List (Term sig ℕ)), (∀ π ∈ πs, π.IsPackage) →
    πs.Pairwise (fun a b => ∀ x ∈ a.vars, x ∉ b.vars) → (menu πs).IsPackage
  | [], _, _ => isPackage_mkEra
  | [t], h, _ => h t (by simp)
  | t :: t' :: ts, h, hd => by
    rw [List.pairwise_cons] at hd
    have ih := IsPackage.menu (t' :: ts) (fun π hπ => h π (List.mem_cons_of_mem _ hπ)) hd.2
    refine IsPackage.mkCon (h t (by simp)) ih ?_
    intro x hx hx'
    obtain ⟨u, hu, hxu⟩ := mem_vars_mux (t' :: ts) hx'
    exact hd.1 u hu x hx hxu

/-- Non-vacuity of `menu_selector` (page 84): the menu `ε & γ(x₀, x₀)` against the selector
`S²₂` (index 1 from 0) reduces to `γ(x₀, x₀)` on the free port `x₁`. -/
example : StepsE system ({s(menu [mkEra, mkCon (var 0) (var 0)], selector 2 1 1)} : CNet)
    {s(mkCon (var 0) (var 0), var 1)} := by
  have h := menu_selector [mkEra, mkCon (var 0) (var 0)] 1 (by simp) 1 (by
    intro π hπ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hπ
    rcases hπ with rfl | rfl
    · exact isPackage_mkEra
    · exact isPackage_mkCon_var 0) 0 (by
    intro y
    simp only [menu, selector, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      List.replicate, List.nil_append, List.cons_append, mux, muxStar,
      Net.vars_cons, Net.vars_zero, eqVars_mk, vars_mkEra, vars_mkCon, vars_var, zero_add,
      add_zero, Multiset.count_add, Multiset.count_singleton]
    split_ifs <;> omega)
  simpa using h

end INet.Comb
