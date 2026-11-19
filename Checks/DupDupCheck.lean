import InteractionCombinators.Lafont.Copier
import InteractionCombinators.Lafont.NormalFormE
import InteractionCombinators.Lafont.CutChain
import InteractionCombinators.Lafont.SimulationCount
import InteractionCombinators.Lafont.PackageDecomp

/-!
# `dup` cannot duplicate `dup` (page 87)

`dup_package` (`Lafont/DupPackage.lean`) and `copier_package` (`Lafont/Copier.lean`) assume
`DupFree π`. Lafont, page 87, after the corollary of Lemma 3: "δ cannot duplicate δ". This file
shows that the hypothesis is needed, on the paper's example `π = dup(0, 0)`.

The net `dup(1, 2) – dup(0, 0)` reduces in one `dup`–`dup` interaction, which joins the auxiliary
ports in order, to `1 – 0, 2 – 0`: the wire joins `1` to `2` and no cell is left. Two copies
`1 – dup(f 0, f 0), 2 – dup(g 0, g 0)` have two cells and no cut. Both nets are irreducible, so
uniqueness of the normal form up to wires (`StepsEN.normal_unique`, pages 73-74) would make them
the same graph, and equivalence keeps the number of cells (`Equiv.cells_eq`).

* `dupDup_not_copies` — `dup(1, 2) – dup(0, 0)` does not reduce to two copies of `dup(0, 0)`.
* `dup_package_needs_dupFree`, `dup_package_needs_dupFree'` — the conclusion of `dup_package` is
  false on this example, though `π` is a package and the net is linear; so the statement of
  `dup_package` without `DupFree` is false.
* `copier_package_needs_dupFree`, `copier_package_needs_dupFree'` — the same for
  `copier_package`, with the copier on two trees, which is one `dup`.
-/

namespace INet.Comb.DupDupCheck

open Term Cut

/-- The paper's example of a package with a `dup` (page 87): `dup(0, 0)`. -/
abbrev π₀ : Term sig ℕ := mkDup (var 0) (var 0)

/-- The net `dup(1, 2) – dup(0, 0)`. -/
abbrev src : CNet := s(mkDup (var 1) (var 2), π₀) ::ₘ 0

/-- What the `dup`–`dup` interaction leaves: `1 – 0, 2 – 0`, with no cell. -/
abbrev res : CNet := s(var 1, var 0) ::ₘ s(var 2, var 0) ::ₘ 0

/-- Two copies of `dup(0, 0)` renamed by `f` and `g`, plugged into `1` and `2`. -/
abbrev copies (f g : ℕ → ℕ) : CNet :=
  s(var 1, π₀.bind (fun x => var (f x))) ::ₘ s(var 2, π₀.bind (fun x => var (g x))) ::ₘ 0

theorem isPackage_π₀ : π₀.IsPackage := by unfold Term.IsPackage; decide

theorem not_dupFree_π₀ : ¬ DupFree π₀ := dupFree_mkDup

theorem src_linear : Net.Linear src := by
  intro y
  simp only [Net.vars_cons, eqVars_mk, vars_mkDup, vars_var, Net.vars_zero, Multiset.count_add,
    Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- One `dup`–`dup` interaction (page 87: the auxiliary ports are joined in order, without
exchange): `dup(1, 2) – dup(0, 0)` reduces to `1 – 0, 2 – 0`. -/
theorem step_src : Step system src res := step_dup_dup _ _ _ _ _

/-- A net without cells has no cut (page 80): equivalence keeps the cells. -/
theorem not_hasCut_of_cells_zero {N : CNet} (h : N.cells = 0) : ¬ N.HasCut := by
  rintro ⟨N', hE, α, β, ts, us, hm⟩
  have hα : α ∈ Net.cells N' := Multiset.mem_bind.2 ⟨_, hm, by simp⟩
  rw [← hE.cells_eq, h] at hα
  simp at hα

/-- Two cells plugged into two distinct names, `1 – P, 2 – Q`, form no cut (page 80): a cut is a
chain of wires between two cells (`Net.HasCut.chainCut`), and here every equation has a name on
one side and a cell on the other, with a different name in each equation. -/
theorem not_hasCut_two {P Q : Term sig ℕ} (hP : P.IsCell) (hQ : Q.IsCell) :
    ¬ Net.HasCut (s(var 1, P) ::ₘ s(var 2, Q) ::ₘ 0 : CNet) := by
  intro h
  obtain ⟨a, b, xs, D, ha, hb, hN⟩ := h.chainCut
  obtain ⟨α, ts, rfl⟩ := hP
  obtain ⟨β, us, rfl⟩ := hQ
  obtain ⟨γ, vs, rfl⟩ := ha
  obtain ⟨δ, ws, rfl⟩ := hb
  have mem : ∀ e, e ∈ (chain (Term.app γ vs) xs (Term.app δ ws) : CNet) →
      e = s(var 1, Term.app α ts) ∨ e = s(var 2, Term.app β us) := fun e he => by
    have : e ∈ (s(var 1, Term.app α ts) ::ₘ s(var 2, Term.app β us) ::ₘ 0 : CNet) :=
      hN ▸ Multiset.mem_add.2 (Or.inl he)
    simpa using this
  rcases xs with _ | ⟨x, ys⟩
  · have := mem s(Term.app γ vs, Term.app δ ws) (by simp)
    simp at this
  · have h1 := mem s(Term.app γ vs, var x) (by simp)
    simp only [Sym2.eq_iff, var.injEq, reduceCtorEq, and_false, false_or] at h1
    rcases ys with _ | ⟨y, zs⟩
    · -- the name `x` is `1` or `2`, and the equation of the other name is missing
      have hc := congrArg Multiset.card hN
      simp only [chain_cons, chain_nil, Multiset.card_cons, Multiset.card_add,
        Multiset.card_singleton, Multiset.card_zero] at hc
      have hD : D = 0 := Multiset.card_eq_zero.1 (by omega)
      subst hD
      rcases h1 with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · have : s(var 2, Term.app β us) ∈ (chain (Term.app γ vs) [1] (Term.app δ ws) + 0 : CNet) :=
          by rw [← hN]; simp
        simp at this
      · have : s(var 1, Term.app α ts) ∈ (chain (Term.app γ vs) [2] (Term.app δ ws) + 0 : CNet) :=
          by rw [← hN]; simp
        simp at this
    · have h2 := mem s(var x, var y) (by simp)
      simp at h2

/-- `dup(1, 2) – dup(0, 0)` does not reduce to two copies of `dup(0, 0)` (page 87: "δ cannot
duplicate δ"), up to wires, whatever the renamings `f` and `g`. It reduces in one step to
`1 – 0, 2 – 0`, which has no cell and so is irreducible; the copies form no cut, so they are
irreducible too. A linear net has one normal form up to wires (`StepsEN.normal_unique`,
pages 73-74), and equivalence keeps the number of cells: `0 = 2`. -/
theorem dupDup_not_copies (f g : ℕ → ℕ) (N : CNet) (hS : StepsE system src N)
    (hE : Equiv N (copies f g)) : False := by
  simp only [copies, π₀, bind_mkDup, bind_var] at hE
  have hNn : StepE.Normal system N :=
    (StepE.Normal.of_not_hasCut (not_hasCut_two ⟨_, _, rfl⟩ ⟨_, _, rfl⟩)).of_equiv hE.symm
  have hPn : StepE.Normal system res :=
    StepE.Normal.of_not_hasCut (not_hasCut_of_cells_zero (by simp [Net.cells]))
  obtain ⟨n, hn⟩ := hS.exists_stepsEN
  have h1 : StepsEN system 1 src res := StepsEN.single ⟨_, Equiv.refl _, step_src⟩
  obtain ⟨-, hPN⟩ := StepsEN.normal_unique system_wellFormed src_linear hPn hNn h1 hn
  have hc := congrArg Multiset.card (hPN.trans hE).cells_eq
  simp [Net.cells, cells_mkDup] at hc
  erw [Multiset.card_singleton] at hc
  omega

/-- **`dup_package` needs `DupFree`** (page 87: "δ cannot duplicate δ"). The tree `π = dup(0, 0)`
is a package with a `dup`, the net `dup(1, 2) – dup(0, 0)` is linear, and the conclusion of
`dup_package` for `π`, `u = 1`, `v = 2` and the empty context is false. -/
theorem dup_package_needs_dupFree :
    π₀.IsPackage ∧ ¬ DupFree π₀ ∧ Net.Linear (s(mkDup (var 1) (var 2), π₀) ::ₘ 0) ∧
      ¬ ∃ (f g : ℕ → ℕ) (N : CNet), Set.InjOn f {x | x ∈ π₀.vars} ∧
        Set.InjOn g {x | x ∈ π₀.vars} ∧
        StepsE system (s(mkDup (var 1) (var 2), π₀) ::ₘ 0) N ∧
        Equiv N (s(var 1, π₀.bind (fun x => var (f x))) ::ₘ
          s(var 2, π₀.bind (fun x => var (g x))) ::ₘ 0) :=
  ⟨isPackage_π₀, not_dupFree_π₀, src_linear,
    fun ⟨f, g, N, _, _, hS, hE⟩ => dupDup_not_copies f g N hS hE⟩

/-- **The statement of `dup_package` without `DupFree` is false** (page 87). -/
theorem dup_package_needs_dupFree' :
    ¬ ∀ (π : Term sig ℕ), π.IsPackage → ∀ (u v : Term sig ℕ) (Δ : CNet),
      Net.Linear (s(mkDup u v, π) ::ₘ Δ) →
      ∃ (f g : ℕ → ℕ) (N : CNet), Set.InjOn f {x | x ∈ π.vars} ∧
        Set.InjOn g {x | x ∈ π.vars} ∧
        StepsE system (s(mkDup u v, π) ::ₘ Δ) N ∧
        Equiv N (s(u, π.bind (fun x => var (f x))) ::ₘ
          s(v, π.bind (fun x => var (g x))) ::ₘ Δ) :=
  fun h => dup_package_needs_dupFree.2.2.2 (h π₀ isPackage_π₀ (var 1) (var 2) 0 src_linear)

/-- The copier on two trees is one `dup` (page 88: `C_n` is the autodual multiplexor `T_n`). -/
theorem copier_two (u v : Term sig ℕ) : copier [u, v] = mkDup u v := rfl

/-- **`copier_package` needs `DupFree`** (pages 87-88). The tree `π = dup(0, 0)` is a package with
a `dup`, the net `C₂(1, 2) – dup(0, 0)` is linear, and the conclusion of `copier_package` for `π`,
the trees `[1, 2]` and the empty context is false: `C₂` is one `dup`, which cannot duplicate
`dup`. -/
theorem copier_package_needs_dupFree :
    π₀.IsPackage ∧ ¬ DupFree π₀ ∧
      Net.Linear (s(copier [(var 1 : Term sig ℕ), var 2], π₀) ::ₘ 0) ∧
      ¬ ∃ (fs : List (ℕ → ℕ)) (N : CNet),
        fs.length = ([var 1, var 2] : List (Term sig ℕ)).length ∧
        (∀ f ∈ fs, Set.InjOn f {x | x ∈ π₀.vars}) ∧
        StepsE system (s(copier [(var 1 : Term sig ℕ), var 2], π₀) ::ₘ 0) N ∧
        Equiv N ((List.zipWith (fun u f => s(u, π₀.bind (fun x => var (f x))))
          ([var 1, var 2] : List (Term sig ℕ)) fs : CNet) + 0) := by
  refine ⟨isPackage_π₀, not_dupFree_π₀, src_linear, ?_⟩
  rintro ⟨fs, N, hlen, -, hS, hE⟩
  match fs, hlen, hE with
  | [f, g], _, hE => exact dupDup_not_copies f g N hS hE

/-- **The statement of `copier_package` without `DupFree` is false** (pages 87-88). -/
theorem copier_package_needs_dupFree' :
    ¬ ∀ (π : Term sig ℕ), π.IsPackage → ∀ (us : List (Term sig ℕ)) (Δ : CNet),
      Net.Linear (s(copier us, π) ::ₘ Δ) →
      ∃ (fs : List (ℕ → ℕ)) (N : CNet), fs.length = us.length ∧
        (∀ f ∈ fs, Set.InjOn f {x | x ∈ π.vars}) ∧
        StepsE system (s(copier us, π) ::ₘ Δ) N ∧
        Equiv N ((List.zipWith (fun u f => s(u, π.bind (fun x => var (f x)))) us fs : CNet) + Δ) :=
  fun h => copier_package_needs_dupFree.2.2.2
    (h π₀ isPackage_π₀ [var 1, var 2] 0 copier_package_needs_dupFree.2.2.1)

end INet.Comb.DupDupCheck
