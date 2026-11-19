import InteractionCombinators.Lafont.ExpandedRoot
import InteractionCombinators.Lafont.TranspositorPerm
import InteractionCombinators.Lafont.AutoMux
import InteractionCombinators.Lafont.Package
import InteractionCombinators.TranslationExists

/-!
# The package `Γ_{i,j}` of Fig. 6 (page 86)

Lafont 1997, Section 2.4, Fig. 6, journal page 86 (PDF page 18). The cell `[α_i]` carries a menu
`Γ_i = Γ_{1,i} & … & Γ_{m,i}`. Each package `Γ_{i,j}` is the dual multiplexor `M*_{n_i+1}`, whose
root is the free port; its first `n_i` leaves go to the `n_i` ports of `[φ_{i,j}]` on the side of
`α_i`; the `k` middle ports of `[φ_{i,j}]` go into the leaves of the transpositor `T_{σ_{i,j}}`,
whose root goes to the last leaf of `M*_{n_i+1}`. Here `[φ]` is `φ` with every cell replaced by
its translation (page 87).

A side `φ : Rule S a k` in expanded form (`Rule.Expanded`) and linear is one tree per port
(`Rule.Expanded.existsUnique_root`), so `Γ_{i,j}` is a single tree.

* `Rule.portTree φ p` — the tree rooted at the port `p` of `φ` (`Rule.portTree_eq`: it is the
  tree of the equation `p = t` of an expanded linear side).
* `gamma Φ φ σ hσ k₀` — the package. The internal wire `w` of `φ` is named `k₀ + w`; the
  internal wires of the translations take consecutive blocks above `k₀ + φ.internal`.
* `vars_gamma` — its names are both ends of each name of `[k₀, k₀ + gammaSize)`.
* `gamma_isPackage`, `mem_vars_gamma` — it is a package, and its names lie in that interval.
-/

namespace INet

variable {S : Signature} {a k : ℕ}

open Term ExpandedIso

/-! ## The tree rooted at a port -/

open Classical in
/-- The tree rooted at the port `p` of a side `φ` of a decomposition (Fig. 6, page 86): the tree
`t` of an equation `p = t` of `φ.net`, if there is one, and the leaf `p` otherwise. For a linear
side in expanded form the equation exists and is unique (`Rule.portTree_eq`). -/
noncomputable def Rule.portTree (φ : Rule S a k) (p : Fin a ⊕ Fin k) :
    Term S (Fin a ⊕ Fin k ⊕ Fin φ.internal) :=
  if h : ∃ t, s(Term.var (port p), t) ∈ φ.net then h.choose else Term.var (port p)

/-- In a linear side in expanded form, `portTree φ p` is the tree of the equation rooted at `p`
(Fig. 6, page 86). -/
theorem Rule.portTree_eq {φ : Rule S a k} (he : φ.Expanded) (hl : φ.Linear)
    {p : Fin a ⊕ Fin k} {t : Term S (Fin a ⊕ Fin k ⊕ Fin φ.internal)}
    (ht : s(Term.var (port p), t) ∈ φ.net) : φ.portTree p = t := by
  have h : ∃ t, s(Term.var (port p), t) ∈ φ.net := ⟨t, ht⟩
  unfold portTree
  split_ifs
  exact (he.existsUnique_root hl p).unique h.choose_spec ht

/-- A linear side in expanded form is the equations `p = portTree φ p`, one per port, and the
leaves of these trees are internal wires (Fig. 6, page 86). -/
theorem Rule.Expanded.net_eq_portTree {φ : Rule S a k} (he : φ.Expanded) (hl : φ.Linear) :
    φ.net = (Finset.univ.val.map fun p => s(Term.var (port p), φ.portTree p)) ∧
      ∀ p, ∀ x ∈ (φ.portTree p).vars, ∃ w, x = .inr (.inr w) := by
  obtain ⟨T, hT, hN⟩ := he.exists_trees hl
  have hpt : ∀ p, φ.portTree p = T p := fun p =>
    Rule.portTree_eq he hl (by rw [hN]; exact Multiset.mem_map.2 ⟨p, Finset.mem_univ_val _, rfl⟩)
  simp only [hpt]
  exact ⟨hN, hT⟩

/-- The leaves of the trees of a linear side in expanded form are its internal wires, each twice
(Fig. 6, page 86). -/
theorem Rule.Expanded.sum_vars_portTree {φ : Rule S a k} (he : φ.Expanded) (hl : φ.Linear) :
    ∑ p, (φ.portTree p).vars =
      2 • Finset.univ.val.map fun w : Fin φ.internal =>
        (.inr (.inr w) : Fin a ⊕ Fin k ⊕ Fin φ.internal) := by
  obtain ⟨hN, hT⟩ := he.net_eq_portTree hl
  have hinj : Function.Injective fun w : Fin φ.internal =>
      (.inr (.inr w) : Fin a ⊕ Fin k ⊕ Fin φ.internal) := fun _ _ h => by simpa using h
  ext x
  rw [Multiset.count_nsmul]
  rcases x with i | j | w
  · rw [Multiset.count_eq_zero.2, Multiset.count_eq_zero.2]
    · simp
    · rw [Multiset.mem_sum]
      rintro ⟨p, -, hp⟩
      obtain ⟨w, hw⟩ := hT p _ hp
      cases hw
  · rw [Multiset.count_eq_zero.2, Multiset.count_eq_zero.2]
    · simp
    · rw [Multiset.mem_sum]
      rintro ⟨p, -, hp⟩
      obtain ⟨w, hw⟩ := hT p _ hp
      cases hw
  · rw [count_internal (n := φ.internal) (N := φ.net) hl hN w,
      Multiset.count_map_eq_count' _ _ hinj, Multiset.count_eq_one_of_mem Finset.univ.nodup
        (Finset.mem_univ_val _)]

end INet

namespace INet.Comb

open Term Translation

variable {S : Signature} {a k : ℕ}

/-! ## The package -/

/-- The names of `Γ_{i,j}` given to the names of `φ` (Fig. 6, page 86): the internal wire `w` is
named `k₀ + w`. A port of `φ` does not occur in its trees when `φ` is expanded; it is sent to
`k₀`. -/
def gammaName (k₀ : ℕ) {n : ℕ} : Fin a ⊕ Fin k ⊕ Fin n → ℕ :=
  Sum.elim (fun _ => k₀) (Sum.elim (fun _ => k₀) fun w => k₀ + w)

/-- The tree of `φ` at the port `p`, its internal wires named from `k₀` (Fig. 6, page 86). -/
noncomputable def gammaTree (φ : Rule S a k) (k₀ : ℕ) (p : Fin a ⊕ Fin k) : Term S ℕ :=
  (φ.portTree p).bind fun x => .var (gammaName k₀ x)

/-- The number of internal wires of the translation of each tree of `φ`, the ports numbered
`0, …, a + k - 1` by `finSumFinEquiv` (page 87). -/
noncomputable def gammaSizes (Φ : Translation S sig) (φ : Rule S a k) (k₀ : ℕ) :
    Fin (a + k) → ℕ :=
  fun q => Φ.size (gammaTree φ k₀ (finSumFinEquiv.symm q))

/-- The number of names of `Γ_{i,j}` (Fig. 6, page 86): the internal wires of `φ`, then those of
the translations of its trees. -/
noncomputable def gammaSize (Φ : Translation S sig) (φ : Rule S a k) (k₀ : ℕ) : ℕ :=
  φ.internal + ∑ q, gammaSizes Φ φ k₀ q

/-- The tree of `[φ]` at the port `p` (pages 86–87): the translation of the tree of `φ` at `p`,
its new wires numbered from the block of `p` above `k₀ + φ.internal`. -/
noncomputable def gammaPort (Φ : Translation S sig) (φ : Rule S a k) (k₀ : ℕ)
    (p : Fin a ⊕ Fin k) : Term sig ℕ :=
  Φ.trTerm (k₀ + φ.internal + off (gammaSizes Φ φ k₀) (finSumFinEquiv p)) (gammaTree φ k₀ p)

/-- **The package `Γ_{i,j}`** (Lafont 1997, Fig. 6, page 86): the dual multiplexor `M*_{a+1}`,
whose first `a` leaves are the trees of `[φ]` at the ports of the first cell and whose last leaf
is the transpositor `T_σ` applied to the trees of `[φ]` at the `k` middle ports. -/
noncomputable def gamma (Φ : Translation S sig) (φ : Rule S a k) (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ) (k₀ : ℕ) : Term sig ℕ :=
  muxStar (List.ofFn (fun i => gammaPort Φ φ k₀ (.inl i)) ++
    [transpositorPerm σ hσ (fun j => gammaPort Φ φ k₀ (.inr j))])

/-- The names `k₀ + w` of the internal wires of `φ` form the interval `[k₀, k₀ + n)`. -/
theorem map_add_univ (k₀ n : ℕ) :
    (Finset.univ.val.map fun w : Fin n => k₀ + (w : ℕ)) = Multiset.Ico k₀ (k₀ + n) := by
  refine Multiset.Nodup.ext (Multiset.Nodup.map (fun x y h => Fin.ext (by simpa using h))
    Finset.univ.nodup) Multiset.nodup_Ico |>.2 fun x => ?_
  simp only [Multiset.mem_map, Finset.mem_univ_val, true_and, Multiset.mem_Ico]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨by omega, by have := w.isLt; omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x - k₀, by omega⟩, by simp; omega⟩

/-- The names of the trees of an expanded linear side, renamed from `k₀`, are both ends of each
name of `[k₀, k₀ + φ.internal)` (Fig. 6, page 86). -/
theorem sum_vars_gammaTree {φ : Rule S a k} (he : φ.Expanded) (hl : φ.Linear) (k₀ : ℕ) :
    ∑ p, (gammaTree φ k₀ p).vars = 2 • Multiset.Ico k₀ (k₀ + φ.internal) := by
  have h : ∀ p, (gammaTree φ k₀ p).vars = (φ.portTree p).vars.map (gammaName k₀) := fun p => by
    rw [gammaTree, Term.vars_bind]
    simp [Multiset.bind_singleton]
  simp only [h]
  have hm : ∑ p, (φ.portTree p).vars.map (gammaName k₀) =
      (∑ p, (φ.portTree p).vars).map (gammaName k₀) :=
    (map_sum (Multiset.mapAddMonoidHom (gammaName k₀)) _ _).symm
  rw [hm, he.sum_vars_portTree hl, Multiset.map_nsmul, Multiset.map_map, ← map_add_univ]
  rfl

/-- **The names of `Γ_{i,j}`** (Fig. 6, page 86): for a linear side in expanded form, they are both
ends of each name of `[k₀, k₀ + gammaSize)`. -/
theorem vars_gamma (Φ : Translation S sig) {φ : Rule S a k} (he : φ.Expanded) (hl : φ.Linear)
    (σ : Equiv.Perm (Fin k)) (hσ : Function.Involutive σ) (k₀ : ℕ) :
    (gamma Φ φ σ hσ k₀).vars = 2 • Multiset.Ico k₀ (k₀ + gammaSize Φ φ k₀) := by
  set s := gammaSizes Φ φ k₀
  set B := k₀ + φ.internal
  have hport : ∀ p, (gammaPort Φ φ k₀ p).vars = (gammaTree φ k₀ p).vars +
      2 • Multiset.Ico (B + off s (finSumFinEquiv p))
        (B + off s (finSumFinEquiv p) + s (finSumFinEquiv p)) := fun p => by
    rw [gammaPort, vars_trTerm]
    simp [s, gammaSizes, B]
  have hsum : (gamma Φ φ σ hσ k₀).vars = ∑ p, (gammaPort Φ φ k₀ p).vars := by
    rw [gamma, vars_muxStar, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn,
      Fintype.sum_sum_type]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      vars_transpositorPerm]
    rfl
  rw [hsum]
  simp only [hport]
  rw [Finset.sum_add_distrib, sum_vars_gammaTree he hl,
    Equiv.sum_comp finSumFinEquiv (fun q => 2 • Multiset.Ico (B + off s q) (B + off s q + s q)),
    ← Finset.smul_sum, sum_Ico_off, ← nsmul_add, gammaSize,
    Multiset.Ico_add_Ico_eq_Ico (by omega) (by omega), add_assoc]

/-- **`Γ_{i,j}` is a package** (Fig. 6, page 86; packages, page 80): for a linear side in expanded
form, every name of `gamma Φ φ σ hσ k₀` occurs exactly twice. -/
theorem gamma_isPackage (Φ : Translation S sig) {φ : Rule S a k} (he : φ.Expanded)
    (hl : φ.Linear) (σ : Equiv.Perm (Fin k)) (hσ : Function.Involutive σ) (k₀ : ℕ) :
    (gamma Φ φ σ hσ k₀).IsPackage := by
  intro x hx
  rw [vars_gamma Φ he hl] at hx ⊢
  rw [Multiset.count_nsmul, Multiset.count_eq_one_of_mem Multiset.nodup_Ico
    (Multiset.mem_of_mem_nsmul hx)]

/-- The names of `Γ_{i,j}` lie in `[k₀, k₀ + gammaSize)` (Fig. 6, page 86), for a linear side in
expanded form. -/
theorem mem_vars_gamma (Φ : Translation S sig) {φ : Rule S a k} (he : φ.Expanded)
    (hl : φ.Linear) (σ : Equiv.Perm (Fin k)) (hσ : Function.Involutive σ) (k₀ : ℕ) {x : ℕ}
    (hx : x ∈ (gamma Φ φ σ hσ k₀).vars) : k₀ ≤ x ∧ x < k₀ + gammaSize Φ φ k₀ := by
  rw [vars_gamma Φ he hl] at hx
  exact Multiset.mem_Ico.1 (Multiset.mem_of_mem_nsmul hx)

end INet.Comb
