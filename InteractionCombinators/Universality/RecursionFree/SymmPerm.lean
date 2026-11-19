import InteractionCombinators.Reduction.RuleInstances
import InteractionCombinators.Universality.RecursionFree.DecompositionSymm

/-!
# Symmetry up to a permutation of the internal wires (page 73)

Lafont 1997, page 73 (PDF page 5): the rule of a symbol with itself must be symmetric, that is,
read from the other cell it is the same graph. A graph does not name its internal wires, so the
condition is `Rule.SymmPerm`: `r.swap.net` is `Equiv` to `r.net` with its internal wires renamed by
a permutation `π`. Issue #236, preparing the change of `System.WellFormed.symm` asked in #136.

The two lemmas that use `System.WellFormed.symm` hold under this weaker hypothesis, with the same
conclusions:

* `Rule.equiv_inst_comm_of_symmPerm` (for Proposition 1): an instance does not depend on the
  names of the internal wires, which absorbs `π` (`Rule.equiv_inst_of_linear`);
* `Rule.exists_symm_decomposition_of_symmPerm` (page 86): after expansion, `π` is transported to
  the expanded rule by extending it along the injective renaming of the internal wires
  (`Rule.exists_perm_extend`), and composed with the permutation given by
  `Rule.exists_perm_of_equiv`.

`Rule.SymmPerm.of_equiv` shows that the condition is weaker than `Equiv r.swap.net r.net`; the
example `twin`, which is `SymmPerm` without being `Equiv` to its swap, is in
`Checks/SymmPermCheck.lean`.
-/

namespace INet

variable {S : Signature} {a : ℕ}

open Term

/-- A rule of a symbol with itself is symmetric: read from the other cell it is the same graph,
that is, the same net up to wires and up to a permutation of its internal wires (page 73). -/
def Rule.SymmPerm (r : Rule S a a) : Prop :=
  ∃ π : _root_.Equiv.Perm (Fin r.internal),
    Equiv r.swap.net (r.net.bind fun x => var (Sum.map id (Sum.map id π) x))

/-- Symmetry up to wires implies symmetry up to wires and a permutation of the internal wires,
with the identity permutation (page 73). -/
theorem Rule.SymmPerm.of_equiv {r : Rule S a a} (h : Equiv r.swap.net r.net) : r.SymmPerm := by
  refine ⟨1, h.trans (Equiv.of_eq ?_)⟩
  conv_lhs => rw [← Net.bind_var_self r.net]
  refine Net.bind_congr fun x _ => ?_
  rcases x with i | j | w <;> rfl

namespace Rule

/-- **A symmetric rule can be read with its two groups of ports exchanged** (Lafont 1997,
page 73, the symmetry condition, used in Proposition 1). If `r.swap.net` is the same graph as
`r.net` up to a permutation of the internal wires, the instances `r.inst as bs f` and
`r.inst bs as f` are the same graph, when linear. -/
theorem equiv_inst_comm_of_symmPerm {a : ℕ} (r : Rule S a a) (hr : r.Linear)
    (hsymm : r.SymmPerm) (as bs : Fin a → Term S ℕ) (f : Fin r.internal → ℕ)
    (Δ : Net S ℕ) (L : (r.inst as bs f + Δ).Linear) :
    Equiv (r.inst as bs f + Δ) (r.inst bs as f + Δ) := by
  obtain ⟨π, hπ⟩ := hsymm
  have hL : ∀ y, ∑ i, (bs i).vars.count y + ∑ j, (as j).vars.count y +
      2 * (∑ w, if y = f w then 1 else 0) + Δ.vars.count y ≤ 2 := by
    intro y
    have := L y
    rw [Net.vars_add, Multiset.count_add, count_vars_inst r hr] at this
    omega
  have E := equiv_bind_args hπ (portShape_net r.swap (DecompositionSymm.swap_linear r hr))
    bs as f Δ hL
  have e1 : (r.swap.net.bind (args bs as f) : Net S ℕ) = r.inst as bs f := swap_inst r as bs f
  have e2 : ((r.net.bind fun x => var (Sum.map id (Sum.map id π) x)).bind (args bs as f) :
      Net S ℕ) = r.inst bs as (f ∘ π) := by
    rw [inst_eq_bind, Net.bind_bind]
    refine Net.bind_congr fun x _ => ?_
    rcases x with i | j | w <;> rfl
  replace E : Equiv (r.inst as bs f + Δ) (r.inst bs as (f ∘ π) + Δ) := by
    rw [← e1, ← e2]
    exact E
  have L2 : (r.inst bs as f + Δ).Linear := by
    intro y
    rw [Net.vars_add, Multiset.count_add, count_vars_inst r hr]
    have := hL y
    omega
  exact E.trans (r.equiv_inst_of_linear hr bs as (f ∘ π) f Δ (E.linear L) L2)

/-- A permutation of `Fin n` extends along an injection `ι : Fin n → Fin m` to a permutation of
`Fin m` that commutes with `ι`. -/
theorem exists_perm_extend {n m : ℕ} (ι : Fin n → Fin m) (hι : Function.Injective ι)
    (π : _root_.Equiv.Perm (Fin n)) :
    ∃ π' : _root_.Equiv.Perm (Fin m), ∀ w, π' (ι w) = ι (π w) := by
  classical
  refine ⟨π.extendDomain (_root_.Equiv.ofInjective ι hι), fun w => ?_⟩
  have := _root_.Equiv.Perm.extendDomain_apply_image π (_root_.Equiv.ofInjective ι hι) w
  simpa using this

/-- Renaming the internal wires of a linear rule by a permutation gives a linear rule. -/
theorem linear_rename {b n : ℕ} {N : Net S (Fin a ⊕ Fin b ⊕ Fin n)} (π : _root_.Equiv.Perm (Fin n))
    (h : (⟨n, N⟩ : Rule S a b).Linear) :
    (⟨n, N.bind fun x => var (Sum.map id (Sum.map id π) x)⟩ : Rule S a b).Linear := by
  classical
  have hinj : Function.Injective
      (Sum.map id (Sum.map id π) : Fin a ⊕ Fin b ⊕ Fin n → Fin a ⊕ Fin b ⊕ Fin n) :=
    Sum.map_injective.2 ⟨Function.injective_id,
      Sum.map_injective.2 ⟨Function.injective_id, π.injective⟩⟩
  have hv : Net.vars (N.bind fun x => var (Sum.map id (Sum.map id π) x)) =
      N.vars.map (Sum.map id (Sum.map id π)) :=
    Net.vars_bind_var _ _
  refine ⟨fun i => ?_, fun j => ?_, fun w => ?_⟩
  · change (Net.vars (N.bind fun x => var (Sum.map id (Sum.map id π) x))).count (.inl i) = 1
    rw [hv, show (.inl i : Fin a ⊕ Fin b ⊕ Fin n) = Sum.map id (Sum.map id π) (.inl i) from rfl,
      Multiset.count_map_eq_count' _ _ hinj]
    exact h.left i
  · change (Net.vars (N.bind fun x => var (Sum.map id (Sum.map id π) x))).count
      (.inr (.inl j)) = 1
    rw [hv, show (.inr (.inl j) : Fin a ⊕ Fin b ⊕ Fin n) =
        Sum.map id (Sum.map id π) (.inr (.inl j)) from rfl,
      Multiset.count_map_eq_count' _ _ hinj]
    exact h.right j
  · change (Net.vars (N.bind fun x => var (Sum.map id (Sum.map id π) x))).count
      (.inr (.inr w)) = 2
    rw [hv, show (.inr (.inr w) : Fin a ⊕ Fin b ⊕ Fin n) =
        Sum.map id (Sum.map id π) (.inr (.inr (π.symm w))) by simp,
      Multiset.count_map_eq_count' _ _ hinj]
    exact h.internal (π.symm w)

/-- Renaming the internal wires of a rule in expanded form by a permutation gives a rule in
expanded form. -/
theorem expanded_rename {b n : ℕ} {N : Net S (Fin a ⊕ Fin b ⊕ Fin n)}
    (π : _root_.Equiv.Perm (Fin n)) (h : (⟨n, N⟩ : Rule S a b).Expanded) :
    (⟨n, N.bind fun x => var (Sum.map id (Sum.map id π) x)⟩ : Rule S a b).Expanded := by
  intro e hmem
  obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.1 hmem
  obtain ⟨p, t, rfl, hp, ht⟩ := h e₀ he₀
  refine ⟨Sum.map id (Sum.map id π) p, t.bind fun x => var (Sum.map id (Sum.map id π) x), rfl,
    ?_, ?_⟩
  · intro w hw
    rcases p with i | j | w'
    · cases hw
    · cases hw
    · exact hp w' rfl
  · intro x hx
    rw [Term.vars_bind] at hx
    obtain ⟨y, hy, hxy⟩ := Multiset.mem_bind.1 hx
    obtain ⟨w, rfl⟩ := ht y hy
    simp only [vars_var, Multiset.mem_singleton] at hxy
    exact ⟨π w, by rw [hxy]; rfl⟩

end Rule

open DecompositionSymm in
/-- **The symmetric decomposition of a rule `α`–`α`, under the symmetry condition of page 73**
(Lafont 1997, page 86: "To sum up, one can assume that in all cases `φ_{j,i} = ψ_{i,j}`,
`σ_{j,i} = σ_{i,j}`, and `σ_{i,j}` is involutive"; Fig. 7). Let `r` be a linear reduced rule of a
symbol with itself which, read from the other cell, is the same graph up to a permutation of its
internal wires. Then `r` has a decomposition `(φ, ψ, σ)` with `ψ = φ` and `σ` involutive, whose
side `φ` is linear and reduced, and whose plug is `r` up to `Equiv` and an injective renaming of
the internal wires. This is `Rule.exists_symm_decomposition` with a weaker hypothesis. -/
theorem Rule.exists_symm_decomposition_of_symmPerm (r : Rule S a a) (hl : r.Linear)
    (hr : r.Reduced) (hsym : r.SymmPerm) :
    ∃ D : Decomposition S a a, D.ψ = D.φ ∧ (∀ l, D.σ (D.σ l) = l) ∧ D.φ.Linear ∧ D.φ.Reduced ∧
      ∃ ι : Fin r.internal → Fin (Rule.plug D.φ D.ψ D.σ).internal, Function.Injective ι ∧
        Equiv (Rule.plug D.φ D.ψ D.σ).net
          (r.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) := by
  obtain ⟨π, hπ⟩ := hsym
  replace hπ : Equiv (show Net S (Fin a ⊕ Fin a ⊕ Fin r.internal) from r.swap.net)
      (r.net.bind fun x => var (Sum.map id (Sum.map id π) x)) := hπ
  -- 1. an expanded form `r'` of `r`
  obtain ⟨r', ι₀, hι₀, hl', he', heq⟩ := r.exists_expanded hl hr
  have hren : ∀ {n m : ℕ} {f : Fin n → Fin m}, Function.Injective f →
      Function.Injective
        (Sum.map id (Sum.map id f) : Fin a ⊕ Fin a ⊕ Fin n → Fin a ⊕ Fin a ⊕ Fin m) :=
    fun hf => Sum.map_injective.2 ⟨Function.injective_id,
      Sum.map_injective.2 ⟨Function.injective_id, hf⟩⟩
  -- 2. `π` carried to the internal wires of `r'`
  obtain ⟨π', hπ'⟩ := Rule.exists_perm_extend ι₀ hι₀ π
  -- 3. `r'` is symmetric up to `Equiv` and `π'`
  have hsym' : Equiv r'.swap.net (r'.net.bind fun x => var (Sum.map id (Sum.map id π') x)) := by
    have h1 := Equiv.bind_var _ (Rule.swapName_injective (a := a) (b := a) (n := r'.internal)) heq
    have h2 := Equiv.bind_var _ (hren hι₀) hπ
    have h3 := Equiv.bind_var _ (hren π'.injective) heq
    rw [← swap_net] at h1
    refine h1.trans (Equiv.trans (Equiv.of_eq ?_) (h2.trans (Equiv.trans (Equiv.of_eq ?_) h3.symm)))
    · rw [swap_net, Net.bind_bind, Net.bind_bind]
      refine Net.bind_congr fun x _ => ?_
      simp only [Term.bind_var]
      exact congrArg var (swapName_map ι₀ x)
    · rw [Net.bind_bind, Net.bind_bind]
      refine Net.bind_congr fun x _ => ?_
      rcases x with i | j | w
      · rfl
      · rfl
      · simp only [Term.bind_var, Sum.map_inr]
        rw [hπ']
  -- 4. and literally symmetric up to a permutation of the internal wires
  obtain ⟨π'', hπ''⟩ := Rule.exists_perm_of_equiv
    (N := r'.net.bind fun x => var (Sum.map id (Sum.map id π') x)) (M := r'.swap.net)
    (Rule.linear_rename π' hl') (swap_linear r' hl') (Rule.expanded_rename π' he')
    (swap_expanded r' he') hsym'.symm
  have hlit : r'.swap.net = r'.net.bind fun x => var (Sum.map id (Sum.map id (π'' * π')) x) := by
    rw [hπ'', Net.bind_bind]
    refine Net.bind_congr fun x _ => ?_
    rcases x with i | j | w <;> rfl
  -- 5. the symmetric decomposition of `r'`
  obtain ⟨D, hψ, hσ, hφl, hφr, ι₁, hι₁, heq₁⟩ :=
    Rule.SymmLit.exists_symm_decomposition r' hl' he' (π'' * π') hlit
  refine ⟨D, hψ, hσ, hφl, hφr, ι₁ ∘ ι₀, hι₁.comp hι₀, ?_⟩
  refine heq₁.trans ((Equiv.bind_var _ (hren hι₁) heq).trans (Equiv.of_eq ?_))
  rw [Net.bind_bind]
  refine Net.bind_congr fun x _ => ?_
  rcases x with i | j | w <;> rfl

end INet
