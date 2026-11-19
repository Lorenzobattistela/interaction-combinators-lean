import InteractionCombinators.Universality.RecursionFree.Expand
import InteractionCombinators.Universality.RecursionFree.DecompositionSymmLiteral

/-!
# The symmetric decomposition of a rule `α`–`α` (page 86)

Lafont 1997, page 86 (PDF page 18): "To sum up, one can assume that in all cases
`φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}`, and `σ_{i,j}` is involutive"; Fig. 7. Issue #66, part 4.

A linear reduced rule `r : Rule S a a` whose net, read from the other cell, is `Equiv` to itself
(the first form of the symmetry condition; for `System.WellFormed.symm` as it is now, up to a
permutation of the internal wires, see `Rule.exists_symm_decomposition_of_symmPerm` in
`RecursionFree/SymmPerm.lean`) has a decomposition `(φ, φ, σ)` with `σ` involutive whose plug
is `r`. The proof assembles the three parts:

1. `Rule.exists_expanded` (`RecursionFree/Expand.lean`): `r` is `Equiv` to an expanded rule `r'`;
2. the symmetry passes to `r'`, and `r'.swap` is linear and expanded, so
   `Rule.exists_perm_of_equiv` (`RecursionFree/ExpandedIso.lean`) makes it literal:
   `r'.swap.net = r'.net` renamed by a permutation of the internal wires;
3. `Rule.SymmLit.exists_symm_decomposition` (`RecursionFree/DecompositionSymmLiteral.lean`)
   applies to `r'`.

Contents, in the order of the file:

1. Auxiliary lemmas: `DecompositionSymm.swap_net`, `DecompositionSymm.swapName_map`,
   `DecompositionSymm.swap_linear`, `DecompositionSymm.swap_expanded`. Reading a rule from the
   other cell is a renaming of its names, which commutes with renaming the internal wires and
   keeps a rule linear and expanded.
2. Main result: `Rule.exists_symm_decomposition`, the decomposition `(φ, φ, σ)` with `σ`
   involutive of a symmetric rule `α`–`α` (page 86).
-/

namespace INet

variable {S : Signature} {a : ℕ}

open Term

namespace DecompositionSymm

-- ============================================================================================
-- 1. Auxiliary lemmas: a rule read from the other cell
-- ============================================================================================

/-- The net of `r.swap` is the net of `r` renamed by `Rule.swapName`. -/
theorem swap_net
    -- a rule between a symbol of arity `a` and one of arity `b`
    {b : ℕ}
    (r : Rule S a b) :
    r.swap.net = r.net.bind fun x => var (Rule.swapName x) := rfl

/-- Renaming the internal wires commutes with exchanging the two groups of ports. -/
theorem swapName_map
    -- the renaming of the internal wires
    {b n m : ℕ}
    (f : Fin n → Fin m)
    -- a name of a rule: a port of the first cell, a port of the second, or an internal wire
    (x : Fin a ⊕ Fin b ⊕ Fin n) :
    Rule.swapName (Sum.map id (Sum.map id f) x)
      = Sum.map id (Sum.map id f) (Rule.swapName x) := by
  rcases x with i | j | w <;> rfl

/-- A rule read from the other cell is linear when the rule is. -/
theorem swap_linear
    -- a linear rule
    {b : ℕ}
    (r : Rule S a b)
    (hl : r.Linear) :
    r.swap.Linear := by
  classical
  have hv : Net.vars (show Net S (Fin b ⊕ Fin a ⊕ Fin r.internal) from r.swap.net) =
      r.net.vars.map Rule.swapName :=
    Net.vars_bind_var _ _
  refine ⟨fun j => ?_, fun i => ?_, fun w => ?_⟩
  · show (Net.vars (show Net S (Fin b ⊕ Fin a ⊕ Fin r.internal) from r.swap.net)).count
      (.inl j) = 1
    rw [hv, show (.inl j : Fin b ⊕ Fin a ⊕ Fin r.internal) = Rule.swapName (.inr (.inl j)) from rfl,
      Multiset.count_map_eq_count' _ _ Rule.swapName_injective]
    exact hl.right j
  · show (Net.vars (show Net S (Fin b ⊕ Fin a ⊕ Fin r.internal) from r.swap.net)).count
      (.inr (.inl i)) = 1
    rw [hv, show (.inr (.inl i) : Fin b ⊕ Fin a ⊕ Fin r.internal) = Rule.swapName (.inl i) from rfl,
      Multiset.count_map_eq_count' _ _ Rule.swapName_injective]
    exact hl.left i
  · let w' : Fin r.internal := w
    show (Net.vars (show Net S (Fin b ⊕ Fin a ⊕ Fin r.internal) from r.swap.net)).count
      (.inr (.inr w')) = 2
    rw [hv, show (.inr (.inr w') : Fin b ⊕ Fin a ⊕ Fin r.internal) =
        Rule.swapName (.inr (.inr w')) from rfl,
      Multiset.count_map_eq_count' _ _ Rule.swapName_injective]
    exact hl.internal w'

/-- A rule read from the other cell is in expanded form when the rule is. -/
theorem swap_expanded
    -- a rule in expanded form
    {b : ℕ}
    (r : Rule S a b)
    (he : r.Expanded) :
    r.swap.Expanded := by
  show ∀ e ∈ (show Net S (Fin b ⊕ Fin a ⊕ Fin r.internal) from r.swap.net), ∃ p t,
    e = s(Term.var p, t) ∧ (∀ w : Fin r.internal, p ≠ .inr (.inr w)) ∧
      ∀ x ∈ Term.vars (S := S) t, ∃ w : Fin r.internal, x = .inr (.inr w)
  intro e hmem
  obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.1 hmem
  obtain ⟨p, t, rfl, hp, ht⟩ := he e₀ he₀
  refine ⟨Rule.swapName p, t.bind fun x => var (Rule.swapName x), rfl, ?_, ?_⟩
  · intro w h
    rcases p with i | j | w'
    · cases h
    · cases h
    · exact hp w' rfl
  · intro x hx
    rw [Term.vars_bind] at hx
    obtain ⟨y, hy, hxy⟩ := Multiset.mem_bind.1 hx
    obtain ⟨w, rfl⟩ := ht y hy
    simp only [vars_var, Multiset.mem_singleton] at hxy
    exact ⟨w, hxy⟩

end DecompositionSymm

-- ============================================================================================
-- 2. Main result: the symmetric decomposition
-- ============================================================================================

open DecompositionSymm in
/-- **The symmetric decomposition of a rule `α`–`α`** (Lafont 1997, page 86: "To sum up, one can
assume that in all cases `φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}`, and `σ_{i,j}` is involutive";
Fig. 7). Let `r` be a linear reduced rule of a symbol with itself which, read from the other cell,
is `Equiv` to itself. Then `r` has a decomposition `(φ, ψ, σ)` with `ψ = φ` and `σ` involutive,
whose side `φ` is linear and reduced, and whose plug is `r` up to `Equiv` and an injective
renaming of the internal wires. -/
theorem Rule.exists_symm_decomposition
    -- a linear reduced rule between a symbol of arity `a` and itself
    (r : Rule S a a)
    (hl : r.Linear)
    (hr : r.Reduced)
    -- the rule, read from the other cell, is the same graph
    (hsym : Equiv r.swap.net r.net) :
    -- there is a decomposition `D` such that
    ∃ D : Decomposition S a a,
      -- its two sides are the same,
      D.ψ = D.φ ∧
      -- its permutation `σ` is involutive,
      (∀ l, D.σ (D.σ l) = l) ∧
      -- its side `φ` is linear and reduced,
      D.φ.Linear ∧
      D.φ.Reduced ∧
      -- and there is an injective renaming `ι` of the internal wires of `r` into those of the
      -- plug of `D`,
      ∃ ι : Fin r.internal → Fin (Rule.plug D.φ D.ψ D.σ).internal,
        Function.Injective ι ∧
        -- such that the plug of `D` is the same graph as `r` renamed by `ι`
        Equiv (Rule.plug D.φ D.ψ D.σ).net
          (r.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) := by
  -- 1. an expanded form `r'` of `r`
  obtain ⟨r', ι₀, hι₀, hl', he', heq⟩ := r.exists_expanded hl hr
  have hren : ∀ {n m : ℕ} {f : Fin n → Fin m}, Function.Injective f →
      Function.Injective (Sum.map id (Sum.map id f) :
        Fin a ⊕ Fin a ⊕ Fin n → Fin a ⊕ Fin a ⊕ Fin m) :=
    fun hf => Sum.map_injective.2 ⟨Function.injective_id,
      Sum.map_injective.2 ⟨Function.injective_id, hf⟩⟩
  -- 2. `r'` is symmetric up to `Equiv`
  have hsym' : Equiv r'.swap.net r'.net := by
    have h1 := Equiv.bind_var _ (Rule.swapName_injective (a := a) (b := a) (n := r'.internal)) heq
    have h2 := Equiv.bind_var _ (hren hι₀) hsym
    rw [← swap_net] at h1
    refine h1.trans (Equiv.trans (Equiv.of_eq ?_) (h2.trans heq.symm))
    rw [swap_net, Net.bind_bind, Net.bind_bind]
    refine Net.bind_congr fun x _ => ?_
    simp only [Term.bind_var]
    exact congrArg var (swapName_map ι₀ x)
  -- 3. and literally symmetric up to a permutation of the internal wires
  obtain ⟨π, hπ⟩ := Rule.exists_perm_of_equiv (N := r'.net) (M := r'.swap.net) hl'
    (swap_linear r' hl') he' (swap_expanded r' he') hsym'.symm
  -- 4. the symmetric decomposition of `r'`
  obtain ⟨D, hψ, hσ, hφl, hφr, ι₁, hι₁, heq₁⟩ :=
    Rule.SymmLit.exists_symm_decomposition r' hl' he' π hπ
  refine ⟨D, hψ, hσ, hφl, hφr, ι₁ ∘ ι₀, hι₁.comp hι₀, ?_⟩
  refine heq₁.trans ((Equiv.bind_var _ (hren hι₁) heq).trans (Equiv.of_eq ?_))
  rw [Net.bind_bind]
  refine Net.bind_congr fun x _ => ?_
  rcases x with i | j | w <;> rfl

end INet
