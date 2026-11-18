import InteractionCombinators.Lafont.TranspositorPerm

/-!
# Checks of `Lafont/TranspositorPerm.lean` against the paper

A review (issue 50) compared `transpositorPerm`, `portList`, `involutive_decomp` and
`transpositorPerm_transpositorPerm` with Lafont 1997, page 84 (PDF page 16): the picture of the
property of `T_σ` and the picture of the "possible implementation", a box `ρ` on top of `T_{p,q}`.
This file records the cases worked by hand as statements that Lean checks.

Ports are numbered from `0`, as in `TranspositorPerm.lean`.

* `transpositorPerm_0312`, `transpositorPerm_transpositorPerm_0312` — σ = (0 3)(1 2), two
  transpositions that are not adjacent: the tree, and the property by hand (one `δδ`, two `γγ`),
  without `transpositorPerm_transpositorPerm`. `_0312'` gets the same from the general theorem.
* `transpositorPerm_12`, `transpositorPerm_transpositorPerm_12` — σ = (1 2) with the fixed points
  `0` and `3`: the same, with two `δδ` and one `γγ`.
* `vars_transpositorPerm_0312` — each name on the ports of `T_σ` occurs once.
* `transpositorPerm_zero` — for `n = 0`, `T_σ` is `ε`.
* `transpositorPerm_one` — for σ the identity, `T_σ` is the autodual multiplexor `T_n`.
* `decomp_0312`, `decomp_12` — the box ρ of the picture: port `i` of `T_σ` is port `ρ i` of
  `T_{p,q}`, and `σ = ρ⁻¹ ∘ ι_{p,q} ∘ ρ` holds with this ρ, not with ρ⁻¹ in its place.
* `portList_finRotate`, `not_involutive_finRotate` — for a 3-cycle, `portList` repeats a port and
  has length 4: the hypothesis `Function.Involutive σ`, unused in the body of `transpositorPerm`,
  is what makes `T_σ` linear. It cannot be dropped, and it is required by the definition, so
  `T_σ` cannot be formed for such σ.
-/

namespace INet.Comb.TranspositorPermCheck

open Term

variable (t₀ t₁ t₂ t₃ u₀ u₁ u₂ u₃ : Term sig ℕ) (Δ : CNet)

/-! ### σ = (0 3)(1 2) -/

/-- σ = (0 3)(1 2) on four ports. -/
def σ₁ : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2

theorem σ₁_inv : Function.Involutive σ₁ := by unfold Function.Involutive; decide

/-- The list of ports of (0 3)(1 2) is `0, 3, 1, 2`: `p = 2`, `q = 0`. -/
theorem portList_σ₁ : portList σ₁ = [0, 3, 1, 2] := by decide

/-- `T_σ` for σ = (0 3)(1 2) (page 84): `T_{2,0}` with ports `0, 3` under one `con` and `1, 2` under
the other. -/
theorem transpositorPerm_0312 (ts : Fin 4 → Term sig ℕ) :
    transpositorPerm σ₁ σ₁_inv ts = mkDup (mkCon (ts 0) (ts 3)) (mkCon (ts 1) (ts 2)) := by
  have hp : pairFst σ₁ = [0, 1] := by decide
  simp only [transpositorPerm, portList_σ₁, hp, List.map_cons, List.map_nil, List.length_cons,
    List.length_nil]
  rfl

/-- The property of `T_σ` for σ = (0 3)(1 2), by hand (page 84): `δδ`, then `γγ` twice. Port `i`
of one copy is joined to port `σ i` of the other: `0–3`, `3–0`, `1–2`, `2–1`. -/
theorem transpositorPerm_transpositorPerm_0312 :
    Red (s(transpositorPerm σ₁ σ₁_inv ![t₀, t₁, t₂, t₃],
          transpositorPerm σ₁ σ₁_inv ![u₀, u₁, u₂, u₃]) ::ₘ Δ)
      (s(t₀, u₃) ::ₘ s(t₃, u₀) ::ₘ s(t₁, u₂) ::ₘ s(t₂, u₁) ::ₘ Δ) := by
  rw [transpositorPerm_0312, transpositorPerm_0312]
  simp only [Matrix.cons_val]
  refine Relation.ReflTransGen.head (step_dup_dup _ _ _ _ Δ) ?_
  refine Relation.ReflTransGen.head (step_con_con t₀ t₃ u₀ u₃ _) ?_
  have h : Red (s(mkCon t₁ t₂, mkCon u₁ u₂) ::ₘ s(t₀, u₃) ::ₘ s(t₃, u₀) ::ₘ Δ)
      (s(t₁, u₂) ::ₘ s(t₂, u₁) ::ₘ s(t₀, u₃) ::ₘ s(t₃, u₀) ::ₘ Δ) :=
    Steps.single (step_con_con t₁ t₂ u₁ u₂ _)
  refine Steps.cast h ?_ ?_ <;> ms

/-- `transpositorPerm_transpositorPerm` gives the result computed by hand for σ = (0 3)(1 2). -/
theorem transpositorPerm_transpositorPerm_0312' :
    Red (s(transpositorPerm σ₁ σ₁_inv ![t₀, t₁, t₂, t₃],
          transpositorPerm σ₁ σ₁_inv ![u₀, u₁, u₂, u₃]) ::ₘ Δ)
      (s(t₀, u₃) ::ₘ s(t₃, u₀) ::ₘ s(t₁, u₂) ::ₘ s(t₂, u₁) ::ₘ Δ) := by
  refine (transpositorPerm_transpositorPerm σ₁ σ₁_inv _ _ Δ).cast rfl ?_
  have hσ : (σ₁ 0, σ₁ 1, σ₁ 2, σ₁ 3) = (3, 2, 1, 0) := by decide
  simp only [Prod.mk.injEq] at hσ
  obtain ⟨h0, h1, h2, h3⟩ := hσ
  rw [show (Finset.univ : Finset (Fin 4)).val = {0, 1, 2, 3} from rfl]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, h0, h1, h2, h3]
  simp only [Matrix.cons_val, ← Multiset.singleton_add, add_assoc]
  ms

/-! ### σ = (1 2), with two fixed points -/

/-- σ = (1 2) on four ports, fixing `0` and `3`. -/
def σ₂ : Equiv.Perm (Fin 4) := Equiv.swap 1 2

theorem σ₂_inv : Function.Involutive σ₂ := by unfold Function.Involutive; decide

/-- The list of ports of (1 2) is `1, 2, 0, 3`: `p = 1`, `q = 2`. -/
theorem portList_σ₂ : portList σ₂ = [1, 2, 0, 3] := by decide

/-- `T_σ` for σ = (1 2) on four ports (page 84): `T_{1,2}`, a `con` on ports `1, 2`, then the fixed
points `0` and `3` on the free ports of the multiplexor `T_3`. -/
theorem transpositorPerm_12 (ts : Fin 4 → Term sig ℕ) :
    transpositorPerm σ₂ σ₂_inv ts = mkDup (mkCon (ts 1) (ts 2)) (mkDup (ts 0) (ts 3)) := by
  have hp : pairFst σ₂ = [1] := by decide
  simp only [transpositorPerm, portList_σ₂, hp, List.map_cons, List.map_nil, List.length_cons,
    List.length_nil]
  rfl

/-- The property of `T_σ` for σ = (1 2) on four ports, by hand (page 84): `δδ`, `γγ`, `δδ`. The
fixed points are joined to themselves, `0–0` and `3–3`, and `1–2`, `2–1`. -/
theorem transpositorPerm_transpositorPerm_12 :
    Red (s(transpositorPerm σ₂ σ₂_inv ![t₀, t₁, t₂, t₃],
          transpositorPerm σ₂ σ₂_inv ![u₀, u₁, u₂, u₃]) ::ₘ Δ)
      (s(t₀, u₀) ::ₘ s(t₁, u₂) ::ₘ s(t₂, u₁) ::ₘ s(t₃, u₃) ::ₘ Δ) := by
  rw [transpositorPerm_12, transpositorPerm_12]
  simp only [Matrix.cons_val]
  refine Relation.ReflTransGen.head (step_dup_dup _ _ _ _ Δ) ?_
  refine Relation.ReflTransGen.head (step_con_con t₁ t₂ u₁ u₂ _) ?_
  have h : Red (s(mkDup t₀ t₃, mkDup u₀ u₃) ::ₘ s(t₁, u₂) ::ₘ s(t₂, u₁) ::ₘ Δ)
      (s(t₀, u₀) ::ₘ s(t₃, u₃) ::ₘ s(t₁, u₂) ::ₘ s(t₂, u₁) ::ₘ Δ) :=
    Steps.single (step_dup_dup t₀ t₃ u₀ u₃ _)
  refine Steps.cast h ?_ ?_ <;> ms

/-- `transpositorPerm_transpositorPerm` gives the result computed by hand for σ = (1 2). -/
theorem transpositorPerm_transpositorPerm_12' :
    Red (s(transpositorPerm σ₂ σ₂_inv ![t₀, t₁, t₂, t₃],
          transpositorPerm σ₂ σ₂_inv ![u₀, u₁, u₂, u₃]) ::ₘ Δ)
      (s(t₀, u₀) ::ₘ s(t₁, u₂) ::ₘ s(t₂, u₁) ::ₘ s(t₃, u₃) ::ₘ Δ) := by
  refine (transpositorPerm_transpositorPerm σ₂ σ₂_inv _ _ Δ).cast rfl ?_
  have hσ : (σ₂ 0, σ₂ 1, σ₂ 2, σ₂ 3) = (0, 2, 1, 3) := by decide
  simp only [Prod.mk.injEq] at hσ
  obtain ⟨h0, h1, h2, h3⟩ := hσ
  rw [show (Finset.univ : Finset (Fin 4)).val = {0, 1, 2, 3} from rfl]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, h0, h1, h2, h3]
  simp only [Matrix.cons_val, ← Multiset.singleton_add, add_assoc]

/-! ### `T_σ` is a principal net -/

/-- With the names `0, …, 3` on its ports, `T_σ` for σ = (0 3)(1 2) has each name once (page 84,
"a principal net of arity `n`"); its cells are `con`, `dup`, `era` since it is a `Term sig ℕ`. -/
theorem vars_transpositorPerm_0312 :
    (transpositorPerm σ₁ σ₁_inv ![var 0, var 1, var 2, var 3]).vars = {0, 1, 2, 3} := by
  rw [vars_transpositorPerm, show (Finset.univ : Finset (Fin 4)).val = {0, 1, 2, 3} from rfl]
  rfl

/-! ### Edge cases -/

/-- For `n = 0` (page 84, `2p + q = 0`), `T_σ` is `T_{0,0} = T_0 = ε` (Fig. 5). -/
theorem transpositorPerm_zero (σ : Equiv.Perm (Fin 0)) (hσ : Function.Involutive σ)
    (ts : Fin 0 → Term sig ℕ) : transpositorPerm σ hσ ts = mkEra := by
  have hl : portList σ = [] := List.eq_nil_of_length_eq_zero (length_portList hσ)
  have hp : pairFst σ = [] := by simp [pairFst]
  simp only [transpositorPerm, hl, hp, List.map_nil, List.length_nil]
  rfl

/-- For σ the identity (page 84, `p = 0`, `ρ` the identity), `T_σ` is the autodual multiplexor
`T_n` of Fig. 5, with the trees in the order of the ports. -/
theorem transpositorPerm_one (n : ℕ) (ts : Fin n → Term sig ℕ) :
    transpositorPerm (1 : Equiv.Perm (Fin n)) (fun _ => rfl) ts = autoMux (List.ofFn ts) := by
  have hp : pairFst (1 : Equiv.Perm (Fin n)) = [] := by simp [pairFst]
  have hl : portList (1 : Equiv.Perm (Fin n)) = List.finRange n := by
    simp [portList, hp, fixedPts]
  unfold transpositorPerm
  rw [hp, hl, List.length_nil, ← List.ofFn_eq_map]
  rfl

/-! ### The box ρ of the picture -/

/-- The permutation ρ⁻¹ of `involutive_decomp`: `j ↦ (portList σ)[j]`, here for (0 3)(1 2). -/
def ρinv₁ : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 1 3

theorem ρinv₁_apply : ∀ j : Fin 4, ρinv₁ j = (portList σ₁)[(j : ℕ)]'(by
    rw [portList_σ₁]; exact j.2) := by decide

/-- The decomposition of page 84 for σ = (0 3)(1 2): `σ = ρ⁻¹ ∘ ι_{2,0} ∘ ρ`, with ρ⁻¹ sending
position `j` of `T_{2,0}` to port `(portList σ)[j]` of `T_σ`. -/
theorem decomp_0312 : σ₁ = ρinv₁ * swapPerm 4 2 (by omega) * ρinv₁⁻¹ := by decide

/-- With ρ and ρ⁻¹ exchanged the decomposition fails for (0 3)(1 2): `involutive_decomp` is the
paper's statement with ρ the inverse of `portList`, and not an equation that holds for both
choices. -/
theorem not_decomp_0312 : σ₁ ≠ ρinv₁⁻¹ * swapPerm 4 2 (by omega) * ρinv₁ := by decide

/-- The permutation ρ⁻¹ for (1 2): `0 ↦ 1`, `1 ↦ 2`, `2 ↦ 0`, `3 ↦ 3`. -/
def ρinv₂ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem ρinv₂_apply : ∀ j : Fin 4, ρinv₂ j = (portList σ₂)[(j : ℕ)]'(by
    rw [portList_σ₂]; exact j.2) := by decide

/-- The decomposition of page 84 for σ = (1 2) on four ports: `σ = ρ⁻¹ ∘ ι_{1,2} ∘ ρ`. -/
theorem decomp_12 : σ₂ = ρinv₂ * swapPerm 4 1 (by omega) * ρinv₂⁻¹ := by decide

/-- With ρ and ρ⁻¹ exchanged the decomposition fails for (1 2) on four ports. -/
theorem not_decomp_12 : σ₂ ≠ ρinv₂⁻¹ * swapPerm 4 1 (by omega) * ρinv₂ := by decide

/-! ### A permutation that is not involutive -/

/-- The 3-cycle `0 ↦ 1 ↦ 2 ↦ 0` is not involutive, so `transpositorPerm` cannot be applied to it. -/
theorem not_involutive_finRotate : ¬ Function.Involutive (finRotate 3) := by unfold Function.Involutive; decide

/-- For the 3-cycle, `portList` lists port `1` twice and has length 4: without the hypothesis of
involutivity, the body of `transpositorPerm` would build `T_{2,0}` of arity 4 with the tree of
port `1` used twice, a net that is not linear. -/
theorem portList_finRotate : portList (finRotate 3) = [0, 1, 1, 2] := by decide

end INet.Comb.TranspositorPermCheck
