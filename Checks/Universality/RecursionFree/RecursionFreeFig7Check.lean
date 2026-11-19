import InteractionCombinators.Universality.RecursionFree.RecursionFreeFig7

/-!
# Checks of `translation_cells_meet` (page 86)

The hypotheses of `translation_cells_meet` hold for the recursion-free data
`recursionFreeDataNoConDup` of the combinators without `con`–`dup` (page 87), in both cases of the
proof:

* the rule `con`–`con` (`α = β`, the side of `β` against `α` through `D.self`), with the names
  `0, 1` and `2, 3` on the ports;
* the rule `era`–`con` (`α ≠ β`, the side of `con` against `era` through `rawSide_of_rule_swap`),
  with no port on `era` and the names `0, 1` on the ports of `con`.

In both, the internal wires of `[α]` are named from `4` and those of `[β]` right after them, and
the one-equation net is linear.
-/

namespace INet.Comb.RecursionFreeFig7Check

open Term

/-- The names `0, 1` on the ports of the first cell. -/
def zeroOne : Fin 2 → ℕ := ![0, 1]

/-- The names `2, 3` on the ports of the second cell. -/
def twoThree : Fin 2 → ℕ := ![2, 3]

/-- The names `4, 5, …` of the internal wires of `[α]`. -/
def fromFour {n : ℕ} (w : Fin n) : ℕ := 4 + (w : ℕ)

/-- The names of the internal wires of `[β]`, right after the `P` wires of `[α]`. -/
def afterFour (P : ℕ) {n : ℕ} (w : Fin n) : ℕ := 4 + P + (w : ℕ)

/-- The number of internal wires `w` of a block `K, K + 1, …, K + P - 1` named `z`. -/
theorem sum_ite_block (P K z : ℕ) :
    (∑ w : Fin P, if z = K + (w : ℕ) then 1 else 0) = if K ≤ z ∧ z < K + P then 1 else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨z - K, by omega⟩ : Fin P)]
    · simp only [ite_eq_left_iff]
      omega
    · intro w _ hw
      refine ite_eq_right_iff.2 fun hz => absurd (Fin.ext ?_) hw
      simp only
      omega
    · simp
  · exact Finset.sum_eq_zero fun w _ =>
      ite_eq_right_iff.2 fun hz => absurd ⟨by omega, by have := w.isLt; omega⟩ h

/-- The recursion-free data of `systemNoConDup` (page 87). -/
noncomputable abbrev Dn : systemNoConDup.RecursionFreeData := recursionFreeDataNoConDup

/-- Its translation (Fig. 6, page 86). -/
noncomputable abbrev Tr : Translation sig sig := Dn.translation

/-- `[con]` against `[con]`, ports `0, 1` and `2, 3`, internal wires from `4`. -/
noncomputable def netConCon : CNet :=
  {s((Tr.net Comb.con).inst (fun i => .var (zeroOne i)) fromFour,
    (Tr.net Comb.con).inst (fun j => .var (twoThree j)) (afterFour (Tr.net Comb.con).internal))}

/-- `[era]` against `[con]`, ports `0, 1` on `con`, internal wires from `4`. -/
noncomputable def netEraCon : CNet :=
  {s((Tr.net Comb.era).inst (fun i => .var (Fin.elim0 i)) fromFour,
    (Tr.net Comb.con).inst (fun j => .var (zeroOne j)) (afterFour (Tr.net Comb.era).internal))}

/-- `sum_ite_block` for a naming `F` of the block. -/
theorem sum_ite_block' (P K : ℕ) (F : Fin P → ℕ) (hF : ∀ w, F w = K + (w : ℕ)) (z : ℕ) :
    (∑ w : Fin P, if z = F w then 1 else 0) = if K ≤ z ∧ z < K + P then 1 else 0 := by
  rw [← sum_ite_block P K z]
  exact Finset.sum_congr rfl fun w _ => by rw [hF]

/-- Two instances plugged by their roots, with the names `xs`, `ys` (below `4`, each name at
most once) on their ports and their internal wires named from `4` and right after, form a linear
net. -/
theorem linear_blocks {n m : ℕ} (p : PNet sig n) (q : PNet sig m) (xs : Fin n → ℕ)
    (ys : Fin m → ℕ) (hx : ∀ i, xs i < 4) (hy : ∀ j, ys j < 4)
    (hxy : ∀ z, (∑ i, if z = xs i then 1 else 0) + (∑ j, if z = ys j then 1 else 0) ≤ 1) :
    Net.Linear (s(p.inst (fun i => .var (xs i)) fromFour,
      q.inst (fun j => .var (ys j)) (afterFour p.internal)) ::ₘ 0 : CNet) := by
  intro z
  simp only [Net.vars_cons, Net.vars_zero, add_zero, eqVars_mk, Multiset.count_add,
    PNet.count_vars_inst, vars_var, Multiset.count_singleton]
  rw [sum_ite_block' _ 4 fromFour (fun _ => rfl),
    sum_ite_block' _ (4 + p.internal) (afterFour p.internal) (fun _ => rfl)]
  have h := hxy z
  by_cases hz : z < 4
  · simp only [show ¬ (4 ≤ z ∧ z < 4 + p.internal) by omega,
      show ¬ (4 + p.internal ≤ z ∧ z < 4 + p.internal + q.internal) by omega, ite_false]
    omega
  · have e1 : (∑ i, if z = xs i then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => ite_eq_right_iff.2 fun h => absurd (h ▸ hx i) hz
    have e2 : (∑ j, if z = ys j then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => ite_eq_right_iff.2 fun h => absurd (h ▸ hy j) hz
    rw [e1, e2]
    split_ifs <;> omega

/-- **The hypotheses hold for the rule `con`–`con`** (`α = β`). -/
theorem linear_conCon : netConCon.Linear := by
  refine linear_blocks _ _ zeroOne twoThree ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [zeroOne]
  · intro j; fin_cases j <;> simp [twoThree]
  · intro z
    simp only [Fin.sum_univ_two, zeroOne, twoThree, Matrix.cons_val_zero, Matrix.cons_val_one]
    by_cases h0 : z = 0 <;> by_cases h1 : z = 1 <;> by_cases h2 : z = 2 <;>
      by_cases h3 : z = 3 <;> simp [h0, h1, h2, h3]

/-- **`translation_cells_meet` applies to the rule `con`–`con`** of `systemNoConDup` (page 86):
the case `α = β`, where the side of `β` against `α` is `φ = ψ` (`D.self`). -/
theorem translation_cells_meet_conCon :
    ∃ (M : CNet) (k₀ k₁ ℓ : ℕ), StepsE system netConCon M ∧
      Equiv M
        (s(mux (List.ofFn (fun p => (var (zeroOne p) : Term sig ℕ)) ++ [var ℓ]),
            gamma Tr (Dn.rawφ Comb.con Comb.con ruleConCon rfl).expand.φ
              (Dn.dec Comb.con Comb.con ruleConCon rfl).σ
              (Dn.involutive Comb.con Comb.con ruleConCon rfl) k₀) ::ₘ
          s(mux (List.ofFn (fun q => (var (twoThree q) : Term sig ℕ)) ++ [var ℓ]),
            gamma Tr (Dn.rawψ Comb.con Comb.con ruleConCon rfl).expand.φ
              (Dn.dec Comb.con Comb.con ruleConCon rfl).σ
              (Dn.involutive Comb.con Comb.con ruleConCon rfl) k₁) ::ₘ 0) ∧
      Net.Linear
        (s(mux (List.ofFn (fun p => (var (zeroOne p) : Term sig ℕ)) ++ [var ℓ]),
            gamma Tr (Dn.rawφ Comb.con Comb.con ruleConCon rfl).expand.φ
              (Dn.dec Comb.con Comb.con ruleConCon rfl).σ
              (Dn.involutive Comb.con Comb.con ruleConCon rfl) k₀) ::ₘ
          s(mux (List.ofFn (fun q => (var (twoThree q) : Term sig ℕ)) ++ [var ℓ]),
            gamma Tr (Dn.rawψ Comb.con Comb.con ruleConCon rfl).expand.φ
              (Dn.dec Comb.con Comb.con ruleConCon rfl).σ
              (Dn.involutive Comb.con Comb.con ruleConCon rfl) k₁) ::ₘ 0) :=
  translation_cells_meet systemNoConDup_wellFormed Dn (α := Comb.con) (β := Comb.con)
    (r := ruleConCon) rfl _ _ _ _ linear_conCon

/-- **The hypotheses hold for the rule `era`–`con`** (`α ≠ β`). -/
theorem linear_eraCon : netEraCon.Linear := by
  refine linear_blocks _ _ Fin.elim0 zeroOne (fun i => i.elim0) ?_ ?_
  · intro j; fin_cases j <;> simp [zeroOne]
  · intro z
    simp only [Fin.sum_univ_two, Finset.univ_eq_empty, Finset.sum_empty, zeroOne,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    by_cases h0 : z = 0 <;> by_cases h1 : z = 1 <;> simp [h0, h1]

/-- **`translation_cells_netTr_plug` applies to the rule `era`–`con`** of `systemNoConDup`
(page 86): the case `α ≠ β`, where the package extracted from the menu of `[era]` is built from
the `ψ` of the rule `era`–`con` (`rawSide_of_rule_swap`). -/
theorem translation_cells_netTr_plug_eraCon :
    ∃ (M N' : CNet)
      (h' : Fin (Rule.plug (Dn.rawφ Comb.era Comb.con ruleEraBin rfl).expand.φ
        (Dn.rawψ Comb.con Comb.era ruleEraBin rfl).expand.φ
        (Dn.dec Comb.era Comb.con ruleEraBin rfl).σ).internal → ℕ),
      StepsE system netEraCon M ∧ Equiv M N' ∧
      Tr.NetTr ((Rule.plug (Dn.rawφ Comb.era Comb.con ruleEraBin rfl).expand.φ
        (Dn.rawψ Comb.con Comb.era ruleEraBin rfl).expand.φ
        (Dn.dec Comb.era Comb.con ruleEraBin rfl).σ).inst
          (fun i => .var (Fin.elim0 i)) (fun j => .var (zeroOne j)) h') N' :=
  translation_cells_netTr_plug systemNoConDup_wellFormed Dn (r := ruleEraBin) (α := Comb.era)
    (β := Comb.con) rfl _ _ _ _ linear_eraCon

end INet.Comb.RecursionFreeFig7Check
