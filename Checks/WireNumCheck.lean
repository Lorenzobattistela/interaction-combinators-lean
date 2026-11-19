import InteractionCombinators.Lafont.CodeTr

/-!
# `treePNet` numbers its internal wires in increasing order (page 80)

`wireNum n t` numbers the internal names of a tree (`wireSet n t`, the names `≥ n`) by their
rank, and it is computable, so `treeLeaf`, `treeName` and `treePNet` are compiled. On the tree
`γ(0, γ(δ(5, 3), δ(3, 5)))` with one port `0` and the internal names `3` and `5`, the name `3`
is wire `0` and the name `5` is wire `1`, although `5` is met first from the left: the numbering
follows the order of the names, not the order of the leaves.

* `#eval` computes the two wire numbers, `(0, 1)`.
* `wireNum_t` states them. The kernel does not reduce the sort behind `Finset.orderIsoOfFin`, so
  `decide` cannot; the proof uses `wireNum_strictMono` and the count of two internal wires.
* `treePNet_t` — the tree of `treePNet 1 t`: `γ(0, γ(δ(w₁, w₀), δ(w₀, w₁)))`.
-/

namespace INet.Comb.WireNumCheck

open Term

/-- The tree `γ(0, γ(δ(5, 3), δ(3, 5)))`: the port `0` and the internal names `5` and `3`. -/
def t : Term sig ℕ := mkCon (var 0) (mkCon (mkDup (var 5) (var 3)) (mkDup (var 3) (var 5)))

/-- The port `0` of `t` occurs once. -/
theorem t_hp : ∀ i < 1, t.vars.count i = 1 := by decide

/-- The internal names `3` and `5` of `t` occur twice. -/
theorem t_hw : ∀ x ∈ t.vars, 1 ≤ x → t.vars.count x = 2 := by decide

#eval (wireSet 1 t).card
#eval ((wireNum 1 t ⟨3, by decide⟩ : ℕ), (wireNum 1 t ⟨5, by decide⟩ : ℕ))

/-- `t` has two internal names. -/
theorem card_wireSet_t : (wireSet 1 t).card = 2 := by decide

/-- `3` is an internal name of `t`. -/
theorem mem3 : (3 : ℕ) ∈ wireSet 1 t := by decide

/-- `5` is an internal name of `t`. -/
theorem mem5 : (5 : ℕ) ∈ wireSet 1 t := by decide

/-- The names `3` and `5` are the internal wires `0` and `1`, in this order (page 80): by
`wireNum_strictMono`, since `3 < 5` and there are two internal wires. -/
theorem wireNum_t : (wireNum 1 t ⟨3, mem3⟩ : ℕ) = 0 ∧ (wireNum 1 t ⟨5, mem5⟩ : ℕ) = 1 := by
  have h : wireNum 1 t ⟨3, mem3⟩ < wireNum 1 t ⟨5, mem5⟩ :=
    wireNum_strictMono 1 t (show (⟨3, mem3⟩ : wireSet 1 t) < ⟨5, mem5⟩ by decide)
  have h1 : (wireNum 1 t ⟨5, mem5⟩ : ℕ) < 2 :=
    lt_of_lt_of_eq (wireNum 1 t ⟨5, mem5⟩).isLt card_wireSet_t
  rw [Fin.lt_def] at h
  omega

/-- The leaf of `3` is its wire. -/
theorem treeLeaf_t_3 : treeLeaf 1 t 3 = var (.inr (wireNum 1 t ⟨3, mem3⟩)) := by
  simp [treeLeaf, mem3]

/-- The leaf of `5` is its wire. -/
theorem treeLeaf_t_5 : treeLeaf 1 t 5 = var (.inr (wireNum 1 t ⟨5, mem5⟩)) := by
  simp [treeLeaf, mem5]

/-- **The principal net of `t`** (page 80): the port `0` stays the port `0`, and the leaves `5`
and `3` become the wires `1` and `0`: `γ(0, γ(δ(w₁, w₀), δ(w₀, w₁)))`. -/
theorem treePNet_t (w₀ w₁ : Fin (wireSet 1 t).card) (h₀ : (w₀ : ℕ) = 0) (h₁ : (w₁ : ℕ) = 1) :
    (treePNet 1 t t_hp t_hw).tree =
      mkCon (var (.inl 0)) (mkCon (mkDup (var (.inr w₁)) (var (.inr w₀)))
        (mkDup (var (.inr w₀)) (var (.inr w₁)))) := by
  have e₀ : wireNum 1 t ⟨3, mem3⟩ = w₀ := Fin.ext (wireNum_t.1.trans h₀.symm)
  have e₁ : wireNum 1 t ⟨5, mem5⟩ = w₁ := Fin.ext (wireNum_t.2.trans h₁.symm)
  have l0 : treeLeaf 1 t 0 = var (.inl 0) := by simp [treeLeaf]
  show (mkCon (var 0) (mkCon (mkDup (var 5) (var 3)) (mkDup (var 3) (var 5))) : Term sig ℕ).bind
    (treeLeaf 1 t) = _
  simp only [bind_mkCon, bind_mkDup, bind_var]
  rw [l0, treeLeaf_t_3, treeLeaf_t_5, e₀, e₁]
  rfl

end INet.Comb.WireNumCheck
