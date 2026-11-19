import InteractionCombinators.Lafont.CodeTr

/-!
# Review of `wireNum`, `treeLeaf`, `treeName`, `treePNet` (page 80)

Review of the principal net of a tree (`CodeTr.lean`) after #282, which numbers the internal wires
by `wireNum`, in increasing order. Page 80 (PDF page 12): a principal net is a reduced net with one
free port on a principal port (the root) and the others on auxiliary ports; it decomposes as a tree
and a wiring which does not connect the upper ports. Here a tree `t` over `ℕ` with `n` ports is read
as such a net: its names `< n` are the free ports, each once, and its names `≥ n` are internal
wires, each twice (the wiring joins two leaves of the tree).

**The ports and the wires.**

* `count_inl`, `count_inr` — in the tree of `treePNet n t`, the port `i` occurs as often as the
  name `i` in `t`, and the wire `w` as often as the name `(wireNum n t).symm w`.
* `t₁` — names `{0, 1, 7, 9}` with `n = 2`: `wireSet_t₁` (the internal names are `7` and `9` only,
  the skipped names `2, …, 6, 8` are not wires), `internal_t₁` (two internal wires),
  `treeLeaf_t₁_ports` (port `i` at name `i`), `treePNet_t₁` (the whole tree:
  `γ(δ(w₁, p₀), γ(w₀, δ(p₁, γ(w₁, w₀))))`).
* `t₂` — three internal names `8, 5, 3` met in this order from the left: `wireNum_t₂` gives them the
  wires `2, 1, 0`, the order of the names and not of the leaves.

**The hypotheses.**

* `port_count_iff`, `internal_count_iff` — the fields `port_count`, `internal_count` of the `PNet`
  built by `treePNet` are equivalent to `hp`, `hw`: both hypotheses are needed, and no more is.
  `hp_fails_missing`, `hp_fails_twice`, `hw_fails_once` are trees where they fail, and
  `not_port_count_missing`, `not_port_count_twice`, `not_internal_count_once` show the fields of
  the would-be principal net fail there too.
* `bind_treeLeaf_inst` — the equation of `treePNet_inst` holds for every tree: there `hp`, `hw` are
  only needed so that `treePNet` exists.
* `treePNet_var_not_strict` — the hypothesis `ht` of `treePNet_strict` is needed: the wire `var 0`
  with one port satisfies `hp`, `hw`, and its principal net is not strict.
-/

namespace INet.Comb.WireNumReview

open Term

/-! ## The ports and the wires of `treePNet` -/

/-- **The ports of `treePNet`** (page 80): in the tree `t.bind (treeLeaf n t)`, the port `i` occurs
as often as the name `i` in `t`. -/
theorem count_inl (n : ℕ) (t : Term sig ℕ) (i : Fin n) :
    (t.bind (treeLeaf n t)).vars.count (.inl i) = t.vars.count (i : ℕ) := by
  rw [vars_bind_treeLeaf]
  by_cases hi : (i : ℕ) ∈ t.vars
  · have e : (Sum.inl i : Fin n ⊕ Fin (wireSet n t).card) = treeName n t ⟨i, hi⟩ := by
      simp [treeName, i.isLt]
    rw [e, Multiset.count_map_eq_count' _ _ (treeName_injective n t), Multiset.count_attach]
  · rw [Multiset.count_eq_zero.2 hi, Multiset.count_eq_zero]
    intro hm
    obtain ⟨y, _, hy⟩ := Multiset.mem_map.1 hm
    unfold treeName at hy
    split_ifs at hy with h
    · simp only [Sum.inl.injEq, Fin.ext_iff] at hy
      exact hi (hy ▸ y.2)

/-- **The internal wires of `treePNet`** (page 80): in the tree `t.bind (treeLeaf n t)`, the wire
`w` occurs as often as the internal name `(wireNum n t).symm w` in `t`. -/
theorem count_inr (n : ℕ) (t : Term sig ℕ) (w : Fin (wireSet n t).card) :
    (t.bind (treeLeaf n t)).vars.count (.inr w) = t.vars.count ((wireNum n t).symm w).1 := by
  have hx := Finset.mem_filter.1 ((wireNum n t).symm w).2
  have hxv : ((wireNum n t).symm w).1 ∈ t.vars := Multiset.mem_toFinset.1 hx.1
  have e : (Sum.inr w : Fin n ⊕ Fin (wireSet n t).card) =
      treeName n t ⟨((wireNum n t).symm w).1, hxv⟩ := by
    have hn : ¬ ((wireNum n t).symm w).1 < n := not_lt.2 hx.2
    simp only [treeName, hn, dite_false]
    exact congrArg Sum.inr ((wireNum n t).apply_symm_apply w).symm
  rw [vars_bind_treeLeaf, e, Multiset.count_map_eq_count' _ _ (treeName_injective n t),
    Multiset.count_attach]

/-- **The hypothesis `hp` is the field `port_count`** (page 80): every port of the tree of
`treePNet n t` occurs once exactly when every name `i < n` occurs once in `t`. -/
theorem port_count_iff (n : ℕ) (t : Term sig ℕ) :
    (∀ i : Fin n, (t.bind (treeLeaf n t)).vars.count (.inl i) = 1) ↔
      ∀ i < n, t.vars.count i = 1 := by
  constructor
  · intro h i hi
    simpa [count_inl] using h ⟨i, hi⟩
  · intro h i
    rw [count_inl]
    exact h i i.isLt

/-- **The hypothesis `hw` is the field `internal_count`** (page 80): every internal wire of the
tree of `treePNet n t` has two ends exactly when every name `≥ n` of `t` occurs twice. -/
theorem internal_count_iff (n : ℕ) (t : Term sig ℕ) :
    (∀ w : Fin (wireSet n t).card, (t.bind (treeLeaf n t)).vars.count (.inr w) = 2) ↔
      ∀ x ∈ t.vars, n ≤ x → t.vars.count x = 2 := by
  constructor
  · intro h x hx hn
    have hm : x ∈ wireSet n t := Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hx, hn⟩
    have := h (wireNum n t ⟨x, hm⟩)
    rwa [count_inr, Equiv.symm_apply_apply] at this
  · intro h w
    have hx := Finset.mem_filter.1 ((wireNum n t).symm w).2
    rw [count_inr]
    exact h _ (Multiset.mem_toFinset.1 hx.1) hx.2

/-- **The equation of `treePNet_inst` needs no hypothesis** (page 80): for every tree `t`, the
tree `t.bind (treeLeaf n t)` with the port `i` named `i` and the wires named back by `wireNum` is
`t`. The hypotheses of `treePNet_inst` serve only to form `treePNet`. -/
theorem bind_treeLeaf_inst (n : ℕ) (t : Term sig ℕ) :
    (t.bind (treeLeaf n t)).bind (Sum.elim (fun i : Fin n => var (i : ℕ))
      fun w : Fin (wireSet n t).card => var ((wireNum n t).symm w).1) = t := by
  rw [Term.bind_bind]
  conv_rhs => rw [← Term.bind_var_self t]
  refine Term.bind_congr fun x hx => ?_
  unfold treeLeaf
  by_cases h1 : x < n
  · simp [h1]
  · have h2 : x ∈ wireSet n t :=
      Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hx, not_lt.1 h1⟩
    simp [h1, h2]

/-! ## Names `{0, 1, 7, 9}` with two ports -/

/-- The tree `γ(δ(9, 0), γ(7, δ(1, γ(9, 7))))`: the ports `0`, `1` and the internal names `7`,
`9`; the names `2, …, 6` and `8` are skipped. -/
def t₁ : Term sig ℕ :=
  mkCon (mkDup (var 9) (var 0)) (mkCon (var 7) (mkDup (var 1) (mkCon (var 9) (var 7))))

/-- The ports `0`, `1` of `t₁` occur once. -/
theorem t₁_hp : ∀ i < 2, t₁.vars.count i = 1 := by decide

/-- The internal names of `t₁` occur twice. -/
theorem t₁_hw : ∀ x ∈ t₁.vars, 2 ≤ x → t₁.vars.count x = 2 := by decide

/-- **The internal names of `t₁` are `7` and `9`** (page 80): no skipped name is a wire. -/
theorem wireSet_t₁ : wireSet 2 t₁ = {7, 9} := by decide

/-- **`treePNet 2 t₁` has two internal wires** (page 80), not one for each name from `2` to `9`. -/
theorem internal_t₁ : (treePNet 2 t₁ t₁_hp t₁_hw).internal = 2 := by
  change (wireSet 2 t₁).card = 2
  rw [wireSet_t₁]
  rfl

/-- `7` is an internal name. -/
theorem mem7 : (7 : ℕ) ∈ wireSet 2 t₁ := by decide

/-- `9` is an internal name. -/
theorem mem9 : (9 : ℕ) ∈ wireSet 2 t₁ := by decide

/-- **The port `i` of `treePNet 2 t₁` is at the name `i`** (page 80). -/
theorem treeLeaf_t₁_ports :
    treeLeaf 2 t₁ 0 = var (.inl 0) ∧ treeLeaf 2 t₁ 1 = var (.inl 1) := by
  constructor <;> simp [treeLeaf]

/-- The names `7` and `9` of `t₁` are the wires `0` and `1`. -/
theorem wireNum_t₁ : (wireNum 2 t₁ ⟨7, mem7⟩ : ℕ) = 0 ∧ (wireNum 2 t₁ ⟨9, mem9⟩ : ℕ) = 1 := by
  have h : wireNum 2 t₁ ⟨7, mem7⟩ < wireNum 2 t₁ ⟨9, mem9⟩ :=
    wireNum_strictMono 2 t₁ (show (⟨7, mem7⟩ : wireSet 2 t₁) < ⟨9, mem9⟩ by decide)
  have h1 : (wireNum 2 t₁ ⟨9, mem9⟩ : ℕ) < 2 :=
    lt_of_lt_of_eq (wireNum 2 t₁ ⟨9, mem9⟩).isLt (by rw [wireSet_t₁]; rfl)
  rw [Fin.lt_def] at h
  omega

/-- **The principal net of `t₁`** (page 80): `γ(δ(w₁, p₀), γ(w₀, δ(p₁, γ(w₁, w₀))))`, the ports at
their names and the names `7`, `9` as the wires `0`, `1`. -/
theorem treePNet_t₁ (w₀ w₁ : Fin (wireSet 2 t₁).card) (h₀ : (w₀ : ℕ) = 0) (h₁ : (w₁ : ℕ) = 1) :
    (treePNet 2 t₁ t₁_hp t₁_hw).tree =
      mkCon (mkDup (var (.inr w₁)) (var (.inl 0)))
        (mkCon (var (.inr w₀)) (mkDup (var (.inl 1)) (mkCon (var (.inr w₁)) (var (.inr w₀))))) := by
  have e₀ : wireNum 2 t₁ ⟨7, mem7⟩ = w₀ := Fin.ext (wireNum_t₁.1.trans h₀.symm)
  have e₁ : wireNum 2 t₁ ⟨9, mem9⟩ = w₁ := Fin.ext (wireNum_t₁.2.trans h₁.symm)
  have l7 : treeLeaf 2 t₁ 7 = var (.inr (wireNum 2 t₁ ⟨7, mem7⟩)) := by simp [treeLeaf, mem7]
  have l9 : treeLeaf 2 t₁ 9 = var (.inr (wireNum 2 t₁ ⟨9, mem9⟩)) := by simp [treeLeaf, mem9]
  change (mkCon (mkDup (var 9) (var 0)) (mkCon (var 7) (mkDup (var 1) (mkCon (var 9) (var 7)))) :
    Term sig ℕ).bind (treeLeaf 2 t₁) = _
  simp only [bind_mkCon, bind_mkDup, bind_var]
  rw [treeLeaf_t₁_ports.1, treeLeaf_t₁_ports.2, l7, l9, e₀, e₁]
  rfl

/-! ## Three internal names out of order -/

/-- The tree `γ(8, γ(5, γ(3, δ(0, γ(3, δ(5, 8))))))`: one port `0`, and the internal names met
from the left in the order `8, 5, 3`. -/
def t₂ : Term sig ℕ :=
  mkCon (var 8) (mkCon (var 5) (mkCon (var 3) (mkDup (var 0) (mkCon (var 3) (mkDup (var 5)
    (var 8))))))

/-- `3` is an internal name. -/
theorem mem3 : (3 : ℕ) ∈ wireSet 1 t₂ := by decide

/-- `5` is an internal name. -/
theorem mem5 : (5 : ℕ) ∈ wireSet 1 t₂ := by decide

/-- `8` is an internal name. -/
theorem mem8 : (8 : ℕ) ∈ wireSet 1 t₂ := by decide

/-- `t₂` has three internal names. -/
theorem card_wireSet_t₂ : (wireSet 1 t₂).card = 3 := by decide

#eval ((wireNum 1 t₂ ⟨8, mem8⟩ : ℕ), (wireNum 1 t₂ ⟨5, mem5⟩ : ℕ), (wireNum 1 t₂ ⟨3, mem3⟩ : ℕ))

/-- **The numbering is increasing** (page 80): in `t₂`, the names `3`, `5`, `8` are the wires
`0`, `1`, `2`, although they are met in the order `8, 5, 3`. -/
theorem wireNum_t₂ : (wireNum 1 t₂ ⟨3, mem3⟩ : ℕ) = 0 ∧ (wireNum 1 t₂ ⟨5, mem5⟩ : ℕ) = 1 ∧
    (wireNum 1 t₂ ⟨8, mem8⟩ : ℕ) = 2 := by
  have h35 : wireNum 1 t₂ ⟨3, mem3⟩ < wireNum 1 t₂ ⟨5, mem5⟩ :=
    wireNum_strictMono 1 t₂ (show (⟨3, mem3⟩ : wireSet 1 t₂) < ⟨5, mem5⟩ by decide)
  have h58 : wireNum 1 t₂ ⟨5, mem5⟩ < wireNum 1 t₂ ⟨8, mem8⟩ :=
    wireNum_strictMono 1 t₂ (show (⟨5, mem5⟩ : wireSet 1 t₂) < ⟨8, mem8⟩ by decide)
  have h8 : (wireNum 1 t₂ ⟨8, mem8⟩ : ℕ) < 3 :=
    lt_of_lt_of_eq (wireNum 1 t₂ ⟨8, mem8⟩).isLt card_wireSet_t₂
  rw [Fin.lt_def] at h35 h58
  omega

/-! ## Refutation attempts: the hypotheses are needed -/

/-- **A missing port** (page 80): in `γ(0, γ(2, 2))` with two ports, the name `1` does not occur. -/
theorem hp_fails_missing :
    ¬ ∀ i < 2, (mkCon (var 0) (mkCon (var 2) (var 2)) : Term sig ℕ).vars.count i = 1 := by
  decide

/-- So the port `1` of the would-be principal net does not occur (page 80). -/
theorem not_port_count_missing :
    ¬ ∀ i : Fin 2, ((mkCon (var 0) (mkCon (var 2) (var 2)) : Term sig ℕ).bind
      (treeLeaf 2 (mkCon (var 0) (mkCon (var 2) (var 2))))).vars.count (.inl i) = 1 :=
  fun h => hp_fails_missing ((port_count_iff _ _).1 h)

/-- **A port twice** (page 80): in `γ(0, γ(1, 1))` with two ports, the name `1` occurs twice. -/
theorem hp_fails_twice :
    ¬ ∀ i < 2, (mkCon (var 0) (mkCon (var 1) (var 1)) : Term sig ℕ).vars.count i = 1 := by
  decide

/-- So the port `1` of the would-be principal net occurs twice (page 80). -/
theorem not_port_count_twice :
    ¬ ∀ i : Fin 2, ((mkCon (var 0) (mkCon (var 1) (var 1)) : Term sig ℕ).bind
      (treeLeaf 2 (mkCon (var 0) (mkCon (var 1) (var 1))))).vars.count (.inl i) = 1 :=
  fun h => hp_fails_twice ((port_count_iff _ _).1 h)

/-- **An internal name once** (page 80): in `γ(0, 5)` with one port, the name `5` occurs once. -/
theorem hw_fails_once :
    ¬ ∀ x ∈ (mkCon (var 0) (var 5) : Term sig ℕ).vars, 1 ≤ x →
      (mkCon (var 0) (var 5) : Term sig ℕ).vars.count x = 2 := by
  decide

/-- So the wire of `5` in the would-be principal net has one end (page 80). -/
theorem not_internal_count_once :
    ¬ ∀ w : Fin (wireSet 1 (mkCon (var 0) (var 5) : Term sig ℕ)).card,
      ((mkCon (var 0) (var 5) : Term sig ℕ).bind
        (treeLeaf 1 (mkCon (var 0) (var 5)))).vars.count (.inr w) = 2 :=
  fun h => hw_fails_once ((internal_count_iff _ _).1 h)

/-- **The hypothesis `ht` of `treePNet_strict` is needed** (definition page 80): the wire `var 0`
with one port satisfies the hypotheses of `treePNet`, and its principal net is a wire, not
strict. -/
theorem treePNet_var_not_strict :
    ¬ (treePNet 1 (var 0 : Term sig ℕ) (by decide) (by decide)).Strict :=
  fun h => h (.inl 0) (by simp [treePNet, treeLeaf])

end INet.Comb.WireNumReview
