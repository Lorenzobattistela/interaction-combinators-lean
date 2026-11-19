import InteractionCombinators.Lafont.CodeGamma
import InteractionCombinators.Lafont.RecursionFreeStrict
import InteractionCombinators.RenameMany

/-!
# The principal net `[α]` of Fig. 10 and its strictness (pages 89–90)

Lafont 1997, Section 2.7, journal pages 88–89 (PDF 20–21), Fig. 10, top left: "a principal net
`[α_i]` can be defined for each symbol `α_i` as in Fig. 10". It is the cell of Fig. 6 (page 86),
the transpositor `T_{1,1}` carrying the menu `Γ_i` and the selector `S^i_m` on the multiplexor
`M_{n_i+2}`, whose first leaf is the package `!Γ`, the code of `Γ = Γ_1 & ⋯ & Γ_m` (the "genetic
code"), followed by the `n_i` ports and the loop `ℓ`.

**The names.** The ports of `α` are `0, …, n - 1`, the loop is `n`, the menu `Γ_α` takes the block
of names above `n + 1` (`codeCellMenu side α (n + 1)`), the menu `Γ` the next block
(`codeMenus side (codeMenuBase side α)`), and the code `!Γ` numbers its cut names from the end of
that block (`codeKey side α`). The cut names of `decomp` are distinct and above that bound, but not
consecutive. So the principal net is built by a general constructor `treePNet`: a tree whose names
`< n` occur once and whose other names occur twice is a principal net with `n` ports, its other names
numbered in increasing order as internal wires.

* `treePNet` — a tree with ports `0, …, n - 1` and every other name twice, as a `PNet`;
  `treePNet_inst` (the instance with the ports and wires named back gives the tree),
  `treePNet_strict`, and `treePNet_hyps` (the hypotheses from `Ico 0 n + 2 • X`).
* `codeTree`, `vars_codeTree` — the tree of `[α]` of Fig. 10 and its names.
* `codeNet`, `codeTranslation` — `[α]` as a `PNet sig (S.arity α)` and the translation.
* `codeTranslation_strict` — the translation is strict (definition page 80): the root of `[α]` is
  the root of `T_{1,1}`, a `dup` cell.
-/

namespace INet.Comb

open Term Translation

/-! ## A tree as a principal net -/

/-- The internal names of a tree with `n` ports: its names `≥ n`. -/
noncomputable def wireSet (n : ℕ) (t : Term sig ℕ) : Finset ℕ :=
  t.vars.toFinset.filter (n ≤ ·)

/-- The leaf of a name `x` of `t`: the port `x` if `x < n`, otherwise the internal wire numbered by
the rank of `x` among the internal names. (The eraser is never used for a name of `t`.) -/
noncomputable def treeLeaf (n : ℕ) (t : Term sig ℕ) (x : ℕ) :
    Term sig (Fin n ⊕ Fin (wireSet n t).card) :=
  if h : x < n then var (.inl ⟨x, h⟩)
  else if h' : x ∈ wireSet n t then var (.inr ((wireSet n t).equivFin ⟨x, h'⟩))
  else mkEra

/-- The leaf of a name that occurs in `t`. -/
noncomputable def treeName (n : ℕ) (t : Term sig ℕ) (x : {x // x ∈ t.vars}) :
    Fin n ⊕ Fin (wireSet n t).card :=
  if h : x.1 < n then .inl ⟨x.1, h⟩
  else .inr ((wireSet n t).equivFin
    ⟨x.1, Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 x.2, not_lt.1 h⟩⟩)

theorem treeName_injective (n : ℕ) (t : Term sig ℕ) : Function.Injective (treeName n t) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  unfold treeName at h
  by_cases h1 : x < n <;> by_cases h2 : y < n
  · simp only [h1, h2, dite_true, Sum.inl.injEq, Fin.mk.injEq] at h
    exact Subtype.ext h
  · simp [h1, h2] at h
  · simp [h1, h2] at h
  · simp only [h1, h2, dite_false, Sum.inr.injEq] at h
    have := (wireSet n t).equivFin.injective h
    exact Subtype.ext (by simpa using congrArg Subtype.val this)

theorem vars_treeLeaf (n : ℕ) (t : Term sig ℕ) (x : ℕ) (hx : x ∈ t.vars) :
    (treeLeaf n t x).vars = {treeName n t ⟨x, hx⟩} := by
  unfold treeLeaf treeName
  by_cases h1 : x < n
  · simp [h1]
  · have h2 : x ∈ wireSet n t :=
      Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hx, not_lt.1 h1⟩
    simp [h1, h2]

/-- The names of the tree of `treePNet`: each name `x` of `t` becomes its leaf, with multiplicity. -/
theorem vars_bind_treeLeaf (n : ℕ) (t : Term sig ℕ) :
    (t.bind (treeLeaf n t)).vars = t.vars.attach.map (treeName n t) := by
  rw [vars_bind]
  conv_lhs => rw [← Multiset.attach_map_val t.vars]
  rw [Multiset.bind_map, ← Multiset.bind_singleton]
  exact Multiset.bind_congr fun x _ => vars_treeLeaf n t x.1 x.2

/-- **A tree as a principal net** (principal nets, page 80). A tree `t` whose names `0, …, n - 1`
occur once and whose names `≥ n` occur twice is a principal net with `n` auxiliary ports: the names
`< n` are the ports, the names `≥ n` the internal wires, numbered in increasing order. -/
noncomputable def treePNet (n : ℕ) (t : Term sig ℕ) (hp : ∀ i < n, t.vars.count i = 1)
    (hw : ∀ x ∈ t.vars, n ≤ x → t.vars.count x = 2) : PNet sig n where
  internal := (wireSet n t).card
  tree := t.bind (treeLeaf n t)
  port_count i := by
    have hi : (i : ℕ) ∈ t.vars := Multiset.count_pos.1 (by rw [hp i i.isLt]; omega)
    have e : (Sum.inl i : Fin n ⊕ Fin (wireSet n t).card) = treeName n t ⟨i, hi⟩ := by
      simp [treeName, i.isLt]
    rw [vars_bind_treeLeaf, e, Multiset.count_map_eq_count' _ _ (treeName_injective n t),
      Multiset.count_attach]
    exact hp i i.isLt
  internal_count w := by
    have hx := Finset.mem_filter.1 ((wireSet n t).equivFin.symm w).2
    have hxv : ((wireSet n t).equivFin.symm w).1 ∈ t.vars := Multiset.mem_toFinset.1 hx.1
    have e : (Sum.inr w : Fin n ⊕ Fin (wireSet n t).card) =
        treeName n t ⟨((wireSet n t).equivFin.symm w).1, hxv⟩ := by
      have hn : ¬ ((wireSet n t).equivFin.symm w).1 < n := not_lt.2 hx.2
      simp only [treeName, hn, dite_false]
      exact congrArg Sum.inr ((wireSet n t).equivFin.apply_symm_apply w).symm
    rw [vars_bind_treeLeaf, e, Multiset.count_map_eq_count' _ _ (treeName_injective n t),
      Multiset.count_attach]
    exact hw _ hxv hx.2

/-- **The principal net `treePNet` is the tree `t`** (page 80): its instance with the port `i`
named `i` and each internal wire named back by the numbering of `wireSet` is `t`. -/
theorem treePNet_inst (n : ℕ) (t : Term sig ℕ) (hp : ∀ i < n, t.vars.count i = 1)
    (hw : ∀ x ∈ t.vars, n ≤ x → t.vars.count x = 2) :
    (treePNet n t hp hw).inst (fun i => var (i : ℕ)) (fun w => ((wireSet n t).equivFin.symm w).1) =
      t := by
  show (t.bind (treeLeaf n t)).bind (Sum.elim (fun i : Fin n => var (i : ℕ))
    fun w : Fin (wireSet n t).card => var ((wireSet n t).equivFin.symm w).1) = t
  rw [Term.bind_bind]
  conv_rhs => rw [← Term.bind_var_self t]
  refine Term.bind_congr fun x hx => ?_
  unfold treeLeaf
  by_cases h1 : x < n
  · simp [h1]
  · have h2 : x ∈ wireSet n t :=
      Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hx, not_lt.1 h1⟩
    simp [h1, h2]

/-- **A tree that is not a wire gives a strict principal net** (definition page 80). -/
theorem treePNet_strict (n : ℕ) (t : Term sig ℕ) (hp : ∀ i < n, t.vars.count i = 1)
    (hw : ∀ x ∈ t.vars, n ≤ x → t.vars.count x = 2) (ht : ∀ x, t ≠ var x) :
    (treePNet n t hp hw).Strict := by
  intro x hx
  change t.bind (treeLeaf n t) = var x at hx
  cases t with
  | var y => exact ht y rfl
  | app α ts =>
    rw [bind_app] at hx
    cases hx

/-- The hypotheses of `treePNet` (page 80) for a tree whose names are the ports `0, …, n - 1` once
and both ends of each name of a multiset `X` without repetition, above `n`. -/
theorem treePNet_hyps {n : ℕ} {t : Term sig ℕ} {X : Multiset ℕ}
    (h : t.vars = Multiset.Ico 0 n + 2 • X) (hX : X.Nodup) (hXn : ∀ x ∈ X, n ≤ x) :
    (∀ i < n, t.vars.count i = 1) ∧ (∀ x ∈ t.vars, n ≤ x → t.vars.count x = 2) := by
  refine ⟨fun i hi => ?_, fun x hx hn => ?_⟩
  · have hiX : i ∉ X := fun hm => by have := hXn i hm; omega
    rw [h, Multiset.count_add, Multiset.count_nsmul, Multiset.count_eq_zero.2 hiX, count_Ico]
    simp [hi]
  · have hxX : x ∈ X := by
      rw [h] at hx
      rcases Multiset.mem_add.1 hx with hx | hx
      · rw [Multiset.mem_Ico] at hx; omega
      · exact Multiset.mem_of_mem_nsmul hx
    rw [h, Multiset.count_add, Multiset.count_nsmul, Multiset.count_eq_one_of_mem hX hxX,
      count_Ico]
    split_ifs <;> omega

/-! ## The tree of `[α]` of Fig. 10 -/

/-- The names of the ports `0, …, n - 1`. -/
theorem sum_vars_ofFn_var (n : ℕ) :
    ((List.ofFn fun j : Fin n => (var (j : ℕ) : Term sig ℕ)).map Term.vars).sum =
      Multiset.Ico 0 n := by
  rw [List.map_ofFn, List.sum_ofFn, ← map_val_univ]
  simp only [Function.comp_def, vars_var]
  rw [Finset.sum_eq_multiset_sum]
  have h := Multiset.sum_map_singleton (Finset.univ.val.map fun w : Fin n => (w : ℕ))
  rwa [Multiset.map_map] at h

variable {S : Signature} [Finite S.Sym]
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- The first name of the menu `Γ` in `[α]`: after the ports `0, …, n - 1`, the loop `n` and the
block of the menu `Γ_α`. -/
noncomputable def codeMenuBase (α : S.Sym) : ℕ :=
  S.arity α + 1 + ∑ j, codeCellSizes side α j

/-- The first cut name of the code `!Γ` in `[α]`: after the block of the menu `Γ`. -/
noncomputable def codeKey (α : S.Sym) : ℕ :=
  codeMenuBase side α + ∑ i, codeMenuSizes side i

/-- **The tree of `[α]` of Fig. 10** (top left, page 89): the transpositor `T_{1,1}` carrying the
menu `Γ_α` (names from `n + 1`) and the selector `S^α_m` on the multiplexor `M_{n+2}`, whose leaves
are, from left to right, the code `!Γ` of `Γ = Γ_0 & ⋯ & Γ_{m-1}` (`Γ` named from `codeMenuBase`,
the cut names of the code from `codeKey`), the ports `0, …, n - 1`, and the loop `ℓ = n`. Here
`n = S.arity α`, `m` is the number of symbols, and `side` is any choice of expanded sides (page 90:
no order on the symbols is needed). -/
noncomputable def codeTree (α : S.Sym) : Term sig ℕ :=
  cellSkel (menu (codeCellMenu side α (S.arity α + 1))) (Nat.card S.Sym) (symEnum S α)
    (code (codeKey side α) (menu (codeMenus side (codeMenuBase side α))) ::
      List.ofFn fun j : Fin (S.arity α) => var (j : ℕ)) (S.arity α)

/-- **The names of `[α]` of Fig. 10** (page 89): the ports `0, …, n - 1` once, and twice each the
names of `[n, codeKey)` (the loop, the names of `Γ_α` and those of `Γ`) and the cut names of the
code `!Γ`. -/
theorem vars_codeTree (α : S.Sym) :
    (codeTree side α).vars = Multiset.Ico 0 (S.arity α) +
      2 • (Multiset.Ico (S.arity α) (codeKey side α) +
        (decomp (codeKey side α) (menu (codeMenus side (codeMenuBase side α)))).ports) := by
  have hB : S.arity α + 1 ≤ codeMenuBase side α := Nat.le_add_right _ _
  have hK : codeMenuBase side α ≤ codeKey side α := Nat.le_add_right _ _
  have h1 : Multiset.Ico (S.arity α) (S.arity α + 1) = {S.arity α} :=
    (Multiset.Nodup.ext Multiset.nodup_Ico (Multiset.nodup_singleton _)).2 fun x => by
      simp only [Multiset.mem_Ico, Multiset.mem_singleton]; omega
  have hI : Multiset.Ico (S.arity α) (codeKey side α) = {S.arity α} +
      Multiset.Ico (S.arity α + 1) (codeMenuBase side α) +
      Multiset.Ico (codeMenuBase side α) (codeKey side α) := by
    rw [← h1, Multiset.Ico_add_Ico_eq_Ico (by omega) hB, Multiset.Ico_add_Ico_eq_Ico (by omega) hK]
  have e1 : (menu (codeCellMenu side α (S.arity α + 1))).vars =
      2 • Multiset.Ico (S.arity α + 1) (codeMenuBase side α) :=
    vars_menu_codeCellMenu side α _
  have e2 : (menu (codeMenus side (codeMenuBase side α))).vars =
      2 • Multiset.Ico (codeMenuBase side α) (codeKey side α) :=
    vars_menu_codeMenus side _
  rw [codeTree, vars_cellSkel, e1, List.map_cons, List.sum_cons, sum_vars_ofFn_var, vars_code, e2,
    hI]
  simp only [smul_add, two_nsmul]
  abel

/-- The names of `[α]` other than the ports are distinct and above the ports (page 89). -/
theorem codeTree_wires (α : S.Sym) :
    (Multiset.Ico (S.arity α) (codeKey side α) +
        (decomp (codeKey side α) (menu (codeMenus side (codeMenuBase side α)))).ports).Nodup ∧
      ∀ x ∈ Multiset.Ico (S.arity α) (codeKey side α) +
        (decomp (codeKey side α) (menu (codeMenus side (codeMenuBase side α)))).ports,
        S.arity α ≤ x := by
  obtain ⟨hnd, hr, -⟩ := decomp_ports (menu (codeMenus side (codeMenuBase side α))) (codeKey side α)
  have hn : S.arity α ≤ codeKey side α := by unfold codeKey codeMenuBase; omega
  refine ⟨Multiset.nodup_add.2 ⟨Multiset.nodup_Ico, hnd, Multiset.disjoint_left.2 fun hx hy => ?_⟩,
    fun x hx => ?_⟩
  · have := (hr _ hy).1
    rw [Multiset.mem_Ico] at hx
    omega
  · rcases Multiset.mem_add.1 hx with hx | hx
    · exact (Multiset.mem_Ico.1 hx).1
    · exact hn.trans (hr x hx).1

/-- The tree of `[α]` has the ports `0, …, n - 1` once and every other name twice (page 89). -/
theorem codeTree_hyps (α : S.Sym) :
    (∀ i < S.arity α, (codeTree side α).vars.count i = 1) ∧
      (∀ x ∈ (codeTree side α).vars, S.arity α ≤ x → (codeTree side α).vars.count x = 2) :=
  treePNet_hyps (vars_codeTree side α) (codeTree_wires side α).1 (codeTree_wires side α).2

/-! ## The principal net `[α]` and the translation -/

/-- **The principal net `[α]` of Fig. 10** (top left, page 89; principal nets, page 80): the tree
`codeTree side α` with the ports `0, …, n - 1` and its other names as internal wires. -/
noncomputable def codeNet (α : S.Sym) : PNet sig (S.arity α) :=
  treePNet (S.arity α) (codeTree side α) (codeTree_hyps side α).1 (codeTree_hyps side α).2

/-- **The translation of Fig. 10** (pages 89–90): every symbol `α` is translated into the principal
net `[α]`, built from the choice `side` of expanded sides. -/
noncomputable def codeTranslation : Translation S sig :=
  ⟨codeNet side⟩

/-- The principal net `[α]` is the tree of Fig. 10 (page 89): its instance with the port `i` named
`i` and the internal wires named back is `codeTree side α`. -/
theorem codeNet_inst (α : S.Sym) :
    (codeNet side α).inst (fun i => var (i : ℕ))
      (fun w => ((wireSet (S.arity α) (codeTree side α)).equivFin.symm w).1) = codeTree side α :=
  treePNet_inst _ _ _ _

/-- The root of `[α]` is the `dup` cell of `T_{1,1}` (Fig. 10, page 89). -/
theorem codeTree_eq_mkDup (α : S.Sym) :
    ∃ a b, codeTree side α = mkDup a b :=
  exists_cellSkel_eq_mkDup _ _ _ _ _

/-- The tree of `[α]` is not a wire (page 89). -/
theorem codeTree_ne_var (α : S.Sym) (x : ℕ) : codeTree side α ≠ var x := by
  obtain ⟨a, b, h⟩ := codeTree_eq_mkDup side α
  rw [h]
  intro h'
  cases h'

/-- **`[α]` of Fig. 10 is strict** (definition page 80, Fig. 10 page 89): its principal port is the
root of `T_{1,1}`, a `dup` cell. -/
theorem codeNet_strict (α : S.Sym) : (codeNet side α).Strict :=
  treePNet_strict _ _ _ _ (codeTree_ne_var side α)

/-- **The translation of Fig. 10 is strict** (Lafont 1997, definition page 80, Fig. 10 pages
89–90): no `[α]` is a wire. -/
theorem codeTranslation_strict : (codeTranslation side).Strict :=
  codeNet_strict side

end INet.Comb
