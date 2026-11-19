import InteractionCombinators.Lafont.CodeCell
import InteractionCombinators.Lafont.Gamma

/-!
# `⟨φ_{i,j}⟩` and the package `Γ_{i,j}` of Fig. 10 (page 89)

Lafont 1997, Section 2.7, Fig. 10 (journal page 89, PDF page 21) and the text of page 90.

`⟨φ_{i,j}⟩` is `φ_{i,j}` with every cell `α_k` replaced by `⟨α_k⟩` (`codeCell`). The package
`Γ_{i,j}` (Fig. 10, bottom right) is the dual multiplexor `M*_{n_i+2}` whose root is its free port;
its leaves, from left to right, are the root of the copier `C_{p_{i,j}}`, the `n_i` ports of
`⟨φ_{i,j}⟩` on the side of `α_i`, and the root of the transpositor `T_{σ_{i,j}}` applied to the
middle ports of `⟨φ_{i,j}⟩`. The `p_{i,j}` auxiliary ports of `C_{p_{i,j}}` are joined to the extra
ports of the `p_{i,j}` cells `⟨α_k⟩`. No order on the symbols is needed.

**The extra ports.** A package is one tree. The wire between the extra port of a cell `⟨α_k⟩` and
an auxiliary port of `C_{p_{i,j}}` is therefore not named: the tree on the extra port of `⟨α_k⟩`,
`C_2(D, u)` with the selector `S^k_m(y)` plugged into the free port of `D` (`codeExtra`), sits
directly on that auxiliary port of `C_{p_{i,j}}`. `codeCell_equiv` checks that this is the net
`codeCell` of `CodeCell.lean` once its internal wire `w` (from `D` to `S^k_m`) is contracted.

**The names.** Each cell of `φ_{i,j}` takes a block of five fresh names: the loop `ℓ = b`, the wire
`u = b + 1` (right port of `C_2` to the first leaf of `M_{n_k+2}`), the wire `y = b + 2` (free port of
`S^k_m` to the first port of `T_{1,1}`), and the loop `k₀ = b + 3`, `k₀ + 1 = b + 4` of `D`.

* `codeExtra` — the tree on the extra port of `⟨α_k⟩`; `codeCell_equiv` relates it to `codeCell`.
* `codeTerm`, `codeExtras`, `codeSize` — a tree of `φ` with its cells replaced by `⟨α_k⟩`, the list
  of trees on the extra ports (one per cell, `length_codeExtras`), and the number of new names.
  `vars_codeTerm_add`: together their names are those of the tree and both ends of each new name.
* `codeGamma` — `Γ_{i,j}`; `vars_codeGamma`, `codeGamma_isPackage`, `length_codeGammaExtras`.
* `codeCellMenu`, `codeMenus` — the menus `Γ_i = Γ_{1,i} & ⋯ & Γ_{m,i}` and the list
  `Γ_1, …, Γ_m` whose menu is `Γ`, built from a choice `side` of expanded sides for every pair of
  symbols; `codeMenus_isPackage`, `menu_codeMenus_isPackage`, `menu_codeMenus_below`.
* `codeCell_code_codeMenus` — the extraction of page 90 (`codeCell_code`) applies to this `Γ`.
-/

namespace INet.Comb

open Term Translation

variable {S : Signature} {a k : ℕ}

/-! ## The tree on the extra port of `⟨α_k⟩` -/

/-- **The tree on the extra port of `⟨α_i⟩`** (Fig. 10, bottom left, page 89): the copier `C_2`
whose left auxiliary port carries the decoder `D` (loop `k₀`, `k₀ + 1`) with the selector `S^i_m`
(free port `y`) on the free port of `D`, and whose right auxiliary port is the wire `u`. -/
def codeExtra (m i y u k₀ : ℕ) : Term sig ℕ :=
  copier [muxStar [mkDup (var k₀) (var (k₀ + 1)), var (k₀ + 1), var k₀, selector m i y], var u]

/-- `codeExtra` is the copier `C_2` of `⟨α_i⟩` (page 89) with the selector `S^i_m` plugged into the
free port `w` of the decoder, when `w` is not a name of the loop of the decoder. -/
theorem codeExtra_eq (m i y u k₀ w : ℕ) (hw : w ≠ k₀) (hw' : w ≠ k₀ + 1) :
    codeExtra m i y u k₀ = copier [(decoder w k₀).subst w (selector m i y), var u] := by
  have h1 : k₀ ≠ w := Ne.symm hw
  have h2 : k₀ + 1 ≠ w := Ne.symm hw'
  simp [codeExtra, decoder, muxStar, Term.subst, h1, h2]

/-- The names of the tree on the extra port of `⟨α_i⟩` (page 89): the loop of `D` twice, and the
wires `y` and `u` once. -/
theorem vars_codeExtra (m i y u k₀ : ℕ) :
    (codeExtra m i y u k₀).vars = {k₀} + {k₀ + 1} + {k₀ + 1} + {k₀} + {y} + {u} := by
  simp only [codeExtra, copier, autoMux, muxStar, vars_mkDup, vars_mkCon, vars_var,
    selector_eq_cellSel, vars_cellSel]
  abel

/-- **`codeCell` with its wire `w` contracted** (Fig. 10, page 89): the net `⟨α_i⟩` of three
equations, in any context `Δ`, is `Equiv` to the two equations `x = codeExtra` (the tree on the
extra port) and `P = [α_i]` with the wires `y` and `u` in place of the menu and of the code. -/
theorem codeCell_equiv (m i : ℕ) (P x : Term sig ℕ) (ts : List (Term sig ℕ))
    (ℓ u w y k₀ : ℕ) (Δ : CNet) (hlin : Net.Linear (codeCell m i P x ts ℓ u w y k₀ + Δ)) :
    Equiv (codeCell m i P x ts ℓ u w y k₀ + Δ)
      (s(x, codeExtra m i y u k₀) ::ₘ s(P, cellSkel (var y) m i (var u :: ts) ℓ) ::ₘ Δ) := by
  set Q := cellSkel (var y) m i (var u :: ts) ℓ
  set Sl := (selector m i y : Term sig ℕ)
  set C := (copier [decoder w k₀, var u] : Term sig ℕ)
  have e0 : codeCell m i P x ts ℓ u w y k₀ + Δ = s(var w, Sl) ::ₘ s(x, C) ::ₘ s(P, Q) ::ₘ Δ := by
    simp only [codeCell, Multiset.cons_add, zero_add]
    exact Multiset.cons_swap _ _ _
  rw [e0] at hlin ⊢
  have hc := hlin w
  simp only [Net.vars_cons, eqVars_mk, vars_var, C, autoMux, vars_mkDup, vars_decoder,
    Multiset.count_add, Multiset.count_singleton_self, Multiset.insert_eq_cons,
    Multiset.count_cons_self] at hc
  have hx : w ∉ x.vars := Multiset.count_eq_zero.1 (by omega)
  have hk : w ≠ k₀ := by
    intro h; subst h; simp at hc; omega
  have hk' : w ≠ k₀ + 1 := by
    intro h; subst h; simp at hc; omega
  have hu : u ≠ w := by
    intro h; subst h; simp at hc; omega
  have hC' : C = mkDup (decoder w k₀) (var u) := rfl
  have W := Wire.mk w Sl x C (s(P, Q) ::ₘ Δ) hlin
    (Multiset.mem_add.2 (Or.inr (by rw [hC']; simp [vars_decoder])))
  have hC : C.subst w Sl = codeExtra m i y u k₀ := by
    rw [codeExtra_eq m i y u k₀ w hk hk', hC', subst_mkDup,
      subst_of_notMem (r := var u) (by simp [Ne.symm hu])]
    rfl
  rw [subst_of_notMem hx, hC] at W
  exact W.equiv

/-! ## A tree of `φ` with its cells replaced by `⟨α_k⟩` -/

/-- The number of new names of `⟨t⟩`: five per cell (page 89). -/
def codeSize {ν : Type} : Term S ν → ℕ
  | .var _ => 0
  | .app _ ts => 5 + ∑ i, codeSize (ts i)

/-- `codeSize` is five times the number of cells. -/
theorem codeSize_eq {ν : Type} (t : Term S ν) : codeSize t = 5 * Multiset.card t.cells := by
  induction t with
  | var x => rfl
  | app α ts ih =>
    simp only [codeSize, cells_app, Multiset.card_cons, Multiset.card_sum, ih, ← Finset.mul_sum]
    ring

/-- Renaming the leaves does not change `codeSize`. -/
theorem codeSize_bind_var {ν μ : Type} (f : ν → μ) (t : Term S ν) :
    codeSize (t.bind fun x => var (f x)) = codeSize t := by
  rw [codeSize_eq, codeSize_eq, cells_bind]
  simp

variable (m : ℕ) (idx : S.Sym → ℕ)

/-- **`⟨t⟩`** (Fig. 10, page 89): the tree `t` with every cell `α` replaced by `⟨α⟩`, seen from its
principal port: `cellSkel (var y) m (idx α) (var u :: ts) ℓ`, the cell `[α]` with the wire `y` in
place of the menu and the wire `u` in place of the code. The cell at the root takes the names
`b, …, b + 4` (`ℓ = b`, `u = b + 1`, `y = b + 2`, the loop of `D` is `b + 3`, `b + 4`); each subtree
takes the next block of its size. `m` is the number of symbols and `idx` their numbering. -/
def codeTerm : ℕ → Term S ℕ → Term sig ℕ
  | _, .var x => .var x
  | b, .app α ts => cellSkel (var (b + 2)) m (idx α)
      (var (b + 1) :: List.ofFn fun i => codeTerm (b + 5 + off (fun j => codeSize (ts j)) i) (ts i))
      b

/-- **The trees on the extra ports of `⟨t⟩`** (Fig. 10, page 89), one per cell of `t`, in prefix
order: the cell at the root first, then those of each subtree from left to right. The tree of the
cell `α` with names from `b` is `codeExtra m (idx α) (b + 2) (b + 1) (b + 3)`. -/
def codeExtras : ℕ → Term S ℕ → List (Term sig ℕ)
  | _, .var _ => []
  | b, .app α ts => codeExtra m (idx α) (b + 2) (b + 1) (b + 3) ::
      (List.ofFn fun i => codeExtras (b + 5 + off (fun j => codeSize (ts j)) i) (ts i)).flatten

/-- `⟨t⟩` has one extra port per cell of `t` (page 89): `p` is the number of cells. -/
theorem length_codeExtras (b : ℕ) (t : Term S ℕ) :
    (codeExtras m idx b t).length = Multiset.card t.cells := by
  induction t generalizing b with
  | var x => rfl
  | app α ts ih =>
    simp only [codeExtras, List.length_cons, List.length_flatten, List.map_ofFn, List.sum_ofFn,
      Function.comp_def, ih, cells_app, Multiset.card_cons, Multiset.card_sum]

/-- The five names of a block. -/
theorem Ico_add_five (b : ℕ) :
    Multiset.Ico b (b + 5) = {b} + {b + 1} + {b + 2} + {b + 3} + {b + 4} := by
  ext z
  simp only [count_Ico, Multiset.count_add, Multiset.count_singleton]
  split_ifs <;> omega

/-- The names of the trees of a flattened list of lists. -/
theorem sum_vars_flatten_ofFn {n : ℕ} (f : Fin n → List (Term sig ℕ)) :
    (((List.ofFn f).flatten).map Term.vars).sum = ∑ i, ((f i).map Term.vars).sum := by
  simp [List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def]

/-- **The names of `⟨t⟩`** (Fig. 10, page 89): the names of `⟨t⟩` and of the trees on its extra
ports are those of `t`, with their multiplicity, and both ends of each new name of
`[b, b + codeSize t)`. So the new names are distinct, fresh above `b`, and internal. -/
theorem vars_codeTerm_add (b : ℕ) (t : Term S ℕ) :
    (codeTerm m idx b t).vars + ((codeExtras m idx b t).map Term.vars).sum =
      t.vars + 2 • Multiset.Ico b (b + codeSize t) := by
  induction t generalizing b with
  | var x => simp [codeTerm, codeExtras, codeSize]
  | app α ts ih =>
    have key : (∑ i, (codeTerm m idx (b + 5 + off (fun j => codeSize (ts j)) i) (ts i)).vars) +
        ∑ i, ((codeExtras m idx (b + 5 + off (fun j => codeSize (ts j)) i) (ts i)).map
          Term.vars).sum =
        (∑ i, (ts i).vars) + 2 • Multiset.Ico (b + 5) (b + 5 + ∑ i, codeSize (ts i)) := by
      rw [← Finset.sum_add_distrib]
      simp only [ih, Finset.sum_add_distrib, ← Finset.smul_sum]
      congr 2
      exact sum_Ico_off (fun j => codeSize (ts j)) (b + 5)
    have hI : Multiset.Ico b (b + codeSize (.app α ts)) =
        Multiset.Ico b (b + 5) + Multiset.Ico (b + 5) (b + 5 + ∑ i, codeSize (ts i)) := by
      rw [Multiset.Ico_add_Ico_eq_Ico (by omega) (by omega)]
      simp [codeSize, add_assoc]
    rw [hI, Ico_add_five]
    simp only [codeTerm, codeExtras, vars_cellSkel, List.map_cons, List.sum_cons, vars_codeExtra,
      sum_vars_flatten_ofFn, List.map_ofFn, List.sum_ofFn, vars_app, vars_var, Function.comp_def]
    calc _ = ((∑ i, (codeTerm m idx (b + 5 + off (fun j => codeSize (ts j)) i) (ts i)).vars) +
          ∑ i, ((codeExtras m idx (b + 5 + off (fun j => codeSize (ts j)) i) (ts i)).map
            Term.vars).sum) +
          ({b} + {b + 1} + {b + 2} + {b + 3} + {b + 4} + {b} + {b + 1} + {b + 2} + {b + 3} +
            {b + 4}) := by abel
      _ = _ := by rw [key]; simp only [two_nsmul]; abel

/-! ## The package `Γ_{i,j}` -/

/-- The number of new names of the tree of `⟨φ⟩` at each port, the ports numbered
`0, …, a + k - 1` by `finSumFinEquiv` (page 89). -/
noncomputable def codeSizes (φ : Rule S a k) : Fin (a + k) → ℕ :=
  fun q => codeSize (φ.portTree (finSumFinEquiv.symm q))

/-- The number of names of `Γ_{i,j}` of Fig. 10 (page 89): the internal wires of `φ`, then the new
names of `⟨φ⟩`. -/
noncomputable def codeGammaSize (φ : Rule S a k) : ℕ := φ.internal + ∑ q, codeSizes φ q

/-- The first new name of the tree of `⟨φ⟩` at the port `p`. -/
noncomputable def codeBase (φ : Rule S a k) (k₀ : ℕ) (p : Fin a ⊕ Fin k) : ℕ :=
  k₀ + φ.internal + off (codeSizes φ) (finSumFinEquiv p)

/-- The tree of `⟨φ⟩` at the port `p` (Fig. 10, page 89): the internal wire `w` of `φ` is named
`k₀ + w`, and the new names of the port `p` take its block above `k₀ + φ.internal`. -/
noncomputable def codePort (φ : Rule S a k) (k₀ : ℕ) (p : Fin a ⊕ Fin k) : Term sig ℕ :=
  codeTerm m idx (codeBase φ k₀ p) (gammaTree φ k₀ p)

/-- The trees on the extra ports of the cells of `⟨φ⟩` at the port `p` (page 89). -/
noncomputable def codePortExtras (φ : Rule S a k) (k₀ : ℕ) (p : Fin a ⊕ Fin k) :
    List (Term sig ℕ) :=
  codeExtras m idx (codeBase φ k₀ p) (gammaTree φ k₀ p)

/-- The trees on the extra ports of all the cells of `⟨φ⟩` (page 89), port after port in the order
`finSumFinEquiv` (the ports of `α_i`, then the middle ports), each port in the order of
`codeExtras`: the trees plugged into the auxiliary ports of `C_{p_{i,j}}`. -/
noncomputable def codeGammaExtras (φ : Rule S a k) (k₀ : ℕ) : List (Term sig ℕ) :=
  (List.ofFn fun q => codePortExtras m idx φ k₀ (finSumFinEquiv.symm q)).flatten

/-- **The package `Γ_{i,j}` of Fig. 10** (bottom right, page 89): the dual multiplexor `M*_{a+2}`
whose leaves are, from left to right, the copier `C_p` on the extra ports of the `p` cells of
`⟨φ⟩`, the trees of `⟨φ⟩` at the `a` ports of the first cell, and the transpositor `T_σ` applied to
the trees of `⟨φ⟩` at the `k` middle ports. -/
noncomputable def codeGamma (φ : Rule S a k) (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ) (k₀ : ℕ) : Term sig ℕ :=
  muxStar (copier (codeGammaExtras m idx φ k₀) ::
    (List.ofFn (fun i => codePort m idx φ k₀ (.inl i)) ++
      [transpositorPerm σ hσ (fun j => codePort m idx φ k₀ (.inr j))]))

/-- The cells of a linear side in expanded form are those of its trees (page 86). -/
theorem cells_eq_sum_portTree {φ : Rule S a k} (he : φ.Expanded) (hl : φ.Linear) :
    φ.net.cells = ∑ p, (φ.portTree p).cells := by
  rw [Net.cells, (he.net_eq_portTree hl).1, Multiset.bind_map]
  simp only [eqCells_mk, cells_var, zero_add]
  rfl

/-- **`C_p` has one auxiliary port per cell of `φ`** (Fig. 10, page 89): `p_{i,j}` is the number of
cells of `φ_{i,j}`, for a linear side in expanded form. -/
theorem length_codeGammaExtras {φ : Rule S a k} (he : φ.Expanded) (hl : φ.Linear) (k₀ : ℕ) :
    (codeGammaExtras m idx φ k₀).length = Multiset.card φ.net.cells := by
  rw [codeGammaExtras, List.length_flatten, List.map_ofFn, List.sum_ofFn,
    cells_eq_sum_portTree he hl, Multiset.card_sum]
  simp only [Function.comp_def, codePortExtras, length_codeExtras, gammaTree,
    Rule.portTreeC_eq_portTree he hl, cells_bind]
  simp only [cells_var, Multiset.bind_zero, add_zero]
  exact Equiv.sum_comp finSumFinEquiv.symm (fun p => Multiset.card (φ.portTree p).cells)

/-- **The names of `Γ_{i,j}`** (Fig. 10, page 89): for a linear side in expanded form, they are
both ends of each name of `[k₀, k₀ + codeGammaSize φ)`. -/
theorem vars_codeGamma {φ : Rule S a k} (he : φ.Expanded) (hl : φ.Linear)
    (σ : Equiv.Perm (Fin k)) (hσ : Function.Involutive σ) (k₀ : ℕ) :
    (codeGamma m idx φ σ hσ k₀).vars = 2 • Multiset.Ico k₀ (k₀ + codeGammaSize φ) := by
  set s := codeSizes φ
  set B := k₀ + φ.internal
  have hport : ∀ p, (codePort m idx φ k₀ p).vars +
      ((codePortExtras m idx φ k₀ p).map Term.vars).sum = (gammaTree φ k₀ p).vars +
      2 • Multiset.Ico (B + off s (finSumFinEquiv p))
        (B + off s (finSumFinEquiv p) + s (finSumFinEquiv p)) := fun p => by
    rw [codePort, codePortExtras, vars_codeTerm_add, gammaTree, Rule.portTreeC_eq_portTree he hl,
      codeSize_bind_var]
    simp [s, codeSizes, codeBase, B]
  have hsum : (codeGamma m idx φ σ hσ k₀).vars = ∑ p, ((codePort m idx φ k₀ p).vars +
      ((codePortExtras m idx φ k₀ p).map Term.vars).sum) := by
    rw [Finset.sum_add_distrib, codeGamma, vars_muxStar, List.map_cons, List.sum_cons, copier,
      vars_autoMux, codeGammaExtras, sum_vars_flatten_ofFn,
      Equiv.sum_comp finSumFinEquiv.symm (fun p => ((codePortExtras m idx φ k₀ p).map
        Term.vars).sum),
      List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      vars_transpositorPerm, Fintype.sum_sum_type, Function.comp_def]
    rw [add_comm]
    rfl
  rw [hsum]
  simp only [hport]
  rw [Finset.sum_add_distrib, sum_vars_gammaTree he hl,
    Equiv.sum_comp finSumFinEquiv (fun q => 2 • Multiset.Ico (B + off s q) (B + off s q + s q)),
    ← Finset.smul_sum, sum_Ico_off, ← nsmul_add, codeGammaSize,
    Multiset.Ico_add_Ico_eq_Ico (by omega) (by omega), add_assoc]

/-- A tree whose names are both ends of each name of an interval is a package (page 80). -/
theorem isPackage_of_vars_eq {π : Term sig ℕ} {b c : ℕ} (h : π.vars = 2 • Multiset.Ico b c) :
    π.IsPackage := by
  intro x hx
  rw [h] at hx ⊢
  rw [Multiset.count_nsmul, Multiset.count_eq_one_of_mem Multiset.nodup_Ico
    (Multiset.mem_of_mem_nsmul hx)]

/-- **`Γ_{i,j}` of Fig. 10 is a package** (page 89; packages, page 80): for a linear side in
expanded form, every name of `codeGamma` occurs exactly twice. -/
theorem codeGamma_isPackage {φ : Rule S a k} (he : φ.Expanded) (hl : φ.Linear)
    (σ : Equiv.Perm (Fin k)) (hσ : Function.Involutive σ) (k₀ : ℕ) :
    (codeGamma m idx φ σ hσ k₀).IsPackage :=
  isPackage_of_vars_eq (vars_codeGamma m idx he hl σ hσ k₀)

/-! ## The menus `Γ_i` and `Γ` -/

/-- `Γ_{i,j}` of Fig. 10 for an optional side, numbered from `k₀`; an eraser when there is no rule
between `α_i` and `α_j` (page 89, as `gammaOpt` for Fig. 6). -/
noncomputable def codeGammaOpt : Option (ExpSide S a) → ℕ → Term sig ℕ
  | some s, k₀ => codeGamma m idx s.φ s.σ s.involutive k₀
  | none, _ => mkEra

/-- The number of names of `codeGammaOpt`. -/
noncomputable def codeGammaOptSize : Option (ExpSide S a) → ℕ
  | some s => codeGammaSize s.φ
  | none => 0

/-- The names of `codeGammaOpt m idx o k₀` are both ends of each name of
`[k₀, k₀ + codeGammaOptSize o)` (page 89). -/
theorem vars_codeGammaOpt (o : Option (ExpSide S a)) (k₀ : ℕ) :
    (codeGammaOpt m idx o k₀).vars = 2 • Multiset.Ico k₀ (k₀ + codeGammaOptSize o) := by
  cases o with
  | none => simp [codeGammaOpt, codeGammaOptSize]
  | some s => exact vars_codeGamma m idx s.expanded s.linear s.σ s.involutive k₀

variable [Finite S.Sym] (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- The numbers of names of the packages `Γ_{j,β}` of the menu of `⟨β⟩`. -/
noncomputable def codeCellSizes (β : S.Sym) : Fin (Nat.card S.Sym) → ℕ :=
  fun j => codeGammaOptSize (side ((symEnum S).symm j) β)

/-- **The menu `Γ_β = Γ_{0,β} & ⋯ & Γ_{m-1,β}`** of Fig. 10 (page 89), as a list: `Γ_{j,β}` is built
from the side of `α_j` against `β` given by `side`, with the symbols numbered by `symEnum`, on the
`j`-th block of names above `k₀`. -/
noncomputable def codeCellMenu (β : S.Sym) (k₀ : ℕ) : List (Term sig ℕ) :=
  List.ofFn fun j => codeGammaOpt (Nat.card S.Sym) (fun α => symEnum S α)
    (side ((symEnum S).symm j) β) (k₀ + off (codeCellSizes side β) j)

/-- The names of the menu `Γ_β` (page 89) are both ends of each name of a block above `k₀`. -/
theorem vars_menu_codeCellMenu (β : S.Sym) (k₀ : ℕ) :
    (menu (codeCellMenu side β k₀)).vars =
      2 • Multiset.Ico k₀ (k₀ + ∑ j, codeCellSizes side β j) := by
  rw [menu, vars_mux, codeCellMenu, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, vars_codeGammaOpt]
  rw [← Finset.smul_sum]
  exact congrArg (2 • ·) (sum_Ico_off (codeCellSizes side β) k₀)

/-- The numbers of names of the menus `Γ_0, …, Γ_{m-1}`. -/
noncomputable def codeMenuSizes : Fin (Nat.card S.Sym) → ℕ :=
  fun i => ∑ j, codeCellSizes side ((symEnum S).symm i) j

/-- **The menus `Γ_0, …, Γ_{m-1}`** of Fig. 10 (page 89), whose menu `Γ = Γ_0 & ⋯ & Γ_{m-1}` is
the package coded by `!Γ`: `Γ_i` is the menu of the symbol numbered `i`, on the `i`-th block of
names above `k₀`. -/
noncomputable def codeMenus (k₀ : ℕ) : List (Term sig ℕ) :=
  List.ofFn fun i => menu (codeCellMenu side ((symEnum S).symm i) (k₀ + off (codeMenuSizes side) i))

/-- There is one menu per symbol. -/
theorem length_codeMenus (k₀ : ℕ) : (codeMenus side k₀).length = Nat.card S.Sym :=
  List.length_ofFn

/-- The menu of `codeMenus` at the number of `β` is the menu `Γ_β` of `β` (page 89). -/
theorem getElem_codeMenus (k₀ : ℕ) (β : S.Sym) (h : (symEnum S β : ℕ) < (codeMenus side k₀).length) :
    (codeMenus side k₀)[(symEnum S β : ℕ)] =
      menu (codeCellMenu side β (k₀ + off (codeMenuSizes side) (symEnum S β))) := by
  simp [codeMenus]

/-- The names of `Γ = Γ_0 & ⋯ & Γ_{m-1}` (page 89) are both ends of each name of a block above
`k₀`. -/
theorem vars_menu_codeMenus (k₀ : ℕ) :
    (menu (codeMenus side k₀)).vars = 2 • Multiset.Ico k₀ (k₀ + ∑ i, codeMenuSizes side i) := by
  rw [menu, vars_mux, codeMenus, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, vars_menu_codeCellMenu]
  rw [← Finset.smul_sum]
  exact congrArg (2 • ·) (sum_Ico_off (codeMenuSizes side) k₀)

/-- **Each menu `Γ_i` is a package** (page 89). -/
theorem codeMenus_isPackage (k₀ : ℕ) : ∀ π ∈ codeMenus side k₀, π.IsPackage := by
  intro π hπ
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hπ
  exact isPackage_of_vars_eq (vars_menu_codeCellMenu side _ _)

/-- **`Γ = Γ_0 & ⋯ & Γ_{m-1}` is a package** (page 89), as the extraction of page 90 needs. -/
theorem menu_codeMenus_isPackage (k₀ : ℕ) : (menu (codeMenus side k₀)).IsPackage :=
  isPackage_of_vars_eq (vars_menu_codeMenus side k₀)

/-- The names of `Γ` are below `k₀ + ∑ i, codeMenuSizes side i` (page 89). -/
theorem menu_codeMenus_below (k₀ : ℕ) :
    (menu (codeMenus side k₀)).Below (k₀ + ∑ i, codeMenuSizes side i) := by
  intro x hx
  rw [vars_menu_codeMenus] at hx
  exact (Multiset.mem_Ico.1 (Multiset.mem_of_mem_nsmul hx)).2

/-- **The extraction of page 90 for the `Γ` of Fig. 10.** With `Γ = codeMenus side k₀` (the menus
`Γ_0, …, Γ_{m-1}` built from any choice of expanded sides), a copy of `!Γ` (renamed by `f`,
injective on its names) on the extra port of `⟨β⟩`, in any context `Δ`, reduces to a net that is
`Equiv` to the cell `[β]` of Fig. 10 with a copy of the menu `Γ_β` and a copy of `!Γ`. This is
`codeCell_code`, whose hypotheses on `Γ` hold by `codeMenus_isPackage`,
`menu_codeMenus_isPackage` and `menu_codeMenus_below`. -/
theorem codeCell_code_codeMenus (k₀ K : ℕ) (hK : k₀ + ∑ i, codeMenuSizes side i ≤ K)
    (β : S.Sym) (f : ℕ → ℕ) (hf : Set.InjOn f {x | x ∈ (code K (menu (codeMenus side k₀))).vars})
    (P : Term sig ℕ) (ts : List (Term sig ℕ)) (ℓ u w y k₁ : ℕ) (Δ : CNet)
    (hlin : Net.Linear (codeCell (codeMenus side k₀).length (symEnum S β) P
      ((code K (menu (codeMenus side k₀))).bind fun x => var (f x)) ts ℓ u w y k₁ + Δ)) :
    ∃ (g g' : ℕ → ℕ) (M : CNet),
      Set.InjOn g {x | x ∈ (code K (menu (codeMenus side k₀))).vars} ∧
      Set.InjOn g' {x | x ∈ (code K (menu (codeMenus side k₀))).vars} ∧
      StepsE system (codeCell (codeMenus side k₀).length (symEnum S β) P
        ((code K (menu (codeMenus side k₀))).bind fun x => var (f x)) ts ℓ u w y k₁ + Δ) M ∧
      Equiv M (s(P, cellSkel ((menu (codeCellMenu side β
          (k₀ + off (codeMenuSizes side) (symEnum S β)))).bind fun x => var (g x))
        (codeMenus side k₀).length (symEnum S β)
        (((code K (menu (codeMenus side k₀))).bind fun x => var (g' x)) :: ts) ℓ) ::ₘ Δ) := by
  have hk : (symEnum S β : ℕ) < (codeMenus side k₀).length := by
    rw [length_codeMenus]; exact (symEnum S β).isLt
  have hb : (menu (codeMenus side k₀)).Below K := fun x hx =>
    (menu_codeMenus_below side k₀ x hx).trans_le hK
  have := codeCell_code (codeMenus side k₀) (codeMenus_isPackage side k₀)
    (menu_codeMenus_isPackage side k₀) K hb (symEnum S β) hk f hf P ts ℓ u w y k₁ Δ hlin
  rwa [getElem_codeMenus side k₀ β hk] at this

end INet.Comb
