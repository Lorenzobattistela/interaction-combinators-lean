import Checks.Universality.General.CodeTrCheck
import Checks.Universality.General.CodeGammaReview

/-!
# Review of the principal net `[α]` of Fig. 10 and its strictness (pages 89–90)

Review of `treePNet`, `codeTree`, `codeNet`, `codeTranslation` and `codeTranslation_strict`
(`CodeTr.lean`) against Fig. 10 (journal page 89, PDF page 21, rendered at 300 dpi), the
definition of principal nets and strict translations (page 80) and the port convention of page 72.

**The figure.**

* `codeTree_eq_fig10` — the tree of `[α]` written out: the root is a `dup` cell (`T_{1,1}`); its
  left auxiliary port carries a `con` cell whose left port is the menu `Γ_α` and whose right port is
  the selector `S^α_m`; its right auxiliary port is the loop `ℓ = n`. The free port of the selector
  is the root of `M_{n+2}`, whose leaves are, left to right, `!Γ`, the ports `0, …, n - 1` and the
  loop `n`. This is Fig. 10, top left: `Γ_i` on the left of `T_{1,1}`, `S^i_m` in the middle, the
  loop on the right joining the last leaf of `M_{n_i+2}` (as in Fig. 6).
* `getElem_codeCellMenu` — the entry `j` of the menu `Γ_α` is built from `side α_j α`: it is
  `Γ_{j,α}`. Fig. 10 (top right) writes `Γ_i = Γ_{1,i} & ⋯ & Γ_{m,i}`; the code follows the figure.
  The issue text says "`Γ_i` the menu of `Γ_{i,1}, …, Γ_{i,m}`": that is the transpose of the
  figure, and of the code. (Which index is the cell of the rule is fixed by `side`, whose relation
  to the rules is a separate issue.)
* `codeMenus` takes no symbol: the package `Γ` coded by `!Γ` is the same menu
  `Γ_0 & ⋯ & Γ_{m-1}` of all symbols in every `[α]`, only its names are shifted
  (`codeMenus_two`: two symbols, two entries, in the cell of either symbol).

**Refutation attempts.**

* `treePNet_hp_fails_*`, `treePNet_hw_fails_three` — a port missing, a port twice, a wire three
  times: the hypotheses of `treePNet` fail, so these trees cannot be made principal nets.
* `treePNet_inst_args` — the instance of `treePNet` with any trees on the ports and the wires named
  back is `t` with the port `i` replaced by the `i`-th tree: the ports are not permuted.
* `codeNet_inst_args` — so the port `i` of `[α]` is the leaf of `M_{n+2}` just after `!Γ` and `i`
  others: ports in the order `0, …, n - 1` of page 72, not reversed. `codeNet_sigTwoPorts_inst`
  checks it on a symbol with two ports.
* `codeCellMenu_sideConDup` — the translation on a system with a non-trivial side (the interaction
  combinators with the side `con`–`dup` of four cells, `sideConDup` of `CodeGammaReview`): the
  menu of `[dup]` holds `codeGamma` of that side at the number of `con` and erasers elsewhere; with
  `codeTree_eq_fig10` this gives the tree of `[dup]`. (Three symbols, not two: this is the system
  whose side has already been computed by hand in `codeGamma_conDup`.)

**Strictness.**

* `Translation.Strict` (`Translation.lean`) is `∀ α, ∀ x, (Φ.net α).tree ≠ var x`, the definition
  of page 80 ("no `[α]` is a wire"); `codeTranslation_strict` proves exactly that statement for
  `codeTranslation side`, for every `side`.
* `wireTranslation_not_strict` — it is not vacuous: the translation of a one-symbol, one-port
  system whose `[α]` is a wire is a `Translation` and is not strict.
-/

namespace INet.Comb.CodeTrReview

open Term Translation

/-! ## The tree of Fig. 10 -/

section general

variable {S : Signature} [Finite S.Sym]
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **The tree of `[α]` of Fig. 10** (top left, page 89), written out: a `dup` cell (`T_{1,1}`)
whose left port is a `con` cell carrying the menu `Γ_α` and the selector `S^α_m`, whose right port
is the loop `n`. The selector sits on `M_{n+2}`, with the leaves `!Γ`, the ports `0, …, n - 1` and
the loop `n`, in this order. -/
theorem codeTree_eq_fig10 (α : S.Sym) :
    codeTree side α =
      mkDup
        (mkCon (menu (codeCellMenu side α (S.arity α + 1)))
          (cellSel (Nat.card S.Sym) (symEnum S α)
            (mux (code (codeKey side α) (menu (codeMenus side (codeMenuBase side α))) ::
              ((List.ofFn fun j : Fin (S.arity α) => var (j : ℕ)) ++ [var (S.arity α)])))))
        (var (S.arity α)) :=
  rfl

/-- **The entries of the menu `Γ_α`** (Fig. 10, top right, page 89): the entry `j` is built from
the side of `α_j` against `α`, that is `Γ_{j,α}`, as in `Γ_i = Γ_{1,i} & ⋯ & Γ_{m,i}`. -/
theorem getElem_codeCellMenu (α : S.Sym) (k₀ : ℕ) (j : Fin (Nat.card S.Sym)) :
    (codeCellMenu side α k₀)[(j : ℕ)]'(by simp [codeCellMenu_eq]) =
      codeGammaOpt (Nat.card S.Sym) (fun β => symEnum S β) (side ((symEnum S).symm j) α)
        (k₀ + off (codeCellSizes side α) j) := by
  simp [codeCellMenu_eq]

end general

/-! ## A tree as a principal net: refutation attempts -/

/-- **A missing port** (page 80): in `con(1, 1)` with one port, the port `0` does not occur, so
the first hypothesis of `treePNet` fails. -/
theorem treePNet_hp_fails_missing :
    ¬ ∀ i < 1, (mkCon (var 1) (var 1) : Term sig ℕ).vars.count i = 1 := by
  intro h
  have := h 0 (by omega)
  simp [vars_mkCon] at this

/-- **A port twice** (page 80): in `con(0, 0)` with one port, the port `0` occurs twice. -/
theorem treePNet_hp_fails_twice :
    ¬ ∀ i < 1, (mkCon (var 0) (var 0) : Term sig ℕ).vars.count i = 1 := by
  intro h
  have := h 0 (by omega)
  simp [vars_mkCon] at this

/-- **A wire three times** (page 80): in `con(1, con(1, 1))` with no port, the name `1` occurs
three times, so the second hypothesis of `treePNet` fails. -/
theorem treePNet_hw_fails_three :
    ¬ ∀ x ∈ (mkCon (var 1) (mkCon (var 1) (var 1)) : Term sig ℕ).vars, 0 ≤ x →
      (mkCon (var 1) (mkCon (var 1) (var 1)) : Term sig ℕ).vars.count x = 2 := by
  intro h
  have := h 1 (by simp [vars_mkCon]) (by omega)
  simp [vars_mkCon] at this

/-- **`treePNet` keeps the ports in place** (page 80, page 72): its instance with the tree `args i`
on the port `i` and the internal wires named back is `t` with each name `i < n` replaced by
`args i`, and every other name kept. -/
theorem treePNet_inst_args (n : ℕ) (t : Term sig ℕ) (hp : ∀ i < n, t.vars.count i = 1)
    (hw : ∀ x ∈ t.vars, n ≤ x → t.vars.count x = 2) (args : Fin n → Term sig ℕ) :
    (treePNet n t hp hw).inst args (fun w => ((wireNum n t).symm w).1) =
      t.bind fun x => if h : x < n then args ⟨x, h⟩ else var x := by
  show (t.bind (treeLeaf n t)).bind (Sum.elim args
    fun w : Fin (wireSet n t).card => var ((wireNum n t).symm w).1) = _
  rw [Term.bind_bind]
  refine Term.bind_congr fun x hx => ?_
  unfold treeLeaf
  by_cases h1 : x < n
  · simp [h1]
  · have h2 : x ∈ wireSet n t :=
      Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hx, not_lt.1 h1⟩
    simp [h1, h2]

section general

variable {S : Signature} [Finite S.Sym]
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **The ports of `[α]` are in the order of page 72** (Fig. 10, page 89): the instance of `[α]`
with the tree `args i` on the port `i` (internal wires named back) is the tree of Fig. 10 with
`args 0, …, args (n - 1)` on the leaves of `M_{n+2}` between `!Γ` and the loop, in this order. -/
theorem codeNet_inst_args (α : S.Sym) (args : Fin (S.arity α) → Term sig ℕ) :
    (codeNet side α).inst args
        (fun w => ((wireNum (S.arity α) (codeTree side α)).symm w).1) =
      mkDup
        (mkCon (menu (codeCellMenu side α (S.arity α + 1)))
          (cellSel (Nat.card S.Sym) (symEnum S α)
            (mux (code (codeKey side α) (menu (codeMenus side (codeMenuBase side α))) ::
              (List.ofFn args ++ [var (S.arity α)])))))
        (var (S.arity α)) := by
  refine (treePNet_inst_args (S.arity α) (codeTree side α) (codeTree_hyps side α).1
    (codeTree_hyps side α).2 args).trans ?_
  have keep : ∀ t : Term sig ℕ, (∀ x ∈ t.vars, S.arity α ≤ x) →
      (t.bind fun x => if h : x < S.arity α then args ⟨x, h⟩ else var x) = t := fun t ht => by
    conv_rhs => rw [← Term.bind_var_self t]
    exact Term.bind_congr fun x hx => by simp [not_lt.2 (ht x hx)]
  -- the menu `Γ_α` and the code `!Γ` have no port among their names
  have hΓ : ∀ x ∈ (menu (codeCellMenu side α (S.arity α + 1))).vars, S.arity α ≤ x :=
    fun x hx => by
      rw [vars_menu_codeCellMenu, Multiset.mem_nsmul_of_ne_zero (by omega), Multiset.mem_Ico] at hx
      omega
  have hc : ∀ x ∈ (code (codeKey side α) (menu (codeMenus side (codeMenuBase side α)))).vars,
      S.arity α ≤ x := fun x hx => by
    have hw := (codeTree_wires side α).2
    rw [vars_code, vars_menu_codeMenus] at hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · rcases Multiset.mem_add.1 hx with hx | hx
      · rw [Multiset.mem_nsmul_of_ne_zero (by omega), Multiset.mem_Ico] at hx
        have : S.arity α ≤ codeMenuBase side α := by rw [codeMenuBase_eq]; omega
        omega
      · exact hw x (Multiset.mem_add.2 (Or.inr hx))
    · exact hw x (Multiset.mem_add.2 (Or.inr hx))
  rw [codeTree_eq_fig10, bind_mkDup, bind_mkCon, bind_cellSel, bind_mux, keep _ hΓ]
  have hl : ((var (S.arity α) : Term sig ℕ).bind fun x =>
      if h : x < S.arity α then args ⟨x, h⟩ else var x) = var (S.arity α) := by
    simp
  have hp : (fun j : Fin (S.arity α) => (var (j : ℕ) : Term sig ℕ).bind fun x =>
      if h : x < S.arity α then args ⟨x, h⟩ else var x) = args :=
    funext fun j => by simp [j.isLt]
  simp only [List.map_cons, List.map_append, List.map_ofFn, List.map_nil, keep _ hc, hl,
    Function.comp_def, hp]

end general

/-! ## Two ports, in order -/

/-- A signature with one symbol with two ports. -/
def sigTwoPorts : Signature := ⟨Unit, fun _ => 2⟩

instance : Unique sigTwoPorts.Sym := inferInstanceAs (Unique Unit)

instance : Finite sigTwoPorts.Sym := inferInstanceAs (Finite Unit)

/-- No rule. -/
def sideNoneTwo : ∀ α : sigTwoPorts.Sym, sigTwoPorts.Sym → Option (ExpSide sigTwoPorts
    (sigTwoPorts.arity α)) :=
  fun _ _ => none

theorem card_sigTwoPorts : Nat.card sigTwoPorts.Sym = 1 := Nat.card_unique

theorem symEnum_sigTwoPorts (α : sigTwoPorts.Sym) : (symEnum sigTwoPorts α : ℕ) = 0 := by
  have h1 : Nat.card sigTwoPorts.Sym = 1 := card_sigTwoPorts
  have h2 : (symEnum sigTwoPorts α : ℕ) < Nat.card sigTwoPorts.Sym := (symEnum sigTwoPorts α).isLt
  omega

theorem codeCellMenu_sideNoneTwo (β : sigTwoPorts.Sym) (k : ℕ) :
    codeCellMenu sideNoneTwo β k = [mkEra] := by
  rw [codeCellMenu_eq]
  simp only [sideNoneTwo, codeGammaOpt, List.ofFn_const, card_sigTwoPorts]
  rfl

theorem codeMenus_sideNoneTwo (k : ℕ) : codeMenus sideNoneTwo k = [mkEra] := by
  rw [codeMenus_eq]
  simp only [codeCellMenu_sideNoneTwo, List.ofFn_const, card_sigTwoPorts]
  rfl

/-- **The two ports of `[α]` in order** (page 72, Fig. 10 page 89): with the trees `args 0`,
`args 1` on the ports `0`, `1`, the leaves of `M_4` are `!Γ = M_4(ε, ε, ε, ε)`, then `args 0`, then
`args 1`, then the loop `2`. -/
theorem codeNet_sigTwoPorts_inst (α : sigTwoPorts.Sym)
    (args : Fin (sigTwoPorts.arity α) → Term sig ℕ) :
    (codeNet sideNoneTwo α).inst args
        (fun w => ((wireNum (sigTwoPorts.arity α) (codeTree sideNoneTwo α)).symm w).1) =
      mkDup (mkCon mkEra (cellSel 1 0 (mux [mux [mkEra, mkEra, mkEra, mkEra],
        args ⟨0, Nat.zero_lt_two⟩, args ⟨1, Nat.one_lt_two⟩, var 2]))) (var 2) := by
  rw [codeNet_inst_args, codeCellMenu_sideNoneTwo, codeMenus_sideNoneTwo, symEnum_sigTwoPorts,
    card_sigTwoPorts, show menu [mkEra] = (mkEra : Term sig ℕ) from rfl,
    code_of_dupFree _ _ (by trivial)]
  rfl

/-! ## Two symbols: the menu `Γ` of all symbols -/

/-- A signature with two symbols, of arities `0` and `1`. -/
def sigBool : Signature := ⟨Bool, fun b => if b then 1 else 0⟩

instance : Fintype sigBool.Sym := inferInstanceAs (Fintype Bool)

theorem card_sigBool : Nat.card sigBool.Sym = 2 := Nat.card_eq_fintype_card.trans rfl

/-- No rule. -/
def sideNoneBool : ∀ α : sigBool.Sym, sigBool.Sym → Option (ExpSide sigBool (sigBool.arity α)) :=
  fun _ _ => none

theorem codeCellMenu_sideNoneBool (β : sigBool.Sym) (k : ℕ) :
    codeCellMenu sideNoneBool β k = [mkEra, mkEra] := by
  rw [codeCellMenu_eq]
  simp only [sideNoneBool, codeGammaOpt, List.ofFn_const, card_sigBool]
  rfl

/-- **The menu `Γ` of `!Γ` has one entry per symbol** (Fig. 10, page 89): with two symbols and no
rule, `Γ = Γ_0 & Γ_1` with `Γ_i = ε & ε`. It does not depend on the symbol of the cell. -/
theorem codeMenus_two (k : ℕ) :
    menu (codeMenus sideNoneBool k) =
      (mux [mux [mkEra, mkEra], mux [mkEra, mkEra]] : Term sig ℕ) := by
  rw [codeMenus_eq]
  simp only [codeCellMenu_sideNoneBool, List.ofFn_const, card_sigBool]
  rfl

/-- **`[α]` for two symbols** (Fig. 10, page 89): the cell of the symbol `α`, numbered `i`, carries
the menu `Γ_α = ε & ε` and `S^i_2`, on `M_{n+2}` whose first leaf is the code of the menu of both
symbols. -/
theorem codeTree_two (α : sigBool.Sym) :
    codeTree sideNoneBool α =
      mkDup (mkCon (mux [mkEra, mkEra]) (cellSel (Nat.card sigBool.Sym) (symEnum sigBool α)
          (mux (mux [mkEra, mkEra, mkEra, mux [mux [mkEra, mkEra], mux [mkEra, mkEra]]] ::
            ((List.ofFn fun j : Fin (sigBool.arity α) => var (j : ℕ)) ++
              [var (sigBool.arity α)])))))
        (var (sigBool.arity α)) := by
  rw [codeTree_eq_fig10, codeMenus_two, codeCellMenu_sideNoneBool,
    code_of_dupFree _ _ (by simp [mux]; trivial)]
  rfl

/-! ## A non-trivial side -/

open CodeGammaReview GammaCheck DecompositionReview Classical in
/-- **`[dup]` with the side `con`–`dup`** (Fig. 10, page 89): for the interaction combinators with
the side of `con` against `dup` given by `sideConDup` (four cells) and no other side, the menu
`Γ_dup` of `[dup]` holds at the number of `con` the package `codeGamma` of that side, and erasers at
the other numbers; the menu `Γ_con` of `[con]` holds only erasers. -/
theorem codeCellMenu_sideConDup (k₀ : ℕ) (j : Fin (Nat.card sig.Sym)) :
    (codeCellMenu sideConDup .dup k₀)[(j : ℕ)]'(by simp [codeCellMenu, codeCellMenuE]) =
      (if (symEnum sig).symm j = .con then
        codeGamma (Nat.card sig.Sym) (fun β => symEnum sig β) ruleConDup (Equiv.swap 0 1) hs
          (k₀ + off (codeCellSizes sideConDup .dup) j)
      else mkEra) ∧
    (codeCellMenu sideConDup .con k₀)[(j : ℕ)]'(by simp [codeCellMenu, codeCellMenuE]) = mkEra := by
  simp only [codeCellMenu, codeCellMenuE, List.getElem_ofFn]
  constructor <;> rcases (symEnum sig).symm j with _ | _ | _ <;>
    simp only [sideConDup, codeGammaOpt] <;> split_ifs with hc <;>
    first | rfl | exact absurd rfl hc | contradiction

/-! ## Strictness is not vacuous -/

/-- A single wire from the port to the root, as a principal net with one port. -/
def wirePNet : PNet sigOne 1 where
  internal := 0
  tree := var (.inl ⟨0, Nat.one_pos⟩)
  port_count i := by
    rw [Fin.fin_one_eq_zero i]
    simp
  internal_count w := w.elim0

/-- **A non-strict translation** (definition page 80): the system with one symbol of arity one,
each `[α]` a wire. -/
def wireTranslation : Translation sigOne sigOne := ⟨fun _ => wirePNet⟩

/-- **`Strict` is not vacuous** (page 80): the translation whose `[α]` is a wire is not strict. -/
theorem wireTranslation_not_strict : ¬ wireTranslation.Strict :=
  fun h => h () (.inl ⟨0, Nat.one_pos⟩) rfl

end INet.Comb.CodeTrReview
