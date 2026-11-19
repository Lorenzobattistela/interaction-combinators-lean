import Checks.CodeTreeEReview
import Checks.CodeCellsMeetECheck
import Checks.CodeTrReview

/-!
# Review of `codeNetE` and `codeWiresE`, the principal net `[α]` of Fig. 10 for any `e` (page 89)

Review of `codeNetE`, `codeNetE_inst`, `codeNetE_strict` (`Lafont/CodeTr.lean`), `codeWiresE`,
`inst_codeNetE_fresh`, `codeWiresE_injective`, `le_codeWiresE`, `codeWiresE_lt`
(`Lafont/CodeCellsMeet.lean`) and `codeNetE_inst_eq`, `menu_codeCellMenuE_shift`,
`menu_codeMenusE_shift` (`Lafont/CodeShift.lean`), added by PR #324, against Fig. 10 (journal
page 89, PDF page 21, top left, rendered alone at 600 dpi).

**No defect found.**

**Against the paper.** Fig. 10 draws `[α_i]` as a principal net whose root is the root of
`T_{1,1}` and whose auxiliary ports, from left to right, are the leaves of `M_{n_i+2}` between
`!Γ` and the loop. The tree `codeTreeE` was reviewed in `Checks/CodeTreeEReview.lean`; what
`codeNetE` adds is the passage to a `PNet`, by `treePNet`.

* `codeNetE_tree`, `codeNetE_internal` — by `rfl`, the tree of `codeNetE e side α` is the tree of
  Fig. 10 with each name `x < k` replaced by the port `x` and each other name by its rank among the
  internal names (`wireNum`), and the number of internal wires is the number of those names.
* `codeNetE_inst_args` — for every `e`, the instance of `[α]` with any trees `args` on its ports is
  the tree of Fig. 10 with `args 0, …, args (k - 1)` on the leaves of `M_{k+2}` between `!Γ` and
  the loop, in this order: the ports are in the order of the figure (and of page 72). This is
  `codeNet_inst_args` of `Checks/CodeTrReview.lean`, now for any `e`.
* `codeNetE_tree_eq_mkDup` — the root of the principal net is the `dup` cell of `T_{1,1}`.
* Concrete, by `#guard`, for `sig` with the two numberings `combEnum` (`con, dup, era ↦ 0, 1, 2`)
  and `combEnum₂` (`dup, con, era ↦ 0, 1, 2`) and the two choices of sides `sideConDup`,
  `sideAsym`: the numbers of internal wires (`40, 64, 40` for `sideConDup`, `103, 103, 79` for
  `sideAsym`) are `(card of the names - k) / 2`; the ports occur, in the left-to-right list of
  leaves, as `0, …, k - 1` in this order and **at the same positions under both numberings**; the
  multisets of cells are equal; the root is a `dup` cell; the instance with the wires named back is
  `codeTreeE` (`codeNetE_inst`, evaluated). The two `[α]` are different trees, also after the
  wires are renumbered (`flatTree`): as found for the tree (#315), they differ by the selector
  `S^{e α}_n` (for `con`, `dup`) and by the order of the menus inside `!Γ` and the selectors of the
  packages `⟨α_k⟩` (for all three). These are all numberings of symbols, inside the cells; no port
  moves. The issue expected "only by the numbering of the selectors": the order of the menus in
  `!Γ` is a second, equally harmless, difference (`[β]` reads its menu at the same number `e β`).

**Statements.** Every theorem of PR #324 that replaced an old one keeps the old name, at
`e := symEnum S`, with a statement that is the old one character for character (read in the diff
of #324): `codeNet`, `codeNet_inst`, `codeNet_strict`, `codeWires`, `inst_codeNet_fresh`,
`codeWires_injective`, `le_codeWires`, `codeWires_lt`, `length_codeCellMenu`,
`getElem_codeCellMenu`, `codeCellMenu_isPackage`, `le_of_mem_codeCellMenu`, `codeTree_bind_codeRen`,
`codeCellMenu_bind_isPackage`, `codeCells_meet`, `menu_codeCellMenu_shift`, `menu_codeMenus_shift`,
`codeNet_inst_eq`. None got a hypothesis, none became weaker; the `E` versions have no hypothesis
beyond `e`, `side` and the old ones. `codeNet_eq_codeNetE` and `codeWires_eq_codeWiresE` check by
`rfl` that the old definitions are the new ones at `symEnum S`, so the port orders agree.
`codeNetE_inst` and `codeNetE_strict` are applied below at `combEnum₂` and `sideAsym` (the check
of #324 applied them at `combEnum` and `sideConDup`).

**Refutation attempts.**

* `codeWiresE_injective` at `K = 0` and at `K = 7`, for `era` (arity `0`, so the loop is the name
  `0` and is an internal wire), `con` and `dup`: the list of the names of all wires has no
  repetition, and is the sorted list of the internal names shifted by `K`. Holds.
* `codeWiresE_lt`: every wire is below `K + sup + 1`, and the largest wire is `K + sup`, so the
  bound is attained and cannot be lowered. `le_codeWiresE`: the smallest wire of `[era]` at
  `K = 0` is `0`, so this bound is attained too. Holds.
* An enumeration `e : S.Sym ≃ Fin 0` makes the statements vacuous only for an empty signature,
  where there is no `α` to state them for; nothing to refute.

Not checked: that `[α]` reduces as Fig. 7 does (step 6c and later); the `#guard`s cover one
signature, `sig`, with two numberings and two choices of sides.
-/

namespace INet.Comb.CodeNetEReview

open Term Translation CodeGammaReview CodeMenusECheck CodeMenusEReview CodeTreeEReview

/-! ## For every numbering -/

section General

variable {S : Signature} {n : ℕ} (e : S.Sym ≃ Fin n)
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **The tree of `[α]` as a principal net** (Fig. 10, page 89; principal nets, page 80): the tree
of the figure with the names `x < k` made ports and the other names numbered by `wireNum`. -/
theorem codeNetE_tree (α : S.Sym) :
    (codeNetE e side α).tree =
      (codeTreeE e side α).bind (treeLeaf (S.arity α) (codeTreeE e side α)) :=
  rfl

/-- **The internal wires of `[α]`** (Fig. 10, page 89): one for each name of the tree other than the
ports, that is the loop, the names of `Γ_α`, of `Γ` and the cut names of `!Γ`. -/
theorem codeNetE_internal (α : S.Sym) :
    (codeNetE e side α).internal = (wireSet (S.arity α) (codeTreeE e side α)).card :=
  rfl

/-- **The ports of `[α]` are in the order of Fig. 10** (page 89; page 72), for any numbering `e`:
the instance of `[α]` with the tree `args i` on the port `i` (internal wires named back) is the tree
of the figure with `args 0, …, args (k - 1)` on the leaves of `M_{k+2}` between `!Γ` and the loop,
in this order, where `k = S.arity α`. -/
theorem codeNetE_inst_args (α : S.Sym) (args : Fin (S.arity α) → Term sig ℕ) :
    (codeNetE e side α).inst args
        (fun w => ((wireNum (S.arity α) (codeTreeE e side α)).symm w).1) =
      mkDup
        (mkCon (menu (codeCellMenuE e side α (S.arity α + 1)))
          (cellSel n (e α)
            (mux (code (codeKeyE e side α) (menu (codeMenusE e side (codeMenuBaseE e side α))) ::
              (List.ofFn args ++ [var (S.arity α)])))))
        (var (S.arity α)) := by
  refine (CodeTrReview.treePNet_inst_args (S.arity α) (codeTreeE e side α)
    (codeTreeE_hyps e side α).1 (codeTreeE_hyps e side α).2 args).trans ?_
  have keep : ∀ t : Term sig ℕ, (∀ x ∈ t.vars, S.arity α ≤ x) →
      (t.bind fun x => if h : x < S.arity α then args ⟨x, h⟩ else var x) = t := fun t ht => by
    conv_rhs => rw [← Term.bind_var_self t]
    exact Term.bind_congr fun x hx => by simp [not_lt.2 (ht x hx)]
  have hΓ : ∀ x ∈ (menu (codeCellMenuE e side α (S.arity α + 1))).vars, S.arity α ≤ x :=
    fun x hx => by
      rw [vars_menu_codeCellMenuE, Multiset.mem_nsmul_of_ne_zero (by omega),
        Multiset.mem_Ico] at hx
      omega
  have hc : ∀ x ∈
      (code (codeKeyE e side α) (menu (codeMenusE e side (codeMenuBaseE e side α)))).vars,
      S.arity α ≤ x := fun x hx => by
    have hw := (codeTreeE_wires e side α).2
    rw [vars_code, vars_menu_codeMenusE] at hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · rcases Multiset.mem_add.1 hx with hx | hx
      · rw [Multiset.mem_nsmul_of_ne_zero (by omega), Multiset.mem_Ico] at hx
        have : S.arity α ≤ codeMenuBaseE e side α := by unfold codeMenuBaseE; omega
        omega
      · exact hw x (Multiset.mem_add.2 (Or.inr hx))
    · exact hw x (Multiset.mem_add.2 (Or.inr hx))
  rw [codeTreeE_eq_tree, codeTreeELeaves, bind_mkDup, bind_mkCon, bind_cellSel, bind_mux,
    keep _ hΓ]
  have hl : ((var (S.arity α) : Term sig ℕ).bind fun x =>
      if h : x < S.arity α then args ⟨x, h⟩ else var x) = var (S.arity α) := by
    simp
  have hp : (fun j : Fin (S.arity α) => (var (j : ℕ) : Term sig ℕ).bind fun x =>
      if h : x < S.arity α then args ⟨x, h⟩ else var x) = args :=
    funext fun j => by simp [j.isLt]
  simp only [List.map_cons, List.map_append, List.map_ofFn, List.map_nil, keep _ hc, hl,
    Function.comp_def, hp]

/-- **The root of the principal net `[α]` is the `dup` cell of `T_{1,1}`** (Fig. 10, page 89), for
any numbering `e`. -/
theorem codeNetE_tree_eq_mkDup (α : S.Sym) :
    ∃ a b, (codeNetE e side α).tree = mkDup a b := by
  have key : ∀ {ν : Type} (t : Term sig ℕ) (f : ℕ → Term sig ν), (∃ a b, t = mkDup a b) →
      ∃ a b, t.bind f = mkDup a b := by
    rintro ν t f ⟨a, b, rfl⟩
    exact ⟨_, _, bind_mkDup f a b⟩
  exact key _ _ (codeTreeE_eq_mkDup e side α)

end General

section Symenum

variable {S : Signature} [Finite S.Sym]
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **`codeNet` is `codeNetE` at `symEnum S`** (Fig. 10, page 89), by `rfl`: the two have the same
tree, so the same ports in the same order. -/
theorem codeNet_eq_codeNetE (α : S.Sym) : codeNet side α = codeNetE (symEnum S) side α :=
  rfl

/-- **`codeWires` is `codeWiresE` at `symEnum S`** (page 89), by `rfl`. -/
theorem codeWires_eq_codeWiresE (α : S.Sym) (K : ℕ) :
    codeWires side α K = codeWiresE (symEnum S) side α K :=
  rfl

end Symenum

/-! ## Concrete checks on `sig` -/

/-- The leaves of a tree from left to right. -/
def leafList {ν : Type} : Term sig ν → List ν
  | .var x => [x]
  | .app _ ts => (List.ofFn fun i => leafList (ts i)).flatten

/-- The positions, in the list of leaves, of the ports of a principal net, with the port found
there. -/
def portsAt {k m : ℕ} (t : Term sig (Fin k ⊕ Fin m)) : List (ℕ × ℕ) :=
  (leafList t).zipIdx.filterMap fun p =>
    match p.1 with
    | .inl i => some (p.2, (i : ℕ))
    | .inr _ => none

/-- The tree of a principal net with its ports and wires sent to numbers, to compare principal nets
whose numbers of wires are not syntactically equal. -/
def flatTree {k m : ℕ} (t : Term sig (Fin k ⊕ Fin m)) : Term sig (ℕ ⊕ ℕ) :=
  t.bind fun x => var (Sum.map Fin.val Fin.val x)

/-- The root of a tree is a `dup` cell. -/
def rootIsDup {ν : Type} : Term sig ν → Bool
  | .app Comb.dup _ => true
  | _ => false

/-- The names of the wires of `[α]` shifted by `K`, in the order of the wires. -/
def wireNames {n : ℕ} (e : sig.Sym ≃ Fin n)
    (side : ∀ α : sig.Sym, sig.Sym → Option (ExpSide sig (sig.arity α))) (α : sig.Sym)
    (K : ℕ) : List ℕ :=
  (List.finRange (codeNetE e side α).internal).map (codeWiresE e side α K)

-- The numbers of internal wires: `(card of the names - k) / 2`, the same under both numberings.
#guard ([sideConDup, sideAsym].map fun side => [Comb.con, Comb.dup, Comb.era].map fun α : Comb =>
  ((codeNetE combEnum side α).internal, (codeNetE combEnum₂ side α).internal,
    ((codeTreeE combEnum side α).vars.card - sig.arity α) / 2))
  == [[(40, 40, 40), (64, 64, 64), (40, 40, 40)], [(103, 103, 103), (103, 103, 103), (79, 79, 79)]]

-- The ports `0, …, k - 1` occur once each, in this order, at the same positions of the list of
-- leaves under both numberings; the root is a `dup` cell; the multisets of cells are equal.
#guard [sideConDup, sideAsym].all fun side => [Comb.con, Comb.dup, Comb.era].all fun α : Comb =>
  portsAt (codeNetE combEnum side α).tree == portsAt (codeNetE combEnum₂ side α).tree &&
    (portsAt (codeNetE combEnum side α).tree).map Prod.snd == List.range (sig.arity α) &&
    rootIsDup (codeNetE combEnum side α).tree && rootIsDup (codeNetE combEnum₂ side α).tree &&
    decide ((codeNetE combEnum side α).tree.cells = (codeNetE combEnum₂ side α).tree.cells)

-- Where the ports are, for `sideConDup`: in `[con]` (82 leaves) and `[dup]` (130 leaves) the two
-- ports are leaves `78, 79` and `126, 127`, after the leaves of `Γ_α` and of `!Γ`; the last two
-- leaves are the two ends of the loop (the last leaf of `M_4` and the right port of `T_{1,1}`),
-- which is the smallest internal name `k`, so the wire `0`. `[era]` has no port.
#guard [Comb.con, Comb.dup, Comb.era].map (fun α : Comb =>
    (portsAt (codeNetE combEnum sideConDup α).tree,
      (leafList (codeNetE combEnum sideConDup α).tree).length)) ==
  [([(78, 0), (79, 1)], 82), ([(126, 0), (127, 1)], 130), ([], 80)]

#guard [Comb.con, Comb.dup, Comb.era].all fun α : Comb =>
  ((leafList (codeNetE combEnum sideConDup α).tree).drop
      ((leafList (codeNetE combEnum sideConDup α).tree).length - 2)).map
    (Sum.map Fin.val Fin.val) == [.inr 0, .inr 0]
-- `codeNetE_inst`, evaluated: the instance with the ports `0, …` and the wires named back by
-- `wireNum` is the tree of Fig. 10, for every symbol, numbering and choice of sides.
#guard [sideConDup, sideAsym].all fun side => [Comb.con, Comb.dup, Comb.era].all fun α : Comb =>
  [combEnum, combEnum₂].all fun e =>
    decide ((codeNetE e side α).inst (fun i => var (i : ℕ))
      (fun w => ((wireNum (sig.arity α) (codeTreeE e side α)).symm w).1) = codeTreeE e side α)

-- The two `[α]` are different trees even after the wires are renumbered by `treePNet`: the
-- selectors and the order of the menus inside `!Γ` depend on the numbering.
#guard [Comb.con, Comb.dup, Comb.era].all fun α : Comb =>
  decide (flatTree (codeNetE combEnum sideConDup α).tree ≠
    flatTree (codeNetE combEnum₂ sideConDup α).tree)

/-! ## Refutation attempts on `codeWiresE` -/

-- `codeWiresE_injective`: the wires get distinct names, which are the internal names of the tree,
-- in increasing order, shifted by `K`; at `K = 0` and `K = 7`, for every symbol (`era` has arity
-- `0`: its loop is the name `0`, an internal wire).
#guard [0, 7].all fun K => [Comb.con, Comb.dup, Comb.era].all fun α : Comb =>
  [combEnum, combEnum₂].all fun e =>
    (wireNames e sideConDup α K).Nodup &&
      wireNames e sideConDup α K ==
        ((wireSet (sig.arity α) (codeTreeE e sideConDup α)).sort (· ≤ ·)).map (K + ·)

-- `codeWiresE_lt` and `le_codeWiresE` are sharp: the largest wire is `K + sup` and the smallest
-- is `K + k` (the loop), so for `era` the bound `K ≤ _` is attained.
#guard [0, 7].all fun K => [Comb.con, Comb.dup, Comb.era].all fun α : Comb =>
  (wireNames combEnum sideConDup α K).max? ==
      some (K + (codeTreeE combEnum sideConDup α).vars.sup) &&
    (wireNames combEnum sideConDup α K).min? == some (K + sig.arity α)

/-! ## Instances of the theorems -/

/-- `codeNetE_inst` at `combEnum₂` and `sideAsym` (page 89). -/
example (α : sig.Sym) : (codeNetE combEnum₂ sideAsym α).inst (fun i => var (i : ℕ))
      (fun w => ((wireNum (sig.arity α) (codeTreeE combEnum₂ sideAsym α)).symm w).1) =
    codeTreeE combEnum₂ sideAsym α :=
  codeNetE_inst combEnum₂ sideAsym α

/-- `codeNetE_strict` at `combEnum₂` and `sideAsym`, for `era` (page 80). -/
example : (codeNetE combEnum₂ sideAsym (Comb.era : sig.Sym)).Strict :=
  codeNetE_strict combEnum₂ sideAsym _

set_option maxRecDepth 8000 in
/-- `codeNetE_inst_args` at `combEnum₂` and `sideConDup`, for `con`: the trees `a`, `b` land on the
two leaves of `M_4` after `!Γ`, `a` first. -/
example (a b : Term sig ℕ) :
    (codeNetE combEnum₂ sideConDup (Comb.con : sig.Sym)).inst ![a, b]
        (fun w => ((wireNum 2 (codeTreeE combEnum₂ sideConDup Comb.con)).symm w).1) =
      mkDup (mkCon (menu (codeCellMenuE combEnum₂ sideConDup Comb.con 3))
          (cellSel 3 (combEnum₂ Comb.con)
            (mux (code (codeKeyE combEnum₂ sideConDup Comb.con)
              (menu (codeMenusE combEnum₂ sideConDup (codeMenuBaseE combEnum₂ sideConDup
                Comb.con))) :: [a, b, var 2]))))
        (var 2) :=
  codeNetE_inst_args combEnum₂ sideConDup (Comb.con : sig.Sym) ![a, b]

/-- `codeWiresE_injective` and `codeWiresE_lt` at `combEnum₂` and `sideAsym`, for `era`. -/
example (K : ℕ) : Function.Injective (codeWiresE combEnum₂ sideAsym (Comb.era : sig.Sym) K) ∧
    ∀ w, codeWiresE combEnum₂ sideAsym (Comb.era : sig.Sym) K w <
      K + ((codeTreeE combEnum₂ sideAsym Comb.era).vars.sup + 1) :=
  ⟨codeWiresE_injective combEnum₂ sideAsym _ K, codeWiresE_lt combEnum₂ sideAsym _ K⟩

end INet.Comb.CodeNetEReview
