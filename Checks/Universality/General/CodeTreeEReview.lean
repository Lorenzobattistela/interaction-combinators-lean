import Checks.Universality.General.CodeTreeECheck
import Checks.Universality.Codes.CodeMenusEReview

/-!
# Review of the tree `[α]` of Fig. 10 for a given enumeration `e : S.Sym ≃ Fin n` (pages 89-90)

Review of `codeMenuBaseE`, `codeKeyE` and `codeTreeE`
(`InteractionCombinators/Universality/General/CodeTr.lean`, section `Enum`) against Fig. 10 (journal
page 89, PDF page 21, top left, rendered alone at 600 dpi) and the text of page 90.

Fig. 10 draws `[α_i]` as the transpositor `T_{1,1}` whose three auxiliary ports carry, from left
to right, the menu `Γ_i`, the selector `S^i_m` and a wire that goes up on the right and comes back
as the last auxiliary port of the multiplexor `M_{n_i+2}`, the loop. The root of `M_{n_i+2}` is the
free port of `S^i_m`; its auxiliary ports are, from left to right, the package `!Γ`, the `n_i` ports
of the cell, and the loop. Here `m` is the number of symbols.

* `codeTreeE_eq_tree` — for every `e`, `codeTreeE e side α` is, written out, `T_{1,1}` (a `dup`
  cell on a `con` cell, `transpositor 1`) on `Γ_α`, `S^{e α}_n` applied to `M` and the loop; the
  leaves of `M` are `!Γ`, the ports `0, …, k - 1` and the loop `k`, where `k = S.arity α`.
  `length_codeTreeELeaves`: there are `k + 2` of them. `cellSel_selects`: the selector has `n`
  auxiliary ports (`n` is the number of symbols of `e`) and `M` sits on the one numbered `e α`.
  So the code is right. **Docstring defect** (fixed in this PR, no statement changed): the
  docstring of `codeTreeE` wrote `e : S.Sym ≃ Fin m`, `S^α_m`, `M_{n+2}` and "here
  `n = S.arity α`", while in the code `n` is the number of symbols (`e : S.Sym ≃ Fin n`, and `n` is
  the first argument of `cellSel`); the docstrings of `codeMenuBaseE` and `vars_codeTreeE` also
  called the arity `n`. They now write `k = S.arity α`.
* `codeKeyE_blocks` — the bounds for the three symbols of `sig` under `combEnum` and `combEnum₂`;
  the `#guard`s below check that the names of `Γ_α` lie in `[k + 1, codeMenuBaseE)`, those of `Γ`
  in `[codeMenuBaseE, codeKeyE)`, the cut names of `!Γ` at or above `codeKeyE`, and that the ports
  and the loop are `[0, k]`, for each symbol, under both numberings and both choices of sides
  (`sideConDup`, `sideAsym`).
* Two numberings (`combEnum`: `con, dup, era ↦ 0, 1, 2`; `combEnum₂`: `dup, con, era ↦ 0, 1, 2`):
  the bounds are the same, the names below `codeKeyE` (ports, loop, `Γ_α`, `Γ`) are the same
  multiset, the numbers of names are equal and the multisets of cells are equal (`#guard`). The
  cut names of `!Γ` are not the same numbers (`[43, …, 173]` under `combEnum` against
  `[39, …, 169]` under `combEnum₂` for `[era]`): `decomp` numbers them by the position of the cut
  cells in `Γ`. They are internal wires, each twice, and `treePNet` renumbers them, so this is
  harmless. The trees differ: for `con` and `dup` by the selector index, and for every symbol,
  `era` included, by the menu `Γ` inside `!Γ`, whose menus are listed in the order of `e`. They
  differ in two more ways than the issue says: the cut names above, and the packages `⟨α_k⟩`
  inside each `Γ_{i,j}`, which carry the selector `S^{e α_k}_m` (already found in the review of
  the menus, `codeGamma_idx_ne`). This is harmless: `[β]` selects with the same number `e β`.
  Page 90 does not say in words that the numbering is harmless; nothing in Fig. 10 needs an order on
  the symbols (see `Checks/Universality/Codes/CodeMenusEReview.lean`).
* The theorems `vars_codeTreeE`, `codeTreeE_wires`, `codeTreeE_hyps`, `codeTreeE_eq_mkDup`,
  `codeTreeE_ne_var` have no hypotheses beyond `e`, `side`, `α`; they are instantiated on
  `combEnum`, `combEnum₂` and `sideConDup`, `sideAsym`.

Not checked: that `[α]` reduces as in Fig. 7 (the analogue for Fig. 10 is left to the reader on
page 90, and is the subject of step 6c and later).
-/

namespace INet.Comb.CodeTreeEReview

open Term CodeGammaReview CodeMenusECheck CodeMenusEReview

/-! ## The shape of the tree, for every numbering -/

section General

variable {S : Signature} {n : ℕ} (e : S.Sym ≃ Fin n)
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- The leaves of the multiplexor `M_{k+2}` of `[α]` (Fig. 10, page 89), from left to right: the
code `!Γ`, the ports `0, …, k - 1` and the loop `k`, where `k = S.arity α`. -/
def codeTreeELeaves (α : S.Sym) : List (Term sig ℕ) :=
  code (codeKeyE e side α) (menu (codeMenusE e side (codeMenuBaseE e side α))) ::
    ((List.ofFn fun j : Fin (S.arity α) => var (j : ℕ)) ++ [var (S.arity α)])

/-- **The tree of `[α]` written out** (Fig. 10, page 89): `T_{1,1}`, that is a `dup` cell whose
left auxiliary port is a `con` cell, carries the menu `Γ_α` (names from `k + 1`), the selector
`S^{e α}_n` applied to the multiplexor on `codeTreeELeaves`, and the loop `k`. -/
theorem codeTreeE_eq_tree (α : S.Sym) :
    codeTreeE e side α =
      mkDup (mkCon (menu (codeCellMenuE e side α (S.arity α + 1)))
        (cellSel n (e α) (mux (codeTreeELeaves e side α)))) (var (S.arity α)) :=
  rfl

/-- **The multiplexor of `[α]` has `k + 2` leaves** (Fig. 10, page 89: `M_{n_i+2}`). -/
theorem length_codeTreeELeaves (α : S.Sym) :
    (codeTreeELeaves e side α).length = S.arity α + 2 := by
  simp [codeTreeELeaves]

/-- The leaves of `M_{k+2}` in order (Fig. 10, page 89): leaf `0` is `!Γ`, leaf `j + 1` is the
port `j` for `j < k`, and leaf `k + 1` is the loop `k`. -/
theorem getElem_codeTreeELeaves (α : S.Sym) :
    (codeTreeELeaves e side α)[0]'(by simp [codeTreeELeaves]) =
        code (codeKeyE e side α) (menu (codeMenusE e side (codeMenuBaseE e side α))) ∧
      (∀ j : Fin (S.arity α),
        (codeTreeELeaves e side α)[(j : ℕ) + 1]'(by simp [codeTreeELeaves]) =
          var (j : ℕ)) ∧
      (codeTreeELeaves e side α)[S.arity α + 1]'(by simp [codeTreeELeaves]) =
        var (S.arity α) := by
  refine ⟨rfl, fun j => ?_, ?_⟩
  · simp [codeTreeELeaves, List.getElem_append_left, j.isLt]
  · simp [codeTreeELeaves, List.getElem_append_right]

/-- **The selector is `S^i_n` with `n` the number of symbols** (Fig. 10, page 89; selector,
page 84): `cellSel n i t` is `M_n*` on `n` trees, `t` on the auxiliary port `i` and erasers
elsewhere. In `[α]`, `i = e α`. -/
theorem cellSel_selects (i : Fin n) (t : Term sig ℕ) :
    cellSel n i t = muxStar (List.replicate i mkEra ++ t :: List.replicate (n - i - 1) mkEra) ∧
      (List.replicate i mkEra ++ t :: List.replicate (n - i - 1) mkEra).length = n ∧
      (List.replicate i mkEra ++ t :: List.replicate (n - i - 1) mkEra)[(i : ℕ)]'(by
        simp) = t := by
  refine ⟨rfl, by simp; omega, by simp [List.getElem_append_right]⟩

end General

/-! ## The name blocks, on concrete systems -/

/-- **The bounds of the name blocks** (page 89) for `con`, `dup`, `era` (arities `2, 2, 0`) under
the numberings `combEnum` and `combEnum₂` and the sides `sideConDup`: the same under both
numberings, and in the order ports `<` loop `<` `codeMenuBaseE ≤ codeKeyE`. -/
theorem codeKeyE_blocks :
    [codeMenuBaseE combEnum sideConDup (Comb.con : sig.Sym),
        codeMenuBaseE combEnum sideConDup (Comb.dup : sig.Sym),
        codeMenuBaseE combEnum sideConDup (Comb.era : sig.Sym),
        codeKeyE combEnum sideConDup (Comb.con : sig.Sym),
        codeKeyE combEnum sideConDup (Comb.dup : sig.Sym),
        codeKeyE combEnum sideConDup (Comb.era : sig.Sym)] = [3, 27, 1, 27, 51, 25] ∧
      [codeMenuBaseE combEnum₂ sideConDup (Comb.con : sig.Sym),
        codeMenuBaseE combEnum₂ sideConDup (Comb.dup : sig.Sym),
        codeMenuBaseE combEnum₂ sideConDup (Comb.era : sig.Sym),
        codeKeyE combEnum₂ sideConDup (Comb.con : sig.Sym),
        codeKeyE combEnum₂ sideConDup (Comb.dup : sig.Sym),
        codeKeyE combEnum₂ sideConDup (Comb.era : sig.Sym)] = [3, 27, 1, 27, 51, 25] := by
  decide

/-- Every name of `m` lies in `[lo, hi)`. -/
def inRange (m : Multiset ℕ) (lo hi : ℕ) : Bool := decide (∀ x ∈ m, lo ≤ x ∧ x < hi)

/-- The name blocks of `[α]` with the arity `k` and the bounds `B`, `K` given (page 89): the
names of `Γ_α` lie in `[k + 1, B)`, those of `Γ` in `[B, K)`, the cut names of `!Γ` at or above `K`,
and the leaves other than `!Γ` are `var 0, …, var k`. Evaluated by the compiler. -/
def blocksOkAt {n : ℕ} (e : sig.Sym ≃ Fin n)
    (side : ∀ α : sig.Sym, sig.Sym → Option (ExpSide sig (sig.arity α))) (α : sig.Sym)
    (k B K : ℕ) : Bool :=
  decide (k + 1 ≤ B) && decide (B ≤ K) &&
    inRange (Term.vars (menu (codeCellMenuE e side α (k + 1)))) (k + 1) B &&
    inRange (Term.vars (menu (codeMenusE e side B))) B K &&
    decide (∀ x ∈ (decomp K (menu (codeMenusE e side B))).ports, K ≤ x) &&
    decide ((codeTreeELeaves e side α).tail = (List.range (k + 1)).map var)

/-- The name blocks of `[α]` are disjoint and in order (page 89), at `k = S.arity α`,
`B = codeMenuBaseE`, `K = codeKeyE`. -/
def blocksOk {n : ℕ} (e : sig.Sym ≃ Fin n)
    (side : ∀ α : sig.Sym, sig.Sym → Option (ExpSide sig (sig.arity α))) (α : sig.Sym) : Bool :=
  blocksOkAt e side α (sig.arity α) (codeMenuBaseE e side α) (codeKeyE e side α)

#guard [Comb.con, Comb.dup, Comb.era].all fun α : Comb =>
  blocksOk combEnum sideConDup α && blocksOk combEnum₂ sideConDup α &&
    blocksOk combEnum sideAsym α && blocksOk combEnum₂ sideAsym α

-- The blocks are not empty where the sides are present: under `sideAsym`, `Γ_con` and `Γ_dup`
-- have `24` names each, and `Γ` has `48`.
#guard [Comb.con, Comb.dup, Comb.era].map (fun α : Comb =>
    (codeMenuBaseE combEnum sideAsym α, codeKeyE combEnum sideAsym α)) ==
  [(27, 75), (27, 75), (1, 49)]

/-! ## Two numberings -/

-- The bounds, the names below `codeKeyE` (ports, loop, `Γ_α`, `Γ`), the number of names and the
-- multiset of cells of `[α]` do not depend on the numbering (page 90), for both choices of sides.
#guard [Comb.con, Comb.dup, Comb.era].all fun α : Comb =>
  [sideConDup, sideAsym].all fun side =>
    decide (codeMenuBaseE combEnum side α = codeMenuBaseE combEnum₂ side α) &&
    decide (codeKeyE combEnum side α = codeKeyE combEnum₂ side α) &&
    decide ((codeTreeE combEnum side α).vars.filter (· < codeKeyE combEnum side α) =
      (codeTreeE combEnum₂ side α).vars.filter (· < codeKeyE combEnum side α)) &&
    decide ((codeTreeE combEnum side α).vars.card = (codeTreeE combEnum₂ side α).vars.card) &&
    decide ((codeTreeE combEnum side α).cells = (codeTreeE combEnum₂ side α).cells)

-- The cut names of `!Γ` are not the same numbers: `decomp` numbers them by the position of the
-- cut cells in `Γ`, which lists its menus in the order of `e`. Each occurs twice in both trees
-- (`codeTreeE_hyps`) and they are internal wires of `[α]` (`treePNet` renumbers them), so this is
-- harmless. For `[era]` and `sideConDup`, from `codeKeyE = 25` on:
#guard ((decomp 25 (menu (codeMenusE combEnum sideConDup 1))).ports.sort (· ≤ ·),
    (decomp 25 (menu (codeMenusE combEnum₂ sideConDup 1))).ports.sort (· ≤ ·)) ==
  ([43, 58, 73, 88, 103, 106, 119, 122, 125, 138, 141, 144, 157, 160, 173],
    [39, 54, 69, 84, 99, 102, 115, 118, 121, 134, 137, 140, 153, 156, 169])

-- The trees themselves differ, for every symbol: for `con` and `dup` the selector index changes,
-- and for all three the menu `Γ` inside `!Γ` lists its menus in the order of the numbering.
#guard [Comb.con, Comb.dup, Comb.era].all fun α : Comb =>
  decide (codeTreeE combEnum sideConDup α ≠ codeTreeE combEnum₂ sideConDup α)

-- `[era]` under `combEnum₂` is `[era]` under `combEnum` with the same `Γ_era`, the same selector
-- index `2`, and its own leaves: it differs only inside `!Γ`, the only leaf that can change.
#guard decide ((codeTreeE combEnum₂ sideConDup (Comb.era : sig.Sym)) =
    mkDup (mkCon (menu (codeCellMenuE combEnum sideConDup .era 1))
      (cellSel 3 2 (mux (codeTreeELeaves combEnum₂ sideConDup .era)))) (var 0))
#guard decide ((codeTreeELeaves combEnum₂ sideConDup (Comb.era : sig.Sym)).tail =
    (codeTreeELeaves combEnum sideConDup (Comb.era : sig.Sym)).tail)

/-! ## Instances of the theorems -/

/-- `vars_codeTreeE` on `combEnum₂` and `sideAsym`, for `dup`. -/
example : (codeTreeE combEnum₂ sideAsym .dup).vars = Multiset.Ico 0 2 +
    2 • (Multiset.Ico 2 75 +
      (decomp 75 (menu (codeMenusE combEnum₂ sideAsym 27))).ports) := by
  have h1 : codeKeyE combEnum₂ sideAsym (Comb.dup : sig.Sym) = 75 := by decide
  have h2 : codeMenuBaseE combEnum₂ sideAsym (Comb.dup : sig.Sym) = 27 := by decide
  have h := vars_codeTreeE combEnum₂ sideAsym (Comb.dup : sig.Sym)
  rw [h1, h2] at h
  exact h

/-- `codeTreeE_wires` on `combEnum` and `sideConDup`, for `con`. -/
example := codeTreeE_wires combEnum sideConDup (Comb.con : sig.Sym)

/-- `codeTreeE_hyps` on `combEnum₂` and `sideAsym`, for `con`. -/
example := codeTreeE_hyps combEnum₂ sideAsym (Comb.con : sig.Sym)

/-- `codeTreeE_eq_mkDup` on `combEnum` and `sideAsym`, for `era`. -/
example : ∃ a b, codeTreeE combEnum sideAsym (Comb.era : sig.Sym) = mkDup a b :=
  codeTreeE_eq_mkDup combEnum sideAsym _

/-- `codeTreeE_ne_var` on `combEnum₂` and `sideConDup`, for `dup`. -/
example : codeTreeE combEnum₂ sideConDup (Comb.dup : sig.Sym) ≠ var 0 :=
  codeTreeE_ne_var combEnum₂ sideConDup _ 0

/-- `codeTreeE_hyps` gives a principal net: `treePNet` applies to `[dup]` under `combEnum`. -/
example : PNet sig (sig.arity (Comb.dup : sig.Sym)) :=
  treePNet _ (codeTreeE combEnum sideConDup .dup) (codeTreeE_hyps combEnum sideConDup _).1
    (codeTreeE_hyps combEnum sideConDup _).2

end INet.Comb.CodeTreeEReview
