import Checks.CodeMenusECheck
import Checks.CodeGammaExtractCheck
import Checks.RecursionFreeFig7Check
import InteractionCombinators.Lafont.CodeGammaMeet

/-!
# Check: `codeGamma_extractE` and `codeCells_meet_endE` at `combEnum` (Fig. 10, pages 89–90)

`codeGamma_extractE` (`Lafont/CodeGammaExtract.lean`) and `codeCells_meet_endE`
(`Lafont/CodeGammaMeet.lean`) are the statements of `codeGamma_extract` and `codeCells_meet_end`
for any numbering `e : S.Sym ≃ Fin n` of the symbols. Here they are used at the hand-written
numbering `con, dup, era ↦ 0, 1, 2` (`combEnum`, from `CodeMenusECheck`), without `symEnum`.

* `gamma_extractE_conDup` — `codeGamma_extractE` on the rule `con`–`dup` read as a side (four
  cells), with the menus built from `sideConDup`: the hypothesis is proved, so the statement is not
  vacuous.
* `sideConDupSym` — `sideConDup` has no side of `dup` against `con`, so the hypotheses `hs`, `hs'`
  of `codeCells_meet_endE` cannot both hold for it at any pair of symbols. `sideConDupSym` adds
  the same side for `dup` against `con`; both have two middle ports and `σ = swap 0 1`.
* `meet_endE_conDup` — `codeCells_meet_endE` at `combEnum` and `sideConDupSym`, for `[con]`
  against `[dup]`, with any names and a linearity hypothesis.
* `meet_endE_conDup_concrete` — the same with the ports named `0, 1` and `2, 3`, the internal
  wires from `4`, and the linearity hypothesis proved.
-/

namespace INet.Comb.CodeGammaExtractECheck

open Term Translation CodeGammaReview CodeMenusECheck CodeGammaExtractCheck
  RecursionFreeFig7Check ExpandTrReview

/-! ## `codeGamma_extractE` -/

/-- **`codeGamma_extractE` at `combEnum`, on the rule `con`–`dup`** (Fig. 10, pages 89–90): the
rule `con`–`dup` read as a side with four cells (`k₀ = 0`, names `[0, 24)`), its four ports facing
the fresh wires `24`, …, `27`, and the copy of `!Γ` (for `Γ = codeMenusE combEnum sideConDup 0`)
renamed above `28`. The hypothesis holds (`codeGamma_extract_hyps`), so the net reduces to the four
equations `24 + q = t' q`, each `t' q` a translation by `codeTranslationE combEnum sideConDup` of
the tree of the side at the port `q`. -/
theorem gamma_extractE_conDup :
    ∃ (M : CNet) (t' : Fin 2 ⊕ Fin 2 → Term sig ℕ),
      StepsE system (s(copier (codeGammaExtras 3 (fun α => (combEnum α : ℕ)) ruleConDup 0),
        (code (0 + ∑ i, codeMenuSizesE combEnum sideConDup i)
          (menu (codeMenusE combEnum sideConDup 0))).bind fun x => var (28 + x)) ::ₘ
        ((∑ q, {s(var (24 + (finSumFinEquiv q : ℕ)),
          codePort 3 (fun α => (combEnum α : ℕ)) ruleConDup 0 q)}) + 0)) M ∧
      Equiv M ((∑ q, {s(var (24 + (finSumFinEquiv q : ℕ)), t' q)}) + 0) ∧
      ∀ q, (codeTranslationE combEnum sideConDup).TermTr (gammaTree ruleConDup 0 q) (t' q) := by
  set K := 0 + ∑ i, codeMenuSizesE combEnum sideConDup i
  have hb : (menu (codeMenusE combEnum sideConDup 0)).Below K :=
    menu_codeMenusE_below combEnum sideConDup 0
  have hC : (code K (menu (codeMenusE combEnum sideConDup 0))).IsPackage :=
    code_isPackage K _ (menu_codeMenusE_isPackage combEnum sideConDup 0) hb
  obtain ⟨hinj, hlin⟩ := codeGamma_extract_hyps 3 (fun α => (combEnum α : ℕ))
    ruleConDup_expanded ruleConDup_linear 0 _ hC
  have e : (0 : ℕ) + codeGammaSize ruleConDup = 24 := by
    rw [CodeGammaCheck.codeGammaSize_conDup]
  simp only [e, show (24 : ℕ) + (2 + 2) = 28 from rfl] at hinj hlin
  exact codeGamma_extractE combEnum sideConDup ruleConDup 0 0 K le_rfl _ hinj _ 0 hlin

/-! ## `codeCells_meet_endE` -/

/-- A choice of expanded sides for the interaction combinators with the side `con`–`dup` (four
cells, two middle ports, `σ = swap 0 1`) for both pairs `con, dup` and `dup, con`, and no side
elsewhere. Unlike `sideConDup`, it meets the hypotheses `hs`, `hs'` of `codeCells_meet_endE` at
`α = con`, `β = dup`. -/
def sideConDupSym : ∀ α : sig.Sym, sig.Sym → Option (ExpSide sig (sig.arity α))
  | .con, .dup => some ⟨2, ruleConDup, Equiv.swap 0 1, ruleConDup_linear, ruleConDup_expanded,
      GammaCheck.hs⟩
  | .dup, .con => some ⟨2, ruleConDup, Equiv.swap 0 1, ruleConDup_linear, ruleConDup_expanded,
      GammaCheck.hs⟩
  | _, _ => none

/-- `sideConDup` has no side of `dup` against `con`: the hypotheses `hs`, `hs'` of
`codeCells_meet_endE` cannot both hold for it at `con`, `dup`. -/
example : sideConDup (Comb.dup : sig.Sym) (Comb.con : sig.Sym) = none := rfl

/-- **`codeCells_meet_endE` at `combEnum` and `sideConDupSym`, `[con]` against `[dup]`** (Fig. 10,
pages 89–90): with any names on the ports and wires, in a linear context, the two cells reduce up
to wires to the two codes against the copiers, the ports against the trees of `⟨φ⟩`, and the
middle ports of the two copies of `⟨φ⟩` against each other through `σ = swap 0 1`. -/
theorem meet_endE_conDup (xs : Fin (sig.arity (Comb.con : sig.Sym)) → ℕ)
    (ys : Fin (sig.arity (Comb.dup : sig.Sym)) → ℕ)
    (f : Fin (codeNetE combEnum sideConDupSym (Comb.con : sig.Sym)).internal → ℕ)
    (g : Fin (codeNetE combEnum sideConDupSym (Comb.dup : sig.Sym)).internal → ℕ) (Δ : CNet)
    (hlin : Net.Linear (s((codeNetE combEnum sideConDupSym (Comb.con : sig.Sym)).inst
        (fun i => var (xs i)) f,
      (codeNetE combEnum sideConDupSym (Comb.dup : sig.Sym)).inst (fun j => var (ys j)) g) ::ₘ
        Δ)) :
    ∃ (K K' : ℕ) (M : CNet),
      StepsE system (s((codeNetE combEnum sideConDupSym (Comb.con : sig.Sym)).inst
          (fun i => var (xs i)) f,
        (codeNetE combEnum sideConDupSym (Comb.dup : sig.Sym)).inst (fun j => var (ys j)) g) ::ₘ
          Δ) M ∧
      Equiv M
        (s((code (codeKeyE combEnum sideConDupSym (Comb.con : sig.Sym))
              (menu (codeMenusE combEnum sideConDupSym
                (codeMenuBaseE combEnum sideConDupSym Comb.con)))).bind
              (fun x => var (codeRen xs K x)),
            copier (codeGammaExtras 3 (fun γ => (combEnum γ : ℕ)) ruleConDup
              (K' + (2 + 1 + off (codeCellSizesE combEnum sideConDupSym Comb.dup)
                (combEnum Comb.con))))) ::ₘ
          s((code (codeKeyE combEnum sideConDupSym (Comb.dup : sig.Sym))
              (menu (codeMenusE combEnum sideConDupSym
                (codeMenuBaseE combEnum sideConDupSym Comb.dup)))).bind
              (fun x => var (codeRen ys K' x)),
            copier (codeGammaExtras 3 (fun γ => (combEnum γ : ℕ)) ruleConDup
              (K + (2 + 1 + off (codeCellSizesE combEnum sideConDupSym Comb.con)
                (combEnum Comb.dup))))) ::ₘ
          ((Finset.univ.val.map fun p : Fin 2 =>
              s(var (xs p), codePort 3 (fun γ => (combEnum γ : ℕ)) ruleConDup
                (K' + (2 + 1 + off (codeCellSizesE combEnum sideConDupSym Comb.dup)
                  (combEnum Comb.con))) (.inl p))) +
            (Finset.univ.val.map fun q : Fin 2 =>
              s(var (ys q), codePort 3 (fun γ => (combEnum γ : ℕ)) ruleConDup
                (K + (2 + 1 + off (codeCellSizesE combEnum sideConDupSym Comb.con)
                  (combEnum Comb.dup))) (.inl q))) +
            (Finset.univ.val.map fun l : Fin 2 =>
              s(codePort 3 (fun γ => (combEnum γ : ℕ)) ruleConDup
                  (K' + (2 + 1 + off (codeCellSizesE combEnum sideConDupSym Comb.dup)
                    (combEnum Comb.con))) (.inr l),
                codePort 3 (fun γ => (combEnum γ : ℕ)) ruleConDup
                  (K + (2 + 1 + off (codeCellSizesE combEnum sideConDupSym Comb.con)
                    (combEnum Comb.dup))) (.inr (Equiv.swap 0 1 l)))) + Δ)) :=
  codeCells_meet_endE combEnum sideConDupSym Comb.con Comb.dup xs ys f g Δ ruleConDup ruleConDup
    (Equiv.swap 0 1) GammaCheck.hs ruleConDup_linear ruleConDup_expanded ruleConDup_linear
    ruleConDup_expanded rfl rfl hlin

/-- `[con]` against `[dup]` of Fig. 10 at `combEnum` and `sideConDupSym`, ports `0, 1` and `2, 3`,
internal wires from `4`. -/
def netConDupE : CNet :=
  {s((codeNetE combEnum sideConDupSym (Comb.con : sig.Sym)).inst (fun i => .var (zeroOne i))
      fromFour,
    (codeNetE combEnum sideConDupSym (Comb.dup : sig.Sym)).inst (fun j => .var (twoThree j))
      (afterFour (codeNetE combEnum sideConDupSym (Comb.con : sig.Sym)).internal))}

/-- The hypothesis of `codeCells_meet_endE` holds for `netConDupE`. -/
theorem linear_netConDupE : netConDupE.Linear := by
  refine linear_blocks _ _ zeroOne twoThree ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [zeroOne]
  · intro j; fin_cases j <;> simp [twoThree]
  · intro z
    simp only [Fin.sum_univ_two, zeroOne, twoThree, Matrix.cons_val_zero, Matrix.cons_val_one]
    by_cases h0 : z = 0 <;> by_cases h1 : z = 1 <;> by_cases h2 : z = 2 <;>
      by_cases h3 : z = 3 <;> simp [h0, h1, h2, h3]

/-- **`codeCells_meet_endE` applies to a concrete net** (Fig. 10, pages 89–90): `[con]` against
`[dup]` at `combEnum` and `sideConDupSym`, ports `0, 1` and `2, 3`, internal wires from `4`, with
the linearity hypothesis proved (`linear_netConDupE`), reduces to a net of the stated form; here
only the existence of the reduction is restated. -/
theorem meet_endE_conDup_concrete : ∃ (K K' : ℕ) (M : CNet), StepsE system netConDupE M ∧
    Equiv M
      (s((code (codeKeyE combEnum sideConDupSym (Comb.con : sig.Sym))
            (menu (codeMenusE combEnum sideConDupSym
              (codeMenuBaseE combEnum sideConDupSym Comb.con)))).bind
            (fun x => var (codeRen zeroOne K x)),
          copier (codeGammaExtras 3 (fun γ => (combEnum γ : ℕ)) ruleConDup
            (K' + (2 + 1 + off (codeCellSizesE combEnum sideConDupSym Comb.dup)
              (combEnum Comb.con))))) ::ₘ
        s((code (codeKeyE combEnum sideConDupSym (Comb.dup : sig.Sym))
            (menu (codeMenusE combEnum sideConDupSym
              (codeMenuBaseE combEnum sideConDupSym Comb.dup)))).bind
            (fun x => var (codeRen twoThree K' x)),
          copier (codeGammaExtras 3 (fun γ => (combEnum γ : ℕ)) ruleConDup
            (K + (2 + 1 + off (codeCellSizesE combEnum sideConDupSym Comb.con)
              (combEnum Comb.dup))))) ::ₘ
        ((Finset.univ.val.map fun p : Fin 2 =>
            s(var (zeroOne p), codePort 3 (fun γ => (combEnum γ : ℕ)) ruleConDup
              (K' + (2 + 1 + off (codeCellSizesE combEnum sideConDupSym Comb.dup)
                (combEnum Comb.con))) (.inl p))) +
          (Finset.univ.val.map fun q : Fin 2 =>
            s(var (twoThree q), codePort 3 (fun γ => (combEnum γ : ℕ)) ruleConDup
              (K + (2 + 1 + off (codeCellSizesE combEnum sideConDupSym Comb.con)
                (combEnum Comb.dup))) (.inl q))) +
          (Finset.univ.val.map fun l : Fin 2 =>
            s(codePort 3 (fun γ => (combEnum γ : ℕ)) ruleConDup
                (K' + (2 + 1 + off (codeCellSizesE combEnum sideConDupSym Comb.dup)
                  (combEnum Comb.con))) (.inr l),
              codePort 3 (fun γ => (combEnum γ : ℕ)) ruleConDup
                (K + (2 + 1 + off (codeCellSizesE combEnum sideConDupSym Comb.con)
                  (combEnum Comb.dup))) (.inr (Equiv.swap 0 1 l)))) + 0)) :=
  meet_endE_conDup zeroOne twoThree _ _ 0 linear_netConDupE

end INet.Comb.CodeGammaExtractECheck
