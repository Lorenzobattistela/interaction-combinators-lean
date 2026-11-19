import Checks.CodeMenusECheck
import Checks.CodeTermExtractCheck

/-!
# Check: `codeTerm_extractE` for a hand-written enumeration of the symbols (Fig. 10, page 90)

`codeTerm_extractE` (`Lafont/CodeTermExtract.lean`) takes the numbering `e : S.Sym ≃ Fin n` of the
symbols as an argument. Here it is applied, with no lemma about `symEnum`, to the interaction
combinators with the numbering `combEnum` (`con, dup, era ↦ 0, 1, 2`, from `CodeMenusECheck`), the
side `sideConDup` (the rule `con`–`dup`, from `CodeGammaReview`), and the concrete tree
`con(dup(0, 1), 2)` of two cells (`tConDup`, from `CodeTermExtractCheck`): `⟨t⟩` with a copy of
`!Γ` on each of its two extra ports reduces to a translation of `t` by `codeTranslationE`. The
hypotheses of `codeTerm_extractE` are met by `codeTerm_extract_hyps`, which does not mention the
enumeration.
-/

namespace INet.Comb.CodeTermExtractECheck

open Term Translation CodeGammaReview CodeMenusECheck CodeTermExtractCheck

/-- **`codeTerm_extractE` at `combEnum` and `sideConDup`, on the tree `con(dup(0, 1), 2)`**
(Fig. 10, page 90): `⟨t⟩` (new names from `4`, the cells selecting the menus by `combEnum`), with
the fresh name `3` on its principal port and a copy of `!Γ` (for `Γ = codeMenusE combEnum
sideConDup 0`) on each extra port, reduces to a net that is `Equiv` to `3 = t'`, with `t'` a
translation of `t` by `codeTranslationE combEnum sideConDup`. -/
theorem extractE_conDup :
    ∃ (K : ℕ) (fs : List (ℕ → ℕ)) (M : CNet) (t' : Term sig ℕ),
      StepsE system (s(var 3, codeTerm 3 (fun α => (combEnum α : ℕ)) 4 tConDup) ::ₘ
          (codeCopies (code K (menu (codeMenusE combEnum sideConDup 0)))
            (codeExtras 3 (fun α => (combEnum α : ℕ)) 4 tConDup) fs + 0)) M ∧
        Equiv M (s(var 3, t') ::ₘ 0) ∧
        (codeTranslationE combEnum sideConDup).TermTr tConDup t' := by
  set K := 0 + ∑ i, codeMenuSizesE combEnum sideConDup i
  set Γ := menu (codeMenusE combEnum sideConDup 0)
  have hΓK : Γ.Below K := menu_codeMenusE_below combEnum sideConDup 0
  set W := (decomp K Γ).k + 4 + codeSize tConDup
  have hC : (code K Γ).IsPackage :=
    code_isPackage K Γ (menu_codeMenusE_isPackage combEnum sideConDup 0) hΓK
  have hCW : (code K Γ).Below W := fun x hx => by
    have := code_below K Γ hΓK x hx; omega
  obtain ⟨h1, h2, h3⟩ := codeTerm_extract_hyps 3 (fun α => (combEnum α : ℕ)) (code K Γ)
    hC W hCW tConDup 4 3 (by simp [tConDup]) (by intro x hx; simp [tConDup] at hx; omega)
    (by omega)
  obtain ⟨M, t', hS, hE, hT⟩ :=
    codeTerm_extractE combEnum sideConDup 0 K le_rfl tConDup 4 (var 3) _ 0 h1 h2 h3
  exact ⟨K, _, M, t', hS, hE, hT⟩

end INet.Comb.CodeTermExtractECheck
