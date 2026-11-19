import Checks.CodeMenusECheck
import InteractionCombinators.Lafont.CodeTr

/-!
# Check: the tree of `[α]` of Fig. 10 for a hand-written enumeration of the symbols

`codeTreeE e side α` (`Lafont/CodeTr.lean`) takes the numbering `e : S.Sym ≃ Fin n` of the symbols
as an argument and is computable. For the interaction combinators, with the numbering
`con, dup, era ↦ 0, 1, 2` (`combEnum`) and the side `sideConDup` (the rule `con`–`dup` and no other
side), the bounds `codeMenuBaseE`, `codeKeyE` and the number of names of each tree are computed by
`decide` and by the compiler (Fig. 10, page 89).

The menu `Γ_dup` has the `24` names of `Γ_{con,dup}`, the others none; the menu `Γ` has `24` names;
its code `!Γ` has `15` cut names. So, for `α` of arity `n`, `[α]` has `n` ports and twice the
`codeKeyE - n` names of the loop, `Γ_α` and `Γ`, and the `15` cut names of `!Γ`.
-/

namespace INet.Comb.CodeTreeECheck

open Term CodeGammaReview CodeMenusECheck

/-- The first names of `Γ` and of the cut names of `!Γ` in `[con]`, `[dup]`, `[era]` (page 89):
`Γ` starts after the ports, the loop and `Γ_α` (`24` names for `dup`, none otherwise), and the cut
names start `24` names later. -/
theorem codeKeyE_combEnum :
    [codeMenuBaseE combEnum sideConDup (Comb.con : sig.Sym),
        codeMenuBaseE combEnum sideConDup (Comb.dup : sig.Sym),
        codeMenuBaseE combEnum sideConDup (Comb.era : sig.Sym)] = [3, 27, 1] ∧
      [codeKeyE combEnum sideConDup (Comb.con : sig.Sym),
        codeKeyE combEnum sideConDup (Comb.dup : sig.Sym),
        codeKeyE combEnum sideConDup (Comb.era : sig.Sym)] = [27, 51, 25] := by
  decide

-- The compiler evaluates the trees (they are not `noncomputable`): the numbers of names of
-- `[con]`, `[dup]`, `[era]` are `2 + 2 * (25 + 15)`, `2 + 2 * (49 + 15)` and `2 * (25 + 15)`.
-- (`decide` on these multisets of `80` to `130` names exceeds the recursion depth.)
#guard [(codeTreeE combEnum sideConDup (Comb.con : sig.Sym)).vars.card,
  (codeTreeE combEnum sideConDup (Comb.dup : sig.Sym)).vars.card,
  (codeTreeE combEnum sideConDup (Comb.era : sig.Sym)).vars.card] == [82, 130, 80]

-- The ports `0, 1` of `[dup]` occur once and the loop `2` twice, evaluated.
#guard (List.range 3).map (fun i =>
    (codeTreeE combEnum sideConDup (Comb.dup : sig.Sym)).vars.count i)
  == [1, 1, 2]

/-- The theorems of `CodeTr.lean` for any numbering apply to `combEnum`: the ports of `[dup]` occur
once and its other names twice (page 89). -/
example :
    (∀ i < sig.arity (Comb.dup : sig.Sym),
        (codeTreeE combEnum sideConDup (Comb.dup : sig.Sym)).vars.count i = 1) ∧
      ∀ x ∈ (codeTreeE combEnum sideConDup (Comb.dup : sig.Sym)).vars,
        sig.arity (Comb.dup : sig.Sym) ≤ x →
          (codeTreeE combEnum sideConDup (Comb.dup : sig.Sym)).vars.count x = 2 :=
  codeTreeE_hyps combEnum sideConDup _

end INet.Comb.CodeTreeECheck
