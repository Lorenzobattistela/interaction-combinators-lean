import Checks.CodeGammaReview

/-!
# Check: the menus of Fig. 10 for a hand-written enumeration of the symbols

`codeMenusE e side` (`Lafont/CodeGamma.lean`) takes the numbering `e : S.Sym ≃ Fin n` of the
symbols as an argument and is computable. For the interaction combinators, with the numbering
`con, dup, era ↦ 0, 1, 2` written by hand and the side `sideConDup` (the rule `con`–`dup`, four
cells, and no other side), the number of menus and the number of names of the menus are computed by
`decide` and by the compiler, with no lemma about `symEnum` (Fig. 10, page 89; page 90: "no order on
the symbols is needed").
-/

namespace INet.Comb.CodeMenusECheck

open Term CodeGammaReview

/-- The numbering `con, dup, era ↦ 0, 1, 2` of the symbols of the interaction combinators. -/
def combEnum : sig.Sym ≃ Fin 3 where
  toFun
    | .con => 0
    | .dup => 1
    | .era => 2
  invFun i := match i with
    | 0 => (Comb.con : sig.Sym)
    | 1 => (Comb.dup : sig.Sym)
    | 2 => (Comb.era : sig.Sym)
  left_inv α := by cases α <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- There are three menus `Γ_con, Γ_dup, Γ_era` (Fig. 10, page 89). -/
theorem length_codeMenusE_combEnum : (codeMenusE combEnum sideConDup 0).length = 3 := by
  decide

/-- The compiler accepts the menus: their number, evaluated. -/
example : (codeMenusE combEnum sideConDup 0).length = 3 := by
  rfl

/-- The menus of Fig. 10 for `sideConDup` have `24` names in all: none for `Γ_con` and `Γ_era`
(erasers only), and the `24` names of `Γ_{con,dup}` for `Γ_dup` (page 89). -/
theorem codeMenuSizesE_combEnum :
    List.ofFn (codeMenuSizesE combEnum sideConDup) = [0, 24, 0] ∧
      ∑ i, codeMenuSizesE combEnum sideConDup i = 24 := by
  decide

-- The compiler evaluates the menus (they are not `noncomputable`): the sizes and the number of
-- menus.
#guard (List.ofFn (codeMenuSizesE combEnum sideConDup),
  (codeMenusE combEnum sideConDup 0).length) == ([0, 24, 0], 3)

end INet.Comb.CodeMenusECheck
