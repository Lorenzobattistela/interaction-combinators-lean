import InteractionCombinators.Universality.General.CodeCellsMeet
import InteractionCombinators.Universality.General.CodeData
import Checks.Universality.RecursionFree.RecursionFreeFig7Check

/-!
# Check of `codeCells_meet` (pages 89–90)

The hypothesis of `codeCells_meet` can be met: for the full system of interaction combinators
(not recursion-free, page 87) with the sides chosen by its decomposition data
(`System.WellFormed.decData`, `CodeData.lean`), the principal nets `[con]` and `[dup]` of Fig. 10,
plugged by their roots, with the names `0, 1` and `2, 3` on their ports and their internal wires
named from `4` and right after, form a linear net. The side of `con` against `dup` exists, so the
package `Γ_{con,dup}` met by the multiplexor of `[con]` is a `codeGamma`, to which
`codeCells_meet_gamma` applies.
-/

namespace INet.Comb.CodeCellsMeetCheck

open Term Translation RecursionFreeFig7Check

/-- The sides of the decomposition data of the full system (pages 86, 90). -/
noncomputable abbrev sd := (System.WellFormed.decData system_wellFormed).side

/-- `[con]` against `[dup]` of Fig. 10, ports `0, 1` and `2, 3`, internal wires from `4`. -/
noncomputable def netConDup : CNet :=
  {s((codeNet sd Comb.con).inst (fun i => .var (zeroOne i)) fromFour,
    (codeNet sd Comb.dup).inst (fun j => .var (twoThree j))
      (afterFour (codeNet sd Comb.con).internal))}

/-- **The hypothesis of `codeCells_meet` holds** for `[con]` against `[dup]`. -/
theorem linear_netConDup : netConDup.Linear := by
  refine linear_blocks _ _ zeroOne twoThree ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [zeroOne]
  · intro j; fin_cases j <;> simp [twoThree]
  · intro z
    simp only [Fin.sum_univ_two, zeroOne, twoThree, Matrix.cons_val_zero, Matrix.cons_val_one]
    by_cases h0 : z = 0 <;> by_cases h1 : z = 1 <;> by_cases h2 : z = 2 <;>
      by_cases h3 : z = 3 <;> simp [h0, h1, h2, h3]

/-- **`codeCells_meet` applies to `[con]` against `[dup]`** (Fig. 10, pages 89–90). -/
theorem codeCells_meet_conDup :
    ∃ (K K' : ℕ) (M : CNet), StepsE system netConDup M ∧
      Equiv M
        (s(mux ((code (codeKey sd Comb.con) (menu (codeMenus sd (codeMenuBase sd Comb.con)))).bind
                (fun x => var (codeRen zeroOne K x)) ::
              List.ofFn (fun i => (var (zeroOne i) : Term sig ℕ)) ++ [var (K + 2)]),
            (codeGammaOpt (Nat.card sig.Sym) (fun γ => symEnum sig γ) (sd Comb.con Comb.dup)
              (2 + 1 + off (codeCellSizes sd Comb.dup) (symEnum sig Comb.con))).bind
                (fun x => var (codeRen twoThree K' x))) ::ₘ
          s(mux ((code (codeKey sd Comb.dup) (menu (codeMenus sd (codeMenuBase sd Comb.dup)))).bind
                (fun x => var (codeRen twoThree K' x)) ::
              List.ofFn (fun j => (var (twoThree j) : Term sig ℕ)) ++ [var (K + 2)]),
            (codeGammaOpt (Nat.card sig.Sym) (fun γ => symEnum sig γ) (sd Comb.dup Comb.con)
              (2 + 1 + off (codeCellSizes sd Comb.con) (symEnum sig Comb.dup))).bind
                (fun x => var (codeRen zeroOne K x))) ::ₘ 0) :=
  codeCells_meet sd Comb.con Comb.dup zeroOne twoThree _ _ 0 linear_netConDup

/-- The side of `con` against `dup` exists (rule `con`–`dup`, page 86), so `Γ_{con,dup}` is a
`codeGamma` and `codeCells_meet_gamma` applies to it. -/
example : ∃ s, sd Comb.con Comb.dup = some s :=
  Option.isSome_iff_exists.1 ((System.DecData.side_isSome_iff _ _ _).2 (Or.inl ⟨_, rfl⟩))

end INet.Comb.CodeCellsMeetCheck
