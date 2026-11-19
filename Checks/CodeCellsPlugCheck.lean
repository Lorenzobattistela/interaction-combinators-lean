import InteractionCombinators.Lafont.CodeCellsPlug
import Checks.CodeGammaMeetCheck

/-!
# Check of `codeCells_plug` (pages 89–90)

`codeCells_plug` applied with every hypothesis proved, on the interaction combinators with the
sides `sd` of their decomposition data, for `[dup]` against `[dup]` (ports `0, 1` and `2, 3`,
internal wires from `4`, the net `netDupDup` of `CodeGammaMeetCheck`). The rule `dup`–`dup` exists
(page 86), so the side `s` of `dup` against itself exists, and it is the side on both sides of the
meeting: `hs` and `hs'` are the same equation. The linearity hypothesis is `linear_netDupDup`.
-/

namespace INet.Comb.CodeCellsPlugCheck

open Term Translation CodeCellsMeetCheck CodeGammaMeetCheck RecursionFreeFig7Check

/-- **`codeCells_plug` applies to `[dup]` against `[dup]`** (Fig. 10, pages 89–90). With the side
`s` of `dup` against `dup` in the decomposition data of the interaction combinators, the two cells
plugged by their roots reduce to a net `Equiv` to `plugTermTarget s.σ tφ tψ` on the ports `0, 1`
and `2, 3`, with trees `tφ`, `tψ` that translate the trees of the side. -/
theorem codeCells_plug_dupDup :
    ∃ s : ExpSide sig (sig.arity Comb.dup), sd Comb.dup Comb.dup = some s ∧
      ∃ (k₀ k₁ : ℕ) (M : CNet) (tφ : Fin 2 ⊕ Fin s.k → Term sig ℕ)
        (tψ : Fin 2 ⊕ Fin s.k → Term sig ℕ),
        StepsE system netDupDup M ∧
        Equiv M (plugTermTarget s.σ tφ tψ zeroOne twoThree + 0) ∧
        (∀ p, (codeTranslation sd).TermTr (gammaTree s.φ k₀ p) (tφ p)) ∧
        (∀ q, (codeTranslation sd).TermTr (gammaTree s.φ k₁ q) (tψ q)) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1
    ((System.DecData.side_isSome_iff (System.WellFormed.decData system_wellFormed)
      Comb.dup Comb.dup).2 (Or.inl ⟨_, rfl⟩))
  exact ⟨s, hs, codeCells_plug sd Comb.dup Comb.dup zeroOne twoThree _ _ 0 s.φ s.φ s.σ
    s.involutive s.linear s.expanded s.linear s.expanded hs hs linear_netDupDup⟩

end INet.Comb.CodeCellsPlugCheck
