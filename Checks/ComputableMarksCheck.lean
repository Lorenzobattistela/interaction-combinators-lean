import InteractionCombinators.Lafont.CodeTr
import InteractionCombinators.Lafont.RecursionFreeTr

/-!
# `wireSet`, `cellPNet`, `defaultPNet` and `lowerTr` are compiled (pages 86, 88–90)

These four definitions are no longer marked `noncomputable`: the code generator compiles them, so
`#eval` runs on them. The checks evaluate them on small arguments and state the same values by
`decide` or `rfl`.

* `defaultPNet` of arity 2 (Fig. 6 with an empty menu, page 86): one internal wire, the loop, and
  five cells: the `dup` of `T_{1,1}`, the `con` carrying the menu, the eraser of the empty menu,
  and the two `con` of the multiplexor `M_3` of the two ports and the loop.
* `wireSet 1` of `γ(0, δ(1, 1))` (page 89): the internal names are the names `≥ 1`, here `{1}`.
-/

namespace INet.Comb.ComputableMarksCheck

open Term

#eval (defaultPNet 2).internal
#eval Multiset.card (defaultPNet 2).tree.cells
#eval wireSet 1 (mkCon (var 0) (mkDup (var 1) (var 1)) : Term sig ℕ)

/-- `defaultPNet 2` has one internal wire, the loop of Fig. 6 (page 86). -/
example : (defaultPNet 2).internal = 1 := rfl

/-- `defaultPNet 2` has five cells (Fig. 6 with an empty menu, page 86). -/
example : Multiset.card (defaultPNet 2).tree.cells = 5 := by decide

/-- `wireSet 1` of `γ(0, δ(1, 1))` is `{1}`: its names `≥ 1` (page 89). -/
example : wireSet 1 (mkCon (var 0) (mkDup (var 1) (var 1)) : Term sig ℕ) = {1} := by decide

end INet.Comb.ComputableMarksCheck
