import Checks.Universality.General.CodeTreeECheck
import Demo.Print

/-!
# Check: the printer of `Demo/Print.lean` on the trees of Fig. 10

The trees `[con]`, `[dup]`, `[era]` of Fig. 10 (page 89), for the hand-written numbering
`combEnum` and the side `sideConDup` of `Checks/CodeTreeECheck.lean`, are printed and their cells
counted by the compiler. The printed tree of `[era]` is about a thousand characters long; it begins
with the `dup` cell of the transpositor `T_{1,1}` at the root (`codeTreeE_eq_mkDup`) and ends with
the loop `0` (the arity of `era` is `0`).
-/

namespace INet.Comb.PrintCheck

open CodeGammaReview CodeMenusECheck

-- The numbers of cells of `[con]`, `[dup]`, `[era]`, by `Term.size` and by `Term.cells`, agree
-- (`Term.size_eq_card_cells`).
#guard [(codeTreeE combEnum sideConDup (Comb.con : sig.Sym)).size,
  (codeTreeE combEnum sideConDup (Comb.dup : sig.Sym)).size,
  (codeTreeE combEnum sideConDup (Comb.era : sig.Sym)).size] == [139, 217, 137]
#guard [(codeTreeE combEnum sideConDup (Comb.con : sig.Sym)).cells.card,
  (codeTreeE combEnum sideConDup (Comb.dup : sig.Sym)).cells.card,
  (codeTreeE combEnum sideConDup (Comb.era : sig.Sym)).cells.card] == [139, 217, 137]

-- The printed trees are not empty; `[con]` is `1025` characters long.
#guard (Term.toStr (codeTreeE combEnum sideConDup (Comb.con : sig.Sym))).length == 1025
#guard (Term.toStr (codeTreeE combEnum sideConDup (Comb.era : sig.Sym))).length > 0

-- The root of `[era]` is a `dup` cell, and the tree ends with the loop `0`.
#guard (Term.toStr (codeTreeE combEnum sideConDup (Comb.era : sig.Sym))).startsWith
  "dup(con(con(era, con(era, era)), con(con(con(con(con(43, con(58, "
#guard (Term.toStr (codeTreeE combEnum sideConDup (Comb.era : sig.Sym))).endsWith
  "con(era, con(era, era))))))), 0), era), era)), 0)"

-- The principal net `[era]` names its internal wires `0, 1, …` in increasing order of the names of
-- `codeTreeE` (`wireNum`): the names `43, 58, …` of the tree become `25, 26, …`.
#guard (pnetToStr (codeNetE combEnum sideConDup (Comb.era : sig.Sym))).startsWith
  "dup(con(con(era, con(era, era)), con(con(con(con(con(25, con(26, "

end INet.Comb.PrintCheck
