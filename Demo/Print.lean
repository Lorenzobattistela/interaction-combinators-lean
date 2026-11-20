import InteractionCombinators
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.String.Basic

/-!
# Demo: printing trees and nets of combinators, and the number of cells

Trees of combinators are printed as `con(a, b)`, `dup(a, b)` and `era`, a name as its number
(`con` is Lafont's `γ`, `dup` his `δ`, `era` his `ε`; Lafont 1997,
Section 2.1, page 82).

* `Comb.Term.toStr` — the text of a tree, and an instance `ToString (Term sig ℕ)`, so that
  `#eval` prints a tree.
* `Comb.eqsToStr` — the text of a list of equations, in the order of the list.
* `Comb.netToStr` — the text of a net. A net is a multiset of unordered equations, a quotient: it
  is printed through `Sym2.lift` and `Multiset.sort`, which are computable, by writing the two
  sides of each equation in lexicographic order and sorting the equations. Mathlib's `Repr`
  instances for `Multiset` and `Sym2` go through `Quot.unquot` and are not used.
* `Comb.pnetToStr` — the text of a principal net `PNet sig n`: its tree, with the port `i` named
  `i` and the internal wire `w` named `n + w`.
* `Term.size_eq_card_cells` — the number of cells of a tree, `Term.size`, is the number of its
  cells `Term.cells`; `Net.size` is the number of cells of a net.

Everything here is evaluated by the compiler; the tests below use `#guard`.

Contents, in the order of the file:

1. Definitions: `Net.size`, the number of cells of a net; the printers `name`, `Term.toStr`
   (with the instance `ToString (Term sig ℕ)`), `eqsToStr`, `eqToStr`, `netToStr`, `pnetToStr`.
2. Auxiliary lemmas: `Term.size_eq_card_cells`, `Net.size_cons`, the number of cells of a tree
   and of a net with one more equation.
3. Tests: `#guard` checks of the printers and of the number of cells.
-/

namespace INet

-- ============================================================================================
-- 1. Definitions: the number of cells, and the printers
-- ============================================================================================

/-- The number of cells of a net (Section 1.1, page 71): the cells of all its trees. -/
def Net.size
    -- a net
    {S : Signature}
    {ν : Type}
    (N : Net S ν) :
    ℕ :=
  (Net.cells N).card

namespace Comb

/-- The name of a combinator, as printed (page 82). -/
def name :
    Comb → String
  | con => "con"
  | dup => "dup"
  | era => "era"

/-- The text of a tree of combinators (page 82): `con(a, b)`, `dup(a, b)`, `era`, and a name as
its number. -/
def Term.toStr :
    Term sig ℕ → String
  | .var x => toString x
  | .app α ts =>
    if sig.arity α = 0 then name α
    else name α ++ "(" ++ ", ".intercalate (List.ofFn fun i => Term.toStr (ts i)) ++ ")"

-- A tree of combinators is printed by `Term.toStr`, so that `#eval` shows it.
instance : ToString (Term sig ℕ) := ⟨Term.toStr⟩

/-- The text of a list of equations `a = b, c = d`, in the order of the list (page 71). -/
def eqsToStr
    -- the equations, as pairs of trees
    (L : List (Term sig ℕ × Term sig ℕ)) :
    String :=
  ", ".intercalate (L.map fun e => Term.toStr e.1 ++ " = " ++ Term.toStr e.2)

/-- The text of an unordered equation (page 71): its two sides in lexicographic order, so that a
name, which begins with a digit, comes before a tree with a cell. -/
def eqToStr :
    Sym2 (Term sig ℕ) → String :=
  Sym2.lift ⟨fun a b => min (Term.toStr a) (Term.toStr b) ++ " = " ++
    max (Term.toStr a) (Term.toStr b), fun a b => by dsimp only; rw [min_comm, max_comm]⟩

/-- The text of a net (page 71): its equations, each written by `eqToStr`, sorted in
lexicographic order and separated by commas. It is computed through `Sym2.lift` and
`Multiset.sort`, without `Quot.unquot`. -/
def netToStr
    -- a net of combinators over the names `ℕ`
    (N : Net sig ℕ) :
    String :=
  ", ".intercalate ((N.map eqToStr).sort (· ≤ ·))

/-- The text of a principal net of arity `n` (page 80): its tree, with the port `i` named `i` and
the internal wire `w` named `n + w`. -/
def pnetToStr
    -- a principal net of arity `n`
    {n : ℕ}
    (p : PNet sig n) :
    String :=
  Term.toStr (p.inst (fun i => .var (i : ℕ)) fun w => n + w)

end Comb

-- ============================================================================================
-- 2. Auxiliary lemmas: the number of cells
-- ============================================================================================

/-- The number of cells of a tree, `Term.size` (the numbering of the cells of the raw graph,
Section 1.1, page 71), is the number of its cells `Term.cells`. -/
theorem Term.size_eq_card_cells
    -- a tree
    {S : Signature}
    {ν : Type}
    (t : Term S ν) :
    t.size = t.cells.card := by
  induction t with
  | var x => rfl
  | app α ts ih =>
    have h : (∑ i, (ts i).cells).card = ∑ i, (ts i).cells.card :=
      map_sum Multiset.cardHom (fun i => (ts i).cells) Finset.univ
    rw [Term.cells_app, Multiset.card_cons, h]
    simp only [Term.size, ← ih]
    omega

/-- The number of cells of a net with one more equation `a = b` (page 71): the cells of `a`, of
`b`, and of the rest. -/
theorem Net.size_cons
    -- the signature and the names
    {S : Signature}
    {ν : Type}
    -- the two sides of the new equation
    (a b : Term S ν)
    -- the rest of the net
    (N : Net S ν) :
    Net.size (s(a, b) ::ₘ N) = a.size + b.size + Net.size N := by
  simp [Net.size, Net.cells_cons, Term.size_eq_card_cells]

namespace Comb

-- ============================================================================================
-- 3. Tests
-- ============================================================================================

-- A tree, and the two printers of nets.
#guard Term.toStr (mkCon (.var 0) (mkDup mkEra (.var 1))) == "con(0, dup(era, 1))"
#guard eqsToStr [(mkCon (.var 0) (.var 1), .var 2), (mkEra, .var 3)] == "con(0, 1) = 2, era = 3"
#guard netToStr (s(.var 3, mkEra) ::ₘ s(mkCon (.var 0) (.var 1), .var 2) ::ₘ 0) ==
  "2 = con(0, 1), 3 = era"

-- The two sides of the rule `con`–`dup` (Fig. 2, page 82), with the auxiliary ports of the `con`
-- cell named `0, 1`, those of the `dup` cell `2, 3`, and the new wires `10, 11, 12, 13`.
#guard Term.toStr (mkCon (.var 0) (.var 1)) ++ " = " ++ Term.toStr (mkDup (.var 2) (.var 3)) ==
  "con(0, 1) = dup(2, 3)"
#guard netToStr (ruleConDup.inst ![.var 0, .var 1] ![.var 2, .var 3] ![10, 11, 12, 13]) ==
  "0 = dup(10, 11), 1 = dup(12, 13), 2 = con(10, 12), 3 = con(11, 13)"

-- The number of cells: `Net.size` of the right-hand side of the rule `con`–`dup` is `4`.
#guard Net.size (ruleConDup.inst ![.var 0, .var 1] ![.var 2, .var 3] ![10, 11, 12, 13]) == 4
#guard (mkCon (.var 0) (mkDup mkEra (.var 1)) : Term sig ℕ).size == 3

-- A single cell as a principal net (page 80).
#guard pnetToStr (PNet.cell (Comb.dup : sig.Sym)) == "dup(0, 1)"

end Comb

end INet
