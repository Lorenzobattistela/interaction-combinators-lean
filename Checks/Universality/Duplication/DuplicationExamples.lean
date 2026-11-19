import InteractionCombinators.Universality.Duplication.Duplication

/-!
# Lemma 3 (i) on concrete trees

These examples check, on small trees, that `nested` is the right-hand side of Lemma 3 (i)
(Lafont 1997, page 87) and that the hypotheses of `dup_tree_nested` can hold together.

The original `dup` is `mkDup u v`. Its first auxiliary port `u` gets the first copy `l`. The `dup`
on each original leaf has its first auxiliary port on the leaf of `l` and its second auxiliary port
on the leaf of `r`. Both copies keep the order of the leaves of `τ`.
-/

namespace INet.Comb

open Term

/-- A single name: no cell to copy, one `dup` on the leaf (Lemma 3 (i), page 87). -/
example : nested 4 (var 0) = ⟨var 4, var 5, {s(var 0, mkDup (var 4) (var 5))}, 6⟩ := rfl

/-- An eraser is a cell of the tree, not a leaf: it is copied and gets no `dup` (Lemma 3 (i),
page 87). -/
example : nested 4 mkEra = ⟨mkEra, mkEra, 0, 4⟩ := rfl

/-- Two leaves: leaf `0` is on the left of both copies and leaf `1` on the right. The `dup` on
leaf `0` has `6` (in the first copy) on its first auxiliary port and `7` (in the second copy) on
its second one (Lemma 3 (i), page 87). -/
example : nested 4 (mkCon (var 0) (var 1)) =
    ⟨mkCon (var 6) (var 4), mkCon (var 7) (var 5),
      {s(var 0, mkDup (var 6) (var 7))} + {s(var 1, mkDup (var 4) (var 5))}, 8⟩ := rfl

/-- A tree with a `con` under a `con` and an eraser: both copies are the tree itself with new
leaves, and only the two names get a `dup` (Lemma 3 (i), page 87). -/
example : nested 4 (mkCon (var 0) (mkCon (var 1) mkEra)) =
    ⟨mkCon (var 6) (mkCon (var 4) mkEra), mkCon (var 7) (mkCon (var 5) mkEra),
      {s(var 0, mkDup (var 6) (var 7))} + ({s(var 1, mkDup (var 4) (var 5))} + 0), 8⟩ := rfl

/-- The flat net of the two-leaf tree is exactly what one `con`–`dup` interaction (Fig. 2) gives:
the new wires are `4`, `5`, `6`, `7`, the original `dup` keeps `u = 2` and `v = 3` on the two new
`con` cells (Lemma 3 (i), page 87). -/
example : dupNet 4 (var 2) (var 3) (mkCon (var 0) (var 1)) =
    (s(var 2, mkCon (var 4) (var 6)) ::ₘ s(var 3, mkCon (var 5) (var 7)) ::ₘ
      ({s(mkDup (var 4) (var 5), var 0)} + {s(mkDup (var 6) (var 7), var 1)}), 8) := rfl

/-- The hypotheses of `dup_tree_nested` hold together: a `dup` with free auxiliary ports `2`, `3`
plugged into the tree `con 0 (con 1 era)` with free leaves `0`, `1` (Lemma 3 (i), page 87). -/
example : ∃ N, Red ({s(mkDup (var 2) (var 3), mkCon (var 0) (mkCon (var 1) mkEra))} : CNet) N ∧
    Equiv N (s(var 2, mkCon (var 14) (mkCon (var 12) mkEra)) ::ₘ
      s(var 3, mkCon (var 15) (mkCon (var 13) mkEra)) ::ₘ
      ({s(var 0, mkDup (var 14) (var 15))} + ({s(var 1, mkDup (var 12) (var 13))} + 0) + 0)) := by
  have h := dup_tree_nested (mkCon (var 0) (mkCon (var 1) mkEra)) ⟨trivial, trivial, trivial⟩ 4
    (var 2) (var 3) 0 (by
      simp only [Net.below_cons, Net.below_zero, below_mkDup, below_mkCon, below_mkEra, Term.below_var]
      decide) (by
      intro y
      simp only [Net.vars_cons, Net.vars_zero, eqVars_mk, vars_mkDup, vars_mkCon, vars_mkEra,
        vars_var, add_zero, Multiset.count_add, Multiset.count_singleton]
      split_ifs <;> omega)
  exact h

/-- A leaf of the tree may be wired to an auxiliary port of the `dup`: here leaf `0` is `u`. The net
is linear and the theorem applies (Lemma 3 (i), page 87). -/
example : ∃ N, Red ({s(mkDup (var 0) (var 2), mkCon (var 0) (var 1))} : CNet) N ∧
    Equiv N (s(var 0, mkCon (var 9) (var 7)) ::ₘ s(var 2, mkCon (var 10) (var 8)) ::ₘ
      ({s(var 0, mkDup (var 9) (var 10))} + {s(var 1, mkDup (var 7) (var 8))} + 0)) := by
  have h := dup_tree_nested (mkCon (var 0) (var 1)) ⟨trivial, trivial⟩ 3 (var 0) (var 2) 0
    (by
      simp only [Net.below_cons, Net.below_zero, below_mkDup, below_mkCon, Term.below_var]
      decide) (by
      intro y
      simp only [Net.vars_cons, Net.vars_zero, eqVars_mk, vars_mkDup, vars_mkCon,
        vars_var, add_zero, Multiset.count_add, Multiset.count_singleton]
      split_ifs <;> omega)
  exact h

end INet.Comb
