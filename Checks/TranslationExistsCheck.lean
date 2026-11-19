import InteractionCombinators.TranslationExists
import Checks.DecompositionCheck

/-!
# Checks of `TranslationExists.lean`

Equality of trees is decided with the instance of `Checks/DecompositionCheck.lean`.

* The identity translation: `trTerm` returns the tree unchanged, and uses no new name.
* A translation with internal wires (`con` becomes two `con` cells joined by one wire): the
  numbering of `trTerm`, computed by `rfl` on a tree with two `con` cells.
* `exists_netTr` on a linear net of two equations: its hypotheses can hold.
-/

namespace INet

namespace Translation

variable {S : Signature}

/-- The identity translation of a tree is the tree itself (Lafont 1997, Section 1.7, page 79). -/
theorem trTerm_id (k : ℕ) (t : Term S ℕ) : (Translation.id S).trTerm k t = t := by
  induction t generalizing k with
  | var x => rfl
  | app α ts ih =>
    change Term.app α _ = _
    congr 1
    funext i
    exact ih i _

/-- The identity translation uses no new name (Lafont 1997, Section 1.7, page 79). -/
theorem size_id (t : Term S ℕ) : (Translation.id S).size t = 0 := by
  induction t with
  | var x => rfl
  | app α ts ih =>
    change 0 + ∑ i, (Translation.id S).size (ts i) = 0
    simp [ih]

end Translation

namespace Comb.TranslationExistsCheck

open Term DecompositionCheck

/-- `con` as two `con` cells joined by one internal wire: `con(con(p₀, w), con(w, p₁))`. -/
def conTwice : PNet sig 2 where
  internal := 1
  tree := mkCon (mkCon (.var (.inl 0)) (.var (.inr 0))) (mkCon (.var (.inr 0)) (.var (.inl 1)))
  port_count i := by fin_cases i <;> decide
  internal_count w := by fin_cases w; decide

/-- `con` is doubled, `dup` and `era` are kept. -/
def Φ : Translation sig sig := ⟨fun α => match α with
  | .con => conTwice
  | .dup => PNet.cell (S := sig) Comb.dup
  | .era => PNet.cell (S := sig) Comb.era⟩

/-- Two `con` cells: the root instance takes the name `10`, the inner one `11`. -/
example : Φ.trTerm 10 (mkCon (var 0) (mkCon (var 1) (var 2))) =
    mkCon (mkCon (var 0) (var 10))
      (mkCon (var 10) (mkCon (mkCon (var 1) (var 11)) (mkCon (var 11) (var 2)))) := by
  decide

example : Φ.size (mkCon (var 0) (mkCon (var 1) (var 2)) : Term sig ℕ) = 2 := by
  decide

/-- The identity translation on a concrete tree. -/
example : (Translation.id sig).trTerm 5 (mkCon (var 0) (mkDup (var 1) mkEra)) =
    mkCon (var 0) (mkDup (var 1) mkEra) := Translation.trTerm_id _ _

example : (Translation.id sig).size (mkCon (var 0) (mkDup (var 1) mkEra) : Term sig ℕ) = 0  :=
  Translation.size_id _

/-- A linear net of two equations: `con(0, 1) = 2`, `2 = dup(0, 1)`. -/
def N : Net sig ℕ := s(mkCon (var 0) (var 1), var 2) ::ₘ {s(var 2, mkDup (var 0) (var 1))}

theorem N_linear : N.Linear := by
  intro x
  simp only [N, Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_mkCon, vars_mkDup,
    vars_var, Multiset.count_add, Multiset.count_singleton]
  split_ifs <;> omega

theorem N_below : N.Below 3 := by
  simp [N, Term.Below]

/-- `exists_netTr` applies to `N`: its hypotheses hold. -/
example : ∃ (N' : Net sig ℕ) (k' : ℕ), Φ.NetTr N N' ∧ 3 ≤ k' ∧ N'.Below k' ∧
    N'.vars = N.vars + 2 • Multiset.Ico 3 k' :=
  Φ.exists_netTr N_linear N_below

end Comb.TranslationExistsCheck

end INet
