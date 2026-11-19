import InteractionCombinators.Lafont.CodeData

/-!
# Checks for `System.DecData` (pages 85–86, 90)

Non-vacuity of `System.DecData`: the combinators without `con`–`dup` (page 87, recursion-free)
have decomposition data, from their recursion-free data; the full system of interaction
combinators, which is **not** recursion-free (`system_not_recursionFree`), has decomposition data
too, from `System.exists_decData` and its well-formedness. For the full system, the side of `con`
against `dup` exists and is read from the rule `con`–`dup`, and the side of `dup` against `con` is
read from the same rule, as its `ψ` (page 86, `φ_{j,i} = ψ_{i,j}`).
-/

namespace INet

namespace Comb

/-- The recursion-free combinators of page 87 have decomposition data. -/
example : Nonempty systemNoConDup.DecData := ⟨recursionFreeDataNoConDup.toDecData⟩

/-- The full system of interaction combinators has decomposition data (pages 86, 90). -/
example : Nonempty system.DecData := System.exists_decData system_wellFormed

/-- … although it is not recursion-free (page 87). -/
example : ¬ system.RecursionFree ∧ Nonempty system.DecData :=
  ⟨system_not_recursionFree, System.exists_decData system_wellFormed⟩

/-- In the full system, the side of `con` against `dup` is the `φ` of the decomposition of the
rule `con`–`dup` (page 86). -/
example : system_wellFormed.decData.rawSide Comb.con Comb.dup =
    some (system_wellFormed.decData.rawφ Comb.con Comb.dup ruleConDup rfl) :=
  System.DecData.rawSide_of_rule _ rfl

/-- In the full system, the side of `dup` against `con` is the `ψ` of the decomposition of the
rule `con`–`dup` (page 86, `φ_{j,i} = ψ_{i,j}`). -/
example : system_wellFormed.decData.rawSide Comb.dup Comb.con =
    some (system_wellFormed.decData.rawψ Comb.dup Comb.con ruleConDup rfl) :=
  System.DecData.rawSide_of_rule_swap _ rfl rfl

/-- For a rule `α`–`β` with `α ≠ β`, the side `φ_{α,β}` chosen by `decData` comes with the
identity permutation (page 86). -/
example : (system_wellFormed.decData.rawφ Comb.con Comb.dup ruleConDup rfl).σ = 1 :=
  system_wellFormed.decData.ne _ _ _ rfl (by intro h; cases h)

/-- For the full system, every pair of symbols has a side (every pair has a rule one way). -/
example (α β : sig.Sym) : (system_wellFormed.decData.side α β).isSome := by
  rw [System.DecData.side_isSome_iff]
  cases α <;> cases β <;> first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr ⟨_, rfl⟩

/-- In `systemNoConDup`, neither `con` against `dup` nor `dup` against `con` has a side. -/
example : recursionFreeDataNoConDup.toDecData.side (Comb.con : sig.Sym) Comb.dup = none ∧
    recursionFreeDataNoConDup.toDecData.side (Comb.dup : sig.Sym) Comb.con = none :=
  ⟨Option.map_eq_none_iff.2 (System.DecData.rawSide_eq_none _ rfl rfl),
    Option.map_eq_none_iff.2 (System.DecData.rawSide_eq_none _ rfl rfl)⟩

end Comb

end INet
