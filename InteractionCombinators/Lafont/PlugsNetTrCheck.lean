import InteractionCombinators.Lafont.PlugsNetTr
import InteractionCombinators.Combinators

/-!
# Non-vacuity of `Translation.NetTr.inst_of_equiv_rename`

Every hypothesis of `Translation.NetTr.inst_of_equiv_rename` holds for the rule `con`–`dup` of
the combinators (four internal wires), `P = r`, `ι = id`, the identity translation, the names
`0, 1` on the ports of `con`, `2, 3` on the ports of `dup`, and `4, 5, 6, 7` on the internal
wires.
-/

namespace INet.PlugsNetTrCheck

open Term Comb

/-- Renaming the internal wires by the identity does not change a net. -/
theorem bind_map_id {a b k : ℕ} (K : Net sig (Fin a ⊕ Fin b ⊕ Fin k)) :
    K.bind (fun x => var (Sum.map id (Sum.map id (id : Fin k → Fin k)) x)) = K := by
  have : (fun x : Fin a ⊕ Fin b ⊕ Fin k => (var (Sum.map id (Sum.map id id) x) : Term sig _)) =
      Term.var := by
    funext x; rcases x with i | j | w <;> rfl
  rw [this]
  exact Net.bind_var_self K

/-- The names of the internal wires. -/
def h4 : Fin ruleConDup.internal → ℕ := fun w => 4 + (w : ℕ)

/-- The instance of `con`–`dup` with ports `0, 1`, `2, 3` and internal wires `4` to `7`. -/
abbrev inst4 : Net sig ℕ :=
  ruleConDup.inst (fun i => .var (![0, 1] i)) (fun j => .var (![2, 3] j)) h4

/-- The instance is written out. -/
theorem inst4_eq : inst4 =
    s(var 0, mkDup (var 4) (var 5)) ::ₘ s(var 1, mkDup (var 6) (var 7)) ::ₘ
      s(var 2, mkCon (var 4) (var 6)) ::ₘ {s(var 3, mkCon (var 5) (var 7))} := by
  simp [inst4, Rule.inst, ruleConDup, Net.bind, h4]
  rfl

/-- The instance is linear. -/
theorem inst4_linear : inst4.Linear := by
  rw [inst4_eq]
  intro y
  simp only [Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_var, vars_mkDup, vars_mkCon,
    Multiset.count_add, Multiset.count_singleton]
  split_ifs <;> omega

/-- The identity translation of the instance. -/
theorem netTr_inst4 : (Translation.id sig).NetTr inst4 inst4 :=
  ⟨Multiset.rel_refl_of_refl_on fun e _ => Translation.eqTr_id e, inst4_linear⟩

/-- `Translation.NetTr.inst_of_equiv_rename` is not vacuous: all its hypotheses hold for the rule
`con`–`dup`, `P = r`, `ι = id`, the identity translation and a linear instance (Lafont 1997,
pages 80 and 85). -/
example : ∃ (h' : Fin ruleConDup.internal → ℕ) (N'' : Net sig ℕ),
    (Translation.id sig).NetTr
      (ruleConDup.inst (fun i => .var (![0, 1] i)) (fun j => .var (![2, 3] j)) h') N'' ∧
    Equiv inst4 N'' :=
  Translation.NetTr.inst_of_equiv_rename ruleConDup ruleConDup ruleConDup_linear id
    (Equiv.of_eq (bind_map_id _).symm) _ _ h4 netTr_inst4

/-- `Rule.equiv_inst_of_equiv_rename` is not vacuous, on the same data. -/
example : Equiv inst4
    (ruleConDup.inst (fun i => .var (![0, 1] i)) (fun j => .var (![2, 3] j)) (h4 ∘ id)) :=
  Rule.equiv_inst_of_equiv_rename ruleConDup ruleConDup ruleConDup_linear id
    (Equiv.of_eq (bind_map_id _).symm) _ _ h4 inst4_linear

end INet.PlugsNetTrCheck
