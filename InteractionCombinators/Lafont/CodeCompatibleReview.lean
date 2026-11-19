import InteractionCombinators.Lafont.CodeCompatible
import InteractionCombinators.Lafont.RecursionFreeTr

/-!
# Review of Theorem 1 as proved in `CodeCompatible.lean` (pages 79–81, 88–90)

Checks of the final statements `universal_strict'`, `universal'` and
`System.DecData.codeTranslation_compatible`.

* **The statements are the targets.** `universal_strict'` and `universal'` have the types of the
  two target statements of `Universality.lean`, at the system `INet.Comb.system` of
  `Combinators.lean` (Fig. 2, page 81; Section 2.1, page 82), whose six rules are restated here.
* **`Compatible` is not satisfied for a trivial reason.** `id_not_compatible_noRules`: the
  identity translation of the combinators into the same signature with no rule is not
  compatible: the pair `era`–`era` must reduce to the translation of the empty net, and a target
  with no rule cannot remove its two cells (`Equiv.cells_eq`). So `Compatible` asks the target to
  perform the interactions, as the diagram of page 81 does.
* **Not vacuous.** `codeTranslation_compatible` applies to the system of the combinators itself,
  which has rules between different symbols (`con`–`dup`, `era`–`con`, `era`–`dup`).
-/

namespace INet.Comb.CodeCompatibleReview

open INet INet.Comb

/-! ## The statements are the targets -/

/-- `universal_strict'` has the type of the target `universal_strict` (Theorem 1, page 90), at
the system of the combinators. -/
example : StrictlyUniversal INet.Comb.system := INet.Comb.universal_strict'

/-- `universal'` has the type of the target `universal` (Theorem 1, page 90). -/
example : Universal INet.Comb.system := INet.Comb.universal'

/-- The quantification is over every signature with a finite set of symbols and every well-formed
system on it (page 73: "Fix a finite alphabet"), with no other hypothesis. -/
example : StrictlyUniversal INet.Comb.system ↔
    ∀ (S : Signature) [Finite S.Sym] (I : System S), I.WellFormed →
      ∃ Φ : Translation S sig, Φ.Strict ∧ Φ.Compatible I INet.Comb.system :=
  Iff.rfl

/-- The system of the theorems is Lafont's (Fig. 2, page 81): the six rules, with `con`–`con`
exchanging the auxiliary ports and `dup`–`dup` keeping them in order. -/
example : INet.Comb.system.rule .con .con = some ruleConCon ∧
    INet.Comb.system.rule .dup .dup = some ruleDupDup ∧
    INet.Comb.system.rule .era .era = some ruleEraEra ∧
    INet.Comb.system.rule .era .con = some ruleEraBin ∧
    INet.Comb.system.rule .era .dup = some ruleEraBin ∧
    INet.Comb.system.rule .con .dup = some ruleConDup :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## `Compatible` is not satisfied for a trivial reason -/

/-- The signature of the combinators with no interaction rule. -/
def noRules : System sig := ⟨fun _ _ => none⟩

/-- In a system with no rule, a net reduces only to itself. -/
theorem stepsE_noRules {N M : Net sig ℕ} (h : StepsE noRules N M) : M = N := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨_, _, hs⟩ := hs
    obtain ⟨α, β, r, hr, -⟩ := hs
    exact absurd hr (by simp [noRules])

/-- **`Compatible` asks the target to interact** (page 81). The identity translation of the
combinators into the same signature with no rule is not a translation of interaction systems: the
pair `era`–`era` has two cells, the translation of the empty right-hand side has none, and with no
rule the target cannot remove cells. -/
theorem id_not_compatible_noRules : ¬ (Translation.id sig).Compatible INet.Comb.system noRules := by
  intro h
  have e : ∀ (a : Fin (sig.arity (Comb.era : sig.Sym)) → Term sig ℕ) f,
      ((Translation.id sig).net (Comb.era : sig.Sym)).inst a f = mkEra := fun a f => by
    show Term.app _ a = Term.app _ _
    congr 1
    funext i
    exact (show Fin 0 from i).elim0
  obtain ⟨M, N', w, hS, hE, hN⟩ := h (Comb.era : sig.Sym) (Comb.era : sig.Sym) ruleEraEra rfl
    Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 (fun x => by erw [e]; simp)
  have hN' : N' = 0 := Multiset.rel_zero_left.1 hN.rel
  have hM := stepsE_noRules hS
  subst hN' hM
  have hc := hE.cells_eq
  simp only [Net.cells, Multiset.singleton_bind, eqCells_mk, Multiset.zero_bind] at hc
  erw [e] at hc
  simp only [mkEra, Term.cells, add_eq_zero, and_self] at hc
  exact Multiset.cons_ne_zero hc

/-! ## Not vacuous -/

/-- **The hypotheses of `codeTranslation_compatible` hold** (pages 88–90) for the system of the
combinators, which has rules between different symbols: it is well formed, and decomposition data
for it come from `System.WellFormed.decData`. -/
example : (codeTranslation system_wellFormed.decData.side).Compatible INet.Comb.system
    INet.Comb.system :=
  system_wellFormed.decData.codeTranslation_compatible system_wellFormed

/-- The same translation is strict: the two conclusions of `universal_strict'` hold together for
the combinators translated into themselves. -/
example : (codeTranslation system_wellFormed.decData.side).Strict ∧
    (codeTranslation system_wellFormed.decData.side).Compatible INet.Comb.system
      INet.Comb.system :=
  ⟨codeTranslation_strict _, system_wellFormed.decData.codeTranslation_compatible system_wellFormed⟩

end INet.Comb.CodeCompatibleReview
