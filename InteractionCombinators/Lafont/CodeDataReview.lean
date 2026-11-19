import InteractionCombinators.Lafont.CodeData
import InteractionCombinators.Lafont.CodeDataSides
import InteractionCombinators.Lafont.DecompositionSymmReview
import InteractionCombinators.Lafont.ExpandedIso

/-!
# Review of the decomposition data without an order (pages 85–86, 90)

Review of `System.DecData` and of the side `System.DecData.side` (`Lafont/CodeData.lean`, PR #164)
against Lafont 1997, pages 85–86 (PDF pages 17–18) and page 90 (Section 2.7, Fig. 10, on PDF
page 21). Issue #165.

## What page 86 asks

"To sum up, one can assume that in all cases, `φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}`, and
`σ_{i,j}` is involutive", the sides `φ_{i,j}`, `ψ_{i,j}` being reduced nets (page 85), and, for
`i ≠ j`, `σ_{i,j}` may be taken to be an identity by moving it into `φ_{i,j}`. Page 73 gives at
most one rule for a pair `α_i`, `α_j`, read from either cell; this development stores it once,
as `I.rule α β`, and `System.WellFormed.unique` forbids `I.rule β α` beside it when `α ≠ β`.

`DecData` stores one decomposition per stored rule, and `rawSide β α` reads the missing direction
`φ_{β,α}` as the `ψ` of the rule `α`–`β`, with the same `σ`. So `φ_{j,i} = ψ_{i,j}` and
`σ_{j,i} = σ_{i,j}` hold by construction for `i ≠ j`, provided the system is well formed. For
`i = j` they become the field `self` (`ψ_{i,i} = φ_{i,i}`) and nothing (`σ_{i,i} = σ_{i,i}`).
`involutive` is the last condition. `ne` (`σ = 1` for `i ≠ j`) is the "always possible" step of
page 86; it is more than the summary sentence asks, but `decData` proves it can always be met,
so it narrows the data and not the systems.

Section 2.7 (page 88, "Translation (General Case)") and Fig. 10 use `φ_{i,j}`, `σ_{i,j}` and the
number of cells `p_{i,j}` of `φ_{i,j}`, and no order. Dropping `rank`, `rank_φ`, `rank_ψ` of
`RecursionFreeData` is what that section does. (The module docstring of `CodeData.lean` calls it
"Section 2.5"; Section 2.5 is "Duplication", and the general translation is Section 2.7.)

## The checks

* **The two directions of a rule** (`System.DecData.sides_of_rule`). For a well-formed system and
  a rule `α`–`β`, the side of `α` against `β` is `φ` of its decomposition, the side of `β` against
  `α` is `ψ` of the same decomposition (`rawSide_swap_of_rule`), with the same `σ`; and those two
  sides plugged through that `σ` give back the rule (`Decomposition.Plugs`). This is what the
  compatibility proof of Fig. 10 will need. "Both `I.rule α β` and `I.rule β α` defined" cannot
  happen for `α ≠ β` in a well-formed system, so page 86's equation is not a condition there.
* **`DecData` does not record well-formedness.** `sysBoth` is a (not well-formed) system with both
  a rule `era`–`con` and a rule `con`–`era`; it has decomposition data `decDataBoth`, whose side
  of `con` against `era` has no middle wire while the `ψ` of `era`–`con` has two
  (`sysBoth_sides_disagree`). So every use of `DecData.side` in the compatibility proof must take
  `I.WellFormed` as a hypothesis, as `RecursionFreeFig7` does. `Universal` and
  `StrictlyUniversal` quantify over well-formed systems, so this is not a defect.
* **`σ_{j,i} = σ_{i,j}` for `α ≠ β`.** Both are the `σ` of the one decomposition (fourth part of
  `sides_of_rule`), and that `σ` is `1` (`ne`). Nothing is lost.
* **A non-identity `σ`** (`conCon_σ_ne_one`). For *every* `D : Comb.system.DecData`, the `σ` of
  the rule `con`–`con` is not the identity: with `ψ = φ` and no cell, the identity would join the
  port `0` of the first cell to the port `0` of the second (or to its own port `1`), while
  `con`–`con` joins it to the port `1` of the second (Fig. 2). In particular for
  `system_wellFormed.decData`, whose `σ` comes from `Classical.choose` and cannot be computed;
  `sides_of_rule` and `involutive` say it is an involution.
* **`rawSide_of_rule_swap`** reads `φ_{α,β}` as the `ψ` of the rule `β`–`α`, with its `σ`; this is
  page 86's `φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}` read with `i := β`, `j := α`.
-/

namespace INet

variable {S : Signature}

open Term

namespace System.DecData

variable {I : System S} (D : I.DecData)

/-! `rawψ_self`, `rawSide_swap_of_rule` and `sides_of_rule` are in `Lafont/CodeDataSides.lean`. -/

/-- For `α ≠ β`, the permutation carried by both sides of the rule `α`–`β` is the identity
(page 86). -/
theorem sides_σ_of_ne {α β : S.Sym} {r : Rule S (S.arity α) (S.arity β)}
    (h : I.rule α β = some r) (hab : α ≠ β) :
    (D.rawφ α β r h).σ = 1 ∧ (D.rawψ β α r h).σ = 1 :=
  ⟨D.ne α β r h hab, D.ne α β r h hab⟩

end System.DecData

namespace CodeDataReview

/-- A solution of a renamed net is a solution of the net, composed with the renaming. -/
theorem solves_bind_var {ν μ κ : Type} (f : ν → μ) (g : μ → Term S κ) (N : Net S ν)
    (h : Net.Solves g (N.bind fun x => var (f x))) : Net.Solves (fun x => g (f x)) N := by
  intro e he
  have h' := h _ (Multiset.mem_map_of_mem _ he)
  induction e using Sym2.ind with
  | h u v => simpa [Term.bind_bind] using h'

/-- In a side without cells, every equation joins two names, the first of them not internal. -/
theorem shape_of_cells {a k : ℕ} {φ : Rule S a k} (hr : φ.Reduced) (hc : φ.net.cells = 0) :
    ∀ e ∈ φ.net, ∃ p q, e = s(var p, var q) ∧ ∀ w, p ≠ .inr (.inr w) := by
  intro e he
  obtain ⟨p, t, rfl, hp⟩ := hr _ he
  have hle : eqCells s(var p, t) ≤ φ.net.cells := Multiset.le_bind _ he
  rw [hc, nonpos_iff_eq_zero, eqCells_mk, cells_var, zero_add] at hle
  obtain ⟨q, rfl⟩ := ExpandedIso.eq_var_of_cells_eq_zero hle
  exact ⟨p, q, rfl, hp⟩

/-- **In a linear, reduced side without cells, a port is joined to another port or middle wire.**
For the port `i` there is a name `y`, not `i` and not internal, to which every solution gives the
value of `i`: the other end of the equation of `i`, or, if that end is an internal wire, the other
end of the second equation of that wire. -/
theorem partner {a k : ℕ} (φ : Rule S a k) (hl : φ.Linear) (hr : φ.Reduced)
    (hc : φ.net.cells = 0) (i : Fin a) :
    ∃ y : Fin a ⊕ Fin k ⊕ Fin φ.internal, y ≠ .inl i ∧ (∀ w, y ≠ .inr (.inr w)) ∧
      ∀ {μ : Type} (g : Fin a ⊕ Fin k ⊕ Fin φ.internal → Term S μ), Net.Solves g φ.net →
        g (.inl i) = g y := by
  have shape := shape_of_cells hr hc
  have sol : ∀ {μ : Type} (g : Fin a ⊕ Fin k ⊕ Fin φ.internal → Term S μ), Net.Solves g φ.net →
      ∀ p q, s(var p, var q) ∈ φ.net → g p = g q := fun g hg p q hm => hg _ hm
  have hci := hl.left i
  have hi : (Sum.inl i : Fin a ⊕ Fin k ⊕ Fin φ.internal) ∈ Net.vars φ.net :=
    Multiset.count_pos.1 (by rw [hci]; omega)
  obtain ⟨e, he, hie⟩ := Multiset.mem_bind.1 hi
  obtain ⟨p, q, rfl, hp⟩ := shape _ he
  obtain ⟨R, hR⟩ := Multiset.exists_cons_of_mem he
  have hci' := hci
  rw [hR, Net.vars_cons, eqVars_mk, vars_var, vars_var, Multiset.count_add, Multiset.count_add,
    Multiset.count_singleton, Multiset.count_singleton] at hci'
  simp only [eqVars_mk, vars_var, Multiset.mem_add, Multiset.mem_singleton] at hie
  rcases hie with rfl | rfl
  · -- `i = p`: the partner is `q`, or through `q` if `q` is internal.
    have hq : q ≠ .inl i := by intro e; subst e; simp at hci'; omega
    rcases q with j | l | w
    · exact ⟨.inl j, hq, fun w h => (by cases h), fun g hg => sol g hg _ _ he⟩
    · exact ⟨.inr (.inl l), by simp, fun w h => (by cases h), fun g hg => sol g hg _ _ he⟩
    · have hcw := hl.internal w
      rw [hR, Net.vars_cons, eqVars_mk, vars_var, vars_var, Multiset.count_add,
        Multiset.count_add, Multiset.count_singleton, Multiset.count_singleton] at hcw
      have hw : (Sum.inr (Sum.inr w) : Fin a ⊕ Fin k ⊕ Fin φ.internal) ∈ Net.vars R := by
        refine Multiset.count_pos.1 ?_
        simp only [reduceCtorEq, ↓reduceIte, zero_add] at hcw
        omega
      obtain ⟨e', he', hwe'⟩ := Multiset.mem_bind.1 hw
      have he'φ : e' ∈ φ.net := hR ▸ Multiset.mem_cons_of_mem he'
      obtain ⟨p', q', rfl, hp'⟩ := shape _ he'φ
      simp only [eqVars_mk, vars_var, Multiset.mem_add, Multiset.mem_singleton] at hwe'
      rcases hwe' with h' | rfl
      · exact absurd h'.symm (hp' w)
      have hiR : Multiset.count (Sum.inl i : Fin a ⊕ Fin k ⊕ Fin φ.internal) (Net.vars R) = 0 := by
        simp only [↓reduceIte, reduceCtorEq] at hci'
        omega
      have hp'i : p' ≠ .inl i := by
        rintro rfl
        have : (Sum.inl i : Fin a ⊕ Fin k ⊕ Fin φ.internal) ∈ Net.vars R :=
          Multiset.mem_bind.2 ⟨_, he', by simp⟩
        exact absurd hiR (Multiset.count_ne_zero.2 this)
      exact ⟨p', hp'i, hp', fun g hg => (sol g hg _ _ he).trans (sol g hg _ _ he'φ).symm⟩
  · -- `i = q`: the partner is `p`, which is not internal.
    have hp' : p ≠ .inl i := by intro e; subst e; simp at hci'; omega
    exact ⟨p, hp', hp, fun g hg => (sol g hg _ _ he).symm⟩

end CodeDataReview

namespace Comb.CodeDataReview

open INet.CodeDataReview DecompositionReview DecompositionCheck
open _root_.INet.Comb.DecompositionSymmReview

/-! ### `con`–`con`: the permutation is not the identity -/

/-- **A symmetric decomposition of `con`–`con` has a permutation other than the identity**
(page 86, Fig. 2). If `ψ = φ`, the sides are linear and reduced and plug back `con`–`con`, then
`φ` has no cell, so it joins the port `0` to the port `1` or to a middle wire; through the identity
this would join the port `0` of the first cell to its port `1` or to the port `0` of the second,
while `con`–`con` joins it to the port `1` of the second. -/
theorem σ_ne_one_of_conCon {E : Decomposition sig 2 2} (hψ : E.ψ = E.φ) (hl : E.φ.Linear)
    (hr : E.φ.Reduced) (hP : E.Plugs ruleConCon) : E.σ ≠ 1 := by
  obtain ⟨k, φ, ψ, σ⟩ := E
  simp only at hψ hl hr hP ⊢
  subst hψ
  obtain ⟨ι, hι, hE⟩ := hP
  have hc : ψ.net.cells = 0 := by
    have h := symm_decomposition_cells (D := ⟨k, ψ, ψ, σ⟩) rfl hE
    have h0 : (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0) from ruleConCon.net).cells = 0 := by decide
    rw [show ruleConCon.net.cells = 0 from h0] at h
    exact (add_eq_zero.1 h).1
  intro hσ
  let s : Fin 2 ⊕ Fin 2 ⊕ Fin (Rule.plug ψ ψ σ).internal → Term sig (Fin 2) :=
    Sum.elim (fun i => var i) (Sum.elim (fun j => var (j + 1)) fun _ => var 0)
  have hN : Net.Sol (ruleConCon.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) s := by
    refine ⟨s, ?_, fun _ _ => rfl⟩
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.1 he
    have key : ∀ e ∈ ruleConCon.net, e = s(pl 0, pr 1) ∨ e = s(pl 1, pr 0) := by
      decide
    rcases key e₀ he₀ with rfl | rfl <;> rfl
  obtain ⟨s', hs, hp⟩ := (hE.sol_iff s).2 hN
  have hinj : Function.Injective (Sum.map id (Sum.map id ι) :
      Fin 2 ⊕ Fin 2 ⊕ Fin ruleConCon.internal → _) :=
    Sum.map_injective.2 ⟨Function.injective_id, Sum.map_injective.2 ⟨Function.injective_id, hι⟩⟩
  have hfree : ∀ x : Fin 2 ⊕ Fin 2 ⊕ Fin ruleConCon.internal, (Net.vars ruleConCon.net).count x = 1 →
      s' (Sum.map id (Sum.map id ι) x) = s (Sum.map id (Sum.map id ι) x) := by
    intro x hx
    refine hp _ ((hE.free_iff _).2 ?_)
    rw [Net.vars_bind_var]
    exact (Multiset.count_map_eq_count' _ _ hinj x).trans hx
  have hl0 : s' (.inl 0) = var 0 := hfree (.inl 0) (by decide)
  have hl1 : s' (.inl 1) = var 1 := hfree (.inl 1) (by decide)
  have hr0 : s' (.inr (.inl 0)) = var 1 := hfree (.inr (.inl 0)) (by decide)
  have hs' : Net.Solves s' (ψ.net.bind (fun x => var (Rule.plugL (b := 2) (n := ψ.internal) x))
      + ψ.net.bind (fun x => var (Rule.plugR (a := 2) (m := ψ.internal) σ x))) := hs
  have h1 := solves_bind_var _ _ _ (fun e he => hs' e (Multiset.mem_add.2 (Or.inl he)))
  have h2 := solves_bind_var _ _ _ (fun e he => hs' e (Multiset.mem_add.2 (Or.inr he)))
  obtain ⟨y, hy0, hyint, hy⟩ := partner ψ hl hr hc 0
  have g1 : s' (.inl 0) = s' (Rule.plugL (b := 2) (n := ψ.internal) y) := hy _ h1
  have g2 : s' (.inr (.inl 0)) = s' (Rule.plugR (a := 2) (m := ψ.internal) σ y) := hy _ h2
  rw [hl0] at g1
  rw [hr0] at g2
  rcases y with j | l | w
  · have hj : j = 1 := by
      have : j ≠ 0 := fun h => hy0 (h ▸ rfl)
      omega
    subst hj
    exact absurd (Term.var.inj (g1.trans hl1)) (by decide)
  · have e : Rule.plugR (a := 2) (m := ψ.internal) σ
        (Sum.inr (Sum.inl l) : Fin 2 ⊕ Fin k ⊕ Fin ψ.internal) =
        Rule.plugL (b := 2) (n := ψ.internal) (Sum.inr (Sum.inl l)) := by
      rw [hσ]; rfl
    rw [e, ← g1] at g2
    exact absurd (Term.var.inj g2) (by decide)
  · exact absurd rfl (hyint w)

/-- **Page 86 for `con`–`con`: every decomposition data of the combinators has a permutation other
than the identity for `con`–`con`.** This holds for `system_wellFormed.decData`, whose `σ` is
chosen by `Classical.choose`: the data of page 86 is not vacuous on a rule with a crossing. -/
theorem conCon_σ_ne_one (D : system.DecData) :
    (D.dec Comb.con Comb.con ruleConCon rfl).σ ≠ 1 :=
  σ_ne_one_of_conCon (D.self _ _ rfl) (D.linear _ _ _ rfl).1 (D.reduced _ _ _ rfl).1
    (D.plug _ _ _ rfl)

/-- The permutation of `con`–`con` chosen by `decData` is an involution other than the
identity (page 86). -/
theorem decData_conCon_σ :
    Function.Involutive (system_wellFormed.decData.dec Comb.con Comb.con ruleConCon rfl).σ ∧
      (system_wellFormed.decData.dec Comb.con Comb.con ruleConCon rfl).σ ≠ 1 :=
  ⟨system_wellFormed.decData.involutive _ _ _ rfl, conCon_σ_ne_one _⟩

/-! ### `DecData` does not record well-formedness -/

/-- A rule `con`–`era` that joins the two auxiliary ports of the `con` cell. -/
def loopRule : Rule sig 2 0 := ⟨0, {s(pl 0, pl 1)}⟩

/-- A system that is **not** well formed: it has both a rule `era`–`con` (the erasing rule of the
combinators) and a rule `con`–`era` (`loopRule`), against page 73 ("no other rule is given for
`α_j`, `α_i`"). -/
def sysBoth : System sig where
  rule
    | .era, .con => some ruleEraBin
    | .con, .era => some loopRule
    | _, _ => none

/-- `sysBoth` is not an interaction system: `unique` fails. -/
theorem sysBoth_not_wellFormed : ¬ sysBoth.WellFormed := fun h =>
  absurd (h.unique Comb.era Comb.con (fun e => by cases e) rfl) (by simp [sysBoth])

/-- The decomposition of `loopRule` with no middle wire: everything in `φ`. -/
def decLoop : Decomposition sig 2 0 := ⟨0, loopRule, emptySide, 1⟩

theorem loopRule_linear : loopRule.Linear := ⟨by decide, by decide, by decide⟩

theorem loopRule_reduced : loopRule.Reduced := by
  intro e he
  rw [show e = s(pl 0, pl 1) from Multiset.mem_singleton.1 he]
  exact ⟨_, _, rfl, fun w => w.elim0⟩

theorem decLoop_plugs : decLoop.Plugs loopRule :=
  ⟨Fin.elim0, fun i => i.elim0, Equiv.of_eq (by decide)⟩

/-- The decomposition of each rule of `sysBoth`; arbitrary where there is no rule. -/
def decBoth : (α β : sig.Sym) → Decomposition sig (sig.arity α) (sig.arity β)
  | .era, .con => decEraBin
  | .con, .era => decLoop
  | _, _ => ⟨0, ⟨0, 0⟩, ⟨0, 0⟩, 1⟩

/-- Decomposition data for the system `sysBoth`, which is not well formed: every field of
`DecData` is met. -/
def decDataBoth : sysBoth.DecData where
  dec α β _ _ := decBoth α β
  plug := by
    intro α β r h
    cases α <;> cases β <;> cases h
    · exact decLoop_plugs
    · exact decEraBin_plugs
  linear := by
    intro α β r h
    cases α <;> cases β <;> cases h
    · exact ⟨loopRule_linear, emptySide_linear⟩
    · exact ⟨eraSide_linear, idSide_linear⟩
  reduced := by
    intro α β r h
    cases α <;> cases β <;> cases h
    · exact ⟨loopRule_reduced, emptySide_reduced⟩
    · exact ⟨eraSide_reduced, idSide_reduced⟩
  involutive := by
    intro α β r h
    cases α <;> cases β <;> cases h <;> exact fun _ => rfl
  self := by
    intro α r h
    cases α <;> cases h
  ne := by
    intro α β r h _
    cases α <;> cases β <;> cases h <;> rfl

/-- **Without well-formedness, `φ_{j,i} = ψ_{i,j}` fails for `DecData`** (page 86). In `sysBoth`
both rules `era`–`con` and `con`–`era` are given; the side of `con` against `era` is read from the
rule `con`–`era` and has no middle wire, while the `ψ` of `era`–`con`, which page 86 asks it to
equal, has two. So the compatibility proof of Fig. 10 must assume `I.WellFormed`, as
`System.DecData.sides_of_rule` does. -/
theorem sysBoth_sides_disagree :
    sysBoth.rule Comb.era Comb.con = some ruleEraBin ∧
      sysBoth.rule Comb.con Comb.era = some loopRule ∧
      (decDataBoth.rawSide Comb.con Comb.era).map RawSide.k = some 0 ∧
      (decDataBoth.rawψ Comb.con Comb.era ruleEraBin rfl).k = 2 := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  rw [System.DecData.rawSide_of_rule decDataBoth (α := Comb.con) (β := Comb.era) (r := loopRule) rfl]
  rfl

end Comb.CodeDataReview

end INet
