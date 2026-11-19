import InteractionCombinators.Lafont.StrongConfluenceNoReduced

/-!
# Non-vacuity of Proposition 1 without reducedness (page 73)

Issue #264. A system that satisfies the three hypotheses of `Step.strong_confluence_of` and
`StepE.strong_confluence_of` but is not well-formed: one symbol `o` without auxiliary ports, and
the rule `o`–`o` whose right member is again the active pair `o = o`. The rule is linear (it has
no names) and symmetric (its swap is itself), but its right member is not reduced, so the system
is not `System.WellFormed` (`sysLoop_not_wellFormed`) and `Step.strong_confluence` does not apply.
The new theorems apply to the net `o = o, o = o`, which reduces in two ways.
-/

namespace INet.StrongConfluenceNoReducedCheck

/-- One symbol. -/
inductive LSym : Type
  | o
  deriving DecidableEq

/-- The signature with the symbol `o` of arity `0`. -/
def sigL : Signature where
  Sym := LSym
  arity := fun _ => 0

instance : DecidableEq sigL.Sym := inferInstanceAs (DecidableEq LSym)

instance {ν : Type} [DecidableEq ν] : DecidableEq (Term sigL ν) := Comb.DecompositionCheck.termDecEq

/-- The cell `o`. -/
def cO {ν : Type} : Term sigL ν := .app LSym.o fun i => i.elim0

/-- The rule `o`–`o` whose right member is the active pair `o = o`. -/
def loop : Rule sigL 0 0 := ⟨0, s(cO, cO) ::ₘ 0⟩

/-- The system with the single rule `loop`. -/
def sysLoop : System sigL where
  rule
    | .o, .o => some loop

/-- `loop` is linear: it has no ports and no internal wires. -/
theorem loop_linear : loop.Linear :=
  ⟨fun i => i.elim0, fun j => j.elim0, fun w => w.elim0⟩

/-- Hypothesis `linear` of Proposition 1 holds for `sysLoop`. -/
theorem sysLoop_linear : ∀ α β r, sysLoop.rule α β = some r → r.Linear := by
  intro α β r h
  cases α; cases β; cases h
  exact loop_linear

/-- Hypothesis `unique` holds for `sysLoop`: it has a single symbol. -/
theorem sysLoop_unique : ∀ α β, α ≠ β → (sysLoop.rule α β).isSome → sysLoop.rule β α = none := by
  intro α β h
  cases α; cases β
  exact absurd rfl h

/-- `loop` read from the other cell is `loop`. -/
theorem loop_swap : (show Net sigL (Fin 0 ⊕ Fin 0 ⊕ Fin 0) from loop.swap.net) =
    (show Net sigL (Fin 0 ⊕ Fin 0 ⊕ Fin 0) from loop.net).bind
      fun x => Term.var (Sum.map id (Sum.map id (1 : _root_.Equiv.Perm (Fin 0))) x) := by
  decide

/-- Hypothesis `symm` holds for `sysLoop`. -/
theorem sysLoop_symm : ∀ α r, sysLoop.rule α α = some r → ∃ π : _root_.Equiv.Perm (Fin r.internal),
    Equiv r.swap.net (r.net.bind fun x => Term.var (Sum.map id (Sum.map id π) x)) := by
  intro α r h
  cases α; cases h
  exact ⟨1, Equiv.of_eq loop_swap⟩

/-- `loop` is not reduced: its equation `o = o` has no port on either side. -/
theorem loop_not_reduced : ¬ loop.Reduced := by
  intro h
  obtain ⟨p, t, he, -⟩ := h s(cO, cO) (Multiset.mem_cons_self (s(cO, cO)) (0 : Net sigL _))
  rcases Sym2.eq_iff.1 he with ⟨e, -⟩ | ⟨-, e⟩ <;> cases e

/-- `sysLoop` is not well-formed, so `Step.strong_confluence` does not apply to it. -/
theorem sysLoop_not_wellFormed : ¬ sysLoop.WellFormed :=
  fun h => loop_not_reduced (h.reduced _ _ _ rfl)

/-- The net `o = o, o = o`. -/
def twoLoops : Net sigL ℕ := s(cO, cO) ::ₘ s(cO, cO) ::ₘ 0

/-- `o = o, o = o` has no names. -/
theorem twoLoops_vars : Net.vars twoLoops = 0 := rfl

/-- `o = o, o = o` is linear. -/
theorem twoLoops_linear : twoLoops.Linear := by
  intro x
  rw [twoLoops_vars]
  simp

/-- `o = o, o = o` reduces in one interaction (firing either pair) to `o = o, o = o`. -/
theorem twoLoops_step : Step sysLoop twoLoops twoLoops := by
  have := Step.mk (I := sysLoop) LSym.o LSym.o loop rfl (fun i => i.elim0) (fun i => i.elim0)
    (s(cO, cO) ::ₘ 0) (fun w => w.elim0) (fun w => w.elim0) (fun w => w.elim0)
  have e : (loop.inst (fun i => i.elim0) (fun i => i.elim0) fun w => w.elim0) +
      s(cO, cO) ::ₘ (0 : Net sigL ℕ) = twoLoops := by
    decide
  convert this using 1
  all_goals first | exact e.symm | decide

/-- Non-vacuity of `Step.strong_confluence_of`: it applies to the system `sysLoop`, which is not
well-formed. -/
example : Equiv twoLoops twoLoops ∨
    ∃ P₁ P₂, Step sysLoop twoLoops P₁ ∧ Step sysLoop twoLoops P₂ ∧ Equiv P₁ P₂ :=
  Step.strong_confluence_of sysLoop_linear sysLoop_unique sysLoop_symm twoLoops_linear
    twoLoops_step twoLoops_step

/-- Non-vacuity of `StepE.strong_confluence_of` on the system `sysLoop`, which is not
well-formed. -/
example : Equiv twoLoops twoLoops ∨
    ∃ P₁ P₂, StepE sysLoop twoLoops P₁ ∧ StepE sysLoop twoLoops P₂ ∧ Equiv P₁ P₂ :=
  StepE.strong_confluence_of sysLoop_linear sysLoop_unique sysLoop_symm twoLoops_linear
    ⟨_, Equiv.refl _, twoLoops_step⟩ ⟨_, Equiv.refl _, twoLoops_step⟩

end INet.StrongConfluenceNoReducedCheck
