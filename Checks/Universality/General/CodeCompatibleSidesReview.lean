import Checks.Universality.General.CodeCompatibleSidesCheck

/-!
# Review of `System.SidesPlug` (pages 86, 89–90)

Checks written for the review of issue #262 (PR #261,
`InteractionCombinators/Universality/General/CodeCompatibleSides.lean`).

* **Self-rules.** For a rule `α`–`α`, `SidesPlug` asks `side α α` to be both the side `φ` of the
  first cell and the side `ψ` of the second, so it forces `φ = ψ` (`sidesPlug_self`). This is
  the paper's `φ_{i,i} = ψ_{i,i}` (page 86, `φ_{j,i} = ψ_{i,j}` with `i = j`), and it is
  satisfiable: the sides of `decData system_wellFormed` give it for `con`–`con` and `dup`–`dup`
  (`sidesPlug_conCon`, `sidesPlug_dupDup`).
* **No well-formedness is assumed, and this is a real generalization.** `SidesPlug` does not imply
  `System.WellFormed`:
  - `systemEraPair` has one rule, `era`–`era`, whose right member is the active pair
    `era = era`. It is not reduced, so the system is not well formed (`systemEraPair_not_wf`), yet
    the sides `era = m₀` on both cells, plugged through the identity, give it back
    (`systemEraPair_sidesPlug`), and `codeTranslation_compatible_of_sides` applies to it
    (`systemEraPair_compatible`). The other three conditions hold for it
    (`systemEraPair_linear`, `systemEraPair_unique`, `systemEraPair_symm`).
  - `systemBoth`, on two symbols without auxiliary ports, has the empty rule for `true`–`false` and
    for `false`–`true`. It breaks `unique` (`systemBoth_not_wf`) and satisfies `SidesPlug` with
    empty sides (`systemBoth_sidesPlug`).
-/

namespace INet.Comb.CodeCompatibleSidesReview

open Term

/-! ## Self-rules -/

/-- **A self-rule has the same side on both cells** (Lafont 1997, page 86: `φ_{j,i} = ψ_{i,j}`,
so `φ_{i,i} = ψ_{i,i}`): under `System.SidesPlug`, a rule `α`–`α` is plugged back from the side
`side α α` against itself, through its involution. -/
theorem sidesPlug_self {S : Signature} {I : System S}
    {side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α))} (hside : I.SidesPlug side)
    {α : S.Sym} {r : Rule S (S.arity α) (S.arity α)} (h : I.rule α α = some r) :
    ∃ (k : ℕ) (φ : Rule S (S.arity α) k) (σ : _root_.Equiv.Perm (Fin k))
      (hσ : Function.Involutive σ) (hl : φ.Linear) (he : φ.Expanded),
      side α α = some ⟨k, φ, σ, hl, he, hσ⟩ ∧
      (⟨k, φ, φ, σ⟩ : Decomposition S (S.arity α) (S.arity α)).Plugs r := by
  obtain ⟨k, φ, ψ, σ, hσ, hl, he, hl', he', hs, hs', hP⟩ := hside h
  rw [hs] at hs'
  cases hs'
  exact ⟨k, φ, σ, hσ, hl, he, hs, hP⟩

/-- **`con`–`con` from a single side** (page 86): the sides of decomposition data of the
combinators plug back `ruleConCon` from the side of `con` against `con`, used for both cells. -/
theorem sidesPlug_conCon :
    ∃ (k : ℕ) (φ : Rule sig 2 k) (σ : _root_.Equiv.Perm (Fin k)),
      Function.Involutive σ ∧
      (System.WellFormed.decData system_wellFormed).side Comb.con Comb.con ≠ none ∧
      (⟨k, φ, φ, σ⟩ : Decomposition sig 2 2).Plugs ruleConCon := by
  obtain ⟨k, φ, σ, hσ, hl, he, hs, hP⟩ :=
    sidesPlug_self CodeCompatibleSidesCheck.sidesPlug_system (α := Comb.con) (r := ruleConCon) rfl
  refine ⟨k, φ, σ, hσ, ?_, hP⟩
  rw [hs]
  exact Option.some_ne_none _

/-- **`dup`–`dup` from a single side** (page 86): the same for `ruleDupDup`. -/
theorem sidesPlug_dupDup :
    ∃ (k : ℕ) (φ : Rule sig 2 k) (σ : _root_.Equiv.Perm (Fin k)),
      Function.Involutive σ ∧
      (System.WellFormed.decData system_wellFormed).side Comb.dup Comb.dup ≠ none ∧
      (⟨k, φ, φ, σ⟩ : Decomposition sig 2 2).Plugs ruleDupDup := by
  obtain ⟨k, φ, σ, hσ, hl, he, hs, hP⟩ :=
    sidesPlug_self CodeCompatibleSidesCheck.sidesPlug_system (α := Comb.dup) (r := ruleDupDup) rfl
  refine ⟨k, φ, σ, hσ, ?_, hP⟩
  rw [hs]
  exact Option.some_ne_none _

/-! ## A system that is not reduced -/

/-- A rule `era`–`era` whose right member is the active pair `era = era`. -/
def ruleEraPair : Rule sig 0 0 := ⟨0, s(mkEra, mkEra) ::ₘ 0⟩

/-- The system with the single rule `ruleEraPair`. -/
def systemEraPair : System sig where
  rule
    | Comb.era, Comb.era => some ruleEraPair
    | _, _ => none

/-- The side `era = m₀`: no auxiliary port, one middle wire. -/
def eraSide1 : Rule sig 0 1 := ⟨0, s(var (.inr (.inl 0)), mkEra) ::ₘ 0⟩

/-- The side `era = m₀` is linear (page 86). -/
theorem eraSide1_linear : eraSide1.Linear := ⟨by decide, by decide, by decide⟩

/-- The side `era = m₀` is in expanded form (page 86). -/
theorem eraSide1_expanded : eraSide1.Expanded := by
  intro e he
  rw [show eraSide1.net = s(var (.inr (.inl 0)), mkEra) ::ₘ 0 from rfl] at he
  rw [Multiset.mem_cons, or_iff_left (Multiset.notMem_zero e)] at he
  subst he
  refine ⟨_, _, rfl, fun w => w.elim0, fun x hx => ?_⟩
  rw [vars_mkEra] at hx
  exact absurd hx (Multiset.notMem_zero x)

/-- The sides of `systemEraPair`: `era = m₀` against `era`, with the identity permutation. -/
def eraPairSide : ∀ α : sig.Sym, sig.Sym → Option (ExpSide sig (sig.arity α))
  | Comb.era, Comb.era => some ⟨1, eraSide1, 1, eraSide1_linear, eraSide1_expanded, fun _ => rfl⟩
  | _, _ => none

/-- Plugging `era = m₀` against itself through the identity gives `era = era`. -/
theorem eraPair_plugs :
    (⟨1, eraSide1, eraSide1, 1⟩ : Decomposition sig 0 0).Plugs ruleEraPair := by
  refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
  exact DecompositionReview.equiv_wire_of_eq (ν := Fin 0 ⊕ Fin 0 ⊕ Fin 1)
    (N := (show Net sig (Fin 0 ⊕ Fin 0 ⊕ Fin 1) from
      (Rule.plug eraSide1 eraSide1 1).net))
    (M := (show Net sig (Fin 0 ⊕ Fin 0 ⊕ Fin 1) from ruleEraPair.net.bind
      fun x => var (Sum.map id (Sum.map id (Fin.elim0 : Fin 0 → Fin 1)) x)))
    (.inr (.inr 0)) mkEra (var (.inr (.inr 0))) mkEra 0
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)

/-- **`SidesPlug` holds for a system whose rule is not reduced** (pages 86, 89–90). -/
theorem systemEraPair_sidesPlug : systemEraPair.SidesPlug eraPairSide := by
  intro α β r h
  cases α <;> cases β <;> cases h
  exact ⟨1, eraSide1, eraSide1, 1, fun _ => rfl, eraSide1_linear, eraSide1_expanded,
    eraSide1_linear, eraSide1_expanded, rfl, rfl, eraPair_plugs⟩

/-- **`systemEraPair` is not well formed** (page 73: right members must be reduced): its rule is
the active pair `era = era`. -/
theorem systemEraPair_not_wf : ¬ systemEraPair.WellFormed := by
  intro hW
  obtain ⟨p, t, he, -⟩ := hW.reduced Comb.era Comb.era ruleEraPair rfl _
    (Multiset.mem_singleton_self _)
  rcases Sym2.eq_iff.1 he with ⟨h, -⟩ | ⟨-, h⟩ <;> cases h

/-- The rule of `systemEraPair` is linear. -/
theorem systemEraPair_linear : ∀ α β r, systemEraPair.rule α β = some r → r.Linear := by
  intro α β r h
  cases α <;> cases β <;> cases h
  exact ⟨fun i => i.elim0, fun j => j.elim0, fun w => w.elim0⟩

/-- `systemEraPair` has no rule between distinct symbols, so `unique` holds. -/
theorem systemEraPair_unique :
    ∀ α β, α ≠ β → (systemEraPair.rule α β).isSome → systemEraPair.rule β α = none := by
  intro α β hne h
  cases α <;> cases β <;> first | exact absurd rfl hne | cases h

/-- The rule `era`–`era` of `systemEraPair` is symmetric: it has no auxiliary port. -/
theorem systemEraPair_symm : ∀ α r, systemEraPair.rule α α = some r →
    ∃ π : _root_.Equiv.Perm (Fin r.internal),
      Equiv r.swap.net (r.net.bind fun x => Term.var (Sum.map id (Sum.map id π) x)) := by
  intro α r h
  cases α <;> cases h
  have e₁ : (s(mkEra, mkEra) ::ₘ 0 : Net sig (Fin 0 ⊕ Fin 0 ⊕ Fin 0)) =
      (show Net sig (Fin 0 ⊕ Fin 0 ⊕ Fin 0) from ruleEraPair.swap.net) := by decide
  have e₂ : (s(mkEra, mkEra) ::ₘ 0 : Net sig (Fin 0 ⊕ Fin 0 ⊕ Fin 0)) =
      (show Net sig (Fin 0 ⊕ Fin 0 ⊕ Fin 0) from ruleEraPair.net) := by decide
  exact Rule.symm_of_equiv (Equiv.of_eq (e₁.symm.trans e₂))

/-- **The translation of Fig. 10 is compatible for a system that is not well formed** (pages
89–90): `codeTranslation_compatible_of_sides` applies to `systemEraPair`. -/
theorem systemEraPair_compatible :
    (codeTranslation eraPairSide).Compatible systemEraPair system :=
  codeTranslation_compatible_of_sides systemEraPair_sidesPlug

/-! ## A system with a rule in both orders -/

/-- Two symbols without auxiliary ports. -/
abbrev sigB : Signature := ⟨Bool, fun _ => 0⟩

/-- The empty rule. -/
def ruleEmpty : Rule sigB 0 0 := ⟨0, 0⟩

/-- The empty rule for `true`–`false` and for `false`–`true`. -/
def systemBoth : System sigB where
  rule
    | true, false => some ruleEmpty
    | false, true => some ruleEmpty
    | _, _ => none

/-- The empty rule is linear. -/
theorem ruleEmpty_linear : ruleEmpty.Linear :=
  ⟨fun i => i.elim0, fun j => j.elim0, fun w => w.elim0⟩

/-- The empty rule is in expanded form (page 86). -/
theorem ruleEmpty_expanded : ruleEmpty.Expanded :=
  fun e he => absurd he (Multiset.notMem_zero e)

/-- Every side is the empty side, with no middle wire. -/
def bothSide : ∀ α : sigB.Sym, sigB.Sym → Option (ExpSide sigB (sigB.arity α)) :=
  fun _ _ => some ⟨0, ruleEmpty, 1, ruleEmpty_linear, ruleEmpty_expanded, fun _ => rfl⟩

/-- **`SidesPlug` holds for a system with a rule in both orders** (pages 86, 89–90). -/
theorem systemBoth_sidesPlug : systemBoth.SidesPlug bothSide := by
  intro α β r h
  cases α <;> cases β <;> cases h <;>
  exact ⟨0, ruleEmpty, ruleEmpty, 1, fun _ => rfl, ruleEmpty_linear, ruleEmpty_expanded,
    ruleEmpty_linear, ruleEmpty_expanded, rfl, rfl,
    ⟨Fin.elim0, fun i => i.elim0, Equiv.of_eq rfl⟩⟩

/-- **`systemBoth` is not well formed** (page 73: at most one rule for a pair of symbols): it
has a rule for `true`–`false` and one for `false`–`true`. -/
theorem systemBoth_not_wf : ¬ systemBoth.WellFormed := by
  intro hW
  have := hW.unique true false (by decide) rfl
  cases this

end INet.Comb.CodeCompatibleSidesReview
