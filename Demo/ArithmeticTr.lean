import Demo.Arithmetic
import Demo.Print

/-!
# Demo: the computed translation of unary addition into the combinators

Lafont 1997, page 86 (normal form of a decomposition) and Fig. 10, pages 89–90 (the principal
net `[α]`). `Demo/Arithmetic.lean` proves `2 + 2 = 4` in the combinators through the translation
of Theorem 1, which uses choice. Here the same translation is built from data written by hand,
so it is computed.

* `arithEnum` — the symbols numbered `zero, succ, add ↦ 0, 1, 2`.
* `arithSide` — the expanded sides of the two rules, in both orientations:
  - `add` against `zero`: no middle wire; the side of `add` is `y = w, r = w`, the side of `zero`
    is empty;
  - `add` against `succ`: one middle wire `m`, `σ = 1`; the side of `add` is
    `y = v, r = S(w), m = add(v, w)`, the side of `succ` is `x = u, m = u`.
* `arith_sidesPlug` — these sides plug back into the rules (`System.SidesPlug`).
* `arithTr_strict`, `arithTr_compatible` — the translation `codeTranslationE arithEnum arithSide`
  is strict and compatible with the rules of unary addition and of the combinators.
* `two_plus_two_in_combinators_computed` — `2 + 2 = 4` through this translation.

The nets `[0]`, `[S]`, `[add]` are evaluated by `#guard` at the end of the file (the names
follow HVM: `con` is `γ`, `dup` is `δ`, `era` is `ε`):

| `α`   | cells | internal wires |
|-------|------:|---------------:|
| `0`   |    93 |             23 |
| `S`   |   128 |             34 |
| `add` |    95 |             23 |
-/

namespace INet.Demo.Arith

open Term

instance : DecidableEq sig.Sym := inferInstanceAs (DecidableEq Sym)

instance {ν : Type} [DecidableEq ν] : DecidableEq (Term sig ν) :=
  Comb.DecompositionCheck.termDecEq

/-! ## The numbering of the symbols -/

/-- The symbols numbered by hand: `zero, succ, add ↦ 0, 1, 2`. -/
def arithEnum : sig.Sym ≃ Fin 3 where
  toFun
    | .zero => 0
    | .succ => 1
    | .add => 2
  invFun i := match i with
    | 0 => (Sym.zero : sig.Sym)
    | 1 => (Sym.succ : sig.Sym)
    | 2 => (Sym.add : sig.Sym)
  left_inv α := by cases α <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-! ## The sides -/

section Sides

/-- The `i`-th auxiliary port of the cell of a side. -/
abbrev ap {a k m : ℕ} (i : Fin a) : Term sig (Fin a ⊕ Fin k ⊕ Fin m) := .var (.inl i)
/-- The `l`-th middle wire of a side. -/
abbrev mp {a k m : ℕ} (l : Fin k) : Term sig (Fin a ⊕ Fin k ⊕ Fin m) := .var (.inr (.inl l))
/-- The `w`-th internal wire of a side. -/
abbrev iw {a k m : ℕ} (w : Fin m) : Term sig (Fin a ⊕ Fin k ⊕ Fin m) := .var (.inr (.inr w))

/-- The side of `add` against `zero` (page 86): `y = w, r = w`, no middle wire. -/
def sideAddZero : Rule sig 2 0 := ⟨1, s(ap 0, iw 0) ::ₘ s(ap 1, iw 0) ::ₘ 0⟩

/-- The side of `zero` against `add` (page 86): empty. -/
def sideZeroAdd : Rule sig 0 0 := ⟨0, 0⟩

/-- The side of `add` against `succ` (page 86): `y = v, r = S(w), m = add(v, w)`. -/
def sideAddSucc : Rule sig 2 1 :=
  ⟨2, s(ap 0, iw 0) ::ₘ s(ap 1, mkSucc (iw 1)) ::ₘ s(mp 0, mkAdd (iw 0) (iw 1)) ::ₘ 0⟩

/-- The side of `succ` against `add` (page 86): `x = u, m = u`. -/
def sideSuccAdd : Rule sig 1 1 := ⟨1, s(ap 0, iw 0) ::ₘ s(mp 0, iw 0) ::ₘ 0⟩

theorem sideAddZero_linear : sideAddZero.Linear := ⟨by decide, by decide, by decide⟩
theorem sideZeroAdd_linear : sideZeroAdd.Linear := ⟨by decide, by decide, by decide⟩
theorem sideAddSucc_linear : sideAddSucc.Linear := ⟨by decide, by decide, by decide⟩
theorem sideSuccAdd_linear : sideSuccAdd.Linear := ⟨by decide, by decide, by decide⟩

theorem sideAddZero_expanded : sideAddZero.Expanded := by
  show ∀ e ∈ (s(ap 0, iw 0) ::ₘ s(ap 1, iw 0) ::ₘ 0 : Net sig (Fin 2 ⊕ Fin 0 ⊕ Fin 1)),
    ∃ p t, e = s(var p, t) ∧
    (∀ w : Fin 1, p ≠ .inr (.inr w)) ∧ ∀ x ∈ t.vars, ∃ w : Fin 1, x = .inr (.inr w)
  intro e he
  obtain rfl | rfl : e = _ ∨ e = _ := by
    rcases Multiset.mem_cons.1 he with h | he; · exact .inl h
    rcases Multiset.mem_cons.1 he with h | he; · exact .inr h
    exact absurd he (Multiset.notMem_zero _)
  all_goals
    exact ⟨_, _, rfl, fun w => by simp, fun x hx => by
      rw [vars_var, Multiset.mem_singleton] at hx; exact ⟨_, hx⟩⟩

theorem sideZeroAdd_expanded : sideZeroAdd.Expanded := fun e he =>
  absurd he (Multiset.notMem_zero e)

theorem sideAddSucc_expanded : sideAddSucc.Expanded := by
  show ∀ e ∈ (s(ap 0, iw 0) ::ₘ s(ap 1, mkSucc (iw 1)) ::ₘ s(mp 0, mkAdd (iw 0) (iw 1)) ::ₘ 0 :
      Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 2)), ∃ p t, e = s(var p, t) ∧
    (∀ w : Fin 2, p ≠ .inr (.inr w)) ∧ ∀ x ∈ t.vars, ∃ w : Fin 2, x = .inr (.inr w)
  intro e he
  obtain rfl | rfl | rfl : e = _ ∨ e = _ ∨ e = _ := by
    rcases Multiset.mem_cons.1 he with h | he; · exact .inl h
    rcases Multiset.mem_cons.1 he with h | he; · exact .inr (.inl h)
    rcases Multiset.mem_cons.1 he with h | he; · exact .inr (.inr h)
    exact absurd he (Multiset.notMem_zero _)
  · exact ⟨_, _, rfl, fun w => by simp, fun x hx => by
      rw [vars_var, Multiset.mem_singleton] at hx; exact ⟨_, hx⟩⟩
  · exact ⟨_, _, rfl, fun w => by simp, fun x hx => by
      rw [vars_mkSucc, vars_var, Multiset.mem_singleton] at hx; exact ⟨_, hx⟩⟩
  · refine ⟨_, _, rfl, fun w => by simp, fun x hx => ?_⟩
    rw [vars_mkAdd, vars_var, vars_var, Multiset.mem_add, Multiset.mem_singleton,
      Multiset.mem_singleton] at hx
    rcases hx with hx | hx <;> exact ⟨_, hx⟩

theorem sideSuccAdd_expanded : sideSuccAdd.Expanded := by
  show ∀ e ∈ (s(ap 0, iw 0) ::ₘ s(mp 0, iw 0) ::ₘ 0 : Net sig (Fin 1 ⊕ Fin 1 ⊕ Fin 1)),
    ∃ p t, e = s(var p, t) ∧
    (∀ w : Fin 1, p ≠ .inr (.inr w)) ∧ ∀ x ∈ t.vars, ∃ w : Fin 1, x = .inr (.inr w)
  intro e he
  obtain rfl | rfl : e = _ ∨ e = _ := by
    rcases Multiset.mem_cons.1 he with h | he; · exact .inl h
    rcases Multiset.mem_cons.1 he with h | he; · exact .inr h
    exact absurd he (Multiset.notMem_zero _)
  all_goals
    exact ⟨_, _, rfl, fun w => by simp, fun x hx => by
      rw [vars_var, Multiset.mem_singleton] at hx; exact ⟨_, hx⟩⟩

/-- The expanded sides of unary addition (page 86), in both orientations; none for the pairs
without a rule. -/
def arithSide : ∀ α : sig.Sym, sig.Sym → Option (ExpSide sig (sig.arity α))
  | .add, .zero => some ⟨0, sideAddZero, 1, sideAddZero_linear, sideAddZero_expanded,
      fun _ => rfl⟩
  | .zero, .add => some ⟨0, sideZeroAdd, 1, sideZeroAdd_linear, sideZeroAdd_expanded,
      fun _ => rfl⟩
  | .add, .succ => some ⟨1, sideAddSucc, 1, sideAddSucc_linear, sideAddSucc_expanded,
      fun _ => rfl⟩
  | .succ, .add => some ⟨1, sideSuccAdd, 1, sideSuccAdd_linear, sideSuccAdd_expanded,
      fun _ => rfl⟩
  | _, _ => none

/-- One wire substitution between two nets given as texts. -/
theorem equiv_wire {ν : Type} [DecidableEq ν] {N M : Net sig ν} (x : ν) (t a b : Term sig ν)
    (Δ : Net sig ν) (hlin : Net.Linear (s(var x, t) ::ₘ s(a, b) ::ₘ Δ)) (hx : x ∈ a.vars + b.vars)
    (hN : N = s(var x, t) ::ₘ s(a, b) ::ₘ Δ) (hM : M = s(a.subst x t, b.subst x t) ::ₘ Δ) :
    Equiv N M := by
  rw [hN, hM]
  exact (Wire.mk x t a b Δ hlin hx).equiv

/-- Plugging the two sides of `add`–`zero` gives back the rule `y = r` (page 86). -/
theorem addZero_plugs :
    (⟨0, sideAddZero, sideZeroAdd, 1⟩ : Decomposition sig 2 0).Plugs ruleAddZero := by
  refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
  exact equiv_wire (ν := Fin 2 ⊕ Fin 0 ⊕ Fin 1)
    (N := (show Net sig (Fin 2 ⊕ Fin 0 ⊕ Fin 1) from
      (Rule.plug sideAddZero sideZeroAdd 1).net))
    (M := (show Net sig (Fin 2 ⊕ Fin 0 ⊕ Fin 1) from ruleAddZero.net.bind
      fun x => var (Sum.map id (Sum.map id (Fin.elim0 : Fin 0 → Fin 1)) x)))
    (.inr (.inr 0)) (ap 0) (ap 1) (iw 0) 0
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)

/-- The plugged net of `add`–`succ` (page 86) after the wire `v` is substituted. -/
private abbrev addSuccMid₁ : Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 4) :=
  s(iw 0, mkAdd (ap 0) (iw 2)) ::ₘ s(mp 0, iw 3) ::ₘ s(iw 0, iw 3) ::ₘ
    s(ap 1, mkSucc (iw 2)) ::ₘ 0

/-- The plugged net of `add`–`succ` after the wires `v` and `u` are substituted. -/
private abbrev addSuccMid₂ : Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 4) :=
  s(iw 0, mp 0) ::ₘ s(iw 0, mkAdd (ap 0) (iw 2)) ::ₘ s(ap 1, mkSucc (iw 2)) ::ₘ 0

/-- Plugging the two sides of `add`–`succ` through `σ = 1` gives back the rule
`r = S(w), x = add(y, w)` (page 86), up to three wires. -/
theorem addSucc_plugs :
    (⟨1, sideAddSucc, sideSuccAdd, 1⟩ : Decomposition sig 2 1).Plugs ruleAddSucc := by
  refine ⟨fun _ => ⟨2, by decide⟩, fun i j _ => Subsingleton.elim (α := Fin 1) i j, ?_⟩
  have h₁ := equiv_wire (ν := Fin 2 ⊕ Fin 1 ⊕ Fin 4)
    (N := (show Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 4) from
      (Rule.plug sideAddSucc sideSuccAdd 1).net))
    (M := addSuccMid₁)
    (.inr (.inr 1)) (ap 0) (iw 0) (mkAdd (iw 1) (iw 2))
    (s(mp 0, iw 3) ::ₘ s(iw 0, iw 3) ::ₘ s(ap 1, mkSucc (iw 2)) ::ₘ 0)
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have h₂ := equiv_wire (ν := Fin 2 ⊕ Fin 1 ⊕ Fin 4) (N := addSuccMid₁) (M := addSuccMid₂)
    (.inr (.inr 3)) (mp 0) (iw 0) (iw 3)
    (s(iw 0, mkAdd (ap 0) (iw 2)) ::ₘ s(ap 1, mkSucc (iw 2)) ::ₘ 0)
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have h₃ := equiv_wire (ν := Fin 2 ⊕ Fin 1 ⊕ Fin 4) (N := addSuccMid₂)
    (M := (show Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 4) from ruleAddSucc.net.bind
      fun x => var (Sum.map id (Sum.map id (fun _ : Fin 1 => (2 : Fin 4))) x)))
    (.inr (.inr 0)) (mp 0) (iw 0) (mkAdd (ap 0) (iw 2))
    (s(ap 1, mkSucc (iw 2)) ::ₘ 0)
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  exact h₁.trans (h₂.trans h₃)

/-- **The hand-written sides plug back into the rules of unary addition** (Lafont 1997, page 86,
normal form of a decomposition; Fig. 10, pages 89–90): for `add`–`zero` and `add`–`succ`, both
sides are defined, share `k` and `σ`, and plug back the rule. -/
theorem arith_sidesPlug : system.SidesPlug arithSide := by
  intro α β r h
  cases α <;> cases β <;> cases h
  · exact ⟨0, sideAddZero, sideZeroAdd, 1, fun _ => rfl, sideAddZero_linear,
      sideAddZero_expanded, sideZeroAdd_linear, sideZeroAdd_expanded, rfl, rfl, addZero_plugs⟩
  · exact ⟨1, sideAddSucc, sideSuccAdd, 1, fun _ => rfl, sideAddSucc_linear,
      sideAddSucc_expanded, sideSuccAdd_linear, sideSuccAdd_expanded, rfl, rfl, addSucc_plugs⟩

end Sides

/-! ## The computed translation -/

/-- The translation of Fig. 10 (pages 89–90) for unary addition, numbered by `arithEnum` and built
from the sides `arithSide`. It is computed: no choice is used. -/
abbrev arithTr : Translation sig Comb.sig := Comb.codeTranslationE arithEnum arithSide

/-- **The computed translation is strict** (definition page 80, Fig. 10 pages 89–90): no `[α]`
is a wire. -/
theorem arithTr_strict : (Comb.codeTranslationE arithEnum arithSide).Strict :=
  Comb.codeTranslationE_strict arithEnum arithSide

/-- **The computed translation is compatible** (Lafont 1997, Section 2.7, Fig. 10, pages 89–90):
for each rule of unary addition, the two translated cells plugged by their roots reduce in the
combinators, up to wires, to a translation of the right member. -/
theorem arithTr_compatible :
    (Comb.codeTranslationE arithEnum arithSide).Compatible system Comb.system :=
  Comb.codeTranslationE_compatible_of_sides arithEnum arith_sidesPlug

/-- **`2 + 2 = 4` in the combinators, through the computed translation** (Theorem 1, page 89,
applied to unary addition): every translation `N'` of the net of `2 + 2` by
`codeTranslationE arithEnum arithSide` reduces, by the rules of `con`, `dup` and `era` and up to
wires, to a net that is the same graph as a translation of the net of `4`. -/
theorem two_plus_two_in_combinators_computed :
    ∀ N' : Net Comb.sig ℕ, (Comb.codeTranslationE arithEnum arithSide).NetTr twoPlusTwo N' →
      ∃ M₁ M' : Net Comb.sig ℕ, StepsE Comb.system N' M₁ ∧ Equiv M₁ M' ∧
        (Comb.codeTranslationE arithEnum arithSide).NetTr four M' := by
  intro N' hN'
  obtain ⟨M₁, M₂, h1, e1, t2⟩ := Translation.Compatible.stepsE system_wellFormed.linear
    Comb.system_wellFormed.linear arithTr_compatible twoPlusTwo_steps.stepsE hN'
  obtain ⟨M', t', e'⟩ := Translation.NetTr.of_equiv fourUnfolded_equiv t2
  exact ⟨M₁, M', h1, e1.trans e', t'⟩

/-- The statement above is not empty: the net of `2 + 2` has a translation by
`codeTranslationE arithEnum arithSide`. -/
example : ∃ N' : Net Comb.sig ℕ, (Comb.codeTranslationE arithEnum arithSide).NetTr twoPlusTwo N' :=
  twoPlusTwo_has_translation _

/-! ## Evaluation -/

-- The number of internal wires of `[0]`, `[S]`, `[add]`.
#guard [(Comb.codeNetE arithEnum arithSide (Sym.zero : sig.Sym)).internal,
  (Comb.codeNetE arithEnum arithSide (Sym.succ : sig.Sym)).internal,
  (Comb.codeNetE arithEnum arithSide (Sym.add : sig.Sym)).internal] == [23, 34, 23]

-- The number of cells of `[0]`, `[S]`, `[add]`.
#guard [(Comb.codeNetE arithEnum arithSide (Sym.zero : sig.Sym)).tree.size,
  (Comb.codeNetE arithEnum arithSide (Sym.succ : sig.Sym)).tree.size,
  (Comb.codeNetE arithEnum arithSide (Sym.add : sig.Sym)).tree.size] == [93, 128, 95]

-- `[0]` printed in full: it has no port, so its names `0`, …, `22` are its internal wires, each
-- occurring twice; the root is a `dup` cell (Fig. 10, page 89).
#guard Comb.pnetToStr (Comb.codeNetE arithEnum arithSide (Sym.zero : sig.Sym)) ==
  "dup(con(con(era, con(era, con(con(con(era, 1), 1), era))), con(con(era, era), con(co" ++
  "n(con(16, con(17, con(18, con(19, con(20, con(21, 22)))))), con(con(con(con(con(con(" ++
  "con(13, con(con(con(con(con(12, era), era), 14), 13), 22)), 8), con(con(con(con(con(" ++
  "era, 7), era), 9), 8), 20)), 19), con(7, con(con(era, con(6, con(4, 5))), era))), co" ++
  "n(12, con(con(con(11, con(3, con(4, 10))), era), era))), con(con(con(con(con(con(con" ++
  "(14, 11), 9), 6), 21), 5), 10), con(con(era, con(era, con(con(con(era, 2), 2), era))" ++
  "), con(con(era, con(era, con(con(con(16, 17), 3), 18))), con(con(era, era), con(con(" ++
  "con(15, 15), era), era))))))), 0))), 0)"
#guard (List.range 23).all fun x =>
  ((Comb.codeNetE arithEnum arithSide (Sym.zero : sig.Sym)).inst (fun i => .var (i : ℕ))
    (fun w => (w : ℕ))).vars.count x == 2

end INet.Demo.Arith
