import InteractionCombinators

/-!
# Demo: unary arithmetic, translated into the interaction combinators

Lafont's first example of an interaction system (*Interaction Nets*, POPL 1990): the numerals
`0` and `S`, and addition. A cell `add` has its principal port on its first argument; its two
auxiliary ports are the second argument `y` and the result `r`:

* `add(y, r) ~ 0`      reduces to   `y ~ r`
* `add(y, r) ~ S(x)`   reduces to   `r ~ S(w)`, `x ~ add(y, w)`

The second rule has an `add` cell in its right member, so the system is recursive: it falls under
the general case of Theorem 1 (Lafont 1997, Section 2.7, Fig. 10), not the recursion-free one.

This file shows:

* `system_wellFormed` — the system is an interaction system in the sense of the formalization;
* `two_plus_two` — the net of `2 + 2` reduces to the net of `4`;
* `exists_translation` — it has a strict translation into the combinators (Theorem 1);
* `two_plus_two_in_combinators` — under that translation, any translation of the net of `2 + 2`
  reduces, in the combinators `con`, `dup`, `era`, to a translation of the net of `4`.

The translation is the one built in the proof of Theorem 1. It is not computed here: its
construction uses choice (an enumeration of the symbols and the decomposition of the rules), so
the combinator net itself is not displayed.
-/

namespace INet.Demo.Arith

open Term

/-- The symbols: `0`, successor and addition. -/
inductive Sym : Type
  | zero | succ | add
  deriving DecidableEq

/-- `0` has no auxiliary port, `S` has one, `add` has two (second argument, result). -/
def sig : Signature where
  Sym := Sym
  arity
    | .zero => 0
    | .succ => 1
    | .add => 2

instance : Finite sig.Sym :=
  Finite.of_injective (fun α : Sym => (match α with | .zero => 0 | .succ => 1 | .add => 2 : Fin 3))
    (by intro α β h; cases α <;> cases β <;> first | rfl | exact absurd h (by decide))

variable {ν : Type}

/-- The numeral `0`. -/
def mkZero : Term sig ν := .app Sym.zero ![]
/-- The successor of `t`. -/
def mkSucc (t : Term sig ν) : Term sig ν := .app Sym.succ ![t]
/-- An `add` cell seen from its principal port (the first argument), with second argument `y` and
result `r`. -/
def mkAdd (y r : Term sig ν) : Term sig ν := .app Sym.add ![y, r]

/-- The numeral `n`. -/
def num : ℕ → Term sig ν
  | 0 => mkZero
  | n + 1 => mkSucc (num n)

@[simp] theorem vars_mkZero : (mkZero : Term sig ν).vars = 0 := by simp [mkZero, sig]
@[simp] theorem vars_mkSucc (t : Term sig ν) : (mkSucc t).vars = t.vars := by simp [mkSucc, sig]
@[simp] theorem vars_mkAdd (y r : Term sig ν) : (mkAdd y r).vars = y.vars + r.vars := by
  simp [mkAdd, sig, Fin.sum_univ_two]

@[simp] theorem bind_mkZero {μ : Type} (f : ν → Term sig μ) :
    (mkZero : Term sig ν).bind f = mkZero := by
  show Term.app (S := sig) Sym.zero _ = Term.app (S := sig) Sym.zero _
  congr 1; funext (i : Fin 0); exact i.elim0
@[simp] theorem bind_mkSucc {μ : Type} (f : ν → Term sig μ) (t : Term sig ν) :
    (mkSucc t).bind f = mkSucc (t.bind f) := by
  show Term.app Sym.succ (fun i => (![t] i).bind f) = Term.app Sym.succ _
  congr 1; funext (i : Fin 1); fin_cases i; rfl
@[simp] theorem bind_mkAdd {μ : Type} (f : ν → Term sig μ) (y r : Term sig ν) :
    (mkAdd y r).bind f = mkAdd (y.bind f) (r.bind f) := by
  show Term.app Sym.add (fun i => (![y, r] i).bind f) = Term.app Sym.add _
  congr 1; funext (i : Fin 2); fin_cases i <;> rfl

@[simp] theorem vars_num (n : ℕ) : (num n : Term sig ν).vars = 0 := by
  induction n with
  | zero => simp [num]
  | succ n ih => simp [num, ih]

@[simp] theorem bind_num {μ : Type} (f : ν → Term sig μ) (n : ℕ) :
    (num n : Term sig ν).bind f = num n := by
  induction n with
  | zero => simp [num]
  | succ n ih => simp [num, ih]

/-! ## The two rules -/

section Rules

/-- The `i`-th auxiliary port of the first cell. -/
private def l {a b m : ℕ} (i : Fin a) : Term sig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inl i)
/-- The `i`-th auxiliary port of the second cell. -/
private def r {a b m : ℕ} (i : Fin b) : Term sig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inr (.inl i))
/-- The `i`-th wire created by the rule. -/
private def w {a b m : ℕ} (i : Fin m) : Term sig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inr (.inr i))

/-- `add(y, r) ~ 0`: the second argument is the result. -/
def ruleAddZero : Rule sig 2 0 := ⟨0, {s(l 0, l 1)}⟩

/-- `add(y, r) ~ S(x)`: the result is the successor of a new wire `w`, and `add(y, w)` goes on
with `x`. -/
def ruleAddSucc : Rule sig 2 1 := ⟨1, s(l 1, mkSucc (w 0)) ::ₘ {s(r 0, mkAdd (l 0) (w 0))}⟩

/-- The interaction system of unary addition. -/
def system : System sig where
  rule
    | .add, .zero => some ruleAddZero
    | .add, .succ => some ruleAddSucc
    | _, _ => none

theorem ruleAddZero_linear : ruleAddZero.Linear := by
  constructor
  · intro i; fin_cases i <;> simp [ruleAddZero, l]
  · intro j; exact j.elim0
  · intro i; exact i.elim0

theorem ruleAddSucc_linear : ruleAddSucc.Linear := by
  constructor
  · intro i; fin_cases i <;> simp [ruleAddSucc, l, r, w]
  · intro j; fin_cases j; simp [ruleAddSucc, l, r, w]
  · intro i; fin_cases i; simp [ruleAddSucc, l, r, w]

theorem ruleAddZero_reduced : ruleAddZero.Reduced := by
  intro e he
  unfold ruleAddZero at he
  dsimp only at he
  obtain rfl := Multiset.mem_singleton.1 he
  exact ⟨.inl 0, _, rfl, by simp⟩

theorem ruleAddSucc_reduced : ruleAddSucc.Reduced := by
  intro e he
  unfold ruleAddSucc at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 1, _, rfl, by simp⟩
  obtain rfl := Multiset.mem_singleton.1 he
  exact ⟨.inr (.inl 0), _, rfl, by simp⟩

/-- Unary addition is an interaction system: its rules are linear and reduced, no pair of symbols
has two rules, and no symbol interacts with itself. -/
theorem system_wellFormed : system.WellFormed where
  linear := by
    intro α β r h
    cases α <;> cases β <;> cases h <;>
      first | exact ruleAddZero_linear | exact ruleAddSucc_linear
  reduced := by
    intro α β r h
    cases α <;> cases β <;> cases h <;>
      first | exact ruleAddZero_reduced | exact ruleAddSucc_reduced
  unique := by
    intro α β hne h
    cases α <;> cases β <;> first | rfl | cases h
  symm := by
    intro α r h
    cases α <;> cases h

end Rules

/-! ## Computing with the system -/

section Steps

variable (y res x : Term sig ℕ) (Δ : Net sig ℕ)

/-- `add(y, r) ~ 0` rewrites to `y ~ r`. -/
theorem step_add_zero :
    Step system (s(mkAdd y res, mkZero) ::ₘ Δ) (s(y, res) ::ₘ Δ) := by
  have h : Step system (s(mkAdd y res, mkZero) ::ₘ Δ)
      (ruleAddZero.inst ![y, res] (![] : Fin 0 → Term sig ℕ) (Fin.elim0 : Fin 0 → ℕ) + Δ) :=
    Step.mk (I := system) Sym.add Sym.zero ruleAddZero rfl ![y, res] ![] Δ
      (Fin.elim0 : Fin 0 → ℕ) (fun (i : Fin 0) => i.elim0) (fun (i : Fin 0) => i.elim0)
  have e : ruleAddZero.inst ![y, res] (![] : Fin 0 → Term sig ℕ) (Fin.elim0 : Fin 0 → ℕ) =
      {s(y, res)} := by
    simp [Rule.inst, Net.bind, ruleAddZero, l]
  rw [e] at h
  simpa using h

/-- `add(y, r) ~ S(x)` rewrites to `r ~ S(w)`, `x ~ add(y, w)`, for a name `w` not used in the
net. -/
theorem step_add_succ (k : ℕ)
    (hk : k ∉ Net.vars (s(mkAdd y res, mkSucc x) ::ₘ Δ)) :
    Step system (s(mkAdd y res, mkSucc x) ::ₘ Δ)
      (s(res, mkSucc (.var k)) ::ₘ s(x, mkAdd y (.var k)) ::ₘ Δ) := by
  have h : Step system (s(mkAdd y res, mkSucc x) ::ₘ Δ)
      (ruleAddSucc.inst ![y, res] ![x] (fun _ : Fin 1 => k) + Δ) :=
    Step.mk (I := system) Sym.add Sym.succ ruleAddSucc rfl ![y, res] ![x] Δ
      (fun _ : Fin 1 => k) (fun (i j : Fin 1) _ => Subsingleton.elim i j) (fun _ => hk)
  have e : ruleAddSucc.inst ![y, res] ![x] (fun _ : Fin 1 => k) =
      s(res, mkSucc (.var k)) ::ₘ {s(x, mkAdd y (.var k))} := by
    simp [Rule.inst, Net.bind, ruleAddSucc, l, r, w]
  rw [e] at h
  simpa using h

end Steps

/-- The net of `2 + 2`: an `add` cell whose first argument is `2`, second argument `2`, and whose
result is the free port `0`. -/
def twoPlusTwo : Net sig ℕ := {s(mkAdd (num 2) (.var 0), num 2)}

/-- The net of `4` on the free port `0`. -/
def four : Net sig ℕ := {s(.var 0, num 4)}

/-- What `2 + 2` literally reduces to, before the wires are substituted: the result is `S(w₁)`,
`w₁` is `S(w₂)`, and `w₂` is `2`. -/
def fourUnfolded : Net sig ℕ :=
  s(num 2, .var 2) ::ₘ s(.var 1, mkSucc (.var 2)) ::ₘ {s(.var 0, mkSucc (.var 1))}

/-- `2 + 2` reduces in three interactions: two for the successors, one for the zero. -/
theorem twoPlusTwo_steps : Steps system twoPlusTwo fourUnfolded := by
  have s1 : Step system twoPlusTwo
      (s(.var 0, mkSucc (.var 1)) ::ₘ s(num 1, mkAdd (num 2) (.var 1)) ::ₘ 0) :=
    step_add_succ (num 2) (.var 0) (num 1) 0 1 (by simp [Net.vars, num])
  have s2 : Step system
      (s(mkAdd (num 2) (.var 1), mkSucc (num 0)) ::ₘ {s(.var 0, mkSucc (.var 1))})
      (s(.var 1, mkSucc (.var 2)) ::ₘ s(num 0, mkAdd (num 2) (.var 2)) ::ₘ
        {s(.var 0, mkSucc (.var 1))}) :=
    step_add_succ (num 2) (.var 1) (num 0) _ 2 (by simp [Net.vars, num])
  have s3 : Step system
      (s(mkAdd (num 2) (.var 2), mkZero) ::ₘ s(.var 1, mkSucc (.var 2)) ::ₘ
        {s(.var 0, mkSucc (.var 1))})
      fourUnfolded :=
    step_add_zero (num 2) (.var 2) _
  have e1 : (s(.var 0, mkSucc (.var 1)) ::ₘ s(num 1, mkAdd (num 2) (.var 1)) ::ₘ 0 :
      Net sig ℕ) =
      s(mkAdd (num 2) (.var 1), mkSucc (num 0)) ::ₘ {s(.var 0, mkSucc (.var 1))} := by
    rw [Multiset.cons_swap]
    congr 1
    exact Sym2.eq_swap
  have e2 : (s(.var 1, mkSucc (.var 2)) ::ₘ s(num 0, mkAdd (num 2) (.var 2)) ::ₘ
      {s(.var 0, mkSucc (.var 1))} : Net sig ℕ) =
      s(mkAdd (num 2) (.var 2), mkZero) ::ₘ s(.var 1, mkSucc (.var 2)) ::ₘ
        {s(.var 0, mkSucc (.var 1))} := by
    rw [Multiset.cons_swap]
    congr 1
    exact Sym2.eq_swap
  rw [e1] at s1
  rw [e2] at s2
  exact (Relation.ReflTransGen.single s1).trans
    ((Relation.ReflTransGen.single s2).trans (Relation.ReflTransGen.single s3))

/-- The net after the wire `w₂` has been substituted. -/
private def fourHalf : Net sig ℕ := s(.var 1, num 3) ::ₘ {s(.var 0, mkSucc (.var 1))}

private theorem wire1 : Equiv fourUnfolded fourHalf := by
  have L : Net.Linear (s(.var 2, num 2) ::ₘ s(.var 1, mkSucc (.var 2)) ::ₘ
      ({s(.var 0, mkSucc (.var 1))} : Net sig ℕ)) := by
    intro z
    simp only [Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_var, vars_num, vars_mkSucc,
      Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
    split_ifs <;> omega
  have hx : (2 : ℕ) ∈ (Term.var 1 : Term sig ℕ).vars + (mkSucc (.var 2) : Term sig ℕ).vars := by
    simp
  have e : (s(.var 2, num 2) ::ₘ s(.var 1, mkSucc (.var 2)) ::ₘ
      ({s(.var 0, mkSucc (.var 1))} : Net sig ℕ)) = fourUnfolded := by
    unfold fourUnfolded
    congr 1
    exact Sym2.eq_swap
  have r : (s((Term.var 1 : Term sig ℕ).subst 2 (num 2), (mkSucc (.var 2)).subst 2 (num 2)) ::ₘ
      ({s(.var 0, mkSucc (.var 1))} : Net sig ℕ)) = fourHalf := by
    simp [Term.subst, num, fourHalf]
  exact (Equiv.of_eq e.symm).trans
    ((Wire.mk 2 (num 2) (.var 1) (mkSucc (.var 2)) _ L hx).equiv.trans (Equiv.of_eq r))

private theorem wire2 : Equiv fourHalf four := by
  have L : Net.Linear (s(.var 1, num 3) ::ₘ s(.var 0, mkSucc (.var 1)) ::ₘ (0 : Net sig ℕ)) := by
    intro z
    simp only [Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_num, vars_mkSucc,
      Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
    split_ifs <;> omega
  have hx : (1 : ℕ) ∈ (Term.var 0 : Term sig ℕ).vars + (mkSucc (.var 1) : Term sig ℕ).vars := by
    simp
  have r : (s((Term.var 0 : Term sig ℕ).subst 1 (num 3), (mkSucc (.var 1)).subst 1 (num 3)) ::ₘ
      (0 : Net sig ℕ)) = four := by
    simp [Term.subst, num, four]
  exact (Wire.mk 1 (num 3) (.var 0) (mkSucc (.var 1)) _ L hx).equiv.trans (Equiv.of_eq r)

/-- The wires of `fourUnfolded` can be substituted: it is the same graph as `4`. -/
theorem fourUnfolded_equiv : Equiv fourUnfolded four :=
  wire1.trans wire2

/-- **`2 + 2 = 4`**: the net of `2 + 2` reduces to a net that is the same graph as the net of
`4`. -/
theorem two_plus_two : ∃ M, Steps system twoPlusTwo M ∧ Equiv M four :=
  ⟨fourUnfolded, twoPlusTwo_steps, fourUnfolded_equiv⟩

/-! ## Into the combinators -/

/-- **Unary addition translates into the interaction combinators** (Theorem 1 of Lafont 1997,
applied to this system): there is a strict translation, that is, one whose principal nets all
start with a cell, that is compatible with the two rules. -/
theorem exists_translation :
    ∃ Φ : Translation sig Comb.sig, Φ.Strict ∧ Φ.Compatible system Comb.system :=
  Comb.universal_strict sig system system_wellFormed

/-- **`2 + 2 = 4` in the combinators.** For the translation of Theorem 1, every translation `N'`
of the net of `2 + 2` reduces, by the rules of `con`, `dup` and `era` and up to wires, to a net
that is the same graph as a translation of the net of `4`. -/
theorem two_plus_two_in_combinators :
    ∃ Φ : Translation sig Comb.sig, Φ.Strict ∧ Φ.Compatible system Comb.system ∧
      ∀ N' : Net Comb.sig ℕ, Φ.NetTr twoPlusTwo N' →
        ∃ M₁ M' : Net Comb.sig ℕ, StepsE Comb.system N' M₁ ∧ Equiv M₁ M' ∧ Φ.NetTr four M' := by
  obtain ⟨Φ, hs, hc⟩ := exists_translation
  refine ⟨Φ, hs, hc, fun N' hN' => ?_⟩
  obtain ⟨M₁, M₂, h1, e1, t2⟩ := Translation.Compatible.stepsE system_wellFormed.linear
    Comb.system_wellFormed.linear hc twoPlusTwo_steps.stepsE hN'
  obtain ⟨M', t', e'⟩ := Translation.NetTr.of_equiv fourUnfolded_equiv t2
  exact ⟨M₁, M', h1, e1.trans e', t'⟩

/-- The statement above is not empty: the net of `2 + 2` has a translation. -/
theorem twoPlusTwo_has_translation (Φ : Translation sig Comb.sig) :
    ∃ N' : Net Comb.sig ℕ, Φ.NetTr twoPlusTwo N' := by
  have hlin : twoPlusTwo.Linear := by
    intro z
    simp only [twoPlusTwo, Net.vars_singleton, eqVars_mk, vars_var, vars_num, vars_mkAdd,
      Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
    split_ifs <;> omega
  have hk : twoPlusTwo.Below 1 := by
    intro z hz
    simp [twoPlusTwo, Net.vars] at hz
    omega
  obtain ⟨N', _, h, _⟩ := Φ.exists_netTr hlin hk
  exact ⟨N', h⟩

end INet.Demo.Arith
