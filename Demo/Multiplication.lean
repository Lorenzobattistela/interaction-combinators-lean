import InteractionCombinators

/-!
# Demo: unary multiplication, with a duplicator and an eraser for numerals

Lafont 1997, Section 1.5, pages 76-77. Multiplication on unary numerals follows the equations
`0 × y = 0` and `s x × y = (x × y) + y`. The second argument `y` is used twice in the second
equation and not at all in the first, so the system has a duplicator `δ` and an eraser `ε` for
numerals. The six symbols are `0` (arity 0), `s` (1), `+` (2), `×` (2), `δ` (2) and `ε` (0),
named here `zero`, `succ`, `add`, `mul`, `dup` and `era`. These `dup` and `era` are symbols of
this system, not the combinators.

As in `Demo/Arithmetic.lean`, the first argument of `add` and `mul` is on the principal port; the
two auxiliary ports are the second argument `y` and the result `r`. The eight rules, read from
the pictures on pages 76 and 77:

* `add(y, r) ~ 0`      reduces to   `y ~ r`
* `add(y, r) ~ s(x)`   reduces to   `r ~ s(w)`, `x ~ add(y, w)`
* `mul(y, r) ~ 0`      reduces to   `y ~ ε`, `r ~ 0`
* `mul(y, r) ~ s(x)`   reduces to   `y ~ δ(w₀, w₁)`, `x ~ mul(w₀, add(w₁, r))`
* `dup(a, b) ~ 0`      reduces to   `a ~ 0`, `b ~ 0`
* `dup(a, b) ~ s(x)`   reduces to   `a ~ s(w₀)`, `b ~ s(w₁)`, `x ~ δ(w₀, w₁)`
* `era ~ 0`            reduces to   the empty net
* `era ~ s(x)`         reduces to   `x ~ ε`

In the rule `s×` (page 77) the new `×` cell has its first auxiliary port on the first auxiliary
port of the `δ`, and its second auxiliary port on the principal port of the `+`, whose first
auxiliary port is the second auxiliary port of the `δ` and whose second auxiliary port is the
result `r`. Whether the `δ`, drawn upside down, is read with its ports in the same or in the
opposite order changes only the names `w₀`, `w₁` of the two internal wires, not the rule.

This file shows:

* `system_wellFormed` — the system is an interaction system;
* `era_num`, `dup_num`, `add_num`, `mul_num` — an eraser erases a numeral, a duplicator copies
  it, and addition and multiplication of numerals compute the sum and the product, in any
  context `Δ`;
* `two_times_two` — the net of `2 × 2` reduces to the net of `4`;
* `two_times_two_in_combinators` — the same, after the strict translation of Theorem 1.
-/

namespace INet.Demo.Mul

open Term

/-- The symbols of page 76: `0`, successor, addition, multiplication, duplicator, eraser. -/
inductive Sym : Type
  | zero | succ | add | mul | dup | era
  deriving DecidableEq

/-- The arities of page 76: `0` and `ε` have no auxiliary port, `s` has one, `+`, `×` and `δ`
have two. -/
def sig : Signature where
  Sym := Sym
  arity
    | .zero => 0
    | .succ => 1
    | .add => 2
    | .mul => 2
    | .dup => 2
    | .era => 0

instance : Finite sig.Sym :=
  Finite.of_injective
    (fun α : Sym => (match α with
      | .zero => 0 | .succ => 1 | .add => 2 | .mul => 3 | .dup => 4 | .era => 5 : Fin 6))
    (by intro α β h; cases α <;> cases β <;> first | rfl | exact absurd h (by decide))

variable {ν : Type}

/-- The numeral `0`. -/
def mkZero : Term sig ν := .app Sym.zero ![]
/-- The successor of `t`. -/
def mkSucc (t : Term sig ν) : Term sig ν := .app Sym.succ ![t]
/-- An `add` cell seen from its principal port, with second argument `y` and result `r`. -/
def mkAdd (y r : Term sig ν) : Term sig ν := .app Sym.add ![y, r]
/-- A `mul` cell seen from its principal port, with second argument `y` and result `r`. -/
def mkMul (y r : Term sig ν) : Term sig ν := .app Sym.mul ![y, r]
/-- A duplicator seen from its principal port, with the two copies `a` and `b`. -/
def mkDup (a b : Term sig ν) : Term sig ν := .app Sym.dup ![a, b]
/-- An eraser. -/
def mkEra : Term sig ν := .app Sym.era ![]

/-- The numeral `n`. -/
def num : ℕ → Term sig ν
  | 0 => mkZero
  | n + 1 => mkSucc (num n)

theorem num_succ (n : ℕ) : (num (n + 1) : Term sig ν) = mkSucc (num n) := rfl

/-- `n` successors on top of `t`: the tree `s(s(… s(t)))`. -/
def succs : ℕ → Term sig ν → Term sig ν
  | 0, t => t
  | n + 1, t => mkSucc (succs n t)

@[simp] theorem vars_mkZero : (mkZero : Term sig ν).vars = 0 := by simp [mkZero, sig]
@[simp] theorem vars_mkEra : (mkEra : Term sig ν).vars = 0 := by simp [mkEra, sig]
@[simp] theorem vars_mkSucc (t : Term sig ν) : (mkSucc t).vars = t.vars := by simp [mkSucc, sig]
@[simp] theorem vars_mkAdd (y r : Term sig ν) : (mkAdd y r).vars = y.vars + r.vars := by
  simp [mkAdd, sig, Fin.sum_univ_two]
@[simp] theorem vars_mkMul (y r : Term sig ν) : (mkMul y r).vars = y.vars + r.vars := by
  simp [mkMul, sig, Fin.sum_univ_two]
@[simp] theorem vars_mkDup (a b : Term sig ν) : (mkDup a b).vars = a.vars + b.vars := by
  simp [mkDup, sig, Fin.sum_univ_two]

@[simp] theorem bind_mkZero {μ : Type} (f : ν → Term sig μ) :
    (mkZero : Term sig ν).bind f = mkZero := by
  change Term.app (S := sig) Sym.zero _ = Term.app (S := sig) Sym.zero _
  congr 1; funext (i : Fin 0); exact i.elim0
@[simp] theorem bind_mkEra {μ : Type} (f : ν → Term sig μ) :
    (mkEra : Term sig ν).bind f = mkEra := by
  change Term.app (S := sig) Sym.era _ = Term.app (S := sig) Sym.era _
  congr 1; funext (i : Fin 0); exact i.elim0
@[simp] theorem bind_mkSucc {μ : Type} (f : ν → Term sig μ) (t : Term sig ν) :
    (mkSucc t).bind f = mkSucc (t.bind f) := by
  change Term.app Sym.succ (fun i => (![t] i).bind f) = Term.app Sym.succ _
  congr 1; funext (i : Fin 1); fin_cases i; rfl
@[simp] theorem bind_mkAdd {μ : Type} (f : ν → Term sig μ) (y r : Term sig ν) :
    (mkAdd y r).bind f = mkAdd (y.bind f) (r.bind f) := by
  change Term.app Sym.add (fun i => (![y, r] i).bind f) = Term.app Sym.add _
  congr 1; funext (i : Fin 2); fin_cases i <;> rfl
@[simp] theorem bind_mkMul {μ : Type} (f : ν → Term sig μ) (y r : Term sig ν) :
    (mkMul y r).bind f = mkMul (y.bind f) (r.bind f) := by
  change Term.app Sym.mul (fun i => (![y, r] i).bind f) = Term.app Sym.mul _
  congr 1; funext (i : Fin 2); fin_cases i <;> rfl
@[simp] theorem bind_mkDup {μ : Type} (f : ν → Term sig μ) (a b : Term sig ν) :
    (mkDup a b).bind f = mkDup (a.bind f) (b.bind f) := by
  change Term.app Sym.dup (fun i => (![a, b] i).bind f) = Term.app Sym.dup _
  congr 1; funext (i : Fin 2); fin_cases i <;> rfl

@[simp] theorem vars_num (n : ℕ) : (num n : Term sig ν).vars = 0 := by
  induction n with
  | zero => simp [num]
  | succ n ih => simp [num, ih]

/-- `n` successors on the numeral `m` make the numeral `n + m`. -/
theorem succs_num (n m : ℕ) : (succs n (num m) : Term sig ν) = num (n + m) := by
  induction n with
  | zero => simp [succs]
  | succ n ih => rw [succs, ih, Nat.succ_add]; rfl

/-! ## The eight rules -/

section Rules

/-- The `i`-th auxiliary port of the first cell. -/
private def l {a b m : ℕ} (i : Fin a) : Term sig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inl i)
/-- The `i`-th auxiliary port of the second cell. -/
private def r {a b m : ℕ} (i : Fin b) : Term sig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inr (.inl i))
/-- The `i`-th wire created by the rule. -/
private def w {a b m : ℕ} (i : Fin m) : Term sig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inr (.inr i))

/-- `add(y, r) ~ 0` (page 76): the second argument is the result. -/
def ruleAddZero : Rule sig 2 0 := ⟨0, s(l 0, l 1) ::ₘ 0⟩

/-- `add(y, r) ~ s(x)` (page 76): the result is `s(w)`, and `add(y, w)` goes on with `x`. -/
def ruleAddSucc : Rule sig 2 1 := ⟨1, s(l 1, mkSucc (w 0)) ::ₘ s(r 0, mkAdd (l 0) (w 0)) ::ₘ 0⟩

/-- `mul(y, r) ~ 0` (rule `0×`, page 77): the second argument is erased, the result is `0`. -/
def ruleMulZero : Rule sig 2 0 := ⟨0, s(l 0, mkEra) ::ₘ s(l 1, mkZero) ::ₘ 0⟩

/-- `mul(y, r) ~ s(x)` (rule `s×`, page 77): the second argument goes to a duplicator
`δ(w₀, w₁)`; the first copy `w₀` is the second argument of `mul` on `x`, whose result is the first
argument of `add(w₁, r)`. -/
def ruleMulSucc : Rule sig 2 1 :=
  ⟨2, s(l 0, mkDup (w 0) (w 1)) ::ₘ s(r 0, mkMul (w 0) (mkAdd (w 1) (l 1))) ::ₘ 0⟩

/-- `dup(a, b) ~ 0` (rule `0δ`, page 77): both copies are `0`. -/
def ruleDupZero : Rule sig 2 0 := ⟨0, s(l 0, mkZero) ::ₘ s(l 1, mkZero) ::ₘ 0⟩

/-- `dup(a, b) ~ s(x)` (rule `sδ`, page 77): both copies are successors, of the two copies of
`x` made by a new duplicator. -/
def ruleDupSucc : Rule sig 2 1 :=
  ⟨2, s(l 0, mkSucc (w 0)) ::ₘ s(l 1, mkSucc (w 1)) ::ₘ s(r 0, mkDup (w 0) (w 1)) ::ₘ 0⟩

/-- `ε ~ 0` (rule `0ε`, page 77): both cells disappear. -/
def ruleEraZero : Rule sig 0 0 := ⟨0, 0⟩

/-- `ε ~ s(x)` (rule `sε`, page 77): the eraser goes on with `x`. -/
def ruleEraSucc : Rule sig 0 1 := ⟨0, s(r 0, mkEra) ::ₘ 0⟩

/-- The interaction system of unary multiplication (Lafont 1997, pages 76-77). -/
def system : System sig where
  rule
    | .add, .zero => some ruleAddZero
    | .add, .succ => some ruleAddSucc
    | .mul, .zero => some ruleMulZero
    | .mul, .succ => some ruleMulSucc
    | .dup, .zero => some ruleDupZero
    | .dup, .succ => some ruleDupSucc
    | .era, .zero => some ruleEraZero
    | .era, .succ => some ruleEraSucc
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

theorem ruleMulZero_linear : ruleMulZero.Linear := by
  constructor
  · intro i; fin_cases i <;> simp [ruleMulZero, l]
  · intro j; exact j.elim0
  · intro i; exact i.elim0

theorem ruleMulSucc_linear : ruleMulSucc.Linear := by
  constructor
  · intro i; fin_cases i <;> simp [ruleMulSucc, l, r, w]
  · intro j; fin_cases j; simp [ruleMulSucc, l, r, w]
  · intro i; fin_cases i <;> simp [ruleMulSucc, l, r, w]

theorem ruleDupZero_linear : ruleDupZero.Linear := by
  constructor
  · intro i; fin_cases i <;> simp [ruleDupZero, l]
  · intro j; exact j.elim0
  · intro i; exact i.elim0

theorem ruleDupSucc_linear : ruleDupSucc.Linear := by
  constructor
  · intro i; fin_cases i <;> simp [ruleDupSucc, l, r, w]
  · intro j; fin_cases j; simp [ruleDupSucc, l, r, w]
  · intro i; fin_cases i <;> simp [ruleDupSucc, l, r, w]

theorem ruleEraZero_linear : ruleEraZero.Linear := by
  constructor
  · intro i; exact i.elim0
  · intro j; exact j.elim0
  · intro i; exact i.elim0

theorem ruleEraSucc_linear : ruleEraSucc.Linear := by
  constructor
  · intro i; exact i.elim0
  · intro j; fin_cases j; simp [ruleEraSucc, r]
  · intro i; exact i.elim0

theorem ruleAddZero_reduced : ruleAddZero.Reduced := by
  intro e he
  unfold ruleAddZero at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 0, _, rfl, by simp⟩
  · exact absurd he (Multiset.notMem_zero _)

theorem ruleAddSucc_reduced : ruleAddSucc.Reduced := by
  intro e he
  unfold ruleAddSucc at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 1, _, rfl, by simp⟩
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inr (.inl 0), _, rfl, by simp⟩
  · exact absurd he (Multiset.notMem_zero _)

theorem ruleMulZero_reduced : ruleMulZero.Reduced := by
  intro e he
  unfold ruleMulZero at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 0, _, rfl, by simp⟩
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 1, _, rfl, by simp⟩
  · exact absurd he (Multiset.notMem_zero _)

theorem ruleMulSucc_reduced : ruleMulSucc.Reduced := by
  intro e he
  unfold ruleMulSucc at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 0, _, rfl, by simp⟩
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inr (.inl 0), _, rfl, by simp⟩
  · exact absurd he (Multiset.notMem_zero _)

theorem ruleDupZero_reduced : ruleDupZero.Reduced := by
  intro e he
  unfold ruleDupZero at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 0, _, rfl, by simp⟩
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 1, _, rfl, by simp⟩
  · exact absurd he (Multiset.notMem_zero _)

theorem ruleDupSucc_reduced : ruleDupSucc.Reduced := by
  intro e he
  unfold ruleDupSucc at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 0, _, rfl, by simp⟩
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 1, _, rfl, by simp⟩
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inr (.inl 0), _, rfl, by simp⟩
  · exact absurd he (Multiset.notMem_zero _)

theorem ruleEraZero_reduced : ruleEraZero.Reduced := by
  intro e he
  exact absurd he (Multiset.notMem_zero _)

theorem ruleEraSucc_reduced : ruleEraSucc.Reduced := by
  intro e he
  unfold ruleEraSucc at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inr (.inl 0), _, rfl, by simp⟩
  · exact absurd he (Multiset.notMem_zero _)

/-- Unary multiplication with its duplicator and eraser is an interaction system (Lafont 1997,
pages 76-77): its eight rules are linear and reduced, and no pair of symbols has two rules. No
symbol has a rule with itself, so the symmetry condition holds vacuously. -/
theorem system_wellFormed : system.WellFormed where
  linear := by
    intro α β r h
    cases α <;> cases β <;> cases h <;>
      first
        | exact ruleAddZero_linear | exact ruleAddSucc_linear
        | exact ruleMulZero_linear | exact ruleMulSucc_linear
        | exact ruleDupZero_linear | exact ruleDupSucc_linear
        | exact ruleEraZero_linear | exact ruleEraSucc_linear
  reduced := by
    intro α β r h
    cases α <;> cases β <;> cases h <;>
      first
        | exact ruleAddZero_reduced | exact ruleAddSucc_reduced
        | exact ruleMulZero_reduced | exact ruleMulSucc_reduced
        | exact ruleDupZero_reduced | exact ruleDupSucc_reduced
        | exact ruleEraZero_reduced | exact ruleEraSucc_reduced
  unique := by
    intro α β hne h
    cases α <;> cases β <;> first | rfl | cases h
  symm := by
    intro α r h
    cases α <;> cases h

end Rules

/-! ## One interaction for each rule -/

section Steps

variable (y res x a b : Term sig ℕ) (Δ : Net sig ℕ)

private theorem inj_two (k : ℕ) : Function.Injective (![k, k + 1] : Fin 2 → ℕ) := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all

private theorem fresh_two {k : ℕ} {V : Multiset ℕ} (hk : k ∉ V) (hk1 : k + 1 ∉ V) :
    ∀ i : Fin 2, (![k, k + 1] : Fin 2 → ℕ) i ∉ V := by
  intro i; fin_cases i <;> simpa

/-- `add(y, r) ~ 0` rewrites to `y ~ r` (page 76). -/
theorem step_add_zero :
    Step system (s(mkAdd y res, mkZero) ::ₘ Δ) (s(y, res) ::ₘ Δ) := by
  have h : Step system (s(mkAdd y res, mkZero) ::ₘ Δ)
      (ruleAddZero.inst ![y, res] (![] : Fin 0 → Term sig ℕ) (Fin.elim0 : Fin 0 → ℕ) + Δ) :=
    Step.mk (I := system) Sym.add Sym.zero ruleAddZero rfl ![y, res] ![] Δ
      (Fin.elim0 : Fin 0 → ℕ) (fun (i : Fin 0) => i.elim0) (fun (i : Fin 0) => i.elim0)
  have e : ruleAddZero.inst ![y, res] (![] : Fin 0 → Term sig ℕ) (Fin.elim0 : Fin 0 → ℕ) =
      s(y, res) ::ₘ 0 := by
    simp [Rule.inst, Net.bind, ruleAddZero, l]
  rw [e] at h
  simpa using h

/-- `add(y, r) ~ s(x)` rewrites to `r ~ s(w)`, `x ~ add(y, w)` (page 76), for a name `w` not
used in the net. -/
theorem step_add_succ (k : ℕ) (hk : k ∉ Net.vars (s(mkAdd y res, mkSucc x) ::ₘ Δ)) :
    Step system (s(mkAdd y res, mkSucc x) ::ₘ Δ)
      (s(res, mkSucc (.var k)) ::ₘ s(x, mkAdd y (.var k)) ::ₘ Δ) := by
  have h : Step system (s(mkAdd y res, mkSucc x) ::ₘ Δ)
      (ruleAddSucc.inst ![y, res] ![x] (fun _ : Fin 1 => k) + Δ) :=
    Step.mk (I := system) Sym.add Sym.succ ruleAddSucc rfl ![y, res] ![x] Δ
      (fun _ : Fin 1 => k) (fun (i j : Fin 1) _ => Subsingleton.elim i j) (fun _ => hk)
  have e : ruleAddSucc.inst ![y, res] ![x] (fun _ : Fin 1 => k) =
      s(res, mkSucc (.var k)) ::ₘ s(x, mkAdd y (.var k)) ::ₘ 0 := by
    simp [Rule.inst, Net.bind, ruleAddSucc, l, r, w]
  rw [e] at h
  simpa using h

/-- `mul(y, r) ~ 0` rewrites to `y ~ ε`, `r ~ 0` (rule `0×`, page 77). -/
theorem step_mul_zero :
    Step system (s(mkMul y res, mkZero) ::ₘ Δ) (s(y, mkEra) ::ₘ s(res, mkZero) ::ₘ Δ) := by
  have h : Step system (s(mkMul y res, mkZero) ::ₘ Δ)
      (ruleMulZero.inst ![y, res] (![] : Fin 0 → Term sig ℕ) (Fin.elim0 : Fin 0 → ℕ) + Δ) :=
    Step.mk (I := system) Sym.mul Sym.zero ruleMulZero rfl ![y, res] ![] Δ
      (Fin.elim0 : Fin 0 → ℕ) (fun (i : Fin 0) => i.elim0) (fun (i : Fin 0) => i.elim0)
  have e : ruleMulZero.inst ![y, res] (![] : Fin 0 → Term sig ℕ) (Fin.elim0 : Fin 0 → ℕ) =
      s(y, mkEra) ::ₘ s(res, mkZero) ::ₘ 0 := by
    simp [Rule.inst, Net.bind, ruleMulZero, l]
  rw [e] at h
  simpa using h

/-- `mul(y, r) ~ s(x)` rewrites to `y ~ δ(w₀, w₁)`, `x ~ mul(w₀, add(w₁, r))` (rule `s×`,
page 77), for two names `w₀ = k`, `w₁ = k + 1` not used in the net. -/
theorem step_mul_succ (k : ℕ) (hk : k ∉ Net.vars (s(mkMul y res, mkSucc x) ::ₘ Δ))
    (hk1 : k + 1 ∉ Net.vars (s(mkMul y res, mkSucc x) ::ₘ Δ)) :
    Step system (s(mkMul y res, mkSucc x) ::ₘ Δ)
      (s(y, mkDup (.var k) (.var (k + 1))) ::ₘ
        s(x, mkMul (.var k) (mkAdd (.var (k + 1)) res)) ::ₘ Δ) := by
  have h : Step system (s(mkMul y res, mkSucc x) ::ₘ Δ)
      (ruleMulSucc.inst ![y, res] ![x] (![k, k + 1] : Fin 2 → ℕ) + Δ) :=
    Step.mk (I := system) Sym.mul Sym.succ ruleMulSucc rfl ![y, res] ![x] Δ
      (![k, k + 1] : Fin 2 → ℕ) (inj_two k) (fresh_two hk hk1)
  have e : ruleMulSucc.inst ![y, res] ![x] (![k, k + 1] : Fin 2 → ℕ) =
      s(y, mkDup (.var k) (.var (k + 1))) ::ₘ
        s(x, mkMul (.var k) (mkAdd (.var (k + 1)) res)) ::ₘ 0 := by
    simp [Rule.inst, Net.bind, ruleMulSucc, l, r, w]
  rw [e] at h
  simpa using h

/-- `δ(a, b) ~ 0` rewrites to `a ~ 0`, `b ~ 0` (rule `0δ`, page 77). -/
theorem step_dup_zero :
    Step system (s(mkDup a b, mkZero) ::ₘ Δ) (s(a, mkZero) ::ₘ s(b, mkZero) ::ₘ Δ) := by
  have h : Step system (s(mkDup a b, mkZero) ::ₘ Δ)
      (ruleDupZero.inst ![a, b] (![] : Fin 0 → Term sig ℕ) (Fin.elim0 : Fin 0 → ℕ) + Δ) :=
    Step.mk (I := system) Sym.dup Sym.zero ruleDupZero rfl ![a, b] ![] Δ
      (Fin.elim0 : Fin 0 → ℕ) (fun (i : Fin 0) => i.elim0) (fun (i : Fin 0) => i.elim0)
  have e : ruleDupZero.inst ![a, b] (![] : Fin 0 → Term sig ℕ) (Fin.elim0 : Fin 0 → ℕ) =
      s(a, mkZero) ::ₘ s(b, mkZero) ::ₘ 0 := by
    simp [Rule.inst, Net.bind, ruleDupZero, l]
  rw [e] at h
  simpa using h

/-- `δ(a, b) ~ s(x)` rewrites to `a ~ s(w₀)`, `b ~ s(w₁)`, `x ~ δ(w₀, w₁)` (rule `sδ`, page 77),
for two names `w₀ = k`, `w₁ = k + 1` not used in the net. -/
theorem step_dup_succ (k : ℕ) (hk : k ∉ Net.vars (s(mkDup a b, mkSucc x) ::ₘ Δ))
    (hk1 : k + 1 ∉ Net.vars (s(mkDup a b, mkSucc x) ::ₘ Δ)) :
    Step system (s(mkDup a b, mkSucc x) ::ₘ Δ)
      (s(a, mkSucc (.var k)) ::ₘ s(b, mkSucc (.var (k + 1))) ::ₘ
        s(x, mkDup (.var k) (.var (k + 1))) ::ₘ Δ) := by
  have h : Step system (s(mkDup a b, mkSucc x) ::ₘ Δ)
      (ruleDupSucc.inst ![a, b] ![x] (![k, k + 1] : Fin 2 → ℕ) + Δ) :=
    Step.mk (I := system) Sym.dup Sym.succ ruleDupSucc rfl ![a, b] ![x] Δ
      (![k, k + 1] : Fin 2 → ℕ) (inj_two k) (fresh_two hk hk1)
  have e : ruleDupSucc.inst ![a, b] ![x] (![k, k + 1] : Fin 2 → ℕ) =
      s(a, mkSucc (.var k)) ::ₘ s(b, mkSucc (.var (k + 1))) ::ₘ
        s(x, mkDup (.var k) (.var (k + 1))) ::ₘ 0 := by
    simp [Rule.inst, Net.bind, ruleDupSucc, l, r, w]
  rw [e] at h
  simpa using h

/-- `ε ~ 0` rewrites to the empty net (rule `0ε`, page 77). -/
theorem step_era_zero : Step system (s(mkEra, mkZero) ::ₘ Δ) Δ := by
  have h : Step system (s(mkEra, mkZero) ::ₘ Δ)
      (ruleEraZero.inst (![] : Fin 0 → Term sig ℕ) (![] : Fin 0 → Term sig ℕ)
        (Fin.elim0 : Fin 0 → ℕ) + Δ) :=
    Step.mk (I := system) Sym.era Sym.zero ruleEraZero rfl ![] ![] Δ
      (Fin.elim0 : Fin 0 → ℕ) (fun (i : Fin 0) => i.elim0) (fun (i : Fin 0) => i.elim0)
  have e : ruleEraZero.inst (![] : Fin 0 → Term sig ℕ) (![] : Fin 0 → Term sig ℕ)
      (Fin.elim0 : Fin 0 → ℕ) = 0 := by
    simp [Rule.inst, Net.bind, ruleEraZero]
  rw [e] at h
  simpa using h

/-- `ε ~ s(x)` rewrites to `x ~ ε` (rule `sε`, page 77). -/
theorem step_era_succ : Step system (s(mkEra, mkSucc x) ::ₘ Δ) (s(x, mkEra) ::ₘ Δ) := by
  have h : Step system (s(mkEra, mkSucc x) ::ₘ Δ)
      (ruleEraSucc.inst (![] : Fin 0 → Term sig ℕ) ![x] (Fin.elim0 : Fin 0 → ℕ) + Δ) :=
    Step.mk (I := system) Sym.era Sym.succ ruleEraSucc rfl ![] ![x] Δ
      (Fin.elim0 : Fin 0 → ℕ) (fun (i : Fin 0) => i.elim0) (fun (i : Fin 0) => i.elim0)
  have e : ruleEraSucc.inst (![] : Fin 0 → Term sig ℕ) ![x] (Fin.elim0 : Fin 0 → ℕ) =
      s(x, mkEra) ::ₘ 0 := by
    simp [Rule.inst, Net.bind, ruleEraSucc, r]
  rw [e] at h
  simpa using h

end Steps

/-! ## Reduction up to wires -/

/-- `N` reduces, by interactions up to wires, to a net that is the same graph as `P`. -/
def Reduces (N P : Net sig ℕ) : Prop := ∃ M, StepsE system N M ∧ Equiv M P

namespace Reduces

variable {N P Q : Net sig ℕ}

theorem of_equiv (h : Equiv N P) : Reduces N P := ⟨N, Relation.ReflTransGen.refl, h⟩

theorem of_step (h : Step system N P) : Reduces N P :=
  ⟨P, Relation.ReflTransGen.single h.stepE, Equiv.refl P⟩

theorem of_step_eq (h : Step system N P) (e : P = Q) : Reduces N Q := e ▸ of_step h

theorem trans_equiv (h : Reduces N P) (e : Equiv P Q) : Reduces N Q := by
  obtain ⟨M, hs, he⟩ := h
  exact ⟨M, hs, he.trans e⟩

/-- An equivalence in front of a reduction up to wires is absorbed by its first interaction. -/
private theorem absorb {M₁ P M₂ : Net sig ℕ} (h : StepsE system P M₂) (e : Equiv M₁ P) :
    ∃ M, StepsE system M₁ M ∧ Equiv M M₂ := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨X, ⟨P', eP, s⟩, hX⟩
  · exact ⟨M₁, Relation.ReflTransGen.refl, e⟩
  · exact ⟨M₂, Relation.ReflTransGen.head ⟨P', e.trans eP, s⟩ hX, Equiv.refl M₂⟩

theorem trans (h : Reduces N P) (h' : Reduces P Q) : Reduces N Q := by
  obtain ⟨M₁, h1, e1⟩ := h
  obtain ⟨M₂, h2, e2⟩ := h'
  obtain ⟨M, hM, eM⟩ := absorb h2 e1
  exact ⟨M, h1.trans hM, eM.trans e2⟩

theorem linear (h : Reduces N P) (hN : N.Linear) : P.Linear := by
  obtain ⟨M, hs, he⟩ := h
  exact he.linear (hs.linear system_wellFormed.linear hN)

end Reduces

/-- One wire substitution, with the net and its result given up to reordering. -/
private theorem wire {N M : Net sig ℕ} (k : ℕ) (t u v : Term sig ℕ) (Δ : Net sig ℕ)
    (hN : N = s(.var k, t) ::ₘ s(u, v) ::ₘ Δ) (hM : s(u.subst k t, v.subst k t) ::ₘ Δ = M)
    (hlin : N.Linear) (hx : k ∈ u.vars + v.vars) : Equiv N M := by
  subst hN hM
  exact (Wire.mk k t u v Δ hlin hx).equiv

@[simp] theorem subst_mkSucc (t : Term sig ℕ) (z : ℕ) (q : Term sig ℕ) :
    (mkSucc t).subst z q = mkSucc (t.subst z q) := by simp [Term.subst]
@[simp] theorem subst_mkAdd (y r : Term sig ℕ) (z : ℕ) (q : Term sig ℕ) :
    (mkAdd y r).subst z q = mkAdd (y.subst z q) (r.subst z q) := by simp [Term.subst]
@[simp] theorem subst_mkMul (y r : Term sig ℕ) (z : ℕ) (q : Term sig ℕ) :
    (mkMul y r).subst z q = mkMul (y.subst z q) (r.subst z q) := by simp [Term.subst]
@[simp] theorem subst_num (n z : ℕ) (q : Term sig ℕ) : (num n).subst z q = num n :=
  subst_of_notMem (by simp)
private theorem subst_var_eq (z : ℕ) (q : Term sig ℕ) : (Term.var z).subst z q = q := by
  simp [Term.subst]
private theorem subst_var_ne {z x : ℕ} (q : Term sig ℕ) (h : x ≠ z) :
    (Term.var x).subst z q = Term.var x := by
  simp [Term.subst, h]

@[simp] theorem below_mkZero {k : ℕ} : (mkZero : Term sig ℕ).Below k := by simp [Term.Below]
@[simp] theorem below_mkEra {k : ℕ} : (mkEra : Term sig ℕ).Below k := by simp [Term.Below]
@[simp] theorem below_mkSucc {k : ℕ} {t : Term sig ℕ} : (mkSucc t).Below k ↔ t.Below k := by
  simp [Term.Below]
@[simp] theorem below_mkAdd {k : ℕ} {y r : Term sig ℕ} :
    (mkAdd y r).Below k ↔ y.Below k ∧ r.Below k := by
  simp [Term.Below, or_imp, forall_and]
@[simp] theorem below_mkMul {k : ℕ} {y r : Term sig ℕ} :
    (mkMul y r).Below k ↔ y.Below k ∧ r.Below k := by
  simp [Term.Below, or_imp, forall_and]
@[simp] theorem below_mkDup {k : ℕ} {a b : Term sig ℕ} :
    (mkDup a b).Below k ↔ a.Below k ∧ b.Below k := by
  simp [Term.Below, or_imp, forall_and]
@[simp] theorem below_num {k n : ℕ} : (num n : Term sig ℕ).Below k := by simp [Term.Below]

private theorem notMem_of_below {k x : ℕ} {t : Term sig ℕ} (h : t.Below k) (hx : k ≤ x) :
    x ∉ t.vars :=
  fun hm => absurd (h x hm) (by omega)

/-! ## Erasing, duplicating, adding and multiplying numerals -/

/-- **An eraser erases a numeral** (rules `0ε` and `sε`, page 77): `ε ~ n` reduces to the empty
net, in any context `Δ`. -/
theorem era_num (n : ℕ) : ∀ Δ : Net sig ℕ, Reduces (s(mkEra, num n) ::ₘ Δ) Δ := by
  induction n with
  | zero => intro Δ; exact Reduces.of_step (step_era_zero Δ)
  | succ n ih =>
    intro Δ
    refine (Reduces.of_step_eq (step_era_succ (num n) Δ) ?_).trans (ih Δ)
    rw [Sym2.eq_swap]

/-- **A duplicator copies a numeral** (rules `0δ` and `sδ`, page 77): `δ(a, b) ~ n` reduces, up
to wires, to `a ~ n`, `b ~ n`, in any linear context `Δ` whose names are below `k`. -/
theorem dup_num (n : ℕ) : ∀ (a b : Term sig ℕ) (Δ : Net sig ℕ) (k : ℕ),
    Net.Linear (s(mkDup a b, num n) ::ₘ Δ) → Net.Below k (s(mkDup a b, num n) ::ₘ Δ) →
    Reduces (s(mkDup a b, num n) ::ₘ Δ) (s(a, num n) ::ₘ s(b, num n) ::ₘ Δ) := by
  induction n with
  | zero => intro a b Δ k _ _; exact Reduces.of_step (step_dup_zero a b Δ)
  | succ n ih =>
    intro a b Δ k hlin hk
    have hk' := hk
    simp only [Net.below_cons, below_mkDup] at hk'
    obtain ⟨⟨ha, hb⟩, -, hΔ⟩ := hk'
    have h1 : Reduces (s(mkDup a b, num (n + 1)) ::ₘ Δ)
        (s(mkDup (.var k) (.var (k + 1)), num n) ::ₘ
          s(a, mkSucc (.var k)) ::ₘ s(b, mkSucc (.var (k + 1))) ::ₘ Δ) :=
      Reduces.of_step_eq
        (step_dup_succ (num n) a b Δ k (hk.notMem le_rfl) (hk.notMem (by omega)))
        (by rw [Sym2.eq_swap (a := num n)]; ms)
    have hk1 : Net.Below (k + 2) (s(mkDup (.var k) (.var (k + 1)), num n) ::ₘ
        s(a, mkSucc (.var k)) ::ₘ s(b, mkSucc (.var (k + 1))) ::ₘ Δ) := by
      simp [ha.mono (show k ≤ k + 2 by omega), hb.mono (show k ≤ k + 2 by omega),
        hΔ.mono (show k ≤ k + 2 by omega)]
    have h2 := h1.trans (ih _ _ _ (k + 2) (h1.linear hlin) hk1)
    have hlin2 := h2.linear hlin
    have w1 := wire k (num n) a (mkSucc (.var k))
      (s(.var (k + 1), num n) ::ₘ s(b, mkSucc (.var (k + 1))) ::ₘ Δ) (by ms) rfl hlin2
      (by simp)
    have w2 := wire (k + 1) (num n) b (mkSucc (.var (k + 1)))
      (s(a.subst k (num n), (mkSucc (.var k)).subst k (num n)) ::ₘ Δ) (by ms) rfl
      (w1.linear hlin2) (by simp)
    refine h2.trans_equiv ((w1.trans w2).trans (Equiv.of_eq ?_))
    rw [subst_of_notMem (notMem_of_below ha le_rfl),
      subst_of_notMem (notMem_of_below hb (by omega)), subst_mkSucc, subst_mkSucc,
      subst_var_eq, subst_var_eq, num_succ]
    ms

/-- **Addition of numerals** (rules of `+`, page 76): `add(y, r) ~ n` reduces, up to wires, to
`r ~ sⁿ(y)`, in any linear context `Δ` whose names are below `k`. -/
theorem add_num (n : ℕ) : ∀ (y r : Term sig ℕ) (Δ : Net sig ℕ) (k : ℕ),
    Net.Linear (s(mkAdd y r, num n) ::ₘ Δ) → Net.Below k (s(mkAdd y r, num n) ::ₘ Δ) →
    Reduces (s(mkAdd y r, num n) ::ₘ Δ) (s(r, succs n y) ::ₘ Δ) := by
  induction n with
  | zero =>
    intro y r Δ k _ _
    exact Reduces.of_step_eq (step_add_zero y r Δ) (by rw [Sym2.eq_swap]; rfl)
  | succ n ih =>
    intro y r Δ k hlin hk
    have hk' := hk
    simp only [Net.below_cons, below_mkAdd] at hk'
    obtain ⟨⟨hy, hr⟩, -, hΔ⟩ := hk'
    have h1 : Reduces (s(mkAdd y r, num (n + 1)) ::ₘ Δ)
        (s(mkAdd y (.var k), num n) ::ₘ s(r, mkSucc (.var k)) ::ₘ Δ) :=
      Reduces.of_step_eq (step_add_succ y r (num n) Δ k (hk.notMem le_rfl))
        (by rw [Sym2.eq_swap (a := num n)]; ms)
    have hk1 : Net.Below (k + 1)
        (s(mkAdd y (.var k), num n) ::ₘ s(r, mkSucc (.var k)) ::ₘ Δ) := by
      simp [hy.mono (show k ≤ k + 1 by omega), hr.mono (show k ≤ k + 1 by omega),
        hΔ.mono (show k ≤ k + 1 by omega)]
    have h2 := h1.trans (ih _ _ _ (k + 1) (h1.linear hlin) hk1)
    have w1 := wire k (succs n y) r (mkSucc (.var k)) Δ rfl rfl (h2.linear hlin) (by simp)
    refine h2.trans_equiv (w1.trans (Equiv.of_eq ?_))
    rw [subst_of_notMem (notMem_of_below hr le_rfl), subst_mkSucc, subst_var_eq]
    rfl

/-- **Multiplication of numerals** (rules `0×` and `s×`, page 77, with those of `+`, `δ` and
`ε`): `mul(m, r) ~ n` reduces, up to wires, to `r ~ n × m`, in any linear context `Δ` whose names
are below `k`. -/
theorem mul_num (n m : ℕ) : ∀ (r : Term sig ℕ) (Δ : Net sig ℕ) (k : ℕ),
    Net.Linear (s(mkMul (num m) r, num n) ::ₘ Δ) →
    Net.Below k (s(mkMul (num m) r, num n) ::ₘ Δ) →
    Reduces (s(mkMul (num m) r, num n) ::ₘ Δ) (s(r, num (n * m)) ::ₘ Δ) := by
  induction n with
  | zero =>
    intro r Δ k _ _
    have h1 := Reduces.of_step (step_mul_zero (num m) r Δ)
    rw [Sym2.eq_swap (a := num m)] at h1
    rw [Nat.zero_mul]
    exact h1.trans (era_num m _)
  | succ n ih =>
    intro r Δ k hlin hk
    have hk' := hk
    simp only [Net.below_cons, below_mkMul] at hk'
    obtain ⟨⟨-, hr⟩, -, hΔ⟩ := hk'
    have h1 : Reduces (s(mkMul (num m) r, num (n + 1)) ::ₘ Δ)
        (s(mkDup (.var k) (.var (k + 1)), num m) ::ₘ
          s(num n, mkMul (.var k) (mkAdd (.var (k + 1)) r)) ::ₘ Δ) :=
      Reduces.of_step_eq
        (step_mul_succ (num m) r (num n) Δ k (hk.notMem le_rfl) (hk.notMem (by omega)))
        (by rw [Sym2.eq_swap (a := num m)])
    have hk1 : Net.Below (k + 2) (s(mkDup (.var k) (.var (k + 1)), num m) ::ₘ
        s(num n, mkMul (.var k) (mkAdd (.var (k + 1)) r)) ::ₘ Δ) := by
      simp [hr.mono (show k ≤ k + 2 by omega), hΔ.mono (show k ≤ k + 2 by omega)]
    have h2 := h1.trans (dup_num m _ _ _ (k + 2) (h1.linear hlin) hk1)
    have hlin2 := h2.linear hlin
    have w1 := wire (M := s(num n, mkMul (num m) (mkAdd (.var (k + 1)) r)) ::ₘ
        s(.var (k + 1), num m) ::ₘ Δ)
      k (num m) (num n) (mkMul (.var k) (mkAdd (.var (k + 1)) r))
      (s(.var (k + 1), num m) ::ₘ Δ) (by ms)
      (by rw [subst_num, subst_mkMul, subst_mkAdd, subst_var_eq,
        subst_var_ne _ (show k + 1 ≠ k by omega), subst_of_notMem (notMem_of_below hr le_rfl)])
      hlin2 (by simp)
    have w2 := wire (M := s(mkMul (num m) (mkAdd (num m) r), num n) ::ₘ Δ)
      (k + 1) (num m) (num n) (mkMul (num m) (mkAdd (.var (k + 1)) r)) Δ (by ms)
      (by rw [subst_num, subst_mkMul, subst_mkAdd, subst_num, subst_var_eq,
        subst_of_notMem (notMem_of_below hr (by omega)), Sym2.eq_swap])
      (w1.linear hlin2) (by simp)
    have h3 : Reduces (s(mkMul (num m) r, num (n + 1)) ::ₘ Δ)
        (s(mkMul (num m) (mkAdd (num m) r), num n) ::ₘ Δ) :=
      h2.trans_equiv (w1.trans w2)
    have hk3 : Net.Below k (s(mkMul (num m) (mkAdd (num m) r), num n) ::ₘ Δ) := by
      simp [hr, hΔ]
    have h4 := h3.trans (ih _ _ k (h3.linear hlin) hk3)
    have hk4 : Net.Below k (s(mkAdd (num m) r, num (n * m)) ::ₘ Δ) := by
      simp [hr, hΔ]
    have h5 := h4.trans (add_num (n * m) (num m) r Δ k (h4.linear hlin) hk4)
    rwa [succs_num, ← Nat.succ_mul] at h5

/-! ## `2 × 2 = 4` -/

/-- The net of `n × m`: a `mul` cell whose first argument is `n`, second argument `m`, and whose
result is the free port `0`. -/
def times (n m : ℕ) : Net sig ℕ := s(mkMul (num m) (.var 0), num n) ::ₘ 0

/-- The net of the numeral `n` on the free port `0`. -/
def numNet (n : ℕ) : Net sig ℕ := s(.var 0, num n) ::ₘ 0

theorem times_linear (n m : ℕ) : (times n m).Linear := by
  intro z
  simp only [times, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_num, vars_mkMul,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

theorem times_below (n m : ℕ) : (times n m).Below 1 := by
  simp [times]

/-- **Multiplication is correct** (Lafont 1997, pages 76-77): the net of `n × m` reduces, up to
wires, to the net of the numeral `n * m`. -/
theorem times_reduces (n m : ℕ) :
    ∃ M, StepsE system (times n m) M ∧ Equiv M (numNet (n * m)) :=
  mul_num n m (.var 0) 0 1 (times_linear n m) (times_below n m)

/-- The net of `2 × 2`. -/
def twoTimesTwo : Net sig ℕ := times 2 2

/-- The net of `4` on the free port `0`. -/
def four : Net sig ℕ := numNet 4

/-- **`2 × 2 = 4`** (Lafont 1997, pages 76-77): the net of `2 × 2` reduces, by interactions up to
wires, to a net that is the same graph as the net of `4`. -/
theorem two_times_two : ∃ M, StepsE system twoTimesTwo M ∧ Equiv M four :=
  times_reduces 2 2

/-! ## Into the combinators -/

/-- **Unary multiplication translates into the interaction combinators** (Theorem 1 of Lafont
1997, applied to this system): there is a strict translation compatible with the eight rules. -/
theorem exists_translation :
    ∃ Φ : Translation sig Comb.sig, Φ.Strict ∧ Φ.Compatible system Comb.system :=
  Comb.universal_strict sig system system_wellFormed

/-- **`2 × 2 = 4` in the combinators.** For the translation of Theorem 1, every translation `N'`
of the net of `2 × 2` reduces, by the rules of `con`, `dup` and `era` and up to wires, to a net
that is the same graph as a translation of the net of `4`. -/
theorem two_times_two_in_combinators :
    ∃ Φ : Translation sig Comb.sig, Φ.Strict ∧ Φ.Compatible system Comb.system ∧
      ∀ N' : Net Comb.sig ℕ, Φ.NetTr twoTimesTwo N' →
        ∃ M₁ M' : Net Comb.sig ℕ, StepsE Comb.system N' M₁ ∧ Equiv M₁ M' ∧ Φ.NetTr four M' := by
  obtain ⟨Φ, hs, hc⟩ := exists_translation
  refine ⟨Φ, hs, hc, fun N' hN' => ?_⟩
  obtain ⟨M, hM, eM⟩ := two_times_two
  obtain ⟨M₁, M₂, h1, e1, t2⟩ := Translation.Compatible.stepsE system_wellFormed.linear
    Comb.system_wellFormed.linear hc hM hN'
  obtain ⟨M', t', e'⟩ := Translation.NetTr.of_equiv eM t2
  exact ⟨M₁, M', h1, e1.trans e', t'⟩

/-- The statement above is not empty: the net of `2 × 2` has a translation. -/
theorem twoTimesTwo_has_translation (Φ : Translation sig Comb.sig) :
    ∃ N' : Net Comb.sig ℕ, Φ.NetTr twoTimesTwo N' := by
  obtain ⟨N', _, h, _⟩ := Φ.exists_netTr (times_linear 2 2) (times_below 2 2)
  exact ⟨N', h⟩

end INet.Demo.Mul
