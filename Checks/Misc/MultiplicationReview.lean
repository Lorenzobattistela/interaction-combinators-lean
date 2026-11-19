import Demo.Multiplication
import InteractionCombinators.Universality.RecursionFree.DecompositionLemmas

/-!
# Review of the multiplication system of `Demo/Multiplication.lean` (pages 76-77)

Issue #352. Lafont 1997, Section 1.5, pages 76-77 (PDF pages 8-9). Each of the eight rules of
`INet.Demo.Mul.system` was compared with its figure, read at 600 dpi.

## Conventions

* Page 71: the auxiliary ports of a cell "will always be implicitly numbered in clockwise order",
  and the cell drawn with its principal port down (`▽`) "is obtained from the first one by a
  rotation of 180°". In particular a `▽` and a `△` are the same cell, and the top-left port of a
  `▽` is the bottom-right port of the `△`.
* `Demo/Multiplication.lean` numbers the auxiliary ports of a `△` from left to right: for `+` and
  `×`, port 0 is `y` and port 1 is the result, as in the picture of page 76 (`y` on the left,
  `x + y` on the right). This is the mirror of the clockwise numbering of page 71, applied to every
  symbol at once, which gives an isomorphic system. Under it, the auxiliary ports of a `▽` are
  numbered from right to left: port 0 of a `▽` is its top-right port.

## Verdict, rule by rule

* `s+` (page 76), `ruleAddSucc`: agrees. The new `+` has its principal port on the free port of
  the `s` (`x`), its left port on the free port `y`; its right port goes to the auxiliary port of
  a `▽ s` whose principal port is the free port `r`.
* `0+` (page 76), `ruleAddZero`: agrees, `y ~ r`.
* `s×` (page 77), `ruleMulSucc`: agrees since issue #354 (`ruleMulSucc_eq_paper`). The review
  of issue #352 found the auxiliary ports of the duplicator exchanged; the rule was corrected. In
  the figure the new `×` has its principal port on `x`, its left port on the top-left port of the
  upside-down `δ`, its right port on the principal port of a `+`; the `+` has its left port on the
  top-right port of the `δ` and its right port on the free port `r`; the principal port of the `δ`
  is the free port `y`. By the convention of page 71 the top-left port of the `▽ δ` is its port 1
  (left-to-right numbering of the `△`), so the figure says
  `y ~ δ(w₁, w₀)`, `x ~ mul(w₀, add(w₁, r))` (`ruleMulSuccPaper` below), which is now
  `ruleMulSucc`. The file had `y ~ δ(w₀, w₁)` (`ruleMulSuccSwapped` below), which is not the same
  rule up to a renaming of the internal wires (`ruleMulSuccSwapped_ne`). The mismatch did not
  affect any result of the file: a duplicator makes two equal copies of a numeral (`dup_num`).
* `0×` (page 77), `ruleMulZero`: agrees, `y ~ ε` (left), `r ~ 0` (right).
* `sδ` (page 77), `ruleDupSucc`: agrees. All cells are `△` or the one-port `▽ s`; the new `δ` has
  its left port on the left `s`, whose principal port is the left free port `a`.
* `0δ` (page 77), `ruleDupZero`: agrees.
* `sε` (page 77), `ruleEraSucc`: agrees, `x ~ ε`.
* `0ε` (page 77), `ruleEraZero`: agrees, the empty net.

The text of page 76 prints `sx × y = (x + y) + y`, a misprint for `(x × y) + y`: the figure `s×`
has a `×` cell feeding a `+` cell, and `ruleMulSucc` follows the figure.

`system.rule` is `none` exactly on the pairs with no figure (`system_rule_eq_none`); the
corresponding cuts do not reduce (`no_step_mul_mul`, `no_step_add_dup`, `no_step_mul_add`,
`no_step_succ_zero`).

The first argument of `×` is on its principal port (page 76: "we shall always plug this argument
into the principal port of `+`, and similarly for `×`"); `times n m` puts `n` there
(`times_three_zero_step`, `times_zero_three_step`).
-/

namespace INet.Demo.Mul.Review

open Term

/-! ## The rule `s×` as drawn -/

/-- The `i`-th auxiliary port of the first cell. -/
private def l {a b m : ℕ} (i : Fin a) : Term sig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inl i)
/-- The `i`-th auxiliary port of the second cell. -/
private def r {a b m : ℕ} (i : Fin b) : Term sig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inr (.inl i))
/-- The `i`-th wire created by the rule. -/
private def w {a b m : ℕ} (i : Fin m) : Term sig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inr (.inr i))

/-- The rule `s×` of page 77 read with the convention of page 71 (the upside-down `δ` is a `△`
turned by 180°): `y ~ δ(w₁, w₀)`, `x ~ mul(w₀, add(w₁, r))`. The `×` is on the top-left port of
the `δ`, which is its second auxiliary port. -/
def ruleMulSuccPaper : Rule sig 2 1 :=
  ⟨2, s(l 0, mkDup (w 1) (w 0)) ::ₘ s(r 0, mkMul (w 0) (mkAdd (w 1) (l 1))) ::ₘ 0⟩

/-- **`ruleMulSucc` is the rule `s×` as drawn** (page 77): the rule of `Demo/Multiplication.lean`
is literally `ruleMulSuccPaper`. -/
theorem ruleMulSucc_eq_paper : ruleMulSucc = ruleMulSuccPaper := rfl

/-- The reading of `s×` with the two auxiliary ports of the upside-down `δ` exchanged:
`y ~ δ(w₀, w₁)`, `x ~ mul(w₀, add(w₁, r))`. This was `ruleMulSucc` before issue #354. -/
def ruleMulSuccSwapped : Rule sig 2 1 :=
  ⟨2, s(l 0, mkDup (w 0) (w 1)) ::ₘ s(r 0, mkMul (w 0) (mkAdd (w 1) (l 1))) ::ₘ 0⟩

/-- The internal wires of a rule of type `Rule sig 2 1` renamed by a permutation. -/
def renameInternal (π : _root_.Equiv.Perm (Fin 2))
    (N : Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 2)) : Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 2) :=
  N.bind fun x => Term.var (Sum.map id (Sum.map id π) x)

local instance : DecidableEq sig.Sym := inferInstanceAs (DecidableEq Sym)

local instance : DecidableEq (Term sig (Fin 2 ⊕ Fin 1 ⊕ Fin 2)) :=
  INet.Comb.DecompositionCheck.termDecEq

/-- **The two readings of `s×` are different rules** (page 77). No renaming of the two internal
wires of `ruleMulSuccPaper` gives the net of `ruleMulSuccSwapped`: in `ruleMulSuccSwapped` the
second argument of the new `mul` is the first auxiliary port of the duplicator, in the paper
reading it is the second. So the reading of the upside-down `δ` changes the rule, not only the
names of the internal wires. -/
theorem ruleMulSuccSwapped_ne (π : _root_.Equiv.Perm (Fin 2)) :
    renameInternal π ruleMulSuccPaper.net ≠
      (show Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 2) from ruleMulSuccSwapped.net) := by
  revert π
  decide

/-- `ruleMulSuccSwapped_ne` is not vacuous: `renameInternal` does rename. Exchanging the two
internal wires of the paper reading puts the duplicator in the order of `ruleMulSuccSwapped`, but
moves the `mul` and the `add` to the other copy. -/
theorem renameInternal_swap_ruleMulSuccPaper :
    renameInternal (_root_.Equiv.swap 0 1) ruleMulSuccPaper.net =
      s(l 0, mkDup (w 0) (w 1)) ::ₘ s(r 0, mkMul (w 1) (mkAdd (w 0) (l 1))) ::ₘ 0 := by
  decide

/-- The identity renaming leaves `ruleMulSuccSwapped` unchanged, so the comparison of
`ruleMulSuccSwapped_ne` is made at the right type. -/
theorem renameInternal_one_ruleMulSuccSwapped :
    renameInternal 1 (show Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 2) from ruleMulSuccSwapped.net) =
      (show Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 2) from ruleMulSuccSwapped.net) := by
  decide

/-- The paper reading of `s×` is linear. -/
theorem ruleMulSuccPaper_linear : ruleMulSuccPaper.Linear := by
  constructor
  · intro i; fin_cases i <;> simp [ruleMulSuccPaper, l, r, w]
  · intro j; fin_cases j; simp [ruleMulSuccPaper, l, r, w]
  · intro i; fin_cases i <;> simp [ruleMulSuccPaper, l, r, w]

/-- The paper reading of `s×` is a reduced net. -/
theorem ruleMulSuccPaper_reduced : ruleMulSuccPaper.Reduced := by
  intro e he
  unfold ruleMulSuccPaper at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 0, _, rfl, by simp⟩
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inr (.inl 0), _, rfl, by simp⟩
  · exact absurd he (Multiset.notMem_zero _)

/-! ## Pairs without a rule do not interact -/

/-- `system.rule` is `none` exactly where pages 76-77 draw no rule: the first symbol is not one
of `+`, `×`, `δ`, `ε`, or the second is not `0` or `s`. -/
theorem system_rule_eq_none (α β : sig.Sym) :
    system.rule α β = none ↔
      (α ∉ [Sym.add, Sym.mul, Sym.dup, Sym.era] ∨ β ∉ [Sym.zero, Sym.succ]) := by
  cases α <;> cases β <;> simp [system] <;> decide

/-- Any interaction of `system` happens on a cut whose pair of symbols has a rule. -/
private theorem step_cut {N M : Net sig ℕ} (h : Step system N M) :
    ∃ α β as bs, system.rule α β ≠ none ∧ s(Term.app α as, Term.app β bs) ∈ N := by
  obtain ⟨α, β, r, hr, as, bs, Δ, f, -, -⟩ := h
  exact ⟨α, β, as, bs, by simp [hr], Multiset.mem_cons_self _ _⟩

/-- A cut between two cells with no rule, alone in a net, has no successor. -/
private theorem no_step_of_none (γ δ : sig.Sym) (cs : Fin (sig.arity γ) → Term sig ℕ)
    (ds : Fin (sig.arity δ) → Term sig ℕ) (h1 : system.rule γ δ = none)
    (h2 : system.rule δ γ = none) (M : Net sig ℕ) :
    ¬ Step system (s(Term.app γ cs, Term.app δ ds) ::ₘ 0) M := by
  intro h
  obtain ⟨α, β, as, bs, hr, hm⟩ := step_cut h
  rcases Multiset.mem_cons.1 hm with hm | hm
  swap; · exact absurd hm (Multiset.notMem_zero _)
  rw [Sym2.eq_iff] at hm
  rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · injection e1 with ha; injection e2 with hb; subst ha hb; exact hr h1
  · injection e1 with ha; injection e2 with hb; subst ha hb; exact hr h2

/-- **`×` against `×` does not interact** (pages 76-77 give no rule). -/
theorem no_step_mul_mul (a b c d : Term sig ℕ) (M : Net sig ℕ) :
    ¬ Step system (s(mkMul a b, mkMul c d) ::ₘ 0) M :=
  no_step_of_none Sym.mul Sym.mul _ _ rfl rfl M

/-- **`+` against `δ` does not interact** (pages 76-77 give no rule). -/
theorem no_step_add_dup (a b c d : Term sig ℕ) (M : Net sig ℕ) :
    ¬ Step system (s(mkAdd a b, mkDup c d) ::ₘ 0) M :=
  no_step_of_none Sym.add Sym.dup _ _ rfl rfl M

/-- **`×` against `+` does not interact** (pages 76-77 give no rule). -/
theorem no_step_mul_add (a b c d : Term sig ℕ) (M : Net sig ℕ) :
    ¬ Step system (s(mkMul a b, mkAdd c d) ::ₘ 0) M :=
  no_step_of_none Sym.mul Sym.add _ _ rfl rfl M

/-- **`s` against `0` does not interact**: two numerals plugged together are an irreducible cut
(page 77, Section 1.6). -/
theorem no_step_succ_zero (x : Term sig ℕ) (M : Net sig ℕ) :
    ¬ Step system (s(mkSucc x, mkZero) ::ₘ 0) M :=
  no_step_of_none Sym.succ Sym.zero _ _ rfl rfl M

/-! ## Computed cases and the order of the factors -/

/-- **`1 × 3 = 3`** (pages 76-77): the net of `1 × 3` reduces, up to wires, to the hand-written
net `x ~ s(s(s(0)))`. -/
theorem one_times_three :
    ∃ M, StepsE system (times 1 3) M ∧
      Equiv M (s(.var 0, mkSucc (mkSucc (mkSucc mkZero))) ::ₘ 0) :=
  times_reduces 1 3

/-- **`3 × 0 = 0`** (pages 76-77): the net of `3 × 0` reduces, up to wires, to the hand-written
net `x ~ 0`. -/
theorem three_times_zero :
    ∃ M, StepsE system (times 3 0) M ∧ Equiv M (s(.var 0, mkZero) ::ₘ 0) :=
  times_reduces 3 0

/-- **The first factor is on the principal port of `×`** (page 76). In `times 3 0` the `mul` cell
meets `s`, and its first interaction is `s×`: the second factor `0` goes to a duplicator. If the
factors were exchanged the `mul` cell would meet `0` and the first interaction would be `0×`. -/
theorem times_three_zero_step :
    Step system (times 3 0)
      (s(mkZero, mkDup (.var 2) (.var 1)) ::ₘ
        s(num 2, mkMul (.var 1) (mkAdd (.var 2) (.var 0))) ::ₘ 0) :=
  step_mul_succ (num 0) (.var 0) (num 2) 0 1 (by simp) (by simp)

/-- In `times 0 3` the `mul` cell meets `0`, and its first interaction is `0×`: the second factor
`3` goes to an eraser and the result is `0` (page 77). -/
theorem times_zero_three_step :
    Step system (times 0 3) (s(num 3, mkEra) ::ₘ s(.var 0, mkZero) ::ₘ 0) :=
  step_mul_zero (num 3) (.var 0) 0

end INet.Demo.Mul.Review
