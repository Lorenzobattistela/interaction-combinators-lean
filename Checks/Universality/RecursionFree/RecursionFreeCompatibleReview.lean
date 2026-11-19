import InteractionCombinators.Universality.RecursionFree.RecursionFreeCompatible
import Checks.Universality.RecursionFree.DecompositionCheck

/-!
# Review of `recursionFree_strict` and `translation_cells_meet` (pages 85–87, Fig. 7)

Lafont 1997, Section 2.4, journal pages 85–87 (PDF pages 17–19).

* `Translation.exists_linear_pair` — the linearity hypothesis of `Translation.Compatible` (and of
  `translation_cells_meet`, `translation_cells_netTr_plug`) holds for some names, for every
  translation and every pair of symbols: ports `0, 1, …`, then the internal wires of the two
  instances on two blocks above. So `Translation.Compatible` is not vacuous, for any rule.
* A recursion-free system that is not the combinators, `tsys`, over the alphabet `e < b < c`
  (arities `0, 1, 1`), with rules `e`–`b` (the eraser `e` erases `b`), `b`–`b` (annihilation) and
  `b`–`c` (the port of `b` receives a new `b` cell on the port of `c`). Its decompositions put
  cells in `φ`: the side of `e` against `b` is an `e` cell, the side of `b` against `c` is a `b`
  cell. So `[c]` is built from `[b]`, which is built from `[e]`: two levels of the recursion of
  Fig. 6 (`tsys_two_levels`). `tsys_strict` applies `recursionFree_strict` to it.
-/

namespace INet

variable {S S' : Signature}

open Term

/-- An indicator sum over a block of names: `x` is one of `c, c + 1, …, c + k - 1` at most once. -/
theorem RecursionFreeCompatibleReview.sum_ite_block (k c x : ℕ) :
    (∑ i : Fin k, if x = c + (i : ℕ) then 1 else 0) = if c ≤ x ∧ x < c + k then 1 else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨x - c, by omega⟩ : Fin k)]
    · simp only [ite_eq_left_iff]
      omega
    · intro i _ hi
      rw [ite_eq_right]
      intro hx
      exact hi (Fin.ext (by simp only; omega))
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [ite_eq_right]
    have := i.isLt
    omega

open RecursionFreeCompatibleReview in
/-- **The hypothesis of `Translation.Compatible` can be met** (Lafont 1997, page 80): for every
translation `Φ` and every pair of symbols `α`, `β`, there are names `xs`, `ys` for the auxiliary
ports and `f`, `g` for the internal wires such that the two instances plugged by their roots form
a linear net. The names are `0, …, n - 1` for the ports of `α`, `n, …, n + m - 1` for those of
`β`, and two blocks above for the internal wires. So the hypothesis `hlin` of
`translation_cells_meet` and `translation_cells_netTr_plug` is satisfiable for every rule, and
`Translation.Compatible` is not vacuous. -/
theorem Translation.exists_linear_pair (Φ : Translation S S') (α β : S.Sym) :
    ∃ (xs : Fin (S.arity α) → ℕ) (ys : Fin (S.arity β) → ℕ)
      (f : Fin (Φ.net α).internal → ℕ) (g : Fin (Φ.net β).internal → ℕ),
      Net.Linear ({s((Φ.net α).inst (fun i => .var (xs i)) f,
        (Φ.net β).inst (fun j => .var (ys j)) g)} : Net S' ℕ) := by
  let n := S.arity α
  let m := S.arity β
  let A := (Φ.net α).internal
  let B := (Φ.net β).internal
  refine ⟨fun i => 0 + (i : ℕ), fun j => n + (j : ℕ), fun w => n + m + (w : ℕ),
    fun w => n + m + A + (w : ℕ), fun x => ?_⟩
  simp only [Net.vars_singleton, eqVars_mk, Multiset.count_add, PNet.count_vars_inst,
    Term.vars_var, Multiset.count_singleton, sum_ite_block]
  have hA : A = (Φ.net α).internal := rfl
  have hB : B = (Φ.net β).internal := rfl
  have hn : n = S.arity α := rfl
  have hm : m = S.arity β := rfl
  split_ifs <;> omega

/-! ## A recursion-free system with two levels of recursion -/

namespace Comb.RecursionFreeCompatibleReview

/-- Three symbols: `e` (an eraser), `b` and `c`, each with one auxiliary port. -/
inductive TSym : Type
  | e | b | c
  deriving DecidableEq

/-- The signature of `TSym`: `e` has no auxiliary port, `b` and `c` have one. -/
def tsig : Signature where
  Sym := TSym
  arity
    | .e => 0
    | .b => 1
    | .c => 1

instance : DecidableEq tsig.Sym := inferInstanceAs (DecidableEq TSym)

instance {ν : Type} [DecidableEq ν] : DecidableEq (Term tsig ν) := DecompositionCheck.termDecEq

instance : Finite tsig.Sym :=
  Finite.of_surjective (fun i : Fin 3 => ![TSym.e, TSym.b, TSym.c] i) (by
    intro x
    cases x
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩])

/-- A port of the first cell. -/
abbrev pl {a b m : ℕ} (i : Fin a) : Term tsig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inl i)
/-- A port of the second cell (in a side: a middle wire). -/
abbrev pr {a b m : ℕ} (j : Fin b) : Term tsig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inr (.inl j))
/-- An internal wire. -/
abbrev pw {a b m : ℕ} (w : Fin m) : Term tsig (Fin a ⊕ Fin b ⊕ Fin m) := .var (.inr (.inr w))

/-- An `e` cell. -/
def mkE {ν : Type} : Term tsig ν := .app TSym.e Fin.elim0

/-- A `b` cell with a tree on its auxiliary port. -/
def mkB {ν : Type} (t : Term tsig ν) : Term tsig ν := .app TSym.b ![t]

/-- `e`–`b`: the eraser erases the port of `b`. -/
def ruleEB : Rule tsig 0 1 := ⟨0, {s(pr 0, mkE)}⟩

/-- `b`–`b`: the two ports are joined. -/
def ruleBB : Rule tsig 1 1 := ⟨0, {s(pl 0, pr 0)}⟩

/-- `b`–`c`: the port of `b` receives a new `b` cell, whose port is the port of `c`. -/
def ruleBC : Rule tsig 1 1 := ⟨0, {s(pl 0, mkB (pr 0))}⟩

/-- The system of `e`, `b`, `c`: the rules `e`–`b`, `b`–`b`, `b`–`c`, and nothing else. -/
def tsys : System tsig where
  rule
    | .e, .b => some ruleEB
    | .b, .b => some ruleBB
    | .b, .c => some ruleBC
    | _, _ => none

theorem ruleEB_reduced : ruleEB.Reduced := by
  intro e he
  have key : ∀ e ∈ (show Net tsig (Fin 0 ⊕ Fin 1 ⊕ Fin 0) from ruleEB.net),
      e = s(pr 0, mkE) := by decide
  rw [key e he]
  exact ⟨_, _, rfl, fun w => w.elim0⟩

theorem ruleBB_reduced : ruleBB.Reduced := by
  intro e he
  have key : ∀ e ∈ (show Net tsig (Fin 1 ⊕ Fin 1 ⊕ Fin 0) from ruleBB.net),
      e = s(pl 0, pr 0) := by decide
  rw [key e he]
  exact ⟨_, _, rfl, fun w => w.elim0⟩

theorem ruleBC_reduced : ruleBC.Reduced := by
  intro e he
  have key : ∀ e ∈ (show Net tsig (Fin 1 ⊕ Fin 1 ⊕ Fin 0) from ruleBC.net),
      e = s(pl 0, mkB (pr 0)) := by decide
  rw [key e he]
  exact ⟨_, _, rfl, fun w => w.elim0⟩

/-- `tsys` is an interaction system: linear and reduced rules, at most one of `α`–`β`, `β`–`α`,
and `b`–`b` symmetric. -/
theorem tsys_wellFormed : tsys.WellFormed where
  linear := by
    intro α β r h
    cases α <;> cases β <;> cases h <;> exact ⟨by decide, by decide, by decide⟩
  reduced := by
    intro α β r h
    cases α <;> cases β <;> cases h
    exacts [ruleEB_reduced, ruleBB_reduced, ruleBC_reduced]
  unique := by
    intro α β hne h
    cases α <;> cases β <;> first | rfl | exact absurd rfl hne | cases h
  symm := by
    refine fun α r h => Rule.symm_of_equiv ?_
    revert α r h
    intro α r h
    cases α <;> cases h
    exact Equiv.of_eq (show (show Net tsig (Fin 1 ⊕ Fin 1 ⊕ Fin 0) from ruleBB.swap.net) =
      (show Net tsig (Fin 1 ⊕ Fin 1 ⊕ Fin 0) from ruleBB.net) by decide)

/-! ### The decompositions -/

/-- The side that joins the port to the middle wire. -/
def idSide : Rule tsig 1 1 := ⟨0, {s(pl 0, pr 0)}⟩

/-- The side of `e` against `b`: an `e` cell on the middle wire. -/
def eSide : Rule tsig 0 1 := ⟨0, {s(mkE, pr 0)}⟩

/-- The side of `b` against `c`: the port of `b` receives a `b` cell on the middle wire. -/
def bSide : Rule tsig 1 1 := ⟨0, {s(pl 0, mkB (pr 0))}⟩

/-- `e`–`b`, non-canonical: the eraser goes into `φ`, on the middle wire. -/
def decEB : Decomposition tsig 0 1 := ⟨1, eSide, idSide, 1⟩

/-- `b`–`b`: both sides join the port to the middle wire. -/
def decBB : Decomposition tsig 1 1 := ⟨1, idSide, idSide, 1⟩

/-- `b`–`c`: the new `b` cell goes into `φ`, on the side of the first `b`. -/
def decBC : Decomposition tsig 1 1 := ⟨1, bSide, idSide, 1⟩

/-- The decomposition of each rule of `tsys`; arbitrary where there is no rule. -/
def tdec : (α β : tsig.Sym) → Decomposition tsig (tsig.arity α) (tsig.arity β)
  | .e, .b => decEB
  | .b, .b => decBB
  | .b, .c => decBC
  | _, _ => ⟨0, ⟨0, 0⟩, ⟨0, 0⟩, 1⟩

/-- The order `e < b < c`. -/
def trank : tsig.Sym → ℕ
  | .e => 0
  | .b => 1
  | .c => 2

/-- One wire substitution between two nets given as texts. -/
theorem equiv_wire_of_eq {ν : Type} [DecidableEq ν] {N M : Net tsig ν} (x : ν)
    (t a b : Term tsig ν) (Δ : Net tsig ν) (hlin : Net.Linear (s(var x, t) ::ₘ s(a, b) ::ₘ Δ))
    (hx : x ∈ a.vars + b.vars) (hN : N = s(var x, t) ::ₘ s(a, b) ::ₘ Δ)
    (hM : M = s(a.subst x t, b.subst x t) ::ₘ Δ) : Equiv N M := by
  rw [hN, hM]
  exact (Wire.mk x t a b Δ hlin hx).equiv

theorem decEB_plugs : decEB.Plugs ruleEB := by
  refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
  have h₁ := equiv_wire_of_eq (ν := Fin 0 ⊕ Fin 1 ⊕ Fin 1)
    (N := (show Net tsig (Fin 0 ⊕ Fin 1 ⊕ Fin 1) from
      (Rule.plug decEB.φ decEB.ψ decEB.σ).net))
    (M := {s(pr 0, mkE)}) (.inr (.inr 0)) mkE (pr 0) (pw 0) 0
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have e : ({s(pr 0, mkE)} : Net tsig (Fin 0 ⊕ Fin 1 ⊕ Fin 1)) =
      (show Net tsig (Fin 0 ⊕ Fin 1 ⊕ Fin 1) from ruleEB.net.bind
        fun x => var (Sum.map id (Sum.map id (Fin.elim0 : Fin 0 → Fin 1)) x)) := by decide
  exact h₁.trans (Equiv.of_eq e)

theorem decBB_plugs : decBB.Plugs ruleBB := by
  refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
  have h₁ := equiv_wire_of_eq (ν := Fin 1 ⊕ Fin 1 ⊕ Fin 1)
    (N := (show Net tsig (Fin 1 ⊕ Fin 1 ⊕ Fin 1) from
      (Rule.plug decBB.φ decBB.ψ decBB.σ).net))
    (M := {s(pr 0, pl 0)}) (.inr (.inr 0)) (pl 0) (pr 0) (pw 0) 0
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have e : ({s(pr 0, pl 0)} : Net tsig (Fin 1 ⊕ Fin 1 ⊕ Fin 1)) =
      (show Net tsig (Fin 1 ⊕ Fin 1 ⊕ Fin 1) from ruleBB.net.bind
        fun x => var (Sum.map id (Sum.map id (Fin.elim0 : Fin 0 → Fin 1)) x)) := by decide
  exact h₁.trans (Equiv.of_eq e)

theorem decBC_plugs : decBC.Plugs ruleBC := by
  refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
  have h₁ := equiv_wire_of_eq (ν := Fin 1 ⊕ Fin 1 ⊕ Fin 1)
    (N := (show Net tsig (Fin 1 ⊕ Fin 1 ⊕ Fin 1) from
      (Rule.plug decBC.φ decBC.ψ decBC.σ).net))
    (M := {s(pl 0, mkB (pr 0))}) (.inr (.inr 0)) (pr 0) (pl 0) (mkB (pw 0)) 0
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have e : ({s(pl 0, mkB (pr 0))} : Net tsig (Fin 1 ⊕ Fin 1 ⊕ Fin 1)) =
      (show Net tsig (Fin 1 ⊕ Fin 1 ⊕ Fin 1) from ruleBC.net.bind
        fun x => var (Sum.map id (Sum.map id (Fin.elim0 : Fin 0 → Fin 1)) x)) := by decide
  exact h₁.trans (Equiv.of_eq e)

theorem idSide_reduced : idSide.Reduced := by
  intro e he
  have key : ∀ e ∈ (show Net tsig (Fin 1 ⊕ Fin 1 ⊕ Fin 0) from idSide.net),
      e = s(pl 0, pr 0) := by decide
  rw [key e he]
  exact ⟨_, _, rfl, fun w => w.elim0⟩

theorem eSide_reduced : eSide.Reduced := by
  intro e he
  have key : ∀ e ∈ (show Net tsig (Fin 0 ⊕ Fin 1 ⊕ Fin 0) from eSide.net),
      e = s(pr 0, mkE) := by decide
  rw [key e he]
  exact ⟨_, _, rfl, fun w => w.elim0⟩

theorem bSide_reduced : bSide.Reduced := by
  intro e he
  have key : ∀ e ∈ (show Net tsig (Fin 1 ⊕ Fin 1 ⊕ Fin 0) from bSide.net),
      e = s(pl 0, mkB (pr 0)) := by decide
  rw [key e he]
  exact ⟨_, _, rfl, fun w => w.elim0⟩

/-- **`tsys` is recursion-free** (Lafont 1997, page 86), with the order `e < b < c`: the side of
`e` against `b` is an `e` cell, smaller than `b`; the side of `b` against `c` is a `b` cell,
smaller than `c`; the other sides have no cell. -/
def tdata : tsys.RecursionFreeData where
  rank := trank
  dec α β _ _ := tdec α β
  plug := by
    intro α β r h
    cases α <;> cases β <;> cases h
    exacts [decEB_plugs, decBB_plugs, decBC_plugs]
  linear := by
    intro α β r h
    cases α <;> cases β <;> cases h <;>
      exact ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩
  reduced := by
    intro α β r h
    cases α <;> cases β <;> cases h
    exacts [⟨eSide_reduced, idSide_reduced⟩, ⟨idSide_reduced, idSide_reduced⟩,
      ⟨bSide_reduced, idSide_reduced⟩]
  involutive := by
    intro α β r h
    cases α <;> cases β <;> cases h <;> exact fun l => rfl
  self := by
    intro α r h
    cases α <;> cases h
    rfl
  ne := by
    intro α β r h hne
    cases α <;> cases β <;> cases h <;> rfl
  rank_φ := by
    intro α β r h
    cases α <;> cases β <;> cases h <;> decide
  rank_ψ := by
    intro α β r h
    cases α <;> cases β <;> cases h <;> decide

/-- **Two levels of the recursion of Fig. 6** (Lafont 1997, page 86). In the menu of `[c]`, the
package `Γ_{b,c}` is built from the side of `b` against `c`, the `φ` of the rule `b`–`c`, which
has a `b` cell; in the menu of `[b]`, the package `Γ_{e,b}` is built from the side of `e` against
`b`, the `φ` of the rule `e`–`b`, which has an `e` cell. So `[c]` contains `[b]`, which contains
`[e]`: the translation is not only the base case of Fig. 6. -/
theorem tsys_two_levels :
    tdata.rawSide TSym.b TSym.c = some (tdata.rawφ TSym.b TSym.c ruleBC rfl) ∧
      (tdata.rawφ TSym.b TSym.c ruleBC rfl).φ.net.cells = {TSym.b} ∧
    tdata.rawSide TSym.e TSym.b = some (tdata.rawφ TSym.e TSym.b ruleEB rfl) ∧
      (tdata.rawφ TSym.e TSym.b ruleEB rfl).φ.net.cells = {TSym.e} :=
  ⟨tdata.rawSide_of_rule rfl, by decide, tdata.rawSide_of_rule rfl, by decide⟩

/-- **`recursionFree_strict` applies to `tsys`** (Lafont 1997, Section 2.4, pages 85–87): a
recursion-free system that is not the combinators, whose translation uses two levels of the
recursion of Fig. 6 (`tsys_two_levels`), has a strict translation into the interaction
combinators. -/
theorem tsys_strict : ∃ Φ : Translation tsig sig, Φ.Strict ∧ Φ.Compatible tsys system :=
  recursionFree_strict tsys tsys_wellFormed ⟨tdata⟩

/-- The hypothesis of `Compatible` holds for the rule `b`–`c` of `tsys` under `D.translation`
(`Translation.exists_linear_pair`), so `tsys_strict` gives an actual reduction for it. -/
theorem tsys_bc_reduces : ∃ (xs : Fin 1 → ℕ) (ys : Fin 1 → ℕ)
    (f : Fin (tdata.translation.net TSym.b).internal → ℕ)
    (g : Fin (tdata.translation.net TSym.c).internal → ℕ)
    (M N' : Net sig ℕ) (h : Fin ruleBC.internal → ℕ),
    StepsE system {s((tdata.translation.net TSym.b).inst (fun i => .var (xs i)) f,
      (tdata.translation.net TSym.c).inst (fun j => .var (ys j)) g)} M ∧
    Equiv M N' ∧
    tdata.translation.NetTr (ruleBC.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N' := by
  obtain ⟨xs, ys, f, g, hlin⟩ := tdata.translation.exists_linear_pair TSym.b TSym.c
  obtain ⟨M, N', h, hS, hE, hN⟩ :=
    tdata.translation_compatible tsys_wellFormed TSym.b TSym.c ruleBC rfl xs ys f g hlin
  exact ⟨xs, ys, f, g, M, N', h, hS, hE, hN⟩

end Comb.RecursionFreeCompatibleReview

end INet
