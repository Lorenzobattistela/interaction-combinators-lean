import Checks.SymmPermCheck

/-!
# Review of `Rule.SymmPerm` against the symmetry condition of page 73

Issue #241, review of PR #238. Lafont 1997, page 73 (PDF page 5): "if a symbol `α_i` interacts
with itself then `ν_{i,i} = ν̄_{i,i}`", where `ν̄_{i,j}` "is obtained by exchanging the `n_i` first
free ports with the `n_j` last ones in `ν_{i,j}`". The equality is equality of nets, that is of
graphs: same cells, same wiring, free ports fixed, internal wires unnamed.

`Rule.SymmPerm r` says `Equiv r.swap.net (r.net.bind (Sum.map id (Sum.map id π)))` for some
permutation `π` of the internal wires.

* `Rule.swap` sends `inl i` to `inr (inl i)` and `inr (inl j)` to `inl j`, and fixes the internal
  wires: this is the exchange of the `n_i` first free ports with the `n_i` last ones.
* `π` acts through `Sum.map id (Sum.map id π)`, so only on the internal wires; the free ports of
  both cells are fixed. The direction of `π` does not matter, as `π` is existentially bound and
  renaming by `π⁻¹` preserves `Equiv`.
* Not weaker: `Equiv` keeps the cells and the wiring, and renaming internal wires does not change
  the graph. So `SymmPerm` implies equality of graphs.
* Not stronger: two texts of the same graph, with the same type of names, differ by wire
  substitutions and a bijective renaming of the internal names. Both texts here are on
  `Fin a ⊕ Fin a ⊕ Fin r.internal`, so a renaming is a permutation of `Fin r.internal`.

## The checks in Lean

* `link3`, a linear reduced rule with five internal wires, symmetric with the permutation
  `π = (w₀ w₁)(w₂ w₃ w₄)`, which is not an involution (`link3_symmPerm`, `link3_perm_sq_ne_one`).
  The three wires `w₂, w₃, w₄` merely link `L_k` to `R_k`; `Equiv` eliminates them, so any
  permutation of them is allowed.
* `skew`, a linear reduced rule `a = β(α(w₀), w₁)`, `b = β(w₀, w₁)` that is not the same graph
  read from the other cell: the tree on the first port has two cells, the one on the second port
  has one. `skew_not_symmPerm` proves `¬ skew.SymmPerm`.
* `link3_inst_comm`: the conclusion of `Rule.equiv_inst_comm_of_symmPerm` on a concrete instance
  of `link3`, with its hypotheses proved, and `link3_inst_ne`: the two instances are different
  texts, so the conclusion is not an equality.

## A remark on the issue's request

The issue asks for a rule whose *needed* `π` is not an involution. For a linear reduced rule, the
set of admissible `π` is a coset of the group of renamings that fix the net up to `Equiv`, and the
square of an admissible `π` lies in that group (apply the swap twice). When that group is trivial,
the admissible `π` is unique and involutive. So a non-involutive `π` can be admissible only when
some renaming fixes the net, as in `link3`, where an involution (`(w₀ w₁)`) is admissible as well.
-/

namespace INet.SymmPermReview

open Term

/-- Decidable equality of trees on any signature with decidable symbols. -/
local instance {S : Signature} [DecidableEq S.Sym] {ν : Type} [DecidableEq ν] :
    DecidableEq (Term S ν) := Comb.DecompositionCheck.termDecEq

/-- Eliminating a wire `x` that links two names `p` and `q` (page 73: the text of a graph names
its wires freely). -/
theorem link_equiv {S : Signature} {ν : Type} [DecidableEq ν] (x p q : ν) (Δ : Net S ν)
    (hqx : q ≠ x) (hlin : Net.Linear (s(var x, var p) ::ₘ s(var q, var x) ::ₘ Δ)) :
    Equiv (s(var x, var p) ::ₘ s(var q, var x) ::ₘ Δ) (s(var q, var p) ::ₘ Δ) := by
  refine (Wire.mk x (var p) (var q) (var x) Δ hlin (by simp)).equiv.trans (Equiv.of_eq ?_)
  simp [Term.subst, Term.bind, hqx]

/-! ### `link3`: a non-involutive permutation -/

/-- Two symbols: `α` with four auxiliary ports, which interacts with itself, and `β` with two. -/
inductive LSym : Type
  | α | β
  deriving DecidableEq

/-- The signature of `LSym`. -/
def sigL : Signature where
  Sym := LSym
  arity
    | .α => 4
    | .β => 2

instance : DecidableEq sigL.Sym := inferInstanceAs (DecidableEq LSym)

/-- The names of a rule `α`–`α` of `sigL` with five internal wires. -/
abbrev LN := Fin 4 ⊕ Fin 4 ⊕ Fin 5

/-- An auxiliary port of the first cell. -/
abbrev lp (i : Fin 4) : Term sigL LN := var (.inl i)

/-- An auxiliary port of the second cell. -/
abbrev rp (j : Fin 4) : Term sigL LN := var (.inr (.inl j))

/-- An internal wire. -/
abbrev lw (w : Fin 5) : Term sigL LN := var (.inr (.inr w))

/-- A `β` cell. -/
def mkL {ν : Type} (u v : Term sigL ν) : Term sigL ν := .app LSym.β ![u, v]

/-- The rule `α`–`α` with right member `L₀ = β(w₀, w₁)`, `R₀ = β(w₁, w₀)` (the rule `twin`) and
three links `L_k = w_{k+1} = R_k` for `k = 1, 2, 3`. -/
def link3 : Rule sigL 4 4 :=
  ⟨5, s(lp 0, mkL (lw 0) (lw 1)) ::ₘ s(rp 0, mkL (lw 1) (lw 0)) ::ₘ
    s(lp 1, lw 2) ::ₘ s(rp 1, lw 2) ::ₘ s(lp 2, lw 3) ::ₘ s(rp 2, lw 3) ::ₘ
    s(lp 3, lw 4) ::ₘ s(rp 3, lw 4) ::ₘ 0⟩

/-- The permutation `(w₀ w₁)(w₂ w₃ w₄)` of the internal wires of `link3`. -/
def link3Perm : _root_.Equiv.Perm (Fin 5) :=
  _root_.Equiv.swap 0 1 * (_root_.Equiv.swap 2 4 * _root_.Equiv.swap 2 3)

/-- `link3Perm` is not an involution. -/
theorem link3_perm_sq_ne_one : link3Perm * link3Perm ≠ 1 := by decide

/-- `link3` is linear. -/
theorem link3_linear : link3.Linear := ⟨by decide, by decide, by decide⟩

/-- `link3` is reduced: every equation is rooted at a port. -/
theorem link3_reduced : link3.Reduced := by
  show ∀ e ∈ (show Net sigL LN from link3.net), ∃ (p : LN) (t : Term sigL LN),
    e = s(var p, t) ∧ ∀ w : Fin 5, p ≠ .inr (.inr w)
  intro e he
  have hk : ∀ e ∈ (show Net sigL LN from link3.net), e ∈ [s(lp 0, mkL (lw 0) (lw 1)),
      s(rp 0, mkL (lw 1) (lw 0)), s(lp 1, lw 2), s(rp 1, lw 2), s(lp 2, lw 3), s(rp 2, lw 3),
      s(lp 3, lw 4), s(rp 3, lw 4)] := by
    decide
  have key := hk e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at key
  rcases key with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, rfl, fun w h => by cases h⟩

/-- The common normal form of `link3` read from either cell, renamed: the links are
eliminated. -/
def link3Normal : Net sigL LN :=
  s(lp 0, mkL (lw 1) (lw 0)) ::ₘ s(rp 0, mkL (lw 0) (lw 1)) ::ₘ
    s(rp 1, lp 1) ::ₘ s(rp 2, lp 2) ::ₘ s(rp 3, lp 3) ::ₘ 0

/-- `link3` read from the other cell is `Equiv` to the normal form. -/
theorem link3_swap_equiv : Equiv link3.swap.net link3Normal := by
  have e0 : (show Net sigL LN from link3.swap.net) =
      s(lw 2, rp 1) ::ₘ s(lp 1, lw 2) ::ₘ (s(lw 3, rp 2) ::ₘ s(lp 2, lw 3) ::ₘ
        s(lw 4, rp 3) ::ₘ s(lp 3, lw 4) ::ₘ
        s(lp 0, mkL (lw 1) (lw 0)) ::ₘ s(rp 0, mkL (lw 0) (lw 1)) ::ₘ 0) := by decide
  refine (Equiv.of_eq e0).trans ((link_equiv _ _ _ _ (by decide)
    (by unfold Net.Linear; decide)).trans ?_)
  have e1 : (s(lp 1, rp 1) ::ₘ s(lw 3, rp 2) ::ₘ s(lp 2, lw 3) ::ₘ
        s(lw 4, rp 3) ::ₘ s(lp 3, lw 4) ::ₘ
        s(lp 0, mkL (lw 1) (lw 0)) ::ₘ s(rp 0, mkL (lw 0) (lw 1)) ::ₘ 0 : Net sigL LN) =
      s(lw 3, rp 2) ::ₘ s(lp 2, lw 3) ::ₘ (s(lp 1, rp 1) ::ₘ
        s(lw 4, rp 3) ::ₘ s(lp 3, lw 4) ::ₘ
        s(lp 0, mkL (lw 1) (lw 0)) ::ₘ s(rp 0, mkL (lw 0) (lw 1)) ::ₘ 0) := by decide
  refine (Equiv.of_eq e1).trans ((link_equiv _ _ _ _ (by decide)
    (by unfold Net.Linear; decide)).trans ?_)
  have e2 : (s(lp 2, rp 2) ::ₘ s(lp 1, rp 1) ::ₘ s(lw 4, rp 3) ::ₘ s(lp 3, lw 4) ::ₘ
        s(lp 0, mkL (lw 1) (lw 0)) ::ₘ s(rp 0, mkL (lw 0) (lw 1)) ::ₘ 0 : Net sigL LN) =
      s(lw 4, rp 3) ::ₘ s(lp 3, lw 4) ::ₘ (s(lp 2, rp 2) ::ₘ s(lp 1, rp 1) ::ₘ
        s(lp 0, mkL (lw 1) (lw 0)) ::ₘ s(rp 0, mkL (lw 0) (lw 1)) ::ₘ 0) := by decide
  refine (Equiv.of_eq e2).trans ((link_equiv _ _ _ _ (by decide)
    (by unfold Net.Linear; decide)).trans (Equiv.of_eq ?_))
  decide

/-- `link3` renamed by `link3Perm` is `Equiv` to the normal form. -/
theorem link3_perm_equiv :
    Equiv (link3.net.bind fun x => var (Sum.map id (Sum.map id link3Perm) x)) link3Normal := by
  have e0 : (show Net sigL LN from
        link3.net.bind fun x => var (Sum.map id (Sum.map id link3Perm) x)) =
      s(lw 3, lp 1) ::ₘ s(rp 1, lw 3) ::ₘ (s(lw 4, lp 2) ::ₘ s(rp 2, lw 4) ::ₘ
        s(lw 2, lp 3) ::ₘ s(rp 3, lw 2) ::ₘ
        s(lp 0, mkL (lw 1) (lw 0)) ::ₘ s(rp 0, mkL (lw 0) (lw 1)) ::ₘ 0) := by decide
  refine (Equiv.of_eq e0).trans ((link_equiv _ _ _ _ (by decide)
    (by unfold Net.Linear; decide)).trans ?_)
  have e1 : (s(rp 1, lp 1) ::ₘ s(lw 4, lp 2) ::ₘ s(rp 2, lw 4) ::ₘ
        s(lw 2, lp 3) ::ₘ s(rp 3, lw 2) ::ₘ
        s(lp 0, mkL (lw 1) (lw 0)) ::ₘ s(rp 0, mkL (lw 0) (lw 1)) ::ₘ 0 : Net sigL LN) =
      s(lw 4, lp 2) ::ₘ s(rp 2, lw 4) ::ₘ (s(rp 1, lp 1) ::ₘ
        s(lw 2, lp 3) ::ₘ s(rp 3, lw 2) ::ₘ
        s(lp 0, mkL (lw 1) (lw 0)) ::ₘ s(rp 0, mkL (lw 0) (lw 1)) ::ₘ 0) := by decide
  refine (Equiv.of_eq e1).trans ((link_equiv _ _ _ _ (by decide)
    (by unfold Net.Linear; decide)).trans ?_)
  have e2 : (s(rp 2, lp 2) ::ₘ s(rp 1, lp 1) ::ₘ s(lw 2, lp 3) ::ₘ s(rp 3, lw 2) ::ₘ
        s(lp 0, mkL (lw 1) (lw 0)) ::ₘ s(rp 0, mkL (lw 0) (lw 1)) ::ₘ 0 : Net sigL LN) =
      s(lw 2, lp 3) ::ₘ s(rp 3, lw 2) ::ₘ (s(rp 2, lp 2) ::ₘ s(rp 1, lp 1) ::ₘ
        s(lp 0, mkL (lw 1) (lw 0)) ::ₘ s(rp 0, mkL (lw 0) (lw 1)) ::ₘ 0) := by decide
  refine (Equiv.of_eq e2).trans ((link_equiv _ _ _ _ (by decide)
    (by unfold Net.Linear; decide)).trans (Equiv.of_eq ?_))
  decide

/-- **`link3` satisfies the symmetry condition of page 73 with the permutation
`(w₀ w₁)(w₂ w₃ w₄)`**, which is not an involution (`link3_perm_sq_ne_one`). -/
theorem link3_symmPerm :
    Equiv link3.swap.net (link3.net.bind fun x => var (Sum.map id (Sum.map id link3Perm) x)) :=
  link3_swap_equiv.trans link3_perm_equiv.symm

/-- `link3` is `Rule.SymmPerm` (page 73). -/
theorem link3_isSymmPerm : link3.SymmPerm := ⟨link3Perm, link3_symmPerm⟩

/-! ### The conclusion of `equiv_inst_comm_of_symmPerm` on an instance of `link3` -/

/-- The trees plugged into the first cell: the names `0, 1, 2, 3`. -/
def asL : Fin 4 → Term sigL ℕ := fun i => var i.val

/-- The trees plugged into the second cell: the names `4, 5, 6, 7`. -/
def bsL : Fin 4 → Term sigL ℕ := fun j => var (j.val + 4)

/-- The names of the internal wires: `8, …, 12`. -/
def fL : Fin 5 → ℕ := fun w => w.val + 8

/-- A context: a wire between the names `20` and `21`. -/
def ΔL : Net sigL ℕ := s(var 20, var 21) ::ₘ 0

/-- The names of the instance, listed. -/
theorem link3_inst_vars : Net.vars (link3.inst asL bsL fL + ΔL) =
    ↑[0, 8, 9, 4, 9, 8, 1, 10, 5, 10, 2, 11, 6, 11, 3, 12, 7, 12, 20, 21] := by
  decide +kernel

/-- The instance of `link3` with its context is linear. -/
theorem link3_inst_linear : (link3.inst asL bsL fL + ΔL).Linear := by
  intro x
  rw [link3_inst_vars, Multiset.coe_count]
  rcases Nat.lt_or_ge x 22 with hx | hx
  · interval_cases x <;> decide
  · rw [List.count_eq_zero_of_not_mem (by simp; omega)]
    omega

/-- **The conclusion of `Rule.equiv_inst_comm_of_symmPerm` on a concrete instance** (page 73): the
instances of `link3` read from either cell are the same graph. All hypotheses are met. -/
theorem link3_inst_comm :
    Equiv (link3.inst asL bsL fL + ΔL) (link3.inst bsL asL fL + ΔL) :=
  link3.equiv_inst_comm_of_symmPerm link3_linear link3_isSymmPerm asL bsL fL ΔL link3_inst_linear

/-- The two instances are different texts: the conclusion of `link3_inst_comm` is not an
equality. -/
theorem link3_inst_ne : link3.inst asL bsL fL + ΔL ≠ link3.inst bsL asL fL + ΔL := by
  decide

/-! ### `skew`: a rule the paper rejects -/

open DecompositionSymmReview

/-- The tree `α(t)` of `sigT`. -/
def mkA {ν : Type} (t : Term sigT ν) : Term sigT ν := .app TSym.α ![t]

/-- The rule `α`–`α` of `sigT` with right member `a = β(α(w₀), w₁)`, `b = β(w₀, w₁)`. Read from the
other cell, the tree on the port `a` has one cell and the tree on `b` has two: it is not the same
graph, so the paper rejects it (page 73). -/
def skew : Rule sigT 1 1 :=
  ⟨2, s(var (.inl 0), mkB (mkA (tw 0)) (tw 1)) ::ₘ
    {s(var (.inr (.inl 0)), mkB (tw 0) (tw 1))}⟩

/-- `skew` is linear. -/
theorem skew_linear : skew.Linear := ⟨by decide, by decide, by decide⟩

/-- `skew` is reduced: both equations are rooted at a port. -/
theorem skew_reduced : skew.Reduced := by
  intro e he
  dsimp only [skew] at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 0, _, rfl, fun w h => by cases h⟩
  obtain rfl := Multiset.mem_singleton.1 he
  exact ⟨.inr (.inl 0), _, rfl, fun w h => by cases h⟩

/-- **`skew` does not satisfy `Rule.SymmPerm`** (page 73). Its swap admits no wire substitution in
either direction (`Net.equiv_eq_of_rigid`), so it would have to be literally the renamed rule, and
no permutation of the two internal wires gives that. -/
theorem skew_not_symmPerm : ¬ skew.SymmPerm := by
  rintro ⟨π, h⟩
  have hr := Net.equiv_eq_of_rigid (N := skew.swap.net) (fun y => ?_) ?_ h
  · clear h
    revert π
    decide
  · revert y
    decide
  · show ∀ (x : Fin 1 ⊕ Fin 1 ⊕ Fin 2) (t : Term sigT (Fin 1 ⊕ Fin 1 ⊕ Fin 2)),
      s(var x, t) ∈ (show Net sigT (Fin 1 ⊕ Fin 1 ⊕ Fin 2) from skew.swap.net) →
        (Net.vars (show Net sigT (Fin 1 ⊕ Fin 1 ⊕ Fin 2) from skew.swap.net)).count x ≤ 1
    intro x t hm
    have key : ∀ e ∈ (show Net sigT (Fin 1 ⊕ Fin 1 ⊕ Fin 2) from skew.swap.net),
        e ∈ [s(var (.inr (.inl 0)), mkB (mkA (tw 0)) (tw 1)),
          s(var (.inl 0), mkB (tw 0) (tw 1))] := by
      decide
    have hm' := key _ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
    rcases hm' with e | e <;> rcases Sym2.eq_iff.1 e with ⟨e1, -⟩ | ⟨e1, -⟩ <;> cases e1 <;>
      decide

end INet.SymmPermReview
