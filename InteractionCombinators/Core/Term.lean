import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Basic.Finite.Defs
import Mathlib.Basic.Finite.Sum
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Inv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Fintype
import Mathlib.Data.Multiset.Lattice
import Mathlib.Data.Multiset.Sum
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Logic.Relation
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Trees over a signature

The textual presentation of interaction nets: a net is a set of equations between trees, and a
name stands for a wire, occurring once at each of its two ends.

* `Signature` — symbols with the number of their auxiliary ports.
* `Term S ν` — trees of cells whose leaves are names in `ν`.
* `Term.bind` — plug a tree into every leaf; `Term.subst` — plug a tree into one name.
-/

namespace INet

/-- Symbols, each with the number of its auxiliary ports. Every cell also has one principal
port. -/
structure Signature where
  /-- The symbols. -/
  Sym : Type
  /-- The number of auxiliary ports of a symbol. -/
  arity : Sym → ℕ

/-- A tree of cells with leaves named in `ν`. The root of `app α ts` is the principal port of an
`α` cell whose `i`-th auxiliary port is plugged into the root of `ts i`. -/
inductive Term (S : Signature) (ν : Type) : Type
  | var : ν → Term S ν
  | app : (α : S.Sym) → (Fin (S.arity α) → Term S ν) → Term S ν

namespace Term

variable {S : Signature} {ν μ : Type}

/-- The leaves of a tree, with multiplicity. -/
def vars : Term S ν → Multiset ν
  | var x => {x}
  | app _ ts => ∑ i, (ts i).vars

/-- Plug the tree `f x` into every leaf `x`. -/
def bind (f : ν → Term S μ) : Term S ν → Term S μ
  | var x => f x
  | app α ts => app α fun i => (ts i).bind f

@[simp] theorem vars_var (x : ν) : (var x : Term S ν).vars = {x} := rfl
@[simp] theorem vars_app (α : S.Sym) (ts : Fin (S.arity α) → Term S ν) :
    (app α ts).vars = ∑ i, (ts i).vars := rfl
@[simp] theorem bind_var (f : ν → Term S μ) (x : ν) : (var x).bind f = f x := rfl
@[simp] theorem bind_app (f : ν → Term S μ) (α : S.Sym) (ts : Fin (S.arity α) → Term S ν) :
    (app α ts).bind f = app α fun i => (ts i).bind f := rfl

theorem _root_.Multiset.sum_bind' {ι α β : Type} (s : Finset ι) (f : ι → Multiset α)
    (g : α → Multiset β) : (∑ i ∈ s, f i).bind g = ∑ i ∈ s, (f i).bind g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, Multiset.add_bind, ih]

theorem vars_bind (f : ν → Term S μ) (t : Term S ν) :
    (t.bind f).vars = t.vars.bind fun x => (f x).vars := by
  induction t with
  | var x => simp
  | app α ts ih => simp [Multiset.sum_bind', ih]

/-- The cells of a tree: the symbols occurring in it, with multiplicity. -/
def cells : Term S ν → Multiset S.Sym
  | var _ => 0
  | app α ts => α ::ₘ ∑ i, (ts i).cells

@[simp] theorem cells_var (x : ν) : (var x : Term S ν).cells = 0 := rfl
@[simp] theorem cells_app (α : S.Sym) (ts : Fin (S.arity α) → Term S ν) :
    (app α ts).cells = α ::ₘ ∑ i, (ts i).cells := rfl

theorem cells_bind (f : ν → Term S μ) (t : Term S ν) :
    (t.bind f).cells = t.cells + t.vars.bind fun x => (f x).cells := by
  induction t with
  | var x => simp
  | app α ts ih =>
    simp only [bind_app, cells_app, vars_app, Multiset.sum_bind', ih, Finset.sum_add_distrib,
      Multiset.cons_add]

variable [DecidableEq ν]

/-- Plug the tree `t` into the name `x`. -/
def subst (r : Term S ν) (x : ν) (t : Term S ν) : Term S ν :=
  r.bind fun y => if y = x then t else var y

theorem subst_of_notMem {x : ν} {t : Term S ν} {r : Term S ν} (h : x ∉ r.vars) :
    r.subst x t = r := by
  induction r with
  | var y =>
    have : y ≠ x := by simpa [eq_comm] using h
    simp [subst, this]
  | app α ts ih =>
    simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and, not_exists] at h
    simp only [subst, bind_app]
    congr 1
    funext i
    exact ih i (h i)

theorem count_bind_ite (m : Multiset ν) (x y : ν) (t : Term S ν) :
    (m.bind fun z => (if z = x then t else var z : Term S ν).vars).count y =
      m.count x * t.vars.count y + if y = x then 0 else m.count y := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons z m ih =>
    rw [Multiset.cons_bind, Multiset.count_add, ih]
    by_cases hz : z = x
    · subst hz
      by_cases hy : y = z
      · subst hy; simp; ring
      · simp [hy]; ring
    · by_cases hy : y = x
      · subst hy; simp [hz, Ne.symm hz]
      · simp only [hz, ite_false, hy, vars_var, Multiset.count_singleton,
          Multiset.count_cons_of_ne (Ne.symm hz), Multiset.count_cons]
        split_ifs <;> omega

/-- The leaves of `r.subst x t`: every `x` is replaced by the leaves of `t`. -/
theorem count_vars_subst (r : Term S ν) (x y : ν) (t : Term S ν) :
    (r.subst x t).vars.count y =
      r.vars.count x * t.vars.count y + if y = x then 0 else r.vars.count y := by
  rw [subst, vars_bind]
  exact count_bind_ite _ _ _ _

theorem bind_ite_cells (m : Multiset ν) (x : ν) (t : Term S ν) :
    (m.bind fun z => (if z = x then t else var z : Term S ν).cells) = m.count x • t.cells := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons z m ih =>
    rw [Multiset.cons_bind, ih]
    by_cases hz : z = x
    · subst hz; simp [add_nsmul, add_comm]
    · simp [hz, Multiset.count_cons_of_ne (Ne.symm hz)]

/-- Substitution adds one copy of the cells of `t` for each occurrence of `x`. -/
theorem cells_subst (r : Term S ν) (x : ν) (t : Term S ν) :
    (r.subst x t).cells = r.cells + r.vars.count x • t.cells := by
  rw [subst, cells_bind, bind_ite_cells]

end Term

end INet
