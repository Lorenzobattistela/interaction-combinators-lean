import InteractionCombinators.Term

/-!
# Nets, linearity and equivalence up to wires

* `Net S ν` — a multiset of unordered equations between trees. An equation `t = u` plugs the root
  of `t` into the root of `u`.
* `Net.Linear` — every name occurs at most twice. A name occurring twice is an internal wire; a
  name occurring once is a free port.
* `Wire`, `Equiv` — two nets are the same graph when they differ by wire substitution: an equation
  `x = t` whose `x` has its other end elsewhere is the same as plugging `t` there. Interactions are
  not part of this equivalence. Renaming an internal wire is a special case.
-/

namespace INet

variable {S : Signature} {ν μ : Type}

/-- A net: a multiset of unordered equations between trees. -/
abbrev Net (S : Signature) (ν : Type) := Multiset (Sym2 (Term S ν))

/-- The names of an equation, with multiplicity. -/
def eqVars : Sym2 (Term S ν) → Multiset ν :=
  Sym2.lift ⟨fun a b => a.vars + b.vars, fun _ _ => add_comm _ _⟩

@[simp] theorem eqVars_mk (a b : Term S ν) : eqVars s(a, b) = a.vars + b.vars := rfl

/-- The cells of an equation, with multiplicity. -/
def eqCells : Sym2 (Term S ν) → Multiset S.Sym :=
  Sym2.lift ⟨fun a b => a.cells + b.cells, fun _ _ => add_comm _ _⟩

@[simp] theorem eqCells_mk (a b : Term S ν) : eqCells s(a, b) = a.cells + b.cells := rfl

namespace Net

/-- The cells of a net: the symbols occurring in it, with multiplicity. -/
def cells (N : Net S ν) : Multiset S.Sym := N.bind eqCells

@[simp] theorem cells_cons (e : Sym2 (Term S ν)) (N : Net S ν) :
    cells (e ::ₘ N) = eqCells e + N.cells := by simp [cells]

/-- The names of a net, with multiplicity. -/
def vars (N : Net S ν) : Multiset ν := N.bind eqVars

@[simp] theorem vars_zero : (0 : Net S ν).vars = 0 := by simp [vars]
@[simp] theorem vars_cons (e : Sym2 (Term S ν)) (N : Net S ν) :
    vars (e ::ₘ N) = eqVars e + N.vars := by simp [vars]
@[simp] theorem vars_singleton (e : Sym2 (Term S ν)) : vars ({e} : Net S ν) = eqVars e := by
  simp [vars]
@[simp] theorem vars_add (N M : Net S ν) : (N + M).vars = N.vars + M.vars := by simp [vars]

/-- Plug a tree into every name of the net. -/
def bind (f : ν → Term S μ) (N : Net S ν) : Net S μ := N.map (Sym2.map (Term.bind f))

theorem vars_bind (f : ν → Term S μ) (N : Net S ν) :
    (N.bind f).vars = N.vars.bind fun x => (f x).vars := by
  unfold bind vars
  rw [Multiset.bind_map, Multiset.bind_assoc]
  congr 1
  funext e
  induction e using Sym2.ind with
  | _ a b => simp [Term.vars_bind, Multiset.add_bind]

/-- Every name occurs at most twice: once at each end of a wire, or once for a free port. -/
def Linear [DecidableEq ν] (N : Net S ν) : Prop := ∀ x, N.vars.count x ≤ 2

/-- Every name of the net is below `k`: the names from `k` on are unused. -/
def Below (k : ℕ) (N : Net S ℕ) : Prop := ∀ x ∈ N.vars, x < k

theorem Below.notMem {k x : ℕ} {N : Net S ℕ} (h : N.Below k) (hx : k ≤ x) : x ∉ N.vars :=
  fun hm => absurd (h x hm) (by omega)

theorem Below.mono {k m : ℕ} {N : Net S ℕ} (h : N.Below k) (hkm : k ≤ m) : N.Below m :=
  fun x hx => (h x hx).trans_le hkm

end Net

/-- Every name of the tree is below `k`. -/
def Term.Below (k : ℕ) (t : Term S ℕ) : Prop := ∀ x ∈ t.vars, x < k

@[simp] theorem Term.below_var {k x : ℕ} : (Term.var x : Term S ℕ).Below k ↔ x < k := by
  simp [Term.Below]

theorem Term.Below.mono {k m : ℕ} {t : Term S ℕ} (h : t.Below k) (hkm : k ≤ m) : t.Below m :=
  fun x hx => (h x hx).trans_le hkm

namespace Net

@[simp] theorem below_zero {k : ℕ} : (0 : Net S ℕ).Below k := by simp [Below]
@[simp] theorem below_cons {k : ℕ} {a b : Term S ℕ} {N : Net S ℕ} :
    Below k (s(a, b) ::ₘ N) ↔ a.Below k ∧ b.Below k ∧ N.Below k := by
  simp [Below, Term.Below, or_imp, forall_and, and_assoc]
@[simp] theorem below_singleton {k : ℕ} {a b : Term S ℕ} :
    Below k ({s(a, b)} : Net S ℕ) ↔ a.Below k ∧ b.Below k := by
  simp [Below, Term.Below, or_imp, forall_and]
@[simp] theorem below_add {k : ℕ} {N M : Net S ℕ} :
    Below k (N + M) ↔ N.Below k ∧ M.Below k := by
  simp [Below, or_imp, forall_and]

theorem Linear.cast [DecidableEq ν] {N M : Net S ν} (h : N.Linear) (e : N = M) : M.Linear :=
  e ▸ h

theorem Below.cast {k : ℕ} {N M : Net S ℕ} (h : N.Below k) (e : N = M) : M.Below k := e ▸ h

/-- Adding both ends of some new wires to a linear net keeps it linear. -/
theorem Linear.add_fresh [DecidableEq ν] {N M : Net S ν} (hN : N.Linear) (F : Multiset ν)
    (hF : F.Nodup) (hfresh : ∀ x ∈ F, x ∉ N.vars) (hv : M.vars = N.vars + (F + F)) :
    M.Linear := by
  intro y
  rw [hv, Multiset.count_add, Multiset.count_add]
  by_cases hy : y ∈ F
  · have h0 : N.vars.count y = 0 := Multiset.count_eq_zero_of_notMem (hfresh y hy)
    have h1 := Multiset.nodup_iff_count_le_one.1 hF y
    omega
  · have := hN y
    simp only [Multiset.count_eq_zero_of_notMem hy, add_zero]
    exact this

end Net

variable [DecidableEq ν]

open Term in
/-- One wire substitution. The wire `x` has one end on the root of `t` and its other end inside
the equation `a = b`; plugging `t` there gives the same graph. Linearity of the net guarantees
that `x` occurs nowhere else. -/
inductive Wire : Net S ν → Net S ν → Prop
  | mk (x : ν) (t a b : Term S ν) (Δ : Net S ν)
      (hlin : Net.Linear (s(var x, t) ::ₘ s(a, b) ::ₘ Δ)) (hx : x ∈ a.vars + b.vars) :
      Wire (s(var x, t) ::ₘ s(a, b) ::ₘ Δ) (s(a.subst x t, b.subst x t) ::ₘ Δ)

/-- Nets that are the same graph, spelled differently. -/
def Equiv : Net S ν → Net S ν → Prop := Relation.EqvGen Wire

namespace Wire

variable {N M : Net S ν}

theorem linear_left (h : Wire N M) : N.Linear := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  exact hlin

/-- A wire substitution removes both ends of the wire and changes no other name. -/
theorem count_vars (h : Wire N M) (y : ν) : M.vars.count y ≤ N.vars.count y := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hxl := hlin x
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hxl
  have hx1 : 1 ≤ (a.vars + b.vars).count x := Multiset.one_le_count_iff_mem.2 hx
  rw [Multiset.count_add] at hx1
  have hone : a.vars.count x + b.vars.count x = 1 := by omega
  have key : a.vars.count x * t.vars.count y + b.vars.count x * t.vars.count y
      = t.vars.count y := by rw [← add_mul, hone, one_mul]
  simp only [Net.vars_cons, eqVars_mk, Multiset.count_add, Term.count_vars_subst, Term.vars_var,
    Multiset.count_singleton]
  split_ifs <;> omega

/-- A wire substitution does not change which names are free ports. -/
theorem free_iff (h : Wire N M) (y : ν) : N.vars.count y = 1 ↔ M.vars.count y = 1 := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hxl := hlin x
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hxl
  have hx1 : 1 ≤ (a.vars + b.vars).count x := Multiset.one_le_count_iff_mem.2 hx
  rw [Multiset.count_add] at hx1
  have hone : a.vars.count x + b.vars.count x = 1 := by omega
  have key : a.vars.count x * t.vars.count y + b.vars.count x * t.vars.count y
      = t.vars.count y := by rw [← add_mul, hone, one_mul]
  simp only [Net.vars_cons, eqVars_mk, Multiset.count_add, Term.count_vars_subst, Term.vars_var,
    Multiset.count_singleton]
  by_cases hy : y = x
  · subst hy
    simp only [if_true]
    omega
  · simp only [hy, if_false]
    omega

/-- A wire substitution creates and destroys no cell. -/
theorem cells_eq (h : Wire N M) : M.cells = N.cells := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hxl := hlin x
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hxl
  have hx1 : 1 ≤ (a.vars + b.vars).count x := Multiset.one_le_count_iff_mem.2 hx
  rw [Multiset.count_add] at hx1
  have hone : a.vars.count x + b.vars.count x = 1 := by omega
  have key : a.vars.count x • t.cells + b.vars.count x • t.cells = t.cells := by
    rw [← add_nsmul, hone, one_nsmul]
  simp only [Net.cells_cons, eqCells_mk, Term.cells_subst, Term.cells_var, zero_add]
  calc a.cells + a.vars.count x • t.cells + (b.cells + b.vars.count x • t.cells) + Δ.cells
      = (a.vars.count x • t.cells + b.vars.count x • t.cells) + (a.cells + b.cells) + Δ.cells := by
        abel
    _ = t.cells + (a.cells + b.cells + Δ.cells) := by rw [key]; abel

theorem linear_right (h : Wire N M) : M.Linear :=
  fun y => (h.count_vars y).trans (h.linear_left y)

theorem mem_vars (h : Wire N M) {y : ν} (hy : y ∈ M.vars) : y ∈ N.vars :=
  Multiset.one_le_count_iff_mem.1 ((Multiset.one_le_count_iff_mem.2 hy).trans (h.count_vars y))

theorem equiv (h : Wire N M) : Equiv N M := Relation.EqvGen.rel _ _ h

theorem cast {N' M' : Net S ν} (h : Wire N M) (e : N = N') (e' : M = M') : Wire N' M' :=
  e ▸ e' ▸ h

end Wire

theorem Wire.below {k : ℕ} {N M : Net S ℕ} (h : Wire N M) (hN : N.Below k) : M.Below k :=
  fun x hx => hN x (h.mem_vars hx)

namespace Equiv

variable {N M K : Net S ν}

theorem refl (N : Net S ν) : Equiv N N := Relation.EqvGen.refl _
theorem of_eq (h : N = M) : Equiv N M := h ▸ refl N
theorem symm (h : Equiv N M) : Equiv M N := Relation.EqvGen.symm _ _ h
theorem trans (h : Equiv N M) (h' : Equiv M K) : Equiv N K := Relation.EqvGen.trans _ _ _ h h'

/-- Equivalent nets are linear together. -/
theorem linear_iff (h : Equiv N M) : N.Linear ↔ M.Linear := by
  induction h with
  | rel _ _ h => exact ⟨fun _ => h.linear_right, fun _ => h.linear_left⟩
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem linear (h : Equiv N M) (hN : N.Linear) : M.Linear := h.linear_iff.1 hN

/-- Equivalent nets have the same free ports. -/
theorem free_iff (h : Equiv N M) (y : ν) : N.vars.count y = 1 ↔ M.vars.count y = 1 := by
  induction h with
  | rel _ _ h => exact h.free_iff y
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- Equivalent nets have the same cells: the equivalence performs no interaction. -/
theorem cells_eq (h : Equiv N M) : N.cells = M.cells := by
  induction h with
  | rel _ _ h => exact h.cells_eq.symm
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end Equiv

end INet
