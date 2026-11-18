import InteractionCombinators.Net

/-!
# Interaction systems and reduction

* `Rule S a b` — the right-hand side of an interaction between a cell with `a` auxiliary ports and
  a cell with `b`: a net whose names are the auxiliary ports of the two cells and some internal
  wires.
* `System S` — at most one rule for each pair of symbols.
* `Step`, `Steps` — reduction. Only interactions are steps; wire substitution is not.
-/

namespace INet

variable {S : Signature}

/-- The right-hand side of an interaction rule. Its names are the `a` auxiliary ports of the first
cell, the `b` auxiliary ports of the second, and `internal` new wires. -/
structure Rule (S : Signature) (a b : ℕ) where
  /-- The number of wires created by the rule. -/
  internal : ℕ
  /-- The net that replaces the two cells. -/
  net : Net S (Fin a ⊕ Fin b ⊕ Fin internal)

/-- The right-hand side of a rule, with trees plugged into the auxiliary ports and the internal
wires named by `f`. -/
def Rule.inst {a b : ℕ} (r : Rule S a b) (as : Fin a → Term S ℕ) (bs : Fin b → Term S ℕ)
    (f : Fin r.internal → ℕ) : Net S ℕ :=
  r.net.bind (Sum.elim as (Sum.elim bs fun i => Term.var (f i)))

namespace Rule

variable {a b : ℕ}

/-- In the right-hand side of a rule, every auxiliary port of the two cells occurs exactly once and
every internal wire exactly twice. -/
structure Linear (r : Rule S a b) : Prop where
  left : ∀ i, r.net.vars.count (.inl i) = 1
  right : ∀ j, r.net.vars.count (.inr (.inl j)) = 1
  internal : ∀ w, r.net.vars.count (.inr (.inr w)) = 2

/-- The right-hand side is a reduced net, written as trees rooted at the auxiliary ports: every
equation has an auxiliary port on one side. Together with linearity this excludes pairs of cells
plugged by their principal ports, vicious circles and cyclic wires. -/
def Reduced (r : Rule S a b) : Prop :=
  ∀ e ∈ r.net, ∃ p t, e = s(Term.var p, t) ∧ ∀ w, p ≠ .inr (.inr w)

/-- The same rule read from the other cell: the two groups of auxiliary ports are exchanged. -/
def swap (r : Rule S a b) : Rule S b a where
  internal := r.internal
  net := r.net.bind fun p =>
    Term.var (Sum.elim (fun i => .inr (.inl i)) (Sum.elim .inl fun w => .inr (.inr w)) p)

theorem _root_.Multiset.count_bind_fintype {P ν : Type} [Fintype P] [DecidableEq P]
    [DecidableEq ν] (m : Multiset P) (g : P → Multiset ν) (y : ν) :
    (m.bind g).count y = ∑ p, m.count p * (g p).count y := by
  rw [Multiset.count_bind, Finset.sum_multiset_map_count]
  simp only [smul_eq_mul]
  refine Finset.sum_subset (Finset.subset_univ _) fun p _ hp => ?_
  rw [Multiset.count_eq_zero_of_notMem (by simpa using hp), zero_mul]

/-- The names of an instance of a linear rule: those of the trees plugged into the ports, and both
ends of each internal wire. -/
theorem count_vars_inst (r : Rule S a b) (hr : r.Linear) (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ) (f : Fin r.internal → ℕ) (y : ℕ) :
    (r.inst as bs f).vars.count y =
      ∑ i, (as i).vars.count y + ∑ j, (bs j).vars.count y +
        2 * ∑ w, if y = f w then 1 else 0 := by
  rw [inst, Net.vars_bind, Multiset.count_bind_fintype, Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  simp only [hr.left, hr.right, hr.internal, one_mul, Sum.elim_inl, Sum.elim_inr, Term.vars_var,
    Multiset.count_singleton, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  ring

end Rule

/-- An interaction system: at most one rule for each pair of symbols. An equation is unordered, so
a rule given for `α`, `β` also applies to `β`, `α`. -/
structure System (S : Signature) where
  /-- The rule for a pair of symbols, if any. -/
  rule : (α β : S.Sym) → Option (Rule S (S.arity α) (S.arity β))

/-- One interaction: two cells plugged by their principal ports are replaced by the right-hand
side of their rule. The wires the rule creates get names not used in the net. -/
inductive Step (I : System S) : Net S ℕ → Net S ℕ → Prop
  | mk (α β : S.Sym) (r : Rule S (S.arity α) (S.arity β)) (hr : I.rule α β = some r)
      (as : Fin (S.arity α) → Term S ℕ) (bs : Fin (S.arity β) → Term S ℕ) (Δ : Net S ℕ)
      (f : Fin r.internal → ℕ) (hf : Function.Injective f)
      (hfresh : ∀ i, f i ∉ Net.vars (s(Term.app α as, Term.app β bs) ::ₘ Δ)) :
      Step I (s(Term.app α as, Term.app β bs) ::ₘ Δ) (r.inst as bs f + Δ)

/-- An interaction system in the sense of Lafont: rules are linear and reduced, and can be applied
without ambiguity. -/
structure System.WellFormed (I : System S) : Prop where
  /-- Every rule is linear. -/
  linear : ∀ α β r, I.rule α β = some r → r.Linear
  /-- Every right-hand side is a reduced net. -/
  reduced : ∀ α β r, I.rule α β = some r → r.Reduced
  /-- A rule given for `α`, `β` excludes another rule for `β`, `α`. -/
  unique : ∀ α β, α ≠ β → (I.rule α β).isSome → I.rule β α = none
  /-- A rule of a symbol with itself is symmetric. -/
  symm : ∀ α r, I.rule α α = some r → Equiv r.swap.net r.net

/-- An interaction of a linear rule keeps the net linear. -/
theorem Step.linear {I : System S} (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    {N N' : Net S ℕ} (h : Step I N N') (hN : N.Linear) : N'.Linear := by
  obtain ⟨α, β, r, hr, as, bs, Δ, f, hf, hfresh⟩ := h
  intro y
  have hy := hN y
  simp only [Net.vars_cons, Net.vars_add, eqVars_mk, Term.vars_app, Multiset.count_add,
    Multiset.count_sum'] at hy ⊢
  rw [Rule.count_vars_inst r (hI _ _ _ hr)]
  by_cases hex : ∃ w, y = f w
  · obtain ⟨w0, rfl⟩ := hex
    have hsum : ∑ w, (if f w0 = f w then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single w0]
      · simp
      · intro w _ hw
        exact if_neg fun h => hw (hf h).symm
      · simp
    have h0 := Multiset.count_eq_zero_of_notMem (hfresh w0)
    simp only [Net.vars_cons, eqVars_mk, Term.vars_app, Multiset.count_add,
      Multiset.count_sum'] at h0
    omega
  · have hsum : ∑ w, (if y = f w then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun w _ => if_neg fun h => hex ⟨w, h⟩
    omega

/-- Reduction in any number of interactions. -/
abbrev Steps (I : System S) : Net S ℕ → Net S ℕ → Prop := Relation.ReflTransGen (Step I)

namespace Steps

variable {I : System S} {N N' M M' : Net S ℕ}

theorem single (h : Step I N N') : Steps I N N' := Relation.ReflTransGen.single h

theorem cast (h : Steps I N N') (hN : N = M) (hN' : N' = M') : Steps I M M' := hN ▸ hN' ▸ h

theorem linear (hI : ∀ α β r, I.rule α β = some r → r.Linear) (h : Steps I N N')
    (hN : N.Linear) : N'.Linear := by
  induction h with
  | refl => exact hN
  | tail _ hstep ih => exact hstep.linear hI ih

end Steps

/-- One interaction up to wires: the net is first rewritten into an equivalent one, then two
cells interact. This lets two cells interact when their principal ports are joined by a named
wire, as in `x = α(…)`, `x = β(…)`, which is an active pair of the graph. -/
def StepE (I : System S) (N M : Net S ℕ) : Prop := ∃ N', Equiv N N' ∧ Step I N' M

/-- Reduction up to wires, in any number of interactions. -/
abbrev StepsE (I : System S) : Net S ℕ → Net S ℕ → Prop := Relation.ReflTransGen (StepE I)

theorem Step.stepE {I : System S} {N M : Net S ℕ} (h : Step I N M) : StepE I N M :=
  ⟨N, Equiv.refl N, h⟩

theorem Steps.stepsE {I : System S} {N M : Net S ℕ} (h : Steps I N M) : StepsE I N M := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail hstep.stepE

theorem StepE.linear {I : System S} (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    {N M : Net S ℕ} (h : StepE I N M) (hN : N.Linear) : M.Linear := by
  obtain ⟨N', he, hs⟩ := h
  exact hs.linear hI (he.linear hN)

theorem StepsE.linear {I : System S} (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    {N M : Net S ℕ} (h : StepsE I N M) (hN : N.Linear) : M.Linear := by
  induction h with
  | refl => exact hN
  | tail _ hstep ih => exact hstep.linear hI ih

/-- Reorder a sum of multisets. -/
macro "ms" : tactic =>
  `(tactic| first | rfl | (simp only [← Multiset.singleton_add, add_zero, zero_add]; abel) | abel)

end INet
