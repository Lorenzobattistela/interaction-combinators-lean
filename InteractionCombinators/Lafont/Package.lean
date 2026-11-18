import InteractionCombinators.Lafont.Basic

/-!
# Lafont, "Interaction Combinators" (1997): packages and erasing them

* `Term.IsPackage` — a package (page 80): a reduced net with one free port, which by
  Proposition 2 is a tree `τ` whose leaves are joined in pairs by a wiring `ω`. In the text
  presentation, a tree in which every name occurs exactly twice; its root is the free port.
* `erase_wiring` — Lemma 2 (ii), page 85: a wiring with an eraser on each of its free ports
  reduces to the empty net.
* `erase_package` — the corollary on page 84: a package plugged into an eraser reduces to the
  empty net.
-/

namespace INet

/-- A package (Lafont, page 80): a tree whose leaves are joined in pairs by internal wires. In the
text presentation every name of the tree occurs exactly twice, and the root is the only free
port. -/
def Term.IsPackage {S : Signature} (π : Term S ℕ) : Prop := ∀ x ∈ π.vars, π.vars.count x = 2

namespace Term

variable {S : Signature}

/-- A tree with no leaf is a package (page 80, the case of an empty wiring). -/
theorem isPackage_of_vars_eq_zero {π : Term S ℕ} (h : π.vars = 0) : π.IsPackage := by
  intro x hx
  simp [h] at hx

/-- The leaves of a package are its wires, each counted twice (page 80: the leaves of `τ` are
paired by the wiring `ω`). -/
theorem IsPackage.vars_eq {π : Term S ℕ} (hπ : π.IsPackage) :
    π.vars = π.vars.dedup + π.vars.dedup := by
  ext x
  rw [Multiset.count_add]
  by_cases hx : x ∈ π.vars
  · rw [hπ x hx, Multiset.count_eq_one_of_mem (Multiset.nodup_dedup _)
      (Multiset.mem_dedup.2 hx)]
  · rw [Multiset.count_eq_zero_of_notMem hx,
      Multiset.count_eq_zero_of_notMem (fun h => hx (Multiset.mem_dedup.1 h))]

end Term

namespace Comb

open Term

/-- An eraser is a package with no wire (page 80). -/
theorem isPackage_mkEra : (mkEra : Term sig ℕ).IsPackage :=
  isPackage_of_vars_eq_zero vars_mkEra

/-- Two packages with no common name, plugged into the auxiliary ports of a `con`, form a package
(page 80). -/
theorem IsPackage.mkCon {a b : Term sig ℕ} (ha : a.IsPackage) (hb : b.IsPackage)
    (hab : ∀ x ∈ a.vars, x ∉ b.vars) : (mkCon a b).IsPackage := by
  intro x hx
  rw [vars_mkCon, Multiset.mem_add] at hx
  rw [vars_mkCon, Multiset.count_add]
  rcases hx with hx | hx
  · rw [ha x hx, Multiset.count_eq_zero_of_notMem (hab x hx)]
  · have : x ∉ a.vars := fun h => hab x h hx
    rw [hb x hx, Multiset.count_eq_zero_of_notMem this]

/-- Two packages with no common name, plugged into the auxiliary ports of a `dup`, form a package
(page 80). -/
theorem IsPackage.mkDup {a b : Term sig ℕ} (ha : a.IsPackage) (hb : b.IsPackage)
    (hab : ∀ x ∈ a.vars, x ∉ b.vars) : (mkDup a b).IsPackage := by
  intro x hx
  rw [vars_mkDup, Multiset.mem_add] at hx
  rw [vars_mkDup, Multiset.count_add]
  rcases hx with hx | hx
  · rw [ha x hx, Multiset.count_eq_zero_of_notMem (hab x hx)]
  · have : x ∉ a.vars := fun h => hab x h hx
    rw [hb x hx, Multiset.count_eq_zero_of_notMem this]

/-- A `con` whose two auxiliary ports are joined by a wire is a package (page 80). -/
theorem isPackage_mkCon_var (x : ℕ) : (mkCon (var x) (var x) : Term sig ℕ).IsPackage := by
  intro y hy
  simp only [vars_mkCon, vars_var, Multiset.mem_add, Multiset.mem_singleton, or_self] at hy
  subst hy
  simp

/-- A sub-net of a linear net is linear. -/
theorem linear_of_add {N M : CNet} (h : (N + M).Linear) : M.Linear := by
  intro x
  have := h x
  rw [Net.vars_add, Multiset.count_add] at this
  omega

/-- Two erasers joined by the wire `x` erase each other: a wire substitution makes them an active
pair, then they annihilate (page 85, one wire of Lemma 2 (ii)). -/
theorem stepE_era_wire (x : ℕ) (Δ : CNet)
    (hlin : Net.Linear (s(mkEra, var x) ::ₘ s(mkEra, var x) ::ₘ Δ)) :
    StepE system (s(mkEra, var x) ::ₘ s(mkEra, var x) ::ₘ Δ) Δ := by
  have e : (s(mkEra, var x) ::ₘ s(mkEra, var x) ::ₘ Δ : CNet) =
      s(var x, mkEra) ::ₘ s(mkEra, var x) ::ₘ Δ := by rw [Sym2.eq_swap]
  have hw := Wire.mk x mkEra mkEra (var x) Δ (hlin.cast e) (by simp)
  rw [subst_var_self, subst_of_notMem (by simp)] at hw
  exact ⟨_, (hw.cast e.symm rfl).equiv, step_era_era Δ⟩

/-- Lafont's Lemma 2 (ii), page 85: a wiring `D` with an eraser on every free port reduces to the
empty net. Each wire `x` of `D` has an eraser at both ends; the two erasers are joined by a wire,
so they interact after a wire substitution, hence `StepsE`. -/
theorem erase_wiring (D : Multiset ℕ) (Δ : CNet)
    (hlin : Net.Linear ((D + D).map (fun x => s(mkEra, Term.var x)) + Δ)) :
    StepsE system ((D + D).map (fun x => s(mkEra, Term.var x)) + Δ) Δ := by
  induction D using Multiset.induction_on with
  | empty => simpa using Relation.ReflTransGen.refl
  | cons x D ih =>
    have e : ((x ::ₘ D + x ::ₘ D).map (fun x => s(mkEra, Term.var x)) + Δ : CNet) =
        s(mkEra, var x) ::ₘ s(mkEra, var x) ::ₘ
          ((D + D).map (fun x => s(mkEra, Term.var x)) + Δ) := by
      simp only [Multiset.add_cons, Multiset.cons_add, Multiset.map_cons]
    rw [e] at hlin ⊢
    have hrest : Net.Linear ((D + D).map (fun x => s(mkEra, Term.var x)) + Δ) :=
      linear_of_add (N := {s(mkEra, var x), s(mkEra, var x)})
        (hlin.cast (by simp only [Multiset.insert_eq_cons, Multiset.cons_add,
          Multiset.singleton_add]))
    exact Relation.ReflTransGen.head (stepE_era_wire x _ hlin) (ih hrest)

/-- The corollary of Lemma 2 on page 84: a package `π` plugged into an eraser reduces to the empty
net. Lemma 2 (i) leaves an eraser on each leaf of `π`; the leaves are joined in pairs, and
Lemma 2 (ii) erases the wiring. -/
theorem erase_package (π : Term sig ℕ) (hπ : π.IsPackage) (Δ : CNet)
    (hlin : Net.Linear (s(mkEra, π) ::ₘ Δ)) : StepsE system (s(mkEra, π) ::ₘ Δ) Δ := by
  have h1 := erase_tree π Δ
  rw [hπ.vars_eq] at h1
  exact h1.stepsE.trans
    (erase_wiring _ Δ (h1.linear system_wellFormed.linear hlin))

/-- The hypotheses of `erase_package` hold: a `con` whose auxiliary ports are joined by a wire,
plugged into an eraser, reduces to the empty net. -/
example : StepsE system ({s(mkEra, mkCon (var 0) (var 0))} : CNet) 0 := by
  have h := erase_package (mkCon (var 0) (var 0)) (isPackage_mkCon_var 0) 0 (by
    intro y
    simp only [Net.vars_cons, Net.vars_zero, eqVars_mk, vars_mkEra, vars_mkCon, vars_var,
      zero_add, add_zero, Multiset.count_add, Multiset.count_singleton]
    split_ifs <;> omega)
  simpa using h

end Comb

end INet
