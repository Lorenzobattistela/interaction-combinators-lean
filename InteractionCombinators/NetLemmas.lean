import InteractionCombinators.Net

/-!
# Small facts about the names of a net

Shared by many files, which used to carry their own copies.

* `Net.vars_bind_var` — the names of a renamed net are the renamed names.
* `Net.linear_of_forall_mem` — linearity checked on the names that occur only. This is the form in
  which `decide` proves linearity of a concrete net over `ℕ`: `Net.Linear` quantifies over every
  natural number, and `unfold Net.Linear; decide` cannot check that, while the bounded quantifier
  `∀ y ∈ N.vars` is decidable.
* `Equiv.eq_of_not_linear_any` — a net that is not linear is equivalent only to itself.
-/

namespace INet

variable {S : Signature}

/-- The names of a net renamed by `f` (every name `x` replaced by `f x`) are the names of the net,
renamed by `f`. Names are an artefact of the text (Lafont 1997, Section 1.1, pages 70 to 72). -/
theorem Net.vars_bind_var {ν μ : Type} (f : ν → μ) (N : Net S ν) :
    (N.bind fun x => (Term.var (f x) : Term S μ)).vars = N.vars.map f := by
  rw [Net.vars_bind]
  simp [Multiset.bind_singleton]

/-- A net is linear (every name occurs at most twice, Lafont 1997, Section 1.1, page 70) as soon
as every name that occurs in it occurs at most twice: a name that does not occur has count `0`.
The hypothesis quantifies over a finite multiset, so `decide` checks it on a concrete net. -/
theorem Net.linear_of_forall_mem {ν : Type} [DecidableEq ν] {N : Net S ν}
    (h : ∀ y ∈ N.vars, N.vars.count y ≤ 2) : N.Linear := fun y => by
  by_cases hy : y ∈ N.vars
  · exact h y hy
  · rw [Multiset.count_eq_zero.2 hy]; omega

/-- A net that is not linear is equivalent only to itself: no wire substitution applies to it
(Lafont 1997, Section 1.2, page 71: wire substitution is done in a net). -/
theorem Equiv.eq_of_not_linear_any {ν : Type} [DecidableEq ν] {N M : Net S ν} (h : Equiv N M)
    (hN : ¬ N.Linear) : N = M := by
  induction h with
  | rel _ _ h => exact absurd h.linear_left hN
  | refl _ => rfl
  | symm K L h ih => exact (ih fun hK => hN (Equiv.linear h hK)).symm
  | trans K M L h₁ _ ih₁ ih₂ =>
    rw [ih₁ hN]
    exact ih₂ fun hM => hN ((Equiv.symm h₁).linear hM)

end INet
