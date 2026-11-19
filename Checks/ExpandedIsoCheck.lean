import InteractionCombinators.Lafont.ExpandedIso
import Checks.DecompositionReview

/-!
# Checks for `Lafont/ExpandedIso.lean`

The non-vacuity check of `Rule.exists_perm_of_equiv`: two texts of the expanded `con`–`con` rule
(page 86, with the rule of Fig. 3), `a₀ = x₀, b₁ = x₀, a₁ = x₁, b₀ = x₁` and the same with `x₀`
and `x₁` exchanged. Both are linear and expanded, they are `Equiv` (both contract to
`a₀ = b₁, a₁ = b₀`), and they are different texts, so the permutation given by the theorem is not
the identity. `selfRule` of `DecompositionReview.lean` is expanded too.
-/

namespace INet.Comb.ExpandedIsoCheck

open Term Rule DecompositionReview

/-- The expanded `con`–`con` rule: `a₀ = x₀, b₁ = x₀, a₁ = x₁, b₀ = x₁`. -/
def conConExp : Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2) :=
  s(pl 0, pw 0) ::ₘ s(pr 1, pw 0) ::ₘ s(pl 1, pw 1) ::ₘ {s(pr 0, pw 1)}

/-- The same rule with the two internal wires exchanged. -/
def conConExp' : Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2) :=
  s(pl 0, pw 1) ::ₘ s(pr 1, pw 1) ::ₘ s(pl 1, pw 0) ::ₘ {s(pr 0, pw 0)}

/-- The contracted `con`–`con` rule, `a₀ = b₁, a₁ = b₀`, as a net with two unused names. -/
def conConContr : Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2) := s(pr 0, pl 1) ::ₘ {s(pr 1, pl 0)}

theorem conConExp_linear : (⟨2, conConExp⟩ : Rule sig 2 2).Linear :=
  ⟨by decide, by decide, by decide⟩

theorem conConExp'_linear : (⟨2, conConExp'⟩ : Rule sig 2 2).Linear :=
  ⟨by decide, by decide, by decide⟩

theorem conConExp_expanded : (⟨2, conConExp⟩ : Rule sig 2 2).Expanded := by
  intro e he
  have key : ∀ e ∈ conConExp, e ∈ [s(pl 0, pw 0), s(pr 1, pw 0), s(pl 1, pw 1), s(pr 0, pw 1)] := by
    decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, rfl, fun w h => (by cases h), fun x hx => ⟨_, Multiset.mem_singleton.1 hx⟩⟩

theorem conConExp'_expanded : (⟨2, conConExp'⟩ : Rule sig 2 2).Expanded := by
  intro e he
  have key : ∀ e ∈ conConExp',
      e ∈ [s(pl 0, pw 1), s(pr 1, pw 1), s(pl 1, pw 0), s(pr 0, pw 0)] := by
    decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, rfl, fun w h => (by cases h), fun x hx => ⟨_, Multiset.mem_singleton.1 hx⟩⟩

/-- The expanded rule contracts to `a₀ = b₁, a₁ = b₀` by two wire substitutions. -/
theorem conConExp_equiv_contr : Equiv conConExp conConContr := by
  have h₁ := equiv_wire_of_eq (ν := Fin 2 ⊕ Fin 2 ⊕ Fin 2) (N := conConExp)
    (M := s(pr 1, pl 0) ::ₘ s(pl 1, pw 1) ::ₘ {s(pr 0, pw 1)})
    (.inr (.inr 0)) (pl 0) (pr 1) (pw 0) (s(pl 1, pw 1) ::ₘ {s(pr 0, pw 1)})
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have h₂ := equiv_wire_of_eq (ν := Fin 2 ⊕ Fin 2 ⊕ Fin 2)
    (N := s(pr 1, pl 0) ::ₘ s(pl 1, pw 1) ::ₘ {s(pr 0, pw 1)}) (M := conConContr)
    (.inr (.inr 1)) (pl 1) (pr 0) (pw 1) {s(pr 1, pl 0)}
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  exact h₁.trans h₂

/-- The other text contracts to the same net. -/
theorem conConExp'_equiv_contr : Equiv conConExp' conConContr := by
  have h₁ := equiv_wire_of_eq (ν := Fin 2 ⊕ Fin 2 ⊕ Fin 2) (N := conConExp')
    (M := s(pr 1, pl 0) ::ₘ s(pl 1, pw 0) ::ₘ {s(pr 0, pw 0)})
    (.inr (.inr 1)) (pl 0) (pr 1) (pw 1) (s(pl 1, pw 0) ::ₘ {s(pr 0, pw 0)})
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have h₂ := equiv_wire_of_eq (ν := Fin 2 ⊕ Fin 2 ⊕ Fin 2)
    (N := s(pr 1, pl 0) ::ₘ s(pl 1, pw 0) ::ₘ {s(pr 0, pw 0)}) (M := conConContr)
    (.inr (.inr 0)) (pl 1) (pr 0) (pw 0) {s(pr 1, pl 0)}
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  exact h₁.trans h₂

/-- The two texts are `Equiv`. -/
theorem conConExp_equiv : Equiv conConExp conConExp' :=
  conConExp_equiv_contr.trans conConExp'_equiv_contr.symm

/-- The two texts are different nets. -/
theorem conConExp_ne : conConExp ≠ conConExp' := by decide

/-- `Rule.exists_perm_of_equiv` applies: the second text is the first with its internal wires
permuted. -/
theorem conConExp_perm : ∃ π : Equiv.Perm (Fin 2),
    conConExp' = conConExp.bind fun x => var (Sum.map id (Sum.map id π) x) :=
  Rule.exists_perm_of_equiv conConExp_linear conConExp'_linear conConExp_expanded
    conConExp'_expanded conConExp_equiv

/-- The permutation is not the identity: it exchanges the two wires. -/
theorem conConExp_perm_ne_one : ∀ π : Equiv.Perm (Fin 2),
    conConExp' = conConExp.bind (fun x => var (Sum.map id (Sum.map id π) x)) → π ≠ 1 := by
  rintro π h rfl
  apply conConExp_ne
  rw [h]
  simp only [Equiv.Perm.coe_one, Sum.map_id_id]
  exact (Net.bind_var_self _).symm

/-- `selfRule` (`DecompositionReview.lean`) is in expanded form. -/
theorem selfRule_expanded : selfRule.Expanded := by
  show ∀ e ∈ (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4) from selfRule.net),
    ∃ (p : Fin 3 ⊕ Fin 3 ⊕ Fin 4) (t : Term sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4)),
      e = s(Term.var p, t) ∧ (∀ w : Fin 4, p ≠ .inr (.inr w)) ∧
        ∀ x ∈ t.vars, ∃ w : Fin 4, x = .inr (.inr w)
  intro e he
  have key : ∀ e ∈ (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4) from selfRule.net),
      e ∈ [s(pl 0, mkCon (pw 0) (pw 1)), s(pl 1, mkCon (pw 2) mkEra), s(pl 2, pw 3),
        s(pr 0, mkCon (pw 2) (pw 1)), s(pr 1, mkCon (pw 0) mkEra), s(pr 2, pw 3)] := by
    decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, rfl, fun w h => (by cases h), by decide⟩

end INet.Comb.ExpandedIsoCheck
