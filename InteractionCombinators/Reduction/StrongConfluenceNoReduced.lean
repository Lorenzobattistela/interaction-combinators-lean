import InteractionCombinators.Reduction.StrongConfluenceE

/-!
# Proposition 1 without the condition that rules are reduced (Lafont 1997, page 73)

On page 73 Lafont states Proposition 1 (strong confluence) for an interaction system whose rules
are linear, given at most once for each pair of symbols, and symmetric for a symbol with itself;
only afterwards does he add: "Later we shall add the technical condition that the ν_{i,j} are
reduced nets." `Step.strong_confluence` and `StepE.strong_confluence` assume `System.WellFormed`,
which includes that condition (`System.WellFormed.reduced`) although their proofs do not use it.

This file proves both statements from the three hypotheses the paper uses at that point, given
separately and with the types of the fields `linear`, `unique` and `symm` of `System.WellFormed`:
`Step.strong_confluence_of` and `StepE.strong_confluence_of`. The theorems of `WellFormed`
systems are the instances `Step.strong_confluence_of hI.linear hI.unique hI.symm` and
`StepE.strong_confluence_of hI.linear hI.unique hI.symm` (`Step.strong_confluence_of_wellFormed`,
`StepE.strong_confluence_of_wellFormed` below check that they have the same statements).
-/

namespace INet

variable {S : Signature}

open Term

namespace Rule

/-- **The same active pair, read the other way, without reducedness** (Lafont 1997, Proposition 1,
page 73, implicit). As `Rule.equiv_inst_swap`, from the linearity of the rules and the symmetry of
the rule of a symbol with itself only: firing `α(as) = α(bs)` with `as` on the first cell, or with
`bs` on the first cell, gives the same graph. -/
theorem equiv_inst_swap_of {I : System S} (hlin : ∀ α β r, I.rule α β = some r → r.Linear)
    (hsymm : ∀ α r, I.rule α α = some r → ∃ π : _root_.Equiv.Perm (Fin r.internal),
      Equiv r.swap.net (r.net.bind fun x => Term.var (Sum.map id (Sum.map id π) x)))
    {α : S.Sym} {r : Rule S (S.arity α) (S.arity α)} (hr : I.rule α α = some r)
    (as bs : Fin (S.arity α) → Term S ℕ) (Δ : Net S ℕ)
    (hN : Net.Linear (s(Term.app α as, Term.app α bs) ::ₘ Δ))
    (f f' : Fin r.internal → ℕ) (hf : Function.Injective f) (hf' : Function.Injective f')
    (hfresh : ∀ i, f i ∉ Net.vars (s(Term.app α as, Term.app α bs) ::ₘ Δ))
    (hfresh' : ∀ i, f' i ∉ Net.vars (s(Term.app α as, Term.app α bs) ::ₘ Δ)) :
    Equiv (r.inst as bs f + Δ) (r.inst bs as f' + Δ) := by
  have hrl := hlin _ _ _ hr
  have E := r.equiv_inst_same hrl as bs Δ hN f f' hf hf' hfresh hfresh'
  have L' := r.linear_inst_add hrl (hα := rfl) (hβ := rfl) hf' hN hfresh'
  exact E.trans (r.equiv_inst_comm_of_symmPerm hrl (hsymm _ _ hr) as bs f' Δ L')

end Rule

/-- **Proposition 1: strong confluence, without reducedness** (Lafont 1997, page 73). For an
interaction system whose rules are linear (`hlin`), given at most once for two distinct symbols
(`hunique`), and symmetric for a symbol with itself (`hsymm`), with no condition that right-hand
sides are reduced: if a linear net `N` reduces in one interaction to `M₁` and to `M₂`, then either
`M₁` and `M₂` are the same graph, or each reduces in one interaction to a net, and the two nets
are the same graph. -/
theorem Step.strong_confluence_of {I : System S}
    (hlin : ∀ α β r, I.rule α β = some r → r.Linear)
    (hunique : ∀ α β, α ≠ β → (I.rule α β).isSome → I.rule β α = none)
    (hsymm : ∀ α r, I.rule α α = some r → ∃ π : _root_.Equiv.Perm (Fin r.internal),
      Equiv r.swap.net (r.net.bind fun x => Term.var (Sum.map id (Sum.map id π) x)))
    {N M₁ M₂ : Net S ℕ}
    (hN : N.Linear) (h₁ : Step I N M₁) (h₂ : Step I N M₂) :
    Equiv M₁ M₂ ∨ ∃ P₁ P₂, Step I M₁ P₁ ∧ Step I M₂ P₂ ∧ Equiv P₁ P₂ := by
  obtain ⟨α, β, r₁, hr₁, as, bs, Δ₁, f, hf, hffresh⟩ := h₁
  generalize hNe : (s(Term.app α as, Term.app β bs) ::ₘ Δ₁ : Net S ℕ) = N' at h₂
  obtain ⟨γ, δ, r₂, hr₂, cs, ds, Δ₂, g, hg, hgfresh⟩ := h₂
  rcases Multiset.cons_eq_cons.1 hNe with ⟨he, hΔ⟩ | ⟨-, C, hC₁, hC₂⟩
  · -- the same active pair
    subst hΔ
    rcases Sym2.eq_iff.1 he with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · -- read the same way
      simp only [Term.app.injEq] at hac hbd
      obtain ⟨rfl, hac⟩ := hac
      obtain ⟨rfl, hbd⟩ := hbd
      cases eq_of_heq hac
      cases eq_of_heq hbd
      rw [hr₁] at hr₂
      cases Option.some.inj hr₂
      left
      exact Rule.equiv_inst_same _ (hlin _ _ _ hr₁) _ _ _ hN f g hf hg hffresh hgfresh
    · -- read the other way
      simp only [Term.app.injEq] at had hbc
      obtain ⟨rfl, had⟩ := had
      obtain ⟨rfl, hbc⟩ := hbc
      cases eq_of_heq had
      cases eq_of_heq hbc
      by_cases hαβ : α = β
      · subst hαβ
        rw [hr₁] at hr₂
        cases Option.some.inj hr₂
        left
        exact Rule.equiv_inst_swap_of hlin hsymm hr₁ _ _ _ hN f g hf hg hffresh
          (fun i => by rw [Sym2.eq_swap]; exact hgfresh i)
      · have := hunique α β hαβ (by simp [hr₁])
        rw [this] at hr₂
        cases hr₂
  · -- two different active pairs
    subst hC₁ hC₂
    right
    exact Step.commute hlin hr₁ hr₂ as bs cs ds C hN f hf hffresh g hg hgfresh

open StrongConfluenceE

/-- **Proposition 1 for reduction of graphs, without reducedness** (Lafont 1997, Proposition 1,
page 73). As `StepE.strong_confluence`, for an interaction system whose rules are linear
(`hlin`), given at most once for two distinct symbols (`hunique`), and symmetric for a symbol
with itself (`hsymm`), with no condition that right-hand sides are reduced: if a linear net `N`
reduces by one `StepE` to `M₁` and to `M₂`, then either `M₁` and `M₂` are the same graph, or each
reduces by one `StepE` to a net, and the two nets are the same graph. -/
theorem StepE.strong_confluence_of {I : System S}
    (hlin : ∀ α β r, I.rule α β = some r → r.Linear)
    (hunique : ∀ α β, α ≠ β → (I.rule α β).isSome → I.rule β α = none)
    (hsymm : ∀ α r, I.rule α α = some r → ∃ π : _root_.Equiv.Perm (Fin r.internal),
      Equiv r.swap.net (r.net.bind fun x => Term.var (Sum.map id (Sum.map id π) x)))
    {N M₁ M₂ : Net S ℕ}
    (hN : N.Linear) (h₁ : StepE I N M₁) (h₂ : StepE I N M₂) :
    Equiv M₁ M₂ ∨ ∃ P₁ P₂, StepE I M₁ P₁ ∧ StepE I M₂ P₂ ∧ Equiv P₁ P₂ := by
  obtain ⟨N₁, e₁, s₁⟩ := h₁
  obtain ⟨N₂, e₂, s₂⟩ := h₂
  have hN₁ := e₁.linear hN
  obtain ⟨n, c₂⟩ :=
    (ChainPair.of_equiv hlin (e₂.symm.trans e₁) M₂).1 ⟨0, ChainPair.of_step s₂⟩
  obtain ⟨K, hK, c₂'⟩ := c₂.contract hN₁
  have c₁ := (ChainPair.of_step s₁).wires hlin hK
  have hKl : K.Linear := (equiv_of_wires hK).linear hN₁
  obtain ⟨M₁', t₁, E₁⟩ := c₁.step
  obtain ⟨M₂', t₂, E₂⟩ := c₂'.step
  rcases Step.strong_confluence_of hlin hunique hsymm hKl t₁ t₂ with
    E | ⟨P₁, P₂, u₁, u₂, EP⟩
  · exact Or.inl (E₁.symm.trans (E.trans E₂))
  · exact Or.inr ⟨P₁, P₂, ⟨M₁', E₁.symm, u₁⟩, ⟨M₂', E₂.symm, u₂⟩, EP⟩

/-- `Step.strong_confluence` (Lafont 1997, Proposition 1, page 73) is the instance of
`Step.strong_confluence_of` at the fields `linear`, `unique`, `symm` of a well-formed system. -/
theorem Step.strong_confluence_of_wellFormed {I : System S} (hI : I.WellFormed)
    {N M₁ M₂ : Net S ℕ} (hN : N.Linear) (h₁ : Step I N M₁) (h₂ : Step I N M₂) :
    Equiv M₁ M₂ ∨ ∃ P₁ P₂, Step I M₁ P₁ ∧ Step I M₂ P₂ ∧ Equiv P₁ P₂ :=
  Step.strong_confluence_of hI.linear hI.unique hI.symm hN h₁ h₂

/-- `StepE.strong_confluence` (Lafont 1997, Proposition 1, page 73) is the instance of
`StepE.strong_confluence_of` at the fields `linear`, `unique`, `symm` of a well-formed system. -/
theorem StepE.strong_confluence_of_wellFormed {I : System S} (hI : I.WellFormed)
    {N M₁ M₂ : Net S ℕ} (hN : N.Linear) (h₁ : StepE I N M₁) (h₂ : StepE I N M₂) :
    Equiv M₁ M₂ ∨ ∃ P₁ P₂, StepE I M₁ P₁ ∧ StepE I M₂ P₂ ∧ Equiv P₁ P₂ :=
  StepE.strong_confluence_of hI.linear hI.unique hI.symm hN h₁ h₂

end INet
