import InteractionCombinators.Universality.RecursionFree.PortTreeC
import Checks.Universality.RecursionFree.GammaCheck

/-!
# Checks of the computable tree at a port `Rule.portTreeC` (Fig. 6, page 86)

* The side `ruleConDup` (`a₀ = dup(w₀, w₁)`, `a₁ = dup(w₂, w₃)`, `b₀ = con(w₀, w₂)`,
  `b₁ = con(w₁, w₃)`): `portTreeC` computes the four trees, by `#eval` and by `decide`, and
  `portTreeC_eq_portTree` applies (its hypotheses hold), so these are also the values of
  `portTree` (`portTree_conDup` of `GammaCheck`).
* A side with one equation `a₀ = ε` and no equation at `a₁`: the twin gives the leaf `a₁`, by
  computation and by `portTreeC_of_not_exists`, and so does `portTree`.
* A side, not linear, where the equation `a₀ = ε` occurs twice: the twin gives the leaf `a₀`, so
  the hypothesis of linearity of `portTreeC_eq_of_linear` is needed.
-/

namespace INet.Comb.PortTreeCCheck

open Term Rule DecompositionReview DecompositionCheck ExpandedIsoCheck ExpandTrReview GammaCheck

/-! ## The side `ruleConDup` -/

/-- `portTreeC` on `ruleConDup`, typed at `V 4` (`ruleConDup.internal` is `4` only by
unfolding), so that the decidable equality of trees applies. -/
def conDupTree (p : Fin 2 ⊕ Fin 2) : V 4 := ruleConDup.portTreeC p

-- `portTreeC` is computable: evaluated on the four ports of `ruleConDup`, this prints `true`.
#eval decide (conDupTree (.inl 0) = mkDup (pw 0) (pw 1) ∧
  conDupTree (.inl 1) = mkDup (pw 2) (pw 3) ∧
  conDupTree (.inr 0) = mkCon (pw 0) (pw 2) ∧
  conDupTree (.inr 1) = mkCon (pw 1) (pw 3))

/-- The four trees of `ruleConDup`, by computation (Fig. 6, page 86). -/
theorem portTreeC_conDup :
    ruleConDup.portTreeC (.inl 0) = (mkDup (pw 0) (pw 1) : V 4) ∧
      ruleConDup.portTreeC (.inl 1) = (mkDup (pw 2) (pw 3) : V 4) ∧
      ruleConDup.portTreeC (.inr 0) = (mkCon (pw 0) (pw 2) : V 4) ∧
      ruleConDup.portTreeC (.inr 1) = (mkCon (pw 1) (pw 3) : V 4) :=
  show conDupTree (.inl 0) = mkDup (pw 0) (pw 1) ∧ conDupTree (.inl 1) = mkDup (pw 2) (pw 3) ∧
    conDupTree (.inr 0) = mkCon (pw 0) (pw 2) ∧ conDupTree (.inr 1) = mkCon (pw 1) (pw 3) by
  decide

/-- The hypotheses of `portTreeC_eq_portTree` hold on `ruleConDup`: the twin is `portTree`
there (Fig. 6, page 86). -/
theorem portTreeC_eq_portTree_conDup : ruleConDup.portTreeC = ruleConDup.portTree :=
  portTreeC_eq_portTree ruleConDup_expanded ruleConDup_linear

/-! ## A port with no equation -/

/-- The side `a₀ = ε`, with two left ports, no right port and no internal wire; `a₁` has no
equation. -/
def ψ : Rule sig 2 0 := ⟨0, s(.var (.inl 0), mkEra) ::ₘ 0⟩

-- With no equation at `a₁` the twin computes the leaf `a₁`: this prints `true`.
#eval decide (ψ.portTreeC (.inl 1) = .var (.inl 1))

/-- With no equation at `a₁` the twin is the leaf `a₁`, by computation (Fig. 6, page 86). -/
theorem portTreeC_ψ : ψ.portTreeC (.inl 0) = mkEra ∧ ψ.portTreeC (.inl 1) = .var (.inl 1) := by
  decide

/-- No equation of `ψ` is rooted at `a₁`. -/
theorem ψ_not_exists :
    ¬ ∃ t, s(Term.var (ExpandedIso.port (.inl 1)), t) ∈ ψ.net := by
  rintro ⟨t, ht⟩
  change _ ∈ (s(.var (.inl 0), mkEra) ::ₘ 0 : Net sig (Fin 2 ⊕ Fin 0 ⊕ Fin 0)) at ht
  rcases Multiset.mem_cons.1 ht with h | h
  · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd (Sum.inl_injective (Term.var.inj h)) (by decide)
    · simp [mkEra] at h
  · exact Multiset.notMem_zero _ h

/-- With no equation at `a₁`, `portTree` and its twin are both the leaf `a₁` (Fig. 6, page 86). -/
theorem portTree_ψ :
    ψ.portTreeC (.inl 1) = .var (.inl 1) ∧ ψ.portTree (.inl 1) = .var (.inl 1) :=
  ⟨portTreeC_of_not_exists ψ_not_exists, portTree_of_not_exists ψ_not_exists⟩

/-! ## A repeated equation: linearity is needed -/

/-- The side `a₀ = ε, a₀ = ε`: the same equation twice, so `a₀` occurs twice. -/
def ψ₂ : Rule sig 1 0 := ⟨0, s(.var (.inl 0), mkEra) ::ₘ s(.var (.inl 0), mkEra) ::ₘ 0⟩

/-- The equation `a₀ = ε` is in `ψ₂`, but the twin gives the leaf `a₀`, not `ε`: without
linearity `portTreeC_eq_of_linear` fails (Fig. 6, page 86). -/
theorem portTreeC_ψ₂ :
    s(Term.var (ExpandedIso.port (.inl 0)), mkEra) ∈ ψ₂.net ∧
      ψ₂.portTreeC (.inl 0) = .var (.inl 0) ∧ ψ₂.portTreeC (.inl 0) ≠ mkEra := by
  decide

end INet.Comb.PortTreeCCheck
