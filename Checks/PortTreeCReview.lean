import Checks.PortTreeCCheck

/-!
# Review of the computable tree at a port `Rule.portTreeC` (Fig. 6, page 86)

Checks that try to refute `Rule.portTreeC` (`Lafont/PortTreeC.lean`) and its stated properties.

* `Expanded` is not needed: `portTree_eq_of_linear` and `portTreeC_eq_portTree_of_linear` prove
  `Rule.portTree_eq` and `Rule.portTreeC_eq_portTree` from linearity alone. In a linear side the
  port `p` occurs once, so at most one equation is rooted at `p`, whatever the other trees are.
* An equation written `ε = a₀` (the leaf on the right of the `Sym2`): the twin finds `ε`.
* An equation `a₀ = a₁` joining two ports (a wire between two ports, a tree that is a leaf in
  Fig. 6): the twin gives `a₁` at `a₀` and `a₀` at `a₁`. Such a side is linear and not in
  expanded form, and the twin is still `portTree` there.
* A port `a₀` that is a leaf of the tree `b₀ = con(a₀, w₀)` and not a root: the twin gives the
  leaf `a₀`, as `portTree` does.
* A side that is not linear, with two different equations rooted at `a₀`: the twin gives the
  leaf `a₀`, which is neither tree, and `portTree` gives one of the two trees; so the twin is not
  `portTree` there, and the hypothesis `Linear` of `portTreeC_eq_portTree_of_linear` (and of
  `portTreeC_eq_of_linear`) is needed.
-/

namespace INet.Comb.PortTreeCReview

open Term Rule ExpandedIso PortTreeC

variable {S : Signature} {a k : ℕ}

/-! ## `Expanded` is not needed -/

/-- In a linear side, `portTree φ p` is the tree of an equation rooted at `p`: the hypothesis
`Expanded` of `Rule.portTree_eq` is not needed (Fig. 6, page 86). -/
theorem portTree_eq_of_linear {φ : Rule S a k} (hl : φ.Linear)
    {p : Fin a ⊕ Fin k} {t : Term S (Fin a ⊕ Fin k ⊕ Fin φ.internal)}
    (ht : s(Term.var (port p), t) ∈ φ.net) : φ.portTree p = t := by
  have h : ∃ t, s(Term.var (port p), t) ∈ φ.net := ⟨t, ht⟩
  unfold Rule.portTree
  split_ifs
  exact (portTreeC_eq_of_linear hl h.choose_spec).symm.trans (portTreeC_eq_of_linear hl ht)

/-- On a linear side the computable twin is `Rule.portTree`: the hypothesis `Expanded` of
`Rule.portTreeC_eq_portTree` is not needed (Fig. 6, page 86). -/
theorem portTreeC_eq_portTree_of_linear {φ : Rule S a k} (hl : φ.Linear) :
    φ.portTreeC = φ.portTree := by
  funext p
  by_cases h : ∃ t, s(Term.var (port p), t) ∈ φ.net
  · obtain ⟨t, ht⟩ := h
    rw [portTreeC_eq_of_linear hl ht, portTree_eq_of_linear hl ht]
  · rw [portTreeC_of_not_exists h, portTree_of_not_exists h]

/-! ## The equation written `ε = a₀` -/

/-- The side `ε = a₀`, the leaf on the right of the equation. -/
def ψswap : Rule sig 1 0 := ⟨0, s(mkEra, .var (.inl 0)) ::ₘ 0⟩

/-- The order of the two sides of an equation does not matter: on `ε = a₀` the twin finds `ε`
(Fig. 6, page 86). -/
theorem portTreeC_ψswap : ψswap.portTreeC (.inl 0) = mkEra := by
  decide

/-! ## A wire between two ports -/

/-- The side `a₀ = a₁`: one equation joining the two left ports, no internal wire. -/
def ψpq : Rule sig 2 0 := ⟨0, s(.var (.inl 0), .var (.inl 1)) ::ₘ 0⟩

/-- On `a₀ = a₁` the tree at each port is the leaf of the other port, as for a wire between two
ports in Fig. 6 (page 86). -/
theorem portTreeC_ψpq :
    ψpq.portTreeC (.inl 0) = .var (.inl 1) ∧ ψpq.portTreeC (.inl 1) = .var (.inl 0) := by
  decide

theorem ψpq_linear : ψpq.Linear := ⟨by decide, by decide, fun w => w.elim0⟩

/-- `a₀ = a₁` is not in expanded form: the leaf of the tree is a port. -/
theorem ψpq_not_expanded : ¬ ψpq.Expanded := by
  intro h
  obtain ⟨p, t, he, -, ht⟩ := h s(.var (.inl 0), .var (.inl 1)) (by decide)
  rcases Sym2.eq_iff.1 he with ⟨-, rfl⟩ | ⟨rfl, -⟩
  · obtain ⟨w, hw⟩ := ht (.inl 1) (by simp)
    exact absurd hw (by simp)
  · obtain ⟨w, hw⟩ := ht (.inl 0) (by simp)
    exact absurd hw (by simp)

/-- On `a₀ = a₁`, linear and not in expanded form, the twin is still `portTree`, by
`portTreeC_eq_portTree_of_linear` (Fig. 6, page 86). -/
theorem portTree_ψpq :
    ψpq.portTree (.inl 0) = .var (.inl 1) ∧ ψpq.portTree (.inl 1) = .var (.inl 0) := by
  rw [← portTreeC_eq_portTree_of_linear ψpq_linear]
  exact portTreeC_ψpq

/-! ## A port that is a leaf, not a root -/

/-- The side `b₀ = con(a₀, w₀)`, `b₁ = w₀`: the port `a₀` is a leaf of the tree at `b₀`. -/
def ψleaf : Rule sig 1 2 :=
  ⟨1, s(.var (.inr (.inl 0)), mkCon (.var (.inl 0)) (.var (.inr (.inr 0)))) ::ₘ
    s(.var (.inr (.inl 1)), .var (.inr (.inr 0))) ::ₘ 0⟩

/-- Trees over the names of `ψleaf`: one left port, two right ports, one internal wire. -/
abbrev W := Term sig (Fin 1 ⊕ Fin 2 ⊕ Fin 1)

/-- `portTreeC` on `ψleaf`, typed at `W` (`ψleaf.internal` is `1` only by unfolding). -/
def leafTree (p : Fin 1 ⊕ Fin 2) : W := ψleaf.portTreeC p

/-- On `ψleaf` the twin gives the leaf `a₀` at `a₀`, the tree `con(a₀, w₀)` at `b₀` and the
leaf `w₀` at `b₁` (Fig. 6, page 86). -/
theorem portTreeC_ψleaf :
    ψleaf.portTreeC (.inl 0) = (.var (.inl 0) : W) ∧
      ψleaf.portTreeC (.inr 0) = (mkCon (.var (.inl 0)) (.var (.inr (.inr 0))) : W) ∧
      ψleaf.portTreeC (.inr 1) = (.var (.inr (.inr 0)) : W) :=
  show leafTree (.inl 0) = .var (.inl 0) ∧
    leafTree (.inr 0) = mkCon (.var (.inl 0)) (.var (.inr (.inr 0))) ∧
    leafTree (.inr 1) = .var (.inr (.inr 0)) by
  decide

theorem ψleaf_linear : ψleaf.Linear := ⟨by decide, by decide, by decide⟩

/-- At the port `a₀`, a leaf and not a root, `portTree` is also the leaf `a₀` (Fig. 6,
page 86). -/
theorem portTree_ψleaf : ψleaf.portTree (.inl 0) = (.var (.inl 0) : W) := by
  rw [← portTreeC_eq_portTree_of_linear ψleaf_linear]
  exact portTreeC_ψleaf.1

/-! ## Two different equations at the same port: linearity is needed -/

/-- The side `a₀ = ε`, `a₀ = con(ε, ε)`: two different equations rooted at `a₀`. -/
def ψtwo : Rule sig 1 0 :=
  ⟨0, s(.var (.inl 0), mkEra) ::ₘ s(.var (.inl 0), mkCon mkEra mkEra) ::ₘ 0⟩

/-- `ψtwo` is not linear: `a₀` occurs twice. -/
theorem ψtwo_not_linear : ¬ ψtwo.Linear := fun h => absurd (h.left 0) (by decide)

/-- On `ψtwo` the twin gives the leaf `a₀`, which is neither of the two trees rooted at `a₀`. -/
theorem portTreeC_ψtwo : ψtwo.portTreeC (.inl 0) = .var (.inl 0) := by
  decide

/-- On `ψtwo`, `portTree` gives one of the two trees rooted at `a₀`. -/
theorem portTree_ψtwo :
    ψtwo.portTree (.inl 0) = mkEra ∨ ψtwo.portTree (.inl 0) = mkCon mkEra mkEra := by
  have h : ∃ t, s(Term.var (port (.inl 0)), t) ∈ ψtwo.net := ⟨mkEra, by decide⟩
  unfold Rule.portTree
  split_ifs
  have hs := h.choose_spec
  generalize h.choose = c at hs ⊢
  change s(Term.var (.inl 0), c) ∈
    (s(.var (.inl 0), mkEra) ::ₘ s(.var (.inl 0), mkCon mkEra mkEra) ::ₘ 0 :
    Net sig (Fin 1 ⊕ Fin 0 ⊕ Fin 0)) at hs
  rcases Multiset.mem_cons.1 hs with h1 | hs
  · rcases Sym2.eq_iff.1 h1 with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact .inl h1
    · simp [mkEra] at h1
  rcases Multiset.mem_cons.1 hs with h1 | hs
  · rcases Sym2.eq_iff.1 h1 with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact .inr h1
    · simp [mkCon] at h1
  exact absurd hs (Multiset.notMem_zero _)

/-- Without linearity the twin is not `portTree`: on `ψtwo` they differ at `a₀`, so the
hypothesis `Linear` of `portTreeC_eq_portTree_of_linear` cannot be dropped (Fig. 6, page 86). -/
theorem portTreeC_ne_portTree_ψtwo : ψtwo.portTreeC (.inl 0) ≠ ψtwo.portTree (.inl 0) := by
  rw [portTreeC_ψtwo]
  rcases portTree_ψtwo with h | h <;> rw [h] <;> simp [mkEra, mkCon]

end INet.Comb.PortTreeCReview
