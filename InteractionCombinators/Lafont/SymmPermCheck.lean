import InteractionCombinators.Lafont.SymmPerm
import InteractionCombinators.Lafont.DecompositionSymmReview

/-!
# `Rule.SymmPerm` is strictly weaker than symmetry up to wires (page 73)

Issue #236, item 5. The rule `twin` of `Lafont/DecompositionSymmReview.lean` (two `β` cells whose
auxiliary ports are crossed) is symmetric in the sense of page 73: read from the other cell, it is
the same net with its two internal wires exchanged (`twin_swap`). So it is `Rule.SymmPerm`, while
it is not `Equiv` to its swap (`twin_not_symm`). The two lemmas of `Lafont/SymmPerm.lean` apply to
it, where `Rule.equiv_inst_comm` and `Rule.exists_symm_decomposition` do not.
-/

namespace INet.DecompositionSymmReview

/-- `twin` is symmetric up to the transposition of its two internal wires (page 73). -/
theorem twin_symmPerm : twin.SymmPerm :=
  ⟨(_root_.Equiv.swap (0 : Fin 2) 1 : _root_.Equiv.Perm (Fin 2)), Equiv.of_eq twin_swap⟩

/-- `twin` is `Rule.SymmPerm` but not `Equiv` to its swap: the condition of page 73 is strictly
weaker than `Equiv r.swap.net r.net`. -/
theorem twin_symmPerm_not_equiv : twin.SymmPerm ∧ ¬ Equiv twin.swap.net twin.net :=
  ⟨twin_symmPerm, twin_not_symm⟩

/-- The symmetric decomposition of page 86 applies to `twin`. -/
theorem twin_exists_symm_decomposition :
    ∃ D : Decomposition sigT 1 1, D.ψ = D.φ ∧ (∀ l, D.σ (D.σ l) = l) ∧ D.φ.Linear ∧
      D.φ.Reduced ∧
      ∃ ι : Fin twin.internal → Fin (Rule.plug D.φ D.ψ D.σ).internal, Function.Injective ι ∧
        Equiv (Rule.plug D.φ D.ψ D.σ).net
          (twin.net.bind fun x => Term.var (Sum.map id (Sum.map id ι) x)) :=
  twin.exists_symm_decomposition_of_symmPerm twin_linear twin_reduced twin_symmPerm

/-- **The one-rule system `sysT` is well-formed.** With the symmetry condition of page 73 read as
symmetry of graphs (`System.WellFormed.symm`, up to a permutation of the internal wires), the
system that the earlier condition `Equiv r.swap.net r.net` excluded is an interaction system, so
Theorem 1 applies to it. -/
theorem sysT_wellFormed : sysT.WellFormed where
  linear := sysT_rest.1
  reduced := sysT_rest.2.1
  unique := sysT_rest.2.2
  symm := by
    intro α r h
    cases α <;> cases h
    exact twin_symmPerm

end INet.DecompositionSymmReview
