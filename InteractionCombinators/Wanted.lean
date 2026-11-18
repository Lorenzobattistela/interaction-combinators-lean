import InteractionCombinators.Instance

/-!
# Closure properties still to be proved

Statements that the rest of the development will rely on, checked by Lean and not yet proved.
`proof_wanted` adds no axiom, so nothing can depend on them until they are proved.

They are not needed for Theorem 1, whose lemmas carry their context explicitly. They are needed
to use a translation inside a larger net (Lafont's Proposition 4) and for strong confluence
(Proposition 1).

Two of the three original statements are proved: `Equiv.add_right` in
`InteractionCombinators/EquivAdd.lean` and `Translation.NetTr.equiv` in
`InteractionCombinators/NetTrEquiv.lean`. One is left.

It needs the same idea: a derivation may go through nets whose names clash with the
context, so the derivation has to be renamed first. Wire substitution and interaction are
invariant under an injective renaming of names.
-/

namespace INet

variable {S S' : Signature}

/-- Reduction up to wires can be done inside a larger net. The wires created along the way may
have to be given other names to avoid those of `Γ`, so the result is `M` up to equivalence. -/
proof_wanted StepsE.add_right {I : System S} (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    {N M : Net S ℕ} (Γ : Net S ℕ) (h : StepsE I N M) (hN : (N + Γ).Linear) :
    ∃ M', StepsE I (N + Γ) (M' + Γ) ∧ Equiv M' M ∧ (M' + Γ).Linear

end INet
