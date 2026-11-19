import InteractionCombinators.Lafont.NormalFormE

/-!
# Irreducible and "no cut" (pages 73, 78-80)

Lafont 1997, page 73: a net is irreducible when no interaction applies; page 80: a cut is a pair
of cells joined by their principal ports. Pages 78-79: "An irreducible net is not necessarily
reduced, since it may contain irreducible cuts". A net without a cut is always irreducible
(`StepE.Normal.of_not_hasCut`). The converse holds when every pair of symbols has a rule in one
order or the other, as for the combinators.

* `StepE.Normal.iff_not_hasCut` — in such a system, irreducible is "no cut".
* `Comb.system_complete` — the combinators have a rule for every pair of symbols, in one order or
  the other.
* `Comb.normal_iff_not_hasCut` — for the combinators, irreducible is "no cut".
-/

namespace INet

variable {S : Signature}

/-- **Irreducible is "no cut" in a complete system** (Lafont 1997, pages 73 and 80; pages 78-79:
an irreducible cut is a cut without a rule). If every pair of symbols has a rule in one order or
the other, a net is irreducible exactly when it has no cut. -/
theorem StepE.Normal.iff_not_hasCut {I : System S}
    (hI : ∀ α β, (I.rule α β).isSome ∨ (I.rule β α).isSome) {N : Net S ℕ} :
    StepE.Normal I N ↔ ¬ N.HasCut :=
  ⟨fun h hc => (Net.HasCut.stepE hI hc).elim h, StepE.Normal.of_not_hasCut⟩

namespace Comb

/-- **The combinators are complete** (Lafont 1997, page 83, Fig. 2): every pair of symbols among
`con`, `dup`, `era` has a rule, in one order or the other. -/
theorem system_complete :
    ∀ α β : sig.Sym, (system.rule α β).isSome ∨ (system.rule β α).isSome := by
  intro α β
  cases α <;> cases β <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- **For the combinators, irreducible is "no cut"** (Lafont 1997, pages 73 and 80, with the rules
of Fig. 2, page 83). -/
theorem normal_iff_not_hasCut {N : Net sig ℕ} : StepE.Normal system N ↔ ¬ N.HasCut :=
  StepE.Normal.iff_not_hasCut system_complete

end Comb

end INet
