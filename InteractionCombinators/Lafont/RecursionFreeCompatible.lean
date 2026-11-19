import InteractionCombinators.Lafont.RecursionFreeFig7
import InteractionCombinators.Lafont.PlugsExpand
import InteractionCombinators.Lafont.PlugsNetTr
import InteractionCombinators.Lafont.RecursionFreeStrict

/-!
# A recursion-free system has a strict translation into the combinators (Section 2.4, pages 85–87)

Lafont 1997, Section 2.4, journal pages 85–87 (Fig. 6 and Fig. 7 on page 86, PDF page 18).

* `System.RecursionFreeData.translation_compatible` — the translation `D.translation` of Fig. 6
  is a translation of interaction systems (`Translation.Compatible`): Fig. 7 rows 1–4
  (`translation_cells_netTr_plug`), then the plugged decomposition is the rule
  (`plugs_expand`, `Decomposition.Plugs.netTr_inst_of_sides`).
* `recursionFree_strict` — **the result of Section 2.4**: a well-formed recursion-free system
  over a finite alphabet has a strict translation into the interaction combinators.
* `recursionFree_strict_noConDup` — the example of page 87.

This is not Theorem 1: the hypothesis `I.RecursionFree` is the restriction of Section 2.4.
-/

namespace INet

open Term

namespace Comb

variable {S : Signature} [Finite S.Sym] {I : System S}

/-- **The translation of a recursion-free system is compatible with reduction** (Lafont 1997,
Section 2.4, pages 85–86, Fig. 7). For every rule `α`–`β`, the cells `[α]` and `[β]` of Fig. 6,
plugged by their roots, reduce up to wires (`StepsE system`) to a translation of the right-hand
side of the rule. Rows 1–4 of Fig. 7 give a translation of the plugged rule
`Rule.plug φ ψ σ` of the expanded decomposition (`translation_cells_netTr_plug`); that
decomposition plugs the rule (`plugs_expand`, page 85), so the translation is, up to wires, a
translation of an instance of the rule (`Decomposition.Plugs.netTr_inst_of_sides`). -/
theorem _root_.INet.System.RecursionFreeData.translation_compatible (hI : I.WellFormed)
    (D : I.RecursionFreeData) : D.translation.Compatible I system := by
  intro α β r h xs ys f g hlin
  obtain ⟨M, N', h', hS, hE, hN⟩ := translation_cells_netTr_plug hI D h xs ys f g hlin
  obtain ⟨h'', N'', hN'', hE'⟩ := Decomposition.Plugs.netTr_inst_of_sides
    (D := ⟨(D.dec α β r h).k, (D.rawφ α β r h).expand.φ, (D.rawψ β α r h).expand.φ,
      (D.dec α β r h).σ⟩)
    (D.plugs_expand h) (D.rawφ α β r h).expand.linear (D.rawψ β α r h).expand.linear xs ys h' hN
  exact ⟨M, N'', h'', hS, hE.trans hE', hN''⟩

/-- **A recursion-free system has a strict translation into the interaction combinators**
(Lafont 1997, Section 2.4, pages 85–87). Every well-formed interaction system over a finite
alphabet whose rules have a recursion-free decomposition (`System.RecursionFree`, page 85) has a
strict translation into the interaction combinators that is compatible with reduction: the
translation of Fig. 6 (`D.translation`), strict because the root of each `[α]` is a `dup` cell
(`translation_strict`), and compatible by Fig. 7 (`translation_compatible`). This is the body of
`StrictlyUniversal system` restricted to recursion-free systems. -/
theorem recursionFree_strict (I : System S) (hI : I.WellFormed) (hR : I.RecursionFree) :
    ∃ Φ : Translation S sig, Φ.Strict ∧ Φ.Compatible I system := by
  obtain ⟨D⟩ := hR
  exact ⟨D.translation, D.translation_strict, D.translation_compatible hI⟩

/-- **The example of page 87**: the system `systemNoConDup` (the combinators without the
`con`–`dup` rule) is recursion-free, so it has a strict translation into the interaction
combinators (Lafont 1997, page 87). The hypotheses of `recursionFree_strict` hold. -/
theorem recursionFree_strict_noConDup :
    ∃ Φ : Translation sig sig, Φ.Strict ∧ Φ.Compatible systemNoConDup system :=
  recursionFree_strict systemNoConDup systemNoConDup_wellFormed systemNoConDup_recursionFree

end Comb

end INet
