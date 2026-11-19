import InteractionCombinators.Lafont.Simulation
import InteractionCombinators.Lafont.RecursionFreeCompatible

/-!
# Checks of Proposition 4 for one interaction (page 81)

`Translation.Compatible.step` is applied to a concrete net: an `era`–`con` cut whose `con` cell
has its port `0` wired to a `dup` cell of the context `Δ`. The hypotheses hold, once for the
identity translation of the combinators, and once for the translation of Fig. 6 of the system
`systemNoConDup` of page 87, whose principal nets are not single cells.
-/

namespace INet.SimulationCheck

open Term Comb

/-- `ε = γ(x₀, x₁)`, `x₀ = δ(x₂, x₃)`: an active pair and a context that uses one of its ports. -/
def src : CNet := s(mkEra, mkCon (var 0) (var 1)) ::ₘ {s(var 0, mkDup (var 2) (var 3))}

/-- After the interaction: `ε = x₀`, `ε = x₁`, `x₀ = δ(x₂, x₃)`. -/
def tgt : CNet := s(mkEra, var 0) ::ₘ s(mkEra, var 1) ::ₘ {s(var 0, mkDup (var 2) (var 3))}

theorem src_linear : src.Linear := by
  intro y
  simp only [src, Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_mkCon, vars_mkEra,
    vars_mkDup, vars_var, Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

theorem step_src (I : System sig) (hI : I.rule era con = some ruleEraBin) : Step I src tgt := by
  have h : Step I src
      (ruleEraBin.inst (![] : Fin 0 → Term sig ℕ) ![var 0, var 1] (Fin.elim0 : Fin 0 → ℕ) +
        {s(var 0, mkDup (var 2) (var 3))}) :=
    Step.mk (I := I) era con ruleEraBin hI ![] ![var 0, var 1] _
      (Fin.elim0 : Fin 0 → ℕ) (fun (i : Fin 0) => i.elim0) (fun (i : Fin 0) => i.elim0)
  rw [inst_eraBin] at h
  simpa [tgt] using h

/-- Proposition 4 for one interaction, with the identity translation of the combinators. -/
example : ∃ M₁ M', StepsE system src M₁ ∧ Equiv M₁ M' ∧ (Translation.id sig).NetTr tgt M' :=
  (Translation.id_compatible system system_wellFormed).step system_wellFormed.linear
    system_wellFormed.linear (step_src system rfl)
    ⟨Multiset.rel_refl_of_refl_on fun e _ => Translation.eqTr_id e, src_linear⟩

/-- Proposition 4 for one interaction, with the strict translation of Fig. 6 of `systemNoConDup`
into the combinators (page 87): a translation of `src` exists, and it reduces up to wires to a net
that is the same graph as a translation of `tgt`. -/
example : ∃ Φ : Translation sig sig, Φ.Strict ∧ ∃ N', Φ.NetTr src N' ∧
    ∃ M₁ M', StepsE system N' M₁ ∧ Equiv M₁ M' ∧ Φ.NetTr tgt M' := by
  obtain ⟨Φ, hs, hc⟩ := recursionFree_strict_noConDup
  obtain ⟨N', -, hN', -⟩ := Φ.exists_netTr src_linear (Net.exists_below src).choose_spec
  exact ⟨Φ, hs, N', hN', hc.step systemNoConDup_wellFormed.linear system_wellFormed.linear
    (step_src systemNoConDup rfl) hN'⟩

end INet.SimulationCheck
