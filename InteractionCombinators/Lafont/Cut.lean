import InteractionCombinators.NetTrWire

/-!
# Cuts, and a strict translation keeps them (Proposition 3, page 80)

Lafont 1997, page 80: "a cut" is a pair of cells joined by their principal ports. A net is
reduced when it has no cut and no vicious circle; Proposition 3 says that a translation reflects
reduced nets, and keeps them when it is strict. Its proof checks four points; this file and
`Lafont/CutChain.lean` do the first two, about cuts.

A net is text, so a cut is a cut of the graph: two principal ports joined *up to wires*. The text
`x = α(…), x = β(…)` is a cut, and so is a chain `α(…) = x₁, x₁ = x₂, x₂ = β(…)`.

* `Net.HasCut` — some net equivalent to `N` has an equation `α(…) = β(…)`.
* `Net.HasCut.of_equiv` — the definition does not depend on the spelling of the net.
* `Net.HasCut.stepE` — in a system with a rule for every pair of symbols, a net with a cut can
  be reduced.
* `Translation.NetTr.hasCut_of_strict` — the second point of the proof of Proposition 3: if `Φ`
  is strict and `N` has a cut, so does `Φ(N)`.
-/

namespace INet

variable {S S' : Signature}

open Term

namespace Net

/-- A net has a cut (Lafont 1997, page 80): two cells are joined by their principal ports, up to
wires. Some net that is the same graph as `N` has an equation whose two sides are cells. -/
def HasCut (N : Net S ℕ) : Prop :=
  ∃ N', Equiv N N' ∧ ∃ (α β : S.Sym) (ts : Fin (S.arity α) → Term S ℕ)
    (us : Fin (S.arity β) → Term S ℕ), s(Term.app α ts, Term.app β us) ∈ N'

/-- An equation between two cells is a cut (Lafont 1997, page 80). -/
theorem hasCut_of_mem {N : Net S ℕ} {α β : S.Sym} {ts : Fin (S.arity α) → Term S ℕ}
    {us : Fin (S.arity β) → Term S ℕ} (h : s(Term.app α ts, Term.app β us) ∈ N) : N.HasCut :=
  ⟨N, Equiv.refl N, α, β, ts, us, h⟩

/-- Having a cut is a property of the graph (Lafont 1997, page 80): it does not change under
wire substitution. -/
theorem HasCut.of_equiv {N M : Net S ℕ} (h : N.HasCut) (e : Equiv N M) : M.HasCut := by
  obtain ⟨N', hE, rest⟩ := h
  exact ⟨N', e.symm.trans hE, rest⟩

/-- Equivalent nets have a cut together (Lafont 1997, page 80). -/
theorem hasCut_iff_of_equiv {N M : Net S ℕ} (e : Equiv N M) : N.HasCut ↔ M.HasCut :=
  ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩

/-- **A cut can be reduced** (Lafont 1997, page 80: a net is reduced when it has no cut and no
vicious circle). In a system with a rule for every pair of symbols, a net with a cut reduces in
one interaction up to wires. No linearity is needed: the names given to the new wires are taken
above every name of the net. -/
theorem HasCut.stepE {I : System S} (hI : ∀ α β, (I.rule α β).isSome) {N : Net S ℕ}
    (h : N.HasCut) : ∃ M, StepE I N M := by
  obtain ⟨N', hE, α, β, ts, us, hm⟩ := h
  obtain ⟨Δ, rfl⟩ := Multiset.exists_cons_of_mem hm
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (hI α β)
  let k : ℕ := (Net.vars (s(Term.app α ts, Term.app β us) ::ₘ Δ)).sup + 1
  refine ⟨_, _, hE, Step.mk α β r hr ts us Δ (fun w => k + w)
    (fun a b hab => Fin.ext (by simpa using hab)) (fun w hw => ?_)⟩
  have := Multiset.le_sup hw
  omega

end Net

/-- An instance of a strict principal net is a cell: its root is the principal port of a cell
(Lafont 1997, page 79). -/
theorem PNet.Strict.inst_eq_app {n : ℕ} {p : PNet S' n} (hp : p.Strict) (args : Fin n → Term S' ℕ)
    (f : Fin p.internal → ℕ) : ∃ γ us, p.inst args f = Term.app γ us := by
  unfold PNet.inst
  cases h : p.tree with
  | var x => exact absurd h (hp x)
  | app γ ts => exact ⟨γ, _, rfl⟩

/-- **A strict translation keeps cuts** (Lafont 1997, Proposition 3, second point of the proof,
page 80): if `Φ` is strict, `N'` translates `N` and `N` has a cut, then `N'` has a cut. The cut of
`N` is an equation `α(…) = β(…)` of a net equivalent to `N`; a translation of that net is
equivalent to `N'` (`NetTr.of_equiv`), and strictness makes both sides of the translated equation
cells. -/
theorem Translation.NetTr.hasCut_of_strict {Φ : Translation S S'} (hΦ : Φ.Strict) {N : Net S ℕ}
    {N' : Net S' ℕ} (h : Φ.NetTr N N') (hc : N.HasCut) : N'.HasCut := by
  obtain ⟨N₁, hE, α, β, ts, us, hm⟩ := hc
  obtain ⟨N₁', h₁, hE'⟩ := h.of_equiv hE
  obtain ⟨Δ, rfl⟩ := Multiset.exists_cons_of_mem hm
  obtain ⟨e', Δ', he, -, rfl⟩ := Multiset.rel_cons_left.1 h₁.rel
  obtain ⟨a', b', rfl, ha, hb⟩ := Translation.EqTr.mk he
  cases ha with
  | app _ _ ts' f _ =>
  cases hb with
  | app _ _ us' g _ =>
  obtain ⟨γ, vs, hγ⟩ := (hΦ α).inst_eq_app ts' f
  obtain ⟨δ, ws, hδ⟩ := (hΦ β).inst_eq_app us' g
  refine ⟨_, hE', γ, δ, vs, ws, ?_⟩
  rw [hγ, hδ]
  exact Multiset.mem_cons_self _ _

end INet
