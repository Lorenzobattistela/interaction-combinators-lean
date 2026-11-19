import InteractionCombinators.Lafont.SimulationCount

/-!
# Proposition 4 for reduction of graphs on the source

Lafont 1997, Proposition 4, page 81. `Translation.Compatible.steps` and
`Translation.CompatibleWithin.steps` take a literal reduction (`Steps`, `StepsN`) of the source
net. A net of the paper is a graph (Section 1.3, page 72), and reduction of graphs is `StepsE`: a
wire substitution may come before each interaction. Here the source reduction is `StepsE`,
`StepsEN`:

* `Translation.Compatible.stepsE` — `N` reduces up to wires to `M`, then any translation of `N`
  reduces up to wires to a net that is the same graph as a translation of `M`.
* `Translation.CompatibleWithin.stepsEN` — the same with the lengths, `L n ≤ n' ≤ M n`.

Each step `Equiv N N₀`, `Step I N₀ M` is handled by moving the translation along the equivalence
(`Translation.NetTr.of_equiv`), simulating the literal step, and absorbing the equivalence on the
target side into the first step of the simulation (`StepsE.of_equiv`, `StepsEN.of_equiv`).
-/

namespace INet

variable {S S' : Signature}

namespace Translation

/-- **One interaction up to wires is simulated** (Lafont 1997, Proposition 4, page 81, the case of
one step, for reduction of graphs). If `N` is the same graph as a net `N₀` that reduces to `M` in
one interaction, and `N'` is a translation of `N`, then `N'` reduces up to wires to a net that is
the same graph as a translation of `M`. The rules of `I` and of `I'` are linear. -/
theorem Compatible.stepE {I : System S} {I' : System S'}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    {Φ : Translation S S'} (hΦ : Φ.Compatible I I')
    {N M : Net S ℕ} {N' : Net S' ℕ} (h : StepE I N M) (hT : Φ.NetTr N N') :
    ∃ M₁ M', StepsE I' N' M₁ ∧ Equiv M₁ M' ∧ Φ.NetTr M M' := by
  obtain ⟨N₀, hE, hs⟩ := h
  obtain ⟨N₀', t0, e0⟩ := NetTr.of_equiv hE hT
  obtain ⟨M₁, M', h1, e1, t1⟩ := hΦ.step hI hI' hs t0
  obtain ⟨X, hX, eX⟩ := StepsE.of_equiv e0 h1
  exact ⟨X, M', hX, eX.trans e1, t1⟩

/-- **Proposition 4 for reduction of graphs** (Lafont 1997, page 81: "If N reduces in n steps to M,
then Φ(N) reduces in n′ steps to Φ(M)"; Section 1.3, page 72: nets are graphs). If `Φ` is a
translation of interaction systems from `I` to `I'`, `N` reduces up to wires to `M`, and `N'` is a
translation of `N`, then `N'` reduces up to wires to a net that is the same graph as a translation
of `M`. The rules of `I` and of `I'` are linear. -/
theorem Compatible.stepsE {I : System S} {I' : System S'}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    {Φ : Translation S S'} (hΦ : Φ.Compatible I I')
    {N M : Net S ℕ} {N' : Net S' ℕ} (h : StepsE I N M) (hT : Φ.NetTr N N') :
    ∃ M₁ M', StepsE I' N' M₁ ∧ Equiv M₁ M' ∧ Φ.NetTr M M' := by
  induction h with
  | refl => exact ⟨N', N', Relation.ReflTransGen.refl, Equiv.refl _, hT⟩
  | tail _ hs ih =>
    obtain ⟨M₁, M', h1, e1, t1⟩ := ih
    obtain ⟨M₂, M'', h2, e2, t2⟩ := hΦ.stepE hI hI' hs t1
    obtain ⟨X, hX, eX⟩ := StepsE.of_equiv e1 h2
    exact ⟨X, M'', h1.trans hX, eX.trans e2, t2⟩

/-- **One interaction up to wires is simulated in `k` interactions, `L ≤ k ≤ M`** (Lafont 1997,
Proposition 4, page 81, the case of one step, for reduction of graphs). The rules of `I` and of
`I'` are linear. -/
theorem CompatibleWithin.stepE {I : System S} {I' : System S'}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    {Φ : Translation S S'} {L M : ℕ} (hΦ : Φ.CompatibleWithin I I' L M)
    {N M₀ : Net S ℕ} {N' : Net S' ℕ} (h : StepE I N M₀) (hT : Φ.NetTr N N') :
    ∃ k M₁ M', StepsEN I' k N' M₁ ∧ L ≤ k ∧ k ≤ M ∧ Equiv M₁ M' ∧ Φ.NetTr M₀ M' := by
  obtain ⟨N₀, hE, hs⟩ := h
  obtain ⟨N₀', t0, e0⟩ := NetTr.of_equiv hE hT
  obtain ⟨k, M₁, M', h1, hL, hM, e1, t1⟩ := hΦ.step hI hI' hs t0
  obtain ⟨X, hX, eX⟩ := StepsEN.of_equiv e0 h1
  exact ⟨k, X, M', hX, hL, hM, eX.trans e1, t1⟩

/-- **Proposition 4 for reduction of graphs, with the lengths** (Lafont 1997, page 81: "If `Θ` is a
net built with symbols of `Σ` which reduces in `n` steps to `Θ'`, then `Φ(Θ)` reduces in `n'`
steps to `Φ(Θ')`, with `L n ≤ n' ≤ M n`"). Here `Θ` reduces up to wires in `n` interactions, and
`Φ(Θ')` is reached up to equivalence. The rules of `I` and of `I'` are linear. -/
theorem CompatibleWithin.stepsEN {I : System S} {I' : System S'}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    {Φ : Translation S S'} {L M : ℕ} (hΦ : Φ.CompatibleWithin I I' L M)
    {n : ℕ} {N M₀ : Net S ℕ} {N' : Net S' ℕ} (h : StepsEN I n N M₀) (hT : Φ.NetTr N N') :
    ∃ n' M₁ M', StepsEN I' n' N' M₁ ∧ L * n ≤ n' ∧ n' ≤ M * n ∧ Equiv M₁ M' ∧
      Φ.NetTr M₀ M' := by
  induction h with
  | refl => exact ⟨0, N', N', .refl _, by simp, by simp, Equiv.refl _, hT⟩
  | tail _ hs ih =>
    obtain ⟨n', M₁, M', h1, hL1, hM1, e1, t1⟩ := ih hT
    obtain ⟨k, M₂, M'', h2, hL2, hM2, e2, t2⟩ := hΦ.stepE hI hI' hs t1
    obtain ⟨X, hX, eX⟩ := StepsEN.of_equiv e1 h2
    refine ⟨n' + k, X, M'', h1.trans hX, ?_, ?_, eX.trans e2, t2⟩
    · rw [Nat.mul_succ]; omega
    · rw [Nat.mul_succ]; omega

end Translation

end INet
