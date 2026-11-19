import InteractionCombinators.Lafont.PairStepE
import InteractionCombinators.Lafont.TranslationCompReview
import InteractionCombinators.Combinators

/-!
# Review of `L = M = 1` for an invertible translation (page 81)

Checks of `Lafont/SimulationInvertible.lean` and `Lafont/PairStepE.lean`.

* `Translation.Invertible.length_eq_one` — the reading of the paper where `L` and `M` are the
  minimal and maximal lengths of *all* the reductions of a pair to a translation of the right
  member: with distinct names on the ports, every such reduction has length `1`. The library
  states the existence of one reduction of length `1` (`CompatibleWithin I I' 1 1`); the lemmas
  of the library give the stronger reading too.
* A non-degenerate instance of `Translation.Invertible.compatibleWithin_one_of_wellFormed`: the
  translation `permTr (swap 0 1)` of the one symbol of arity `2` to itself with its two auxiliary
  ports exchanged, which is not the identity, and the system `parSys` with one rule, where two
  cells joined by their principal ports are replaced by two wires joining their auxiliary ports in
  order. The system is well-formed and `permTr (swap 0 1)` is compatible with it.
* The hypotheses of `PairStepE.stepE_pair_not_hasCut_of` are needed:
  - distinct names: the pair `con(5, 1) = dup(5, 3)` of the combinators, with the name `5` on an
    auxiliary port of each cell, reduces in one interaction up to wires to a net with a cut. The
    interaction is done on the net `con(5, 1) = dup(6, 3), 6 = 5`, where a wire joins an auxiliary
    port of each cell, which is the same graph;
  - reduced rules: in a system whose one rule has the right member `w = α, w = α`, linear but not
    reduced, the pair `α = α` reduces to a net with a cut;
  - a closed wire `a = a` cannot occur in the right member of a linear reduced rule
    (`Rule.not_loop_of_reduced`).
-/

namespace INet

open Term

/-! ## Every reduction has length `1` -/

/-- **Every reduction of the pair to a translation of the right member has length `1`** (Lafont
1997, page 81: "if `Φ` is invertible, the reduction must be of length 1"). Let `Φ` be invertible,
`I` and `I'` well-formed. If the translations of the two cells of a rule of `I`, with pairwise
distinct names on their ports, reduce up to wires in `n` interactions to a net that is the same
graph as a translation of the right member, then `n = 1`. -/
theorem Translation.Invertible.length_eq_one {S S' : Signature}
    {Φ : Translation S S'} {I : System S} {I' : System S'}
    (hΦ : Φ.Invertible) (hI : I.WellFormed) (hI' : I'.WellFormed)
    {α β : S.Sym} {r : Rule S (S.arity α) (S.arity β)} (hr : I.rule α β = some r)
    {xs : Fin (S.arity α) → ℕ} {ys : Fin (S.arity β) → ℕ} (hx : Function.Injective xs)
    (hy : Function.Injective ys) (hxy : ∀ i j, xs i ≠ ys j)
    (f : Fin (Φ.net α).internal → ℕ) (g : Fin (Φ.net β).internal → ℕ)
    {n : ℕ} {M N' : Net S' ℕ} {h : Fin r.internal → ℕ}
    (hs : StepsEN I' n (s((Φ.net α).inst (fun i => .var (xs i)) f,
      (Φ.net β).inst (fun j => .var (ys j)) g) ::ₘ 0) M)
    (hE : Equiv M N') (hT : Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N') :
    n = 1 := by
  rcases hs.cases_head with ⟨rfl, rfl⟩ | ⟨K, m, rfl, h1, h2⟩
  · exact absurd hE (not_equiv_pair_of_strict hΦ.strict hI hr hx hy hxy f g hT)
  · rcases h2.cases_head with ⟨rfl, -⟩ | ⟨K', m', rfl, h3, -⟩
    · rfl
    · obtain ⟨α', ρ, hρ⟩ := hΦ.inst_eq α
      obtain ⟨β', σ, hσ⟩ := hΦ.inst_eq β
      rw [hρ, hσ] at h1
      exact absurd h3.hasCut (hI'.stepE_pair_not_hasCut (hx.comp ρ.injective)
        (hy.comp σ.injective) (fun i j => hxy _ _) h1)

end INet

namespace INet.SimulationInvertibleReview

open Term Comb TranslationCompReview

/-! ## A translation that is not the identity -/

/-- The exchange of the two auxiliary ports. -/
abbrev sw : _root_.Equiv.Perm (Fin 2) := _root_.Equiv.swap 0 1

/-- `permTr sw` is not the identity translation: the first auxiliary port of the cell is the
second port of the net. -/
theorem permTr_sw_ne_id : (permTr sw).net (star 2) ≠ (Translation.id (sigN 2)).net (star 2) := by
  intro h
  have h1 := congrArg (fun p : PNet (sigN 2) 2 => p.inst (fun i => .var (i : ℕ)) fun _ => 0) h
  change (Term.app (star 2) fun i => Term.var ((sw i : Fin 2) : ℕ) : Term (sigN 2) ℕ) =
    Term.app (star 2) fun i => Term.var ((i : Fin 2) : ℕ) at h1
  simp only [Term.app.injEq, heq_eq_eq, true_and] at h1
  have h0 := congrFun h1 (0 : Fin 2)
  simp at h0

/-- The rule of `parSys`: the auxiliary port `i` of the first cell is joined to the auxiliary
port `i` of the second. -/
def rulePar : Rule (sigN 2) 2 2 :=
  ⟨0, s(.var (.inl 0), .var (.inr (.inl 0))) ::ₘ {s(.var (.inl 1), .var (.inr (.inl 1)))}⟩

/-- A system on the one symbol of arity `2`, with one rule. -/
def parSys : System (sigN 2) := ⟨fun _ _ => some rulePar⟩

theorem rulePar_linear : rulePar.Linear := by
  constructor
  · intro i; fin_cases i <;> simp [rulePar]
  · intro j; fin_cases j <;> simp [rulePar]
  · intro w; exact w.elim0

theorem rulePar_reduced : rulePar.Reduced := by
  intro e he
  unfold rulePar at he
  dsimp only at he
  rcases Multiset.mem_cons.1 he with rfl | he
  · exact ⟨.inl 0, _, rfl, by simp⟩
  obtain rfl := Multiset.mem_singleton.1 he
  exact ⟨.inl 1, _, rfl, by simp⟩

theorem rulePar_swap : rulePar.swap.net = rulePar.net := by
  change (s(Term.var (.inr (.inl 0)), Term.var (.inl 0)) ::ₘ
      {s(Term.var (.inr (.inl 1)), Term.var (.inl 1))} :
      Net (sigN 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 0)) =
    s(Term.var (.inl 0), Term.var (.inr (.inl 0))) ::ₘ
      {s(Term.var (.inl 1), Term.var (.inr (.inl 1)))}
  exact congrArg₂ (fun x y => (x ::ₘ {y} : Net (sigN 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 0)))
    Sym2.eq_swap Sym2.eq_swap

/-- `parSys` is an interaction system in the sense of Lafont (page 72). -/
theorem parSys_wellFormed : parSys.WellFormed where
  linear _ _ r h := by cases h; exact rulePar_linear
  reduced _ _ r h := by cases h; exact rulePar_reduced
  unique α β hne _ := absurd (Subsingleton.elim (α := Unit) α β) hne
  symm _ r h := by cases h; exact Rule.symm_of_equiv (Equiv.of_eq rulePar_swap)

/-- **`permTr sw` is a translation of `parSys` into itself** (Lafont 1997, page 81): the pair
`α(x₁, x₀) = α(y₁, y₀)` of the translated cells reduces in one interaction to `x₁ = y₁, x₀ = y₀`,
which is the right member `x₀ = y₀, x₁ = y₁` of the rule. -/
theorem permTr_sw_compatible : (permTr sw).Compatible parSys parSys := by
  intro α β r hr xs ys f g hlin
  cases hr
  have hst : Step parSys
      (s((permTr sw).net α |>.inst (fun i => .var (xs i)) f,
        (permTr sw).net β |>.inst (fun j => .var (ys j)) g) ::ₘ 0)
      (rulePar.inst (fun i => .var (xs (sw i))) (fun j => .var (ys (sw j))) Fin.elim0 + 0) :=
    Step.mk (I := parSys) () () rulePar rfl (fun i => .var (xs (sw i)))
      (fun j => .var (ys (sw j))) 0 Fin.elim0 (fun a => a.elim0) (fun a => a.elim0)
  have hN : rulePar.inst (fun i => .var (xs (sw i))) (fun j => .var (ys (sw j))) Fin.elim0 + 0 =
      rulePar.inst (fun i => .var (xs i)) (fun j => .var (ys j)) Fin.elim0 := by
    simp only [rulePar, Rule.inst, Net.bind, add_zero]
    exact Multiset.pair_comm _ _
  refine ⟨_, _, Fin.elim0, (Steps.single hst).stepsE, Equiv.of_eq hN, ?_, ?_⟩
  · exact Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, .var _, .var _⟩
      (Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, .var _, .var _⟩ Multiset.Rel.zero)
  · intro y
    have := hlin y
    change ((∑ i : Fin 2, ({xs (sw i)} : Multiset ℕ)) +
      (∑ j : Fin 2, ({ys (sw j)} : Multiset ℕ)) + 0).count y ≤ 2 at this
    simp [rulePar, Rule.inst, Net.bind, Multiset.count_cons, Fin.sum_univ_two,
      Multiset.count_singleton] at this ⊢
    omega

/-- **A non-degenerate instance of `compatibleWithin_one_of_wellFormed`** (Lafont 1997, page 81):
an invertible translation that is not the identity, and a well-formed system with a rule. -/
example : (permTr sw).CompatibleWithin parSys parSys 1 1 :=
  (permTr_invertible sw).compatibleWithin_one_of_wellFormed parSys_wellFormed parSys_wellFormed
    permTr_sw_compatible

/-! ## The hypotheses of `stepE_pair_not_hasCut_of` are needed -/

/-- The pair `con(5, 1) = dup(5, 3)`: the name `5` is on an auxiliary port of each cell, so the
names of the two cells are not disjoint. -/
abbrev pairShared : Net sig ℕ := s(mkCon (.var 5) (.var 1), mkDup (.var 5) (.var 3)) ::ₘ 0

/-- The same graph with a wire `6 = 5` between an auxiliary port of each cell. -/
abbrev pairWire : Net sig ℕ :=
  s(mkCon (.var 5) (.var 1), mkDup (.var 6) (.var 3)) ::ₘ s(.var 6, .var 5) ::ₘ 0

theorem pairShared_equiv : Equiv pairShared pairWire := by
  have hlin : Net.Linear
      (s(.var 6, .var 5) ::ₘ s(mkCon (.var 5) (.var 1), mkDup (.var 6) (.var 3)) ::ₘ 0 :
        Net sig ℕ) := by
    intro y
    simp [Multiset.count_cons, Multiset.count_singleton]
    split_ifs <;> omega
  have W := Wire.mk 6 (.var 5) (mkCon (.var 5) (.var 1)) (mkDup (.var 6) (.var 3)) 0 hlin
    (by simp)
  have e : (s((mkCon (.var 5) (.var 1)).subst 6 (.var 5),
      (mkDup (.var 6) (.var 3)).subst 6 (.var 5)) ::ₘ 0 : Net sig ℕ) = pairShared := by
    have h1 : (mkCon (.var 5) (.var 1)).subst 6 (.var 5) = mkCon (.var 5) (.var 1) := by
      unfold mkCon Term.subst
      change Term.app _ _ = Term.app _ _
      congr 1
      funext i
      fin_cases i <;> rfl
    have h2 : (mkDup (.var 6) (.var 3)).subst 6 (.var 5) = mkDup (.var 5) (.var 3) := by
      unfold mkDup Term.subst
      change Term.app _ _ = Term.app _ _
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [h1, h2]
  rw [← e]
  exact W.equiv.symm.trans (Equiv.of_eq (Multiset.cons_swap _ _ _))

/-- The net reached from `pairWire` by the `con`–`dup` interaction, with the new wires
`10, 11, 12, 13`. -/
abbrev afterShared : Net sig ℕ :=
  s(.var 5, mkDup (.var 10) (.var 11)) ::ₘ s(.var 1, mkDup (.var 12) (.var 13)) ::ₘ
    s(.var 6, mkCon (.var 10) (.var 12)) ::ₘ s(.var 3, mkCon (.var 11) (.var 13)) ::ₘ
    s(.var 6, .var 5) ::ₘ 0

theorem pairWire_step : Step system pairWire afterShared := by
  have h := Step.mk (I := system) con dup ruleConDup rfl ![.var 5, .var 1] ![.var 6, .var 3]
    (s(.var 6, .var 5) ::ₘ 0) (fun i => 10 + (i : ℕ))
    (fun a b hab => Fin.ext (by simpa using hab))
    (by decide)
  have e : (ruleConDup.inst ![.var 5, .var 1] ![.var 6, .var 3] (fun i : Fin 4 => 10 + (i : ℕ)) +
      (s(.var 6, .var 5) ::ₘ 0) : Net sig ℕ) = afterShared := by
    rw [inst_conDup]
    simp
  rw [← e]
  exact h

/-- **Disjoint names are needed in `stepE_pair_not_hasCut_of`** (Lafont 1997, page 80: the two
cells of a rule have distinct ports). The pair `con(5, 1) = dup(5, 3)` reduces in one interaction
up to wires to a net with a cut: the interaction is done on `pairWire`, the same graph with a wire
between an auxiliary port of each cell, and the `dup` copied onto `5` meets the `con` copied onto
`6`. -/
theorem pairShared_stepE_hasCut : ∃ K, StepE system pairShared K ∧ K.HasCut := by
  refine ⟨afterShared, ⟨_, pairShared_equiv, pairWire_step⟩, ?_⟩
  have hlin : afterShared.Linear :=
    pairWire_step.linear system_wellFormed.linear (pairShared_equiv.linear (by
      intro y
      simp [Multiset.count_cons, Multiset.count_singleton]
      split_ifs <;> omega))
  refine Net.ChainCut.hasCut ⟨mkDup (.var 10) (.var 11), mkCon (.var 10) (.var 12), [5, 6],
    s(.var 1, mkDup (.var 12) (.var 13)) ::ₘ s(.var 3, mkCon (.var 11) (.var 13)) ::ₘ 0,
    ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ?_⟩ hlin
  decide

/-- The cell of the one symbol of arity `0`. -/
abbrev star0 : Term (sigN 0) ℕ := .app (star 0) ![]

/-- A rule whose right member `w = α, w = α` is linear and not reduced: it has a cut. -/
def ruleBad : Rule (sigN 0) 0 0 :=
  ⟨1, s(.var (.inr (.inr 0)), .app (star 0) ![]) ::ₘ {s(.var (.inr (.inr 0)), .app (star 0) ![])}⟩

/-- A system on the one symbol of arity `0` whose one rule is `ruleBad`. -/
def badSys : System (sigN 0) := ⟨fun _ _ => some ruleBad⟩

theorem ruleBad_linear : ruleBad.Linear :=
  ⟨fun i => i.elim0, fun j => j.elim0, fun w => by fin_cases w; decide⟩

/-- **Reduced rules are needed in `stepE_pair_not_hasCut_of`** (Lafont 1997, page 72: the right
member of a rule is reduced). The rule of `badSys` is linear and not reduced, and the pair
`α = α` reduces in one interaction to `0 = α, 0 = α`, which has a cut. -/
theorem badSys_counterexample :
    (∀ α β r, badSys.rule α β = some r → r.Linear) ∧
    ¬ (∀ α β r, badSys.rule α β = some r → r.Reduced) ∧
    ∃ K, StepE badSys (s(star0, star0) ::ₘ 0) K ∧ K.HasCut := by
  have hv : star0.vars = 0 := by
    decide
  refine ⟨fun _ _ r h => ?_, fun h => ?_, ?_⟩
  · cases h
    exact ruleBad_linear
  · have hm : (s(Term.var (Sum.inr (Sum.inr (0 : Fin 1))), Term.app (star 0) ![]) :
        Sym2 (Term (sigN 0) (Fin 0 ⊕ Fin 0 ⊕ Fin 1))) ∈ ruleBad.net :=
      by simp only [ruleBad]; exact Multiset.mem_cons_self _ _
    obtain ⟨p, t, he, hp⟩ := h () () ruleBad rfl _ hm
    rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨-, h1⟩
    · cases h1
      exact hp _ rfl
    · cases h1
  · have hs : Step badSys (s(star0, star0) ::ₘ 0)
        (ruleBad.inst ![] ![] (fun _ => 0) + 0) :=
      Step.mk (I := badSys) () () ruleBad rfl ![] ![] 0 (fun _ => 0)
        (fun a b _ => Subsingleton.elim (α := Fin 1) a b) (by decide)
    have hb : ∀ σ : Fin 0 ⊕ Fin 0 ⊕ Fin 1 → Term (sigN 0) ℕ,
        (Term.app (star 0) ![] : Term (sigN 0) (Fin 0 ⊕ Fin 0 ⊕ Fin 1)).bind σ = star0 := by
      intro σ
      unfold Term.bind
      congr 1
      funext i
      exact Fin.elim0 (i : Fin 0)
    have e : (ruleBad.inst ![] ![] (fun _ => 0) + 0 : Net (sigN 0) ℕ) =
        s(.var 0, star0) ::ₘ s(.var 0, star0) ::ₘ 0 := by
      simp [ruleBad, Rule.inst, Net.bind, hb]
    rw [e] at hs
    refine ⟨_, hs.stepE, Net.ChainCut.hasCut ⟨star0, star0, [0], 0, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩,
      ?_⟩ ?_⟩
    · simp [Cut.chain, Sym2.eq_swap]
    · intro y
      simp [Multiset.count_cons, Multiset.count_singleton, hv]
      split_ifs <;> omega

/-- **A linear reduced rule has no closed wire `a = a`** (Lafont 1997, page 72): each equation of
the right member has an auxiliary port on one side, which occurs once. So the closed wires that
`stepE_pair_not_hasCut_of` meets come from the wire substitution, not from the rule. -/
theorem _root_.INet.Rule.not_loop_of_reduced {S : Signature} {a b : ℕ} {r : Rule S a b}
    (hl : r.Linear) (hr : r.Reduced) (p : Fin a ⊕ Fin b ⊕ Fin r.internal) :
    s(Term.var p, Term.var p) ∉ r.net := by
  intro hm
  obtain ⟨q, t, he, hq⟩ := hr _ hm
  have hpq : p = q := by
    rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨-, h1⟩ <;> cases h1 <;> rfl
  subst hpq
  have h2 := Multiset.count_le_of_le p
    (show eqVars s(Term.var p, Term.var p) ≤ Net.vars r.net from Multiset.le_bind _ hm)
  simp only [eqVars_mk, Term.vars_var, Multiset.count_add, Multiset.count_singleton_self] at h2
  rcases p with i | j | w
  · rw [hl.left i] at h2; omega
  · rw [hl.right j] at h2; omega
  · exact hq w rfl

end INet.SimulationInvertibleReview
