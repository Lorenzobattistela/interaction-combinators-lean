import InteractionCombinators.Graphs.GraphStepEConverse
import Checks.Graphs.GraphStepEConverseCheck
import Checks.Graphs.GraphStepEReview

/-!
# Review of `Graph.interact_unique` and `Net.Linear.interact_stepE` (Lafont 1997, page 73)

Issue #373, on PR #372. **No defect found.** Both statements say what page 73 says, and every
hypothesis of `Graph.interact_unique` tried here is needed.

What was checked, against page 73 (Section 1.2, the figure of an interaction rule, read at
150 dpi):

1. **`interact_unique` fixes the pair.** The graph is written
   `⟨(c, α) ::ₘ (d, β) ::ₘ C, s(port c 0, port d 0) ::ₘ W, n⟩` once, and both interactions use the
   same `c`, `d`, `C`, `W`, `n`. In a well-formed graph a principal port ends one wire, so `c`, `d`
   determine the wire between them, and `C`, `W` are what is left: two different active pairs
   cannot be confused. What may differ is exactly what `Interact` chooses and the paper does not:
   the graph `R` of the rule, the renumbering `σ` of its cells, and the fresh names `g`. The order
   of the pair is fixed too: reading the pair as `d, c` uses the rule for `β, α`, which page 73
   relates to the rule for `α, β` by `ν̄`. That is `System.WellFormed.symm` and `unique`, and is not
   the business of this theorem. Because of this the theorem does not by itself say that *every*
   interaction of a graph gives one result; section 1 does this for three graphs, by inverting
   `Interact` (`pair_inv`) and applying `interact_unique` once for each order.
2. **Hand computations, where the two cells share a second wire** (section 1). Each result was
   computed by hand first, then by the contractions, and `interact_unique` turns it into the result
   of *every* interaction of the graph:
   * `con(x, y) = con(y, x)` (the auxiliary ports joined crosswise): exactly two cyclic wires
     (`conConCross_result`);
   * `dup(x, y) = dup(x, y)` (two shared wires, ports in order): exactly two cyclic wires
     (`dupDupClosed_result`);
   * `con(x, y) = con(x, y)`: exactly one cyclic wire (`conConClosed_result`), as in
     `GraphStepCheck.conCon_closed`. With the previous item, this shows the exchange of the
     auxiliary ports of `con`–`con` (page 71, Fig. 2) and not of `dup`–`dup`.
   No counterexample.
3. **Non-vacuity with different choices** (section 2). `era`–`con` (`ruleEraBin`, two cells in the
   rule) fired twice with different graphs of the rule (`raw 0`, `raw 5`), different renumberings
   (`· + 10`, `id`) and different fresh names (`4, 5` and `7, 8`): `eraCon_unique` applies
   `interact_unique` to them.
4. **The hypotheses** (section 3). Each of the following can be dropped from `interact_unique`
   only at the price of a counterexample, the other hypotheses holding:
   * `hrl` (a linear rule): with `GraphStepEReview.forget`, which loses a port, the fresh name of
     the lost port stays free, so two choices of `g` give graphs with different free ports
     (`forget_not_unique`);
   * `hgW` (fresh names away from `W`): with fresh names equal to the free ports `0`, `1`, one
     contraction order leaves no cyclic wire, another leaves two (`clash_not_unique`);
   * `hg` (injective names): with both fresh names `4`, two contraction orders join the free ports
     either to the erasers or to each other (`noninj_not_unique`);
   * `n₁`, `n₂` (contract to the end): the uncontracted graph is not isomorphic to the result
     (`eraCon_uncontracted_not_iso`).
   Not tested: `hG` (`Graph.WF`) and `hσ`, `hσG`. `hσG` asks that the cells of the rule avoid `c`,
   `d` as well as `C`; avoiding `c`, `d` is not needed, since the cut has already removed their
   ports from `W` and `R` is renamed by `End.map`, not cut, but it can always be met, so it costs
   nothing.
5. **`Net.Linear.interact_stepE`.** Its hypotheses are those of `Interact` plus linear rules `hI`
   and a linear net `N` with graph `G`. An argument for `hI`, not formalized here: the net
   `a(c) = b` of `GraphStepEReview` has no free port, and `GraphStepEReview.G_interact` takes its
   graph by `forget` to a graph with the free port `5`; a `StepE` of a net without free ports
   should give a net without free ports, and `Iso` keeps free ports, so the conclusion would fail.
   `hN` was not tested. The conclusion
   `∃ M H', StepE I N M ∧ M.HasGraph H' ∧ H.Iso H'` is the converse of
   `Net.Linear.stepE_interact` with the same notion of equality of graphs. Its hypotheses hold in
   `Checks/Graphs/GraphStepEConverseCheck.lean` (`conConFree_interact_stepE`,
   `dupDupShared_interact_stepE`). Nothing was found to refute it; it was not tested on a net with
   more than one active pair.
-/

namespace INet.GraphStepEConverseReview

open Comb Graph GraphReview GraphStepCheck GraphStepECheck

/-! ## 1. Every interaction of a two-cell graph -/

/-- **Inverting the shape of `Interact` on a graph of two cells `0`, `1`.** The pair of
`Interact.mk` is `0, 1` or `1, 0`, and the rest of the graph is the rest. -/
theorem pair_inv {c d : ℕ} {α β x y : sig.Sym} {C : Multiset (ℕ × sig.Sym)}
    {W W₀ : Multiset (Sym2 (End ℕ))} {n n₀ : ℕ}
    (h : (⟨(c, α) ::ₘ (d, β) ::ₘ C, s(.port c 0, .port d 0) ::ₘ W, n⟩ : Graph sig ℕ) =
      ⟨(0, x) ::ₘ (1, y) ::ₘ 0, s(.port 0 0, .port 1 0) ::ₘ W₀, n₀⟩) :
    C = 0 ∧ W = W₀ ∧ n = n₀ ∧
      ((c = 0 ∧ d = 1 ∧ α = x ∧ β = y) ∨ (c = 1 ∧ d = 0 ∧ α = y ∧ β = x)) := by
  simp only [Graph.mk.injEq] at h
  obtain ⟨hc, hw, rfl⟩ := h
  have hC : C = 0 := by
    have := congrArg Multiset.card hc
    simp only [Multiset.card_cons, Multiset.card_zero] at this
    exact Multiset.card_eq_zero.1 (by omega)
  subst hC
  have key : (c = 0 ∧ d = 1 ∧ α = x ∧ β = y) ∨ (c = 1 ∧ d = 0 ∧ α = y ∧ β = x) := by
    rcases Multiset.cons_eq_cons.1 hc with ⟨h1, h2⟩ | ⟨-, cs, h1, h2⟩
    · rw [Prod.mk.injEq] at h1
      rw [Multiset.cons_zero, Multiset.cons_zero, Multiset.singleton_inj, Prod.mk.injEq] at h2
      exact .inl ⟨h1.1, h2.1, h1.2, h2.2⟩
    · have hcs : cs = 0 := by
        have := congrArg Multiset.card h1
        simp only [Multiset.card_cons, Multiset.card_zero] at this
        exact Multiset.card_eq_zero.1 (by omega)
      subst hcs
      rw [Multiset.cons_zero, Multiset.cons_zero, Multiset.singleton_inj, Prod.mk.injEq] at h1 h2
      exact .inr ⟨h2.1.symm, h1.1, h2.2.symm, h1.2⟩
  refine ⟨rfl, ?_, rfl, key⟩
  rcases key with ⟨rfl, rfl, -, -⟩ | ⟨rfl, rfl, -, -⟩
  · exact (Multiset.cons_inj_right _).1 hw
  · rw [Sym2.eq_swap] at hw
    exact (Multiset.cons_inj_right _).1 hw

/-- **Every interaction of a closed pair of like cells has one result** (page 73). Let the graph
have two cells `0 : x`, `1 : x` joined by their principal ports, the other wires `W₀` and no cyclic
wire. If the interaction with the rule `r` of `x, x`, a graph `R` of it without cells, no
renumbering and the names `g` contracts to `K` both for the pair `0, 1` and for the pair `1, 0`,
then every interaction of the graph gives a graph isomorphic to `K`. -/
theorem every_result {x : sig.Sym} {r : Rule sig (sig.arity x) (sig.arity x)}
    (hr : system.rule x x = some r)
    {R : Graph sig (Fin (sig.arity x) ⊕ Fin (sig.arity x) ⊕ Fin r.internal)}
    (hR : r.net.HasGraph R) (hRc : R.cells = 0) {W₀ : Multiset (Sym2 (End ℕ))}
    (hwf : Graph.WF (⟨(0, x) ::ₘ (1, x) ::ₘ 0, s(.port 0 0, .port 1 0) ::ₘ W₀, 0⟩ : Graph sig ℕ))
    {g : Fin (sig.arity x) ⊕ Fin (sig.arity x) ⊕ Fin r.internal → ℕ} (hg : Function.Injective g)
    (hgW : ∀ w, End.name (g w) ∉ W₀.bind wireEnds) {K : Graph sig ℕ}
    (h01 : Relation.ReflTransGen Contract (preInteract 0 1 0 W₀ 0 R id g) K)
    (h10 : Relation.ReflTransGen Contract (preInteract 1 0 0 W₀ 0 R id g) K)
    (hK : ∀ z, K.ends.count (.name z) ≤ 1) {H : Graph sig ℕ}
    (h : Interact system ⟨(0, x) ::ₘ (1, x) ::ₘ 0, s(.port 0 0, .port 1 0) ::ₘ W₀, 0⟩ H) :
    H.Iso K := by
  generalize hG : (⟨(0, x) ::ₘ (1, x) ::ₘ 0, s(.port 0 0, .port 1 0) ::ₘ W₀, 0⟩ : Graph sig ℕ)
    = G at h
  obtain ⟨c, d, α, β, C, W, n, r', hr', R', hR', σ, hσ, hσG, g', hg', hgW', H, hH, hH1⟩ := h
  have hwf' := hG ▸ hwf
  obtain ⟨rfl, rfl, rfl, hcd⟩ := pair_inv hG.symm
  have hσR : ∀ z ∈ R.cells.map Prod.fst, False := fun z hz => by simp [hRc] at hz
  rcases hcd with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · obtain rfl := Option.some.inj (hr.symm.trans hr')
    exact interact_unique hwf' (comb_linear _ _ _ hr) hR' hR hσ hσG (Set.injOn_id _)
      (fun z hz => (hσR z hz).elim) hg' hgW' hg hgW hH hH1 h01 hK
  · obtain rfl := Option.some.inj (hr.symm.trans hr')
    exact interact_unique hwf' (comb_linear _ _ _ hr) hR' hR hσ hσG (Set.injOn_id _)
      (fun z hz => (hσR z hz).elim) hg' hgW' hg hgW hH hH1 h10 hK

/-- A graph isomorphic to a graph without cells and wires is that graph. -/
theorem eq_of_iso_loops {H : Graph sig ℕ} {k : ℕ} (h : H.Iso ⟨0, 0, k⟩) : H = ⟨0, 0, k⟩ := by
  obtain ⟨σ, -, hc, hw, hl⟩ := h
  obtain ⟨HC, HW, Hn⟩ := H
  simp only at hc hw hl
  rw [Multiset.map_eq_zero.1 hc.symm, Multiset.map_eq_zero.1 hw.symm, hl]

/-- `con`, typed at `sig.Sym`. -/
abbrev sCon : sig.Sym := Comb.con
/-- `dup`, typed at `sig.Sym`. -/
abbrev sDup : sig.Sym := Comb.dup
/-- `era`, typed at `sig.Sym`. -/
abbrev sEra : sig.Sym := Comb.era

/-- Two cyclic wires and nothing else. -/
def twoLoops : Graph sig ℕ := ⟨0, 0, 2⟩

/-! ### `con(x, y) = con(y, x)` -/

/-- The auxiliary ports joined crosswise: `l0 – r1`, `l1 – r0`. -/
def crossW : Multiset (Sym2 (End ℕ)) := s(.port 0 1, .port 1 2) ::ₘ {s(.port 0 2, .port 1 1)}

/-- The graph of `con(x, y) = con(y, x)`. -/
def conConCross : Graph sig ℕ :=
  ⟨(0, sCon) ::ₘ (1, sCon) ::ₘ 0, s(.port 0 0, .port 1 0) ::ₘ crossW, 0⟩

/-- The pair `0, 1` of `conConCross`, by hand: the cut gives `2–5`, `3–4`, the rule `ruleConCon`
gives `2–5`, `3–4` again (it exchanges the ports, as the crossing did), so two cycles. -/
theorem conConCross_01 :
    Relation.ReflTransGen Contract (preInteract 0 1 0 crossW 0 (raw 0 conConText) id (fresh 2))
      twoLoops := by
  refine .head (join_eq (H := ⟨0, s(.name 5, .name 5) ::ₘ s(.name 3, .name 4) ::ₘ
      {s(.name 3, .name 4)}, 0⟩) 2 (.name 5) (.name 5)
      (s(.name 3, .name 4) ::ₘ {s(.name 3, .name 4)}) (by decide) rfl rfl rfl) ?_
  refine .head (loop_eq (H := ⟨0, s(.name 3, .name 4) ::ₘ {s(.name 3, .name 4)}, 1⟩) 5 _ rfl rfl
    rfl rfl) ?_
  refine .head (join_eq (H := ⟨0, {s(.name 4, .name 4)}, 1⟩) 3 (.name 4) (.name 4) 0
    (by decide) rfl (by decide) rfl) ?_
  exact .single (loop_eq 4 0 rfl rfl rfl rfl)

/-- The pair `1, 0` of `conConCross`: the cut gives `4–3`, `5–2`, the rule `2–5`, `3–4`. -/
theorem conConCross_10 :
    Relation.ReflTransGen Contract (preInteract 1 0 0 crossW 0 (raw 0 conConText) id (fresh 2))
      twoLoops := by
  refine .head (join_eq (H := ⟨0, s(.name 5, .name 5) ::ₘ s(.name 4, .name 3) ::ₘ
      {s(.name 3, .name 4)}, 0⟩) 2 (.name 5) (.name 5)
      (s(.name 4, .name 3) ::ₘ {s(.name 3, .name 4)}) (by decide) rfl rfl rfl) ?_
  refine .head (loop_eq (H := ⟨0, s(.name 4, .name 3) ::ₘ {s(.name 3, .name 4)}, 1⟩) 5 _ rfl rfl
    rfl rfl) ?_
  refine .head (join_eq (H := ⟨0, {s(.name 4, .name 4)}, 1⟩) 3 (.name 4) (.name 4) 0
    (by decide) rfl (by decide) rfl) ?_
  exact .single (loop_eq 4 0 rfl rfl rfl rfl)

/-- **Every interaction of `con(x, y) = con(y, x)` gives exactly two cyclic wires** (page 73). -/
theorem conConCross_result {H : Graph sig ℕ} (h : Interact system conConCross H) :
    H = twoLoops :=
  eq_of_iso_loops (every_result (x := sCon) (r := ruleConCon) rfl conCon_hasGraph rfl
    ((wf_iff _).2 (by decide)) (fresh_injective 2) (by decide) conConCross_01 conConCross_10
    (count_le_one_of_nodup (by decide)) h)

/-! ### `dup(x, y) = dup(x, y)` -/

/-- The auxiliary ports joined in order: `l0 – r0`, `l1 – r1`. -/
def closedW : Multiset (Sym2 (End ℕ)) := s(.port 0 1, .port 1 1) ::ₘ {s(.port 0 2, .port 1 2)}

/-- The graph of `dup(x, y) = dup(x, y)`: two `dup` cells sharing two wires. -/
def dupDupClosed : Graph sig ℕ :=
  ⟨(0, sDup) ::ₘ (1, sDup) ::ₘ 0, s(.port 0 0, .port 1 0) ::ₘ closedW, 0⟩

/-- The pair `0, 1` of `dupDupClosed`: the cut gives `2–4`, `3–5`, the rule `ruleDupDup` gives
`2–4`, `3–5`, so two cycles. -/
theorem dupDupClosed_01 :
    Relation.ReflTransGen Contract (preInteract 0 1 0 closedW 0 (raw 0 dupDupText) id (fresh 2))
      twoLoops := by
  refine .head (join_eq (H := ⟨0, s(.name 4, .name 4) ::ₘ s(.name 3, .name 5) ::ₘ
      {s(.name 3, .name 5)}, 0⟩) 2 (.name 4) (.name 4)
      (s(.name 3, .name 5) ::ₘ {s(.name 3, .name 5)}) (by decide) rfl rfl rfl) ?_
  refine .head (loop_eq (H := ⟨0, s(.name 3, .name 5) ::ₘ {s(.name 3, .name 5)}, 1⟩) 4 _ rfl rfl
    rfl rfl) ?_
  refine .head (join_eq (H := ⟨0, {s(.name 5, .name 5)}, 1⟩) 3 (.name 5) (.name 5) 0
    (by decide) rfl (by decide) rfl) ?_
  exact .single (loop_eq 5 0 rfl rfl rfl rfl)

/-- The pair `1, 0` of `dupDupClosed`: the cut gives `4–2`, `5–3`, the rule `2–4`, `3–5`. -/
theorem dupDupClosed_10 :
    Relation.ReflTransGen Contract (preInteract 1 0 0 closedW 0 (raw 0 dupDupText) id (fresh 2))
      twoLoops := by
  refine .head (join_eq (H := ⟨0, s(.name 4, .name 4) ::ₘ s(.name 5, .name 3) ::ₘ
      {s(.name 3, .name 5)}, 0⟩) 2 (.name 4) (.name 4)
      (s(.name 5, .name 3) ::ₘ {s(.name 3, .name 5)}) (by decide) rfl rfl rfl) ?_
  refine .head (loop_eq (H := ⟨0, s(.name 5, .name 3) ::ₘ {s(.name 3, .name 5)}, 1⟩) 4 _ rfl rfl
    rfl rfl) ?_
  refine .head (join_eq (H := ⟨0, {s(.name 5, .name 5)}, 1⟩) 3 (.name 5) (.name 5) 0
    (by decide) rfl (by decide) rfl) ?_
  exact .single (loop_eq 5 0 rfl rfl rfl rfl)

/-- **Every interaction of `dup(x, y) = dup(x, y)` gives exactly two cyclic wires** (page 73). -/
theorem dupDupClosed_result {H : Graph sig ℕ} (h : Interact system dupDupClosed H) :
    H = twoLoops :=
  eq_of_iso_loops (every_result (x := sDup) (r := ruleDupDup) rfl dupDup_hasGraph rfl
    ((wf_iff _).2 (by decide)) (fresh_injective 2) (by decide) dupDupClosed_01 dupDupClosed_10
    (count_le_one_of_nodup (by decide)) h)

/-! ### `con(x, y) = con(x, y)` -/

/-- The pair `0, 1` of `conConClosed`: the cut gives `2–4`, `3–5`, the rule `2–5`, `3–4`: one
cycle `2 – 4 – 3 – 5 – 2`. -/
theorem conConClosed_01 :
    Relation.ReflTransGen Contract
      (preInteract 0 1 0 conConClosedW 0 (raw 0 conConText) id (fresh 2)) conConClosedAfter := by
  refine .head (join_eq (H := ⟨0, s(.name 4, .name 5) ::ₘ s(.name 3, .name 5) ::ₘ
      {s(.name 3, .name 4)}, 0⟩) 2 (.name 4) (.name 5)
      (s(.name 3, .name 5) ::ₘ {s(.name 3, .name 4)}) (by decide) rfl rfl rfl) ?_
  refine .head (join_eq (H := ⟨0, s(.name 5, .name 3) ::ₘ {s(.name 3, .name 5)}, 0⟩) 4
      (.name 5) (.name 3) {s(.name 3, .name 5)} (by decide) rfl rfl rfl) ?_
  refine .head (join_eq (H := ⟨0, {s(.name 3, .name 3)}, 0⟩) 5 (.name 3) (.name 3) 0
      (by decide) rfl rfl rfl) ?_
  exact .single (loop_eq 3 0 rfl rfl rfl rfl)

/-- The pair `1, 0` of `conConClosed`: the cut gives `4–2`, `5–3`, the rule `2–5`, `3–4`. -/
theorem conConClosed_10 :
    Relation.ReflTransGen Contract
      (preInteract 1 0 0 conConClosedW 0 (raw 0 conConText) id (fresh 2)) conConClosedAfter := by
  refine .head (join_eq (H := ⟨0, s(.name 4, .name 5) ::ₘ s(.name 5, .name 3) ::ₘ
      {s(.name 3, .name 4)}, 0⟩) 2 (.name 4) (.name 5)
      (s(.name 5, .name 3) ::ₘ {s(.name 3, .name 4)}) (by decide) rfl rfl rfl) ?_
  refine .head (join_eq (H := ⟨0, s(.name 5, .name 4) ::ₘ {s(.name 4, .name 5)}, 0⟩) 3
      (.name 5) (.name 4) {s(.name 4, .name 5)} (by decide) rfl rfl rfl) ?_
  refine .head (join_eq (H := ⟨0, {s(.name 4, .name 4)}, 0⟩) 5 (.name 4) (.name 4) 0
      (by decide) rfl rfl rfl) ?_
  exact .single (loop_eq 4 0 rfl rfl rfl rfl)

/-- **Every interaction of `con(x, y) = con(x, y)` gives exactly one cyclic wire** (page 73),
where `dup(x, y) = dup(x, y)` gives two (`dupDupClosed_result`). -/
theorem conConClosed_result {H : Graph sig ℕ} (h : Interact system conConClosed H) :
    H = conConClosedAfter :=
  eq_of_iso_loops (every_result (x := sCon) (r := ruleConCon) rfl conCon_hasGraph rfl
    ((wf_iff _).2 (by decide)) (fresh_injective 2) (by decide) conConClosed_01 conConClosed_10
    (count_le_one_of_nodup (by decide)) h)

/-! ## 2. Two interactions with different choices -/

/-- The names of `ruleEraBin`: no auxiliary port on the eraser, two on the other cell. -/
abbrev EN : Type := Fin 0 ⊕ Fin 2 ⊕ Fin 0

/-- A text of `ruleEraBin`: `era = r0, era = r1`. -/
def eraText : List (Term sig EN × Term sig EN) :=
  [(mkEra, .var (.inr (.inl 0))), (mkEra, .var (.inr (.inl 1)))]

/-- The raw graph of `ruleEraBin` with its cells numbered from `0` is a graph of it. -/
theorem eraBin_hasGraph0 : ruleEraBin.net.HasGraph (raw 0 eraText) :=
  ⟨eraText, 0, rfl, .refl, by decide⟩

/-- The raw graph of `ruleEraBin` with its cells numbered from `5` is another graph of it. -/
theorem eraBin_hasGraph5 : ruleEraBin.net.HasGraph (raw 5 eraText) :=
  ⟨eraText, 5, rfl, .refl, by decide⟩

/-- Fresh names `k`, `k + 1` for the two auxiliary ports of the second cell. -/
def freshE (k : ℕ) : EN → ℕ :=
  Sum.elim (fun i => i.elim0) (Sum.elim (fun j => k + j) fun i => i.elim0)

theorem freshE_injective (k : ℕ) : Function.Injective (freshE k) := by
  rintro (i | j | w) (i' | j' | w') h
  all_goals first
    | exact i.elim0 | exact i'.elim0 | exact w.elim0 | exact w'.elim0
    | exact congrArg _ (congrArg _ (Fin.ext (by simpa [freshE] using h)))

/-- The other wires of `eraCon`: the auxiliary ports of `con` on the free ports `0`, `1`. -/
def eraConW : Multiset (Sym2 (End ℕ)) := s(.port 1 1, .name 0) ::ₘ {s(.port 1 2, .name 1)}

/-- The graph of `era = con(0, 1)`. -/
def eraCon : Graph sig ℕ :=
  ⟨(0, sEra) ::ₘ (1, sCon) ::ₘ 0, s(.port 0 0, .port 1 0) ::ₘ eraConW, 0⟩

theorem eraCon_wf : eraCon.WF := (wf_iff _).2 (by decide)

/-- The result with the erasers numbered `10`, `11`. -/
def eraConAfter₁ : Graph sig ℕ :=
  ⟨(10, sEra) ::ₘ {(11, sEra)}, s(.name 1, .port 11 0) ::ₘ {s(.name 0, .port 10 0)}, 0⟩

/-- The result with the erasers numbered `5`, `6`. -/
def eraConAfter₂ : Graph sig ℕ :=
  ⟨(5, sEra) ::ₘ {(6, sEra)}, s(.name 1, .port 6 0) ::ₘ {s(.name 0, .port 5 0)}, 0⟩

theorem add10_injOn (s : Set ℕ) : Set.InjOn (· + 10) s := fun a _ b _ h => by
  simpa using h

/-- The first interaction of `eraCon`: the graph `raw 0` of the rule, renumbered by `· + 10`,
fresh names `4, 5`. The contractions erase `4`, `5`. -/
theorem eraCon_contracts₁ :
    Relation.ReflTransGen Contract (preInteract 0 1 0 eraConW 0 (raw 0 eraText) (· + 10)
      (freshE 4)) eraConAfter₁ := by
  refine .head (join_eq (H := ⟨(10, sEra) ::ₘ {(11, sEra)}, s(.name 0, .port 10 0) ::ₘ
      s(.name 5, .name 1) ::ₘ {s(.port 11 0, .name 5)}, 0⟩) 4 (.name 0) (.port 10 0)
      (s(.name 5, .name 1) ::ₘ {s(.port 11 0, .name 5)}) (by decide) (by decide) rfl rfl) ?_
  exact .single (join_eq 5 (.name 1) (.port 11 0) {s(.name 0, .port 10 0)} (by decide)
    (by decide) rfl rfl)

/-- The second interaction of `eraCon`: the graph `raw 5` of the rule, not renumbered, fresh
names `7, 8`. -/
theorem eraCon_contracts₂ :
    Relation.ReflTransGen Contract (preInteract 0 1 0 eraConW 0 (raw 5 eraText) id
      (freshE 7)) eraConAfter₂ := by
  refine .head (join_eq (H := ⟨(5, sEra) ::ₘ {(6, sEra)}, s(.name 0, .port 5 0) ::ₘ
      s(.name 8, .name 1) ::ₘ {s(.port 6 0, .name 8)}, 0⟩) 7 (.name 0) (.port 5 0)
      (s(.name 8, .name 1) ::ₘ {s(.port 6 0, .name 8)}) (by decide) (by decide) rfl rfl) ?_
  exact .single (join_eq 8 (.name 1) (.port 6 0) {s(.name 0, .port 5 0)} (by decide)
    (by decide) rfl rfl)

/-- The first interaction is an `Interact` of `eraCon` (page 73). -/
theorem eraCon_interact : Interact system eraCon eraConAfter₁ :=
  Interact.mk (I := system) 0 1 sEra sCon 0 eraConW 0 ruleEraBin rfl (raw 0 eraText)
    eraBin_hasGraph0 (· + 10) (add10_injOn _) (by decide) (freshE 4) (freshE_injective 4)
    (by decide) eraConAfter₁ eraCon_contracts₁ (count_le_one_of_nodup (by decide))

/-- **Non-vacuity of `Graph.interact_unique` with different choices** (page 73). The two
interactions of `era = con(0, 1)` use different graphs of the rule (`raw 0`, `raw 5`), different
renumberings (`· + 10`, `id`) and different fresh names (`4, 5`, `7, 8`); every hypothesis holds
and the theorem gives their results isomorphic. -/
theorem eraCon_unique : eraConAfter₁.Iso eraConAfter₂ :=
  interact_unique (α := sEra) (β := sCon) eraCon_wf (comb_linear _ _ _ rfl) eraBin_hasGraph0
    eraBin_hasGraph5 (add10_injOn _) (by decide) (Set.injOn_id _) (by decide)
    (freshE_injective 4) (by decide) (freshE_injective 7) (by decide) eraCon_contracts₁
    (count_le_one_of_nodup (by decide)) eraCon_contracts₂ (count_le_one_of_nodup (by decide))

/-! ## 3. The hypotheses of `interact_unique` -/

/-- **`n₁` cannot be dropped** (page 73): the graph before contraction is not isomorphic to the
result. It has four wires, the result two. -/
theorem eraCon_uncontracted_not_iso :
    ¬ (preInteract 0 1 0 eraConW 0 (raw 5 eraText) id (freshE 7)).Iso eraConAfter₂ := by
  rintro ⟨σ, -, -, hw, -⟩
  have h := congrArg Multiset.card hw
  rw [Multiset.card_map] at h
  revert h
  decide

/-- With the fresh names `0, 1`, which are the free ports of `eraCon`, every hypothesis of
`interact_unique` holds except `hgW`. -/
theorem clash_not_hgW : ¬ ∀ w, End.name (freshE 0 w) ∉ eraConW.bind wireEnds := by decide

/-- Joining the clashing names to the erasers: no cyclic wire. -/
def clashA : Graph sig ℕ :=
  ⟨(5, sEra) ::ₘ {(6, sEra)}, s(.name 1, .port 6 0) ::ₘ {s(.name 0, .port 5 0)}, 0⟩

/-- Closing the clashing names on themselves: two cyclic wires. -/
def clashB : Graph sig ℕ :=
  ⟨(5, sEra) ::ₘ {(6, sEra)}, s(.port 5 0, .name 0) ::ₘ {s(.port 6 0, .name 1)}, 2⟩

/-- **`hgW` cannot be dropped** (page 73). With the fresh names `0, 1` of the free ports, the cut
makes the wires `0–0` and `1–1`, and the name `0` ends three wires. Joining `0–0` with the eraser
gives `clashA`, closing it gives `clashB`, which has two cyclic wires more. Both are contracted to
the end, and they are not isomorphic. -/
theorem clash_not_unique :
    Relation.ReflTransGen Contract (preInteract 0 1 0 eraConW 0 (raw 5 eraText) id (freshE 0))
      clashA ∧ (∀ x, clashA.ends.count (.name x) ≤ 1) ∧
    Relation.ReflTransGen Contract (preInteract 0 1 0 eraConW 0 (raw 5 eraText) id (freshE 0))
      clashB ∧ (∀ x, clashB.ends.count (.name x) ≤ 1) ∧ ¬ clashA.Iso clashB := by
  refine ⟨?_, count_le_one_of_nodup (by decide), ?_, count_le_one_of_nodup (by decide), ?_⟩
  · refine .head (join_eq (H := ⟨(5, sEra) ::ₘ {(6, sEra)}, s(.name 0, .port 5 0) ::ₘ
        s(.name 1, .name 1) ::ₘ {s(.port 6 0, .name 1)}, 0⟩) 0 (.name 0) (.port 5 0)
        (s(.name 1, .name 1) ::ₘ {s(.port 6 0, .name 1)}) (by decide) (by decide) rfl rfl) ?_
    exact .single (join_eq 1 (.name 1) (.port 6 0) {s(.name 0, .port 5 0)} (by decide)
      (by decide) rfl rfl)
  · refine .head (loop_eq (H := ⟨(5, sEra) ::ₘ {(6, sEra)}, s(.name 1, .name 1) ::ₘ
        s(.port 5 0, .name 0) ::ₘ {s(.port 6 0, .name 1)}, 1⟩) 0
        (s(.name 1, .name 1) ::ₘ s(.port 5 0, .name 0) ::ₘ {s(.port 6 0, .name 1)}) (by decide)
        (by decide) rfl rfl) ?_
    exact .single (loop_eq 1 (s(.port 5 0, .name 0) ::ₘ {s(.port 6 0, .name 1)}) rfl rfl rfl rfl)
  · rintro ⟨σ, -, -, -, hl⟩
    exact absurd hl (by decide)

/-- Both auxiliary ports of `con` get the fresh name `4`. -/
def same4 : EN → ℕ := fun _ => 4

/-- With the fresh names both `4`, every hypothesis of `interact_unique` holds except `hg`. -/
theorem same4_not_injective : ¬ Function.Injective same4 := fun h =>
  absurd (h (a₁ := .inr (.inl 0)) (a₂ := .inr (.inl 1)) rfl) (by decide)

/-- Joining the free ports to each other and the erasers to each other. -/
def sameB : Graph sig ℕ :=
  ⟨(5, sEra) ::ₘ {(6, sEra)}, s(.port 5 0, .port 6 0) ::ₘ {s(.name 0, .name 1)}, 0⟩

/-- **`hg` cannot be dropped** (page 73). With both fresh names `4`, the name `4` ends four wires,
`4–0`, `4–1`, `era₅–4`, `era₆–4`. Joining `0` with `era₅` gives `eraConAfter₂`; joining `0` with
`1` gives `sameB`, where the two erasers face each other. Both are contracted to the end, and they
are not isomorphic: `sameB` has a wire between two free ports, `eraConAfter₂` none. -/
theorem noninj_not_unique :
    Relation.ReflTransGen Contract (preInteract 0 1 0 eraConW 0 (raw 5 eraText) id same4)
      eraConAfter₂ ∧
    Relation.ReflTransGen Contract (preInteract 0 1 0 eraConW 0 (raw 5 eraText) id same4)
      sameB ∧ (∀ x, sameB.ends.count (.name x) ≤ 1) ∧ ¬ eraConAfter₂.Iso sameB := by
  refine ⟨?_, ?_, count_le_one_of_nodup (by decide), ?_⟩
  · refine .head (join_eq (H := ⟨(5, sEra) ::ₘ {(6, sEra)}, s(.name 0, .port 5 0) ::ₘ
        s(.name 4, .name 1) ::ₘ {s(.port 6 0, .name 4)}, 0⟩) 4 (.name 0) (.port 5 0)
        (s(.name 4, .name 1) ::ₘ {s(.port 6 0, .name 4)}) (by decide) (by decide) rfl rfl) ?_
    exact .single (join_eq 4 (.name 1) (.port 6 0) {s(.name 0, .port 5 0)} (by decide)
      (by decide) rfl rfl)
  · refine .head (join_eq (H := ⟨(5, sEra) ::ₘ {(6, sEra)}, s(.name 0, .name 1) ::ₘ
        s(.port 5 0, .name 4) ::ₘ {s(.port 6 0, .name 4)}, 0⟩) 4 (.name 0) (.name 1)
        (s(.port 5 0, .name 4) ::ₘ {s(.port 6 0, .name 4)}) (by decide) (by decide) rfl rfl) ?_
    exact .single (join_eq 4 (.port 5 0) (.port 6 0) {s(.name 0, .name 1)} (by decide)
      (by decide) (by decide) rfl)
  · rintro ⟨σ, -, -, hw, -⟩
    have hm : s(End.name 0, End.name 1) ∈ sameB.wires := by decide
    rw [hw] at hm
    simp [eraConAfter₂, End.mapCell] at hm

section forget

open GraphStepEReview

/-- The graph of `a(c) = b` in the shape of `Interact.mk`, before contraction, with the fresh
name `k` for the auxiliary port of `a` (`forget` has no cell and no wire). -/
def forgetPre (k : ℕ) : Graph sigK ℕ :=
  preInteract 0 2 {(1, symC)} {s(.port 0 1, .port 1 0)} 0
    (⟨0, 0, 0⟩ : Graph sigK (Fin 1 ⊕ Fin 0 ⊕ Fin 0)) id (fun _ => k)

/-- The result with the fresh name `k`: the cell `c` on the free port `k`. -/
def forgetAfter (k : ℕ) : Graph sigK ℕ := ⟨{(1, symC)}, {s(.name k, .port 1 0)}, 0⟩

/-- A constant on the one name of `forget` is injective. -/
theorem const_injective (k : ℕ) : Function.Injective (fun _ : Fin 1 ⊕ Fin 0 ⊕ Fin 0 => k) := by
  rintro (i | j | w) (i' | j' | w') -
  · exact congrArg _ (Subsingleton.elim (α := Fin 1) i i')
  all_goals first
    | exact j.elim0 | exact j'.elim0 | exact w.elim0 | exact w'.elim0

/-- **`hrl` cannot be dropped** (page 73). `forget` is not linear (`forget_not_linear`): it loses
the auxiliary port of `a`. Every other hypothesis of `interact_unique` holds for the graph of
`a(c) = b` with the fresh names `5` and `6`, and the two results are not isomorphic: the free
port of the cell `c` is `5` in one and `6` in the other, and `Iso` keeps free ports. -/
theorem forget_not_unique :
    G.WF ∧ (∀ k : ℕ, Function.Injective (fun _ : Fin 1 ⊕ Fin 0 ⊕ Fin 0 => k)) ∧
    (∀ k : ℕ, End.name k ∉ ({s(.port 0 1, .port 1 0)} : Multiset (Sym2 (End ℕ))).bind wireEnds) ∧
    (∀ k, Relation.ReflTransGen Contract (forgetPre k) (forgetAfter k)) ∧
    (∀ k x, (forgetAfter k).ends.count (.name x) ≤ 1) ∧
    ¬ (forgetAfter 5).Iso (forgetAfter 6) := by
  refine ⟨G_hasGraph.wf, const_injective, fun k => ?_, fun k => ?_, fun k x => ?_, fun h => ?_⟩
  · simp [wireEnds]
  · exact (graphEq rfl rfl rfl : forgetPre k = forgetAfter k) ▸ .refl
  · by_cases hx : x = k
    · subst hx
      simp [forgetAfter, Graph.ends]
    · simp [forgetAfter, Graph.ends, hx]
  · have := h.count_name 5
    revert this
    decide

end forget

end INet.GraphStepEConverseReview
