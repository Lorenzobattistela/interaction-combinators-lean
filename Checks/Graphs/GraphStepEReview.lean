import Checks.Graphs.GraphStepECheck
import InteractionCombinators.Universality.RecursionFree.DecompositionLemmas

/-!
# Review of `Net.Linear.stepE_interact` (Lafont 1997, Section 1.2, page 73)

**Verdict: no defect.** The hypothesis `hI` (every rule of `I` is linear) of
`Net.Linear.stepE_interact` (`InteractionCombinators/Graphs/GraphStepE.lean`, PR #366) is
*necessary*: without it the statement is false (`stepE_interact_needs_linear`). It is not a
weakening. Lafont's rules are linear by definition (page 72: the right member `ν_{i,j}` is a net
with exactly `n_i + n_j` free ports, each a port of the net, so it occurs once), and
`System.WellFormed.linear` says the same. Issue #368 (the converse) may keep it.

What was checked, item by item of issue #369:

1. **Is `hI` necessary?** (proved) The signature `sigK` has `a` of arity `1` and `b`, `c` of
   arity `0`; the system `sysK` has one rule, `forget : a`–`b` with an empty right member, which
   is not linear (`forget_not_linear`). The net `a(c) = b` has no names, so it is linear, and it
   reduces by `Step` to the empty net (`N_step`): `Rule.inst` substitutes the trees into the
   right member, and the tree `c` disappears with the port that the rule does not mention. On
   its graph `G` (cells `a`, `c`, `b`), every `Interact` removes only the two cells `a`, `b`
   (`card_cells_le_of_interact`), so `c` stays; it does interact (`G_interact`, result `GAfter`:
   the cell `c` on the free port `5`). The empty net has only graphs without cells, so no
   result is `Iso` to one (`not_conclusion`). The two definitions part on non-linear rules only:
   `Step` erases (or, for a port used twice, copies) the plugged tree, `Interact` cuts the
   wires and glues, so it neither erases nor copies cells. Neither departs from page 73, which
   defines interaction only for linear rules; `Interact` is the closer reading of the figure
   (the `n_i + n_j` wires are attached to the ports of `ν_{i,j}`).
2. **Non-vacuity and port order** (proved). The figure of the combinator rules is Fig. 2, on
   page 81 (page 73 draws only the generic rule). I read the `γδ` rule there, with the lower and
   the upper cells drawn upside down (their first auxiliary port is on the right), and it is
   `ruleConDup`.
   * `con`–`con`: for every graph `G` of `4 = con(0, 1), 4 = con(2, 3)` (`wireText`, from
     `Checks/Graphs/GraphStepECheck.lean`) and every `H` the theorem can produce, `H` is exactly the
     graph with the wires `0–3`, `1–2` (`wireText_result_eq`), and `0–2` is not a wire
     (`wireText_not_in_order`): Lafont's exchange. Such `H` exist (`wireText_result_exists`).
   * `con`–`dup`: the graph `conDupResult` of the reduct `0 = dup(4, 5), 1 = dup(6, 7),
     2 = con(4, 6), 3 = con(5, 7)` is computed by hand, with its four contractions
     (`conDupAfter_hasGraph`). For every graph of `con(0, 1) = dup(2, 3)`, every `H` the theorem
     can produce is `Iso` to it, has the wiring of Fig. 2 read on the free ports
     (`ConDupShape`), and does not have the auxiliary ports of a `con` cell exchanged
     (`ConDupExchanged`) (`conDup_result`). Such `H` exist (`conDup_result_exists`).
3. **Hypotheses of the general lemmas** (read). `Interact.iso` assumes every port at an end of
   a wire of `G` is a port of a cell of `G`; this is `Graph.WF.portsIn`, which every graph of a
   net has (`Net.HasGraph.wf`), and it is used that way in the proof and here
   (`conDup_result`). `Contract.mapEnd` and `contracts_mapEnd` assume `f` sends names to names,
   which `End.map id g` does; `mapCell_cutEnd` assumes `τ` injective, `map_cutEnd_right` that
   `d ≠ c`, `map_cutEnd_of_ports` that the wires avoid the two cells; all hold where they are
   used (the two cells are `0`, `1`, the rest of the net is numbered from `2`). None can never
   hold. The proof sketch of the progress note matches the proof.

Not checked: whether `hI` could be weakened to linearity of the one rule that fires (it could,
the proof only uses `hI _ _ _ hr`; this is a matter of form, not of truth).
-/

namespace INet.GraphStepEReview

open Graph Term

/-! ## 1. The hypothesis that the rules are linear is necessary -/

/-- Three symbols: `a` of arity `1`, `b` and `c` of arity `0`. -/
inductive KSym : Type
  | a
  | b
  | c
  deriving DecidableEq

/-- The signature of `KSym`. -/
def sigK : Signature where
  Sym := KSym
  arity
    | .a => 1
    | _ => 0

instance : DecidableEq sigK.Sym := inferInstanceAs (DecidableEq KSym)

instance {ν : Type} [DecidableEq ν] : DecidableEq (Term sigK ν) := Comb.DecompositionCheck.termDecEq

/-- The symbol `a`, typed at `sigK.Sym`. -/
def symA : sigK.Sym := KSym.a
/-- The symbol `b`, typed at `sigK.Sym`. -/
def symB : sigK.Sym := KSym.b
/-- The symbol `c`, typed at `sigK.Sym`. -/
def symC : sigK.Sym := KSym.c

/-- The cell `c`, without auxiliary port. -/
def cC {ν : Type} : Term sigK ν := .app symC fun i => i.elim0
/-- The cell `b`, without auxiliary port. -/
def cB {ν : Type} : Term sigK ν := .app symB fun i => i.elim0
/-- The cell `a` with the tree `t` on its auxiliary port. -/
def cA {ν : Type} (t : Term sigK ν) : Term sigK ν := .app symA fun _ => t

/-- The rule `a`–`b` whose right member is empty: it forgets the auxiliary port of `a`. -/
def forget : Rule sigK 1 0 := ⟨0, 0⟩

/-- The system with the single rule `forget`. -/
def sysK : System sigK where
  rule
    | .a, .b => some forget
    | _, _ => none

/-- `forget` is not linear: the auxiliary port of `a` does not occur in its right member
(page 72 asks for `n_i + n_j` free ports). -/
theorem forget_not_linear : ¬ forget.Linear := fun h => by
  exact absurd (h.left 0) (by decide)

/-- The net `a(c) = b`. -/
def N : Net sigK ℕ := s(cA cC, cB) ::ₘ 0

theorem N_vars : Net.vars N = 0 := by decide

/-- `a(c) = b` is linear: it has no names. -/
theorem N_linear : N.Linear := fun x => by simp [N_vars]

/-- `a(c) = b` reduces by `forget` to the empty net: the tree `c` is erased with the port. -/
theorem N_step : Step sysK N 0 := by
  have := Step.mk (I := sysK) symA symB forget rfl (fun _ => cC) (fun i => i.elim0) 0
    (fun w => w.elim0) (fun w => w.elim0) (fun w => w.elim0)
  exact this

/-- The graph of `a(c) = b`: cells `0 : a`, `1 : c`, `2 : b`. -/
def G : Graph sigK ℕ := raw 0 [(cA cC, cB)]

theorem G_hasGraph : N.HasGraph G :=
  ⟨[(cA cC, cB)], 0, rfl, .refl, fun x => by
    rw [G, raw_count_name]
    exact (show (Net.ofList [(cA cC, cB)]).vars = 0 from N_vars) ▸ by simp⟩

theorem card_G : Multiset.card G.cells = 3 := by decide

/-- **An interaction removes two cells** and adds those of the rule. -/
theorem card_cells_le_of_interact {S : Signature} {I : System S} {G H : Graph S ℕ}
    (h : Interact I G H) : Multiset.card G.cells ≤ Multiset.card H.cells + 2 := by
  cases h with
  | mk c d α β C W n r hr R hR σ hσ hσG g hg hgW H hH hH1 =>
    rw [contracts_cells_eq hH]
    simp only [Multiset.card_cons, Multiset.card_add, Multiset.card_map]
    omega

/-- Every graph of the empty net has no cell. -/
theorem cells_of_hasGraph_zero {S : Signature} {H : Graph S ℕ} (h : (0 : Net S ℕ).HasGraph H) :
    H.cells = 0 := by
  obtain ⟨L, k, hL, hc, -⟩ := h
  have hL0 : L = [] := by
    have := congrArg Multiset.card hL
    simp only [Net.ofList, Multiset.card_zero, Multiset.coe_card, List.length_map] at this
    exact List.eq_nil_of_length_eq_zero this.symm
  subst hL0
  rw [contracts_cells_eq hc]
  rfl

/-- **The conclusion of `Net.Linear.stepE_interact` fails for `forget`** (page 73): no interaction
of the graph of `a(c) = b` is isomorphic to a graph of its reduct, the empty net. An interaction
keeps the cell `c` (it removes only `a` and `b`), and the empty net has no cell. -/
theorem not_conclusion :
    ¬ ∃ H H', Interact sysK G H ∧ (0 : Net sigK ℕ).HasGraph H' ∧ H.Iso H' := by
  rintro ⟨H, H', hI, hH', σ, -, hc, -, -⟩
  have h1 := card_cells_le_of_interact hI
  rw [cells_of_hasGraph_zero hH'] at hc
  have h2 : Multiset.card H.cells = 0 := by
    simpa using (congrArg Multiset.card hc).symm
  rw [card_G] at h1
  omega

/-- **The hypothesis `hI` of `Net.Linear.stepE_interact` cannot be dropped** (page 73): without
it the statement is false, on `sysK`, `a(c) = b` and its graph `G`. All the other hypotheses
hold there. -/
theorem stepE_interact_needs_linear :
    ¬ ∀ (I : System sigK) (N M : Net sigK ℕ), N.Linear → StepE I N M → ∀ G : Graph sigK ℕ,
      N.HasGraph G → ∃ H H', Interact I G H ∧ M.HasGraph H' ∧ H.Iso H' :=
  fun h => not_conclusion (h sysK N 0 N_linear N_step.stepE G G_hasGraph)

/-- Two graphs with the same components are equal. -/
theorem graphEq {S : Signature} {G H : Graph S ℕ} (hc : G.cells = H.cells)
    (hw : G.wires = H.wires) (hl : G.loops = H.loops) : G = H := by
  obtain ⟨C, W, n⟩ := G
  obtain ⟨C', W', n'⟩ := H
  simp only at hc hw hl
  rw [hc, hw, hl]

/-- `G`, written in the shape of the conclusion of `Interact.mk`. -/
theorem G_eq : G = ⟨(0, symA) ::ₘ (2, symB) ::ₘ {(1, symC)},
    s(.port 0 0, .port 2 0) ::ₘ {s(.port 0 1, .port 1 0)}, 0⟩ :=
  graphEq (by decide) (by decide) rfl

/-- The graph of `forget`: no cell, no wire. -/
theorem forget_hasGraph :
    forget.net.HasGraph (⟨0, 0, 0⟩ : Graph sigK (Fin 1 ⊕ Fin 0 ⊕ Fin 0)) :=
  ⟨[], 0, rfl, .refl, fun x => by
    change Multiset.count _ (0 : Multiset (End _)) ≤ 1
    simp⟩

/-- What the interaction on graphs gives: the cell `c`, its principal port on the free port `5`
that was the auxiliary port of `a`. -/
def GAfter : Graph sigK ℕ := ⟨{(1, symC)}, {s(.name 5, .port 1 0)}, 0⟩

/-- **The interaction on graphs keeps the tree** (page 73): `Interact` takes `G` to `GAfter`, which
has the cell `c` on a free port, while the step on texts erased it (`N_step`). -/
theorem G_interact : Interact sysK G GAfter := by
  rw [G_eq]
  refine Interact.mk (I := sysK) 0 2 symA symB {(1, symC)} {s(.port 0 1, .port 1 0)} 0 forget rfl _
    forget_hasGraph id (Set.injOn_id _) (fun x hx => by simp at hx) (fun _ => 5) ?_ ?_ GAfter
    ?_ (fun x => Multiset.nodup_iff_count_le_one.1 (by decide) _)
  · rintro (i | j | w) (i' | j' | w') -
    · exact congrArg _ (Subsingleton.elim (α := Fin 1) i i')
    all_goals first
      | exact j.elim0 | exact j'.elim0 | exact w.elim0 | exact w'.elim0
  · intro w
    show End.name 5 ∉ _
    decide
  · exact (graphEq (by decide) (by decide) rfl : _ = GAfter) ▸ .refl

/-! ## 2. Port order on the combinators -/

section Comb

open Comb GraphStepCheck GraphStepECheck

/-- `dup`, typed at `sig.Sym`. -/
abbrev sDup : sig.Sym := Comb.dup
/-- `con`, typed at `sig.Sym`. -/
abbrev sCon : sig.Sym := Comb.con

/-- The graph of `0 = 3, 1 = 2`: two wires, no cell. -/
def conConResult : Graph sig ℕ := ⟨0, s(.name 0, .name 3) ::ₘ {s(.name 1, .name 2)}, 0⟩

/-- The reduct `0 = 3, 1 = 2` of `wireText`. -/
def conConAfterText : CNet := s(var 0, var 3) ::ₘ s(var 1, var 2) ::ₘ 0

theorem conConAfterText_linear : conConAfterText.Linear := Net.linear_of_forall_mem (by decide)

theorem conConAfterText_hasGraph : conConAfterText.HasGraph conConResult :=
  ⟨[(var 0, var 3), (var 1, var 2)], 0, rfl, .refl, count_le_one_of_nodup (by decide)⟩

/-- **`con`–`con` exchanges the auxiliary ports, on graphs** (Fig. 2, page 81; page 73): for every
graph `G` of `4 = con(0, 1), 4 = con(2, 3)`, every `H` that `Net.Linear.stepE_interact` can
produce (an interaction of `G` isomorphic to a graph of the reduct) is exactly the graph with
the wires `0–3` and `1–2`. -/
theorem wireText_result_eq {G : Graph sig ℕ} (hG : wireText.HasGraph G) {H H' : Graph sig ℕ}
    (hI : Interact system G H) (hH' : conConAfterText.HasGraph H') (iH : H.Iso H') :
    H = conConResult := by
  have i₀ : H'.Iso conConResult :=
    Net.Linear.equiv_hasGraph_iso conConAfterText_linear (Equiv.refl _) hH' conConAfterText_hasGraph
  obtain ⟨σ, -, hc, hw, hl⟩ := (iH.trans i₀).symm (hI.wf hG.wf).portsIn
  exact graphEq (by rw [hc]; rfl) (by rw [hw]; rfl) hl

/-- The ports are not joined in order: `0–2` is not a wire of the result. -/
theorem wireText_not_in_order {G : Graph sig ℕ} (hG : wireText.HasGraph G) {H H' : Graph sig ℕ}
    (hI : Interact system G H) (hH' : conConAfterText.HasGraph H') (iH : H.Iso H') :
    s(.name 0, .name 2) ∉ H.wires := by
  rw [wireText_result_eq hG hI hH' iH]
  decide

/-- Non-vacuity: some graph of `wireText` and some `H`, `H'` meet the hypotheses above. -/
theorem wireText_result_exists : ∃ G H H', wireText.HasGraph G ∧ Interact system G H ∧
    conConAfterText.HasGraph H' ∧ H.Iso H' := by
  obtain ⟨G, hG, -⟩ := Net.exists_graph wireText
  obtain ⟨H, H', hI, hH', iH⟩ := Net.Linear.stepE_interact comb_linear wireText_linear
    wireText_stepE hG
  exact ⟨G, H, H', hG, hI, hH', iH⟩

/-! ### `con`–`dup` -/

/-- The net `con(0, 1) = dup(2, 3)`. -/
def conDupText : CNet := s(mkCon (var 0) (var 1), mkDup (var 2) (var 3)) ::ₘ 0

theorem conDupText_linear : conDupText.Linear := Net.linear_of_forall_mem (by decide)

/-- The reduct of `con(0, 1) = dup(2, 3)` by `ruleConDup`, with the new wires `4, 5, 6, 7`:
`0 = dup(4, 5), 1 = dup(6, 7), 2 = con(4, 6), 3 = con(5, 7)`. -/
def conDupAfterList : List (Term sig ℕ × Term sig ℕ) :=
  [(var 0, mkDup (var 4) (var 5)), (var 1, mkDup (var 6) (var 7)),
    (var 2, mkCon (var 4) (var 6)), (var 3, mkCon (var 5) (var 7))]

/-- The reduct, as a net. -/
def conDupAfter : CNet := Net.ofList conDupAfterList

theorem conDupAfter_linear : conDupAfter.Linear := Net.linear_of_forall_mem (by decide)

theorem conDup_step : Step system conDupText conDupAfter :=
  step_con_dup (var 0) (var 1) (var 2) (var 3) 0 4 5 6 7 (by decide) (by decide)

/-- The four new cells: `0`, `1` are `dup`, `2`, `3` are `con`. -/
def conDupCells : Multiset (ℕ × sig.Sym) :=
  (0, sDup) ::ₘ (1, sDup) ::ₘ (2, sCon) ::ₘ {(3, sCon)}

/-- The wires from the free ports to the principal ports of the new cells. -/
def conDupRoots : Multiset (Sym2 (End ℕ)) :=
  s(.name 0, .port 0 0) ::ₘ s(.name 1, .port 1 0) ::ₘ s(.name 2, .port 2 0) ::ₘ
    {s(.name 3, .port 3 0)}

/-- The graph of the reduct, computed by hand (Fig. 2, page 81): `dup` cell `0` on the free
port `0`, `dup` cell `1` on `1`, `con` cell `2` on `2`, `con` cell `3` on `3`; the first
auxiliary port of `0` to the first of `2`, its second to the first of `3`, the first of `1` to
the second of `2`, the second of `1` to the second of `3`. -/
def conDupResult : Graph sig ℕ :=
  ⟨conDupCells, s(.port 0 1, .port 2 1) ::ₘ s(.port 0 2, .port 3 1) ::ₘ
    s(.port 1 1, .port 2 2) ::ₘ s(.port 1 2, .port 3 2) ::ₘ conDupRoots, 0⟩

/-- After contracting `4`. -/
def conDupK₁ : Graph sig ℕ :=
  ⟨conDupCells, s(.port 0 1, .port 2 1) ::ₘ s(.name 5, .port 0 2) ::ₘ s(.name 5, .port 3 1) ::ₘ
    s(.name 6, .port 1 1) ::ₘ s(.name 6, .port 2 2) ::ₘ s(.name 7, .port 1 2) ::ₘ
    s(.name 7, .port 3 2) ::ₘ conDupRoots, 0⟩

/-- After contracting `4`, `5`. -/
def conDupK₂ : Graph sig ℕ :=
  ⟨conDupCells, s(.port 0 2, .port 3 1) ::ₘ s(.port 0 1, .port 2 1) ::ₘ
    s(.name 6, .port 1 1) ::ₘ s(.name 6, .port 2 2) ::ₘ s(.name 7, .port 1 2) ::ₘ
    s(.name 7, .port 3 2) ::ₘ conDupRoots, 0⟩

/-- After contracting `4`, `5`, `6`. -/
def conDupK₃ : Graph sig ℕ :=
  ⟨conDupCells, s(.port 1 1, .port 2 2) ::ₘ s(.port 0 2, .port 3 1) ::ₘ
    s(.port 0 1, .port 2 1) ::ₘ s(.name 7, .port 1 2) ::ₘ s(.name 7, .port 3 2) ::ₘ
    conDupRoots, 0⟩

theorem conDupAfter_hasGraph : conDupAfter.HasGraph conDupResult := by
  refine ⟨conDupAfterList, 0, rfl, ?_, count_le_one_of_nodup (by decide)⟩
  refine .tail (b := conDupK₃) (.tail (b := conDupK₂) (.tail (b := conDupK₁) (.single ?_) ?_) ?_)
    ?_
  · exact join_eq (H := conDupK₁) 4 (.port 0 1) (.port 2 1)
      (s(.name 5, .port 0 2) ::ₘ s(.name 5, .port 3 1) ::ₘ s(.name 6, .port 1 1) ::ₘ
        s(.name 6, .port 2 2) ::ₘ s(.name 7, .port 1 2) ::ₘ s(.name 7, .port 3 2) ::ₘ conDupRoots)
      (by decide) (by decide) rfl rfl
  · exact join_eq (G := conDupK₁) (H := conDupK₂) 5 (.port 0 2) (.port 3 1)
      (s(.port 0 1, .port 2 1) ::ₘ s(.name 6, .port 1 1) ::ₘ s(.name 6, .port 2 2) ::ₘ
        s(.name 7, .port 1 2) ::ₘ s(.name 7, .port 3 2) ::ₘ conDupRoots)
      (by decide) rfl rfl rfl
  · exact join_eq (G := conDupK₂) (H := conDupK₃) 6 (.port 1 1) (.port 2 2)
      (s(.port 0 2, .port 3 1) ::ₘ s(.port 0 1, .port 2 1) ::ₘ s(.name 7, .port 1 2) ::ₘ
        s(.name 7, .port 3 2) ::ₘ conDupRoots)
      (by decide) rfl rfl rfl
  · exact join_eq (G := conDupK₃) 7 (.port 1 2) (.port 3 2)
      (s(.port 1 1, .port 2 2) ::ₘ s(.port 0 2, .port 3 1) ::ₘ s(.port 0 1, .port 2 1) ::ₘ
        conDupRoots)
      (by decide) rfl (by decide) rfl

/-- The wiring of the `con`–`dup` commutation of Fig. 2 (page 81), read on a graph: four cells,
the `dup` cells on the free ports `0`, `1` (the auxiliary ports of `con`), the `con` cells on `2`,
`3` (those of `dup`), and their auxiliary ports joined as in the figure. -/
def ConDupShape (H : Graph sig ℕ) : Prop :=
  ∃ ca cb cc cd : ℕ, (ca, sDup) ∈ H.cells ∧ (cb, sDup) ∈ H.cells ∧
    (cc, sCon) ∈ H.cells ∧ (cd, sCon) ∈ H.cells ∧
    s(.name 0, .port ca 0) ∈ H.wires ∧ s(.name 1, .port cb 0) ∈ H.wires ∧
    s(.name 2, .port cc 0) ∈ H.wires ∧ s(.name 3, .port cd 0) ∈ H.wires ∧
    s(.port ca 1, .port cc 1) ∈ H.wires ∧ s(.port ca 2, .port cd 1) ∈ H.wires ∧
    s(.port cb 1, .port cc 2) ∈ H.wires ∧ s(.port cb 2, .port cd 2) ∈ H.wires

/-- The shape with the auxiliary ports of a `con` cell exchanged: the first auxiliary port of the
cell on `0` goes to the *second* auxiliary port of the cell on `2`. -/
def ConDupExchanged (H : Graph sig ℕ) : Prop :=
  ∃ ca ∈ H.cells.map Prod.fst, ∃ cc ∈ H.cells.map Prod.fst,
    s(.name 0, .port ca 0) ∈ H.wires ∧ s(.name 2, .port cc 0) ∈ H.wires ∧
    s(.port ca 1, .port cc 2) ∈ H.wires

theorem mem_map_mapCell {σ : ℕ → ℕ} {W : Multiset (Sym2 (End ℕ))} {p q : End ℕ}
    (h : s(p, q) ∈ W) : s(End.mapCell σ p, End.mapCell σ q) ∈ W.map (Sym2.map (End.mapCell σ)) :=
  Multiset.mem_map.2 ⟨_, h, rfl⟩

theorem mem_map_cell {σ : ℕ → ℕ} {C : Multiset (ℕ × sig.Sym)} {c : ℕ} {α : sig.Sym}
    (h : (c, α) ∈ C) : (σ c, α) ∈ C.map (Prod.map σ id) :=
  Multiset.mem_map.2 ⟨_, h, rfl⟩

/-- The shape is kept by isomorphism. -/
theorem ConDupShape.iso {G H : Graph sig ℕ} (h : ConDupShape G) (i : G.Iso H) : ConDupShape H := by
  obtain ⟨σ, -, hc, hw, -⟩ := i
  obtain ⟨ca, cb, cc, cd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  unfold ConDupShape
  rw [hc, hw]
  exact ⟨σ ca, σ cb, σ cc, σ cd, mem_map_cell h1, mem_map_cell h2, mem_map_cell h3,
    mem_map_cell h4, mem_map_mapCell h5, mem_map_mapCell h6, mem_map_mapCell h7,
    mem_map_mapCell h8, mem_map_mapCell h9, mem_map_mapCell h10, mem_map_mapCell h11,
    mem_map_mapCell h12⟩

/-- The exchanged shape is kept by isomorphism. -/
theorem ConDupExchanged.iso {G H : Graph sig ℕ} (h : ConDupExchanged G) (i : G.Iso H) :
    ConDupExchanged H := by
  obtain ⟨σ, -, hc, hw, -⟩ := i
  obtain ⟨ca, hca, cc, hcc, h1, h2, h3⟩ := h
  unfold ConDupExchanged
  rw [hc, hw, Multiset.map_map]
  refine ⟨σ ca, ?_, σ cc, ?_, mem_map_mapCell h1, mem_map_mapCell h2, mem_map_mapCell h3⟩
  · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hca
    exact Multiset.mem_map.2 ⟨p, hp, rfl⟩
  · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hcc
    exact Multiset.mem_map.2 ⟨p, hp, rfl⟩

theorem conDupResult_shape : ConDupShape conDupResult := by
  refine ⟨0, 1, 2, 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [conDupResult, conDupCells, conDupRoots] <;> decide

theorem conDupResult_not_exchanged : ¬ ConDupExchanged conDupResult := by
  rintro ⟨ca, -, cc, -, h1, h2, h3⟩
  simp [conDupResult, conDupRoots] at h1 h2
  subst h1 h2
  revert h3
  decide

/-- **`con`–`dup` on graphs has the wiring of Fig. 2** (page 81; page 73): for every graph `G` of
`con(0, 1) = dup(2, 3)`, every `H` that `Net.Linear.stepE_interact` can produce has the shape of
the figure, is isomorphic to `conDupResult`, and does not have the auxiliary ports of a `con`
cell exchanged. -/
theorem conDup_result {G : Graph sig ℕ} (hG : conDupText.HasGraph G) {H H' : Graph sig ℕ}
    (hI : Interact system G H) (hH' : conDupAfter.HasGraph H') (iH : H.Iso H') :
    conDupResult.Iso H ∧ ConDupShape H ∧ ¬ ConDupExchanged H := by
  have i₀ : H'.Iso conDupResult :=
    Net.Linear.equiv_hasGraph_iso conDupAfter_linear (Equiv.refl _) hH' conDupAfter_hasGraph
  have i₁ : H.Iso conDupResult := iH.trans i₀
  have i₂ : conDupResult.Iso H := i₁.symm (hI.wf hG.wf).portsIn
  exact ⟨i₂, conDupResult_shape.iso i₂, fun h => conDupResult_not_exchanged (h.iso i₁)⟩

/-- Non-vacuity: the theorem produces such `H`, `H'` for every graph of `con(0, 1) = dup(2, 3)`. -/
theorem conDup_result_exists {G : Graph sig ℕ} (hG : conDupText.HasGraph G) :
    ∃ H H', Interact system G H ∧ conDupAfter.HasGraph H' ∧ H.Iso H' :=
  Net.Linear.stepE_interact comb_linear conDupText_linear conDup_step.stepE hG

end Comb

end INet.GraphStepEReview
