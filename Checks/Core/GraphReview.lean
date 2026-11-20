import InteractionCombinators.Core.Graph
import InteractionCombinators.Core.Combinators

/-!
# Review of `Graph.lean` against Lafont 1997, Section 1.1, page 71

Attempts to refute the definitions of `InteractionCombinators/Core/Graph.lean`, on small graphs and
texts of the interaction combinators.

* `Graph.WF` is decided through `WFb`, an equivalent condition that quantifies only over the
  cells and the ends of the graph (`wf_iff`). The graphs Lafont allows on page 71 are well formed
  (two auxiliary ports of one cell joined, a wire between two free ports, a cyclic wire, a cell
  of arity `0`, a vicious circle, the empty net); the configurations he does not allow are not
  (a name ending two wires, a port ending no wire, a wire from a port or a name to itself, a port
  number beyond the arity, two cells with one identity).
* `Graph.Iso` identifies two graphs that differ by the order of the wires and the numbers of the
  cells, and does not identify graphs that differ by the exchange of the two auxiliary ports of a
  `con` cell, by the number of cyclic wires, or by a free name.
* `Net.HasGraph` gives the expected graph of `r = con(x, x)`, of the chain `x = y, y = z`, of
  `x = x` and of `x = con(x, y)`. On the non-linear text `x = a, x = b, x = c` it holds of two
  graphs that are not `Iso`: uniqueness needs linearity.
* With names of type `Empty`, a closed vicious circle of two `con` cells is well formed but is the
  graph of no text: "every well-formed graph is a net" needs enough names.
-/

namespace INet.GraphReview

open Comb Graph

variable {S : Signature} {ν : Type} [DecidableEq ν]

/-! ## A decidable form of `Graph.WF` -/

/-- An end is acceptable: a port is a port of a cell of the graph, a name ends at most one
wire. -/
def okEnd (G : Graph S ν) : End ν → Bool
  | .port c i => decide (Multiset.card (G.cells.filter (fun p => p.1 = c ∧ i ≤ S.arity p.2)) ≠ 0)
  | .name x => decide (G.ends.count (.name x) ≤ 1)

/-- `Graph.WF` with quantifiers over the cells and the ends of the graph only. -/
def WFb (G : Graph S ν) : Prop :=
  (G.cells.map Prod.fst).Nodup ∧
    (∀ p ∈ G.cells, ∀ i, i ≤ S.arity p.2 → G.ends.count (.port p.1 i) = 1) ∧
    ∀ e ∈ G.ends, okEnd G e = true

instance (G : Graph S ν) : Decidable (WFb G) := by unfold WFb; infer_instance

/-- `Graph.WF` (page 71) is equivalent to the decidable `WFb`: it is enough to look at the cells
and at the ends of the wires. -/
theorem wf_iff (G : Graph S ν) : G.WF ↔ WFb G := by
  constructor
  · rintro ⟨hn, hp, hc, hx⟩
    refine ⟨hn, fun p hp' i hi => hp p.1 p.2 hp' i hi, fun e he => ?_⟩
    cases e with
    | port c i =>
      obtain ⟨α, hα, hi⟩ := hc c i he
      simp only [okEnd, ne_eq, Multiset.card_eq_zero, Multiset.filter_eq_nil,
        not_forall, not_not, decide_eq_true_eq]
      exact ⟨(c, α), hα, rfl, hi⟩
    | name x => simpa [okEnd] using hx x
  · rintro ⟨hn, hp, he⟩
    refine ⟨hn, fun c α h i hi => hp (c, α) h i hi, fun c i h => ?_, fun x => ?_⟩
    · have := he _ h
      simp only [okEnd, ne_eq, Multiset.card_eq_zero, Multiset.filter_eq_nil, not_forall, not_not,
        decide_eq_true_eq] at this
      obtain ⟨p, hp', rfl, hi⟩ := this
      exact ⟨p.2, hp', hi⟩
    · by_cases h : End.name x ∈ G.ends
      · simpa [okEnd] using he _ h
      · rw [Multiset.count_eq_zero_of_notMem h]
        exact Nat.zero_le _

/-! ## Graphs that are nets (page 71) -/

/-- A `con` cell whose two auxiliary ports are joined by a wire, its principal port free. The
picture of page 71 has such a cell (the `α` in the middle). -/
def auxJoined : Graph sig ℕ :=
  ⟨{(0, Comb.con)}, s(.port 0 1, .port 0 2) ::ₘ {s(.port 0 0, .name 0)}, 0⟩

/-- Page 71: a wire may connect two ports of the same cell. -/
theorem auxJoined_wf : auxJoined.WF := (wf_iff _).2 (by decide)

/-- A wire between two free ports, and nothing else. -/
def freeWire : Graph sig ℕ := ⟨0, {s(.name 0, .name 1)}, 0⟩

/-- Page 71: a wire may join two free ports. -/
theorem freeWire_wf : freeWire.WF := (wf_iff _).2 (by decide)

/-- One cyclic wire. -/
def cyclic : Graph sig ℕ := ⟨0, 0, 1⟩

/-- Page 71: cyclic wires, which connect no port, are allowed. -/
theorem cyclic_wf : cyclic.WF := (wf_iff _).2 (by decide)

/-- An `era` cell (arity `0`) with its principal port free. -/
def eraFree : Graph sig ℕ := ⟨{(0, Comb.era)}, {s(.port 0 0, .name 0)}, 0⟩

/-- Page 71: a cell of arity `0` has only its principal port. -/
theorem eraFree_wf : eraFree.WF := (wf_iff _).2 (by decide)

/-- A vicious circle: the principal port of a `con` cell joined to its first auxiliary port, the
second one free. -/
def vicious : Graph sig ℕ :=
  ⟨{(0, Comb.con)}, s(.port 0 0, .port 0 1) ::ₘ {s(.port 0 2, .name 0)}, 0⟩

/-- A vicious circle is a net (page 71). -/
theorem vicious_wf : vicious.WF := (wf_iff _).2 (by decide)

/-- A vicious circle through two cells: the principal port of each `con` cell joined to the first
auxiliary port of the other. -/
def vicious2 : Graph sig ℕ :=
  ⟨(0, Comb.con) ::ₘ {(1, Comb.con)},
    s(.port 0 0, .port 1 1) ::ₘ s(.port 1 0, .port 0 1) ::ₘ s(.port 0 2, .name 0) ::ₘ
      {s(.port 1 2, .name 1)}, 0⟩

/-- A vicious circle through two cells is a net (page 71). -/
theorem vicious2_wf : vicious2.WF := (wf_iff _).2 (by decide)

/-- The empty net (page 71). -/
theorem empty_wf : (⟨0, 0, 0⟩ : Graph sig ℕ).WF := (wf_iff _).2 (by decide)

/-- Part of the net pictured on page 71, with `α = con` and `γ = era`. The combinators have no
symbol of arity `1`, so the two components that contain `β` are left out; built here are the
middle component (an `α` cell with joined auxiliary ports, its principal port on the right
auxiliary port of a second `α` cell, an `era` on the left one, the free port `z` below) and, in
place of `γ`-`β`-`γ`, two `era` cells joined by their principal ports. -/
def page71 : Graph sig ℕ :=
  ⟨(0, Comb.con) ::ₘ (1, Comb.con) ::ₘ (2, Comb.era) ::ₘ (3, Comb.era) ::ₘ {(4, Comb.era)},
    s(.port 0 1, .port 0 2) ::ₘ s(.port 0 0, .port 1 2) ::ₘ s(.port 1 1, .port 2 0) ::ₘ
      s(.port 1 0, .name 2) ::ₘ {s(.port 3 0, .port 4 0)}, 0⟩

/-- Two components of the net of page 71 form a net. -/
theorem page71_wf : page71.WF := (wf_iff _).2 (by decide)

/-! ## Graphs that are not nets -/

/-- A name that ends two wires is not a free port (page 71). -/
theorem not_wf_name_twice :
    ¬ (⟨0, s(.name 0, .name 1) ::ₘ {s(.name 0, .name 2)}, 0⟩ : Graph sig ℕ).WF := by
  rw [wf_iff]; decide

/-- A port that ends no wire: every port is connected (page 71). -/
theorem not_wf_port_unwired : ¬ (⟨{(0, Comb.era)}, 0, 0⟩ : Graph sig ℕ).WF := by
  rw [wf_iff]; decide

/-- A wire from a port to itself: a wire connects a port to *another* one (page 71). -/
theorem not_wf_port_self :
    ¬ (⟨{(0, Comb.con)}, s(.port 0 0, .port 0 0) ::ₘ {s(.port 0 1, .port 0 2)}, 0⟩ :
      Graph sig ℕ).WF := by
  rw [wf_iff]; decide

/-- A wire from a free port to itself (page 71). -/
theorem not_wf_name_self : ¬ (⟨0, {s(.name 0, .name 0)}, 0⟩ : Graph sig ℕ).WF := by
  rw [wf_iff]; decide

/-- A wire on the port `1` of an `era` cell, which has no auxiliary port (page 71). -/
theorem not_wf_port_beyond :
    ¬ (⟨{(0, Comb.era)}, s(.port 0 0, .name 0) ::ₘ {s(.port 0 1, .name 1)}, 0⟩ :
      Graph sig ℕ).WF := by
  rw [wf_iff]; decide

/-- A wire on a port of a cell that is not in the graph (page 71). -/
theorem not_wf_port_no_cell : ¬ (⟨0, {s(.port 0 0, .name 0)}, 0⟩ : Graph sig ℕ).WF := by
  rw [wf_iff]; decide

/-- Two cells with one identity (page 71). -/
theorem not_wf_same_id :
    ¬ (⟨(0, Comb.era) ::ₘ {(0, Comb.era)}, {s(.port 0 0, .port 0 0)}, 0⟩ : Graph sig ℕ).WF := by
  rw [wf_iff]; decide

/-! ## `Graph.Iso` -/

/-- A `con` cell numbered `0`, its three ports on the free ports `0`, `1`, `2` in order. -/
def con012 : Graph sig ℕ :=
  ⟨{(0, Comb.con)}, s(.port 0 0, .name 0) ::ₘ s(.port 0 1, .name 1) ::ₘ {s(.port 0 2, .name 2)}, 0⟩

/-- The same net, the cell numbered `5`, the wires listed in another order and with their ends
exchanged. -/
def con012' : Graph sig ℕ :=
  ⟨{(5, Comb.con)}, s(.port 5 2, .name 2) ::ₘ s(.name 0, .port 5 0) ::ₘ {s(.port 5 1, .name 1)}, 0⟩

/-- Page 71: the identity of a cell and the order of the wires do not matter. -/
theorem iso_renumber : Iso con012 con012' := by
  refine ⟨fun _ => 5, fun a ha b hb _ => ?_, rfl, by decide, rfl⟩
  have h0 : ∀ c ∈ con012.cells.map Prod.fst, c = 0 := by decide
  exact (h0 a ha).trans (h0 b hb).symm

/-- The net `con(x, y) = dup(x, y)`, its two cells numbered the other way round. -/
def conDupSwapped : Graph sig ℕ :=
  ⟨(1, Comb.con) ::ₘ {(0, Comb.dup)},
    s(.port 1 2, .port 0 2) ::ₘ s(.port 0 1, .port 1 1) ::ₘ {s(.port 1 0, .port 0 0)}, 0⟩

/-- Exchanging the numbers of two cells gives an isomorphic graph (page 71). -/
theorem iso_exchange_numbers :
    Iso (⟨(0, Comb.con) ::ₘ {(1, Comb.dup)},
      s(.port 0 2, .port 1 2) ::ₘ s(.port 1 1, .port 0 1) ::ₘ {s(.port 0 0, .port 1 0)}, 0⟩ :
        Graph sig ℕ) conDupSwapped := by
  refine ⟨fun c => 1 - c, fun a ha b hb h => ?_, rfl, by decide, rfl⟩
  have hle : ∀ c ∈ ((0, Comb.con) ::ₘ {(1, Comb.dup)} : Multiset (ℕ × sig.Sym)).map Prod.fst,
      c ≤ 1 := by decide
  have := hle a ha
  have := hle b hb
  simp only at h
  omega

/-- The `con` cell with its two auxiliary ports exchanged: the free port `1` is now on the second
auxiliary port, the free port `2` on the first. -/
def con021 : Graph sig ℕ :=
  ⟨{(0, Comb.con)}, s(.port 0 0, .name 0) ::ₘ s(.port 0 1, .name 2) ::ₘ {s(.port 0 2, .name 1)}, 0⟩

/-- Page 71: the auxiliary ports "are not interchangeable". Exchanging them gives a graph that is
not isomorphic. -/
theorem not_iso_exchange_aux : ¬ Iso con012 con021 := by
  rintro ⟨σ, -, -, hw, -⟩
  have hm : s(End.port (σ 0) 1, End.name 1) ∈ con021.wires := by
    rw [hw]; simp [con012, End.mapCell]
  simp [con021] at hm

/-- The number of cyclic wires is kept by `Iso` (page 71). -/
theorem not_iso_loops : ¬ Iso (⟨0, 0, 0⟩ : Graph sig ℕ) ⟨0, 0, 1⟩ := by
  rintro ⟨σ, -, -, -, h⟩
  exact absurd h (by decide)

/-- The free ports are kept by `Iso`: a wire between the free ports `0` and `1` is not a wire
between `0` and `2` (page 71). -/
theorem not_iso_free : ¬ Iso freeWire ⟨0, {s(.name 0, .name 2)}, 0⟩ := by
  rintro ⟨σ, -, -, hw, -⟩
  simp [freeWire, End.mapCell] at hw

/-! ## `Net.HasGraph` on small texts -/

omit [DecidableEq ν] in
/-- `Contract.join` with the graphs given by their fields (page 71). -/
theorem join_of {G H : Graph S ν} (x : ν) (p q : End ν) (W : Multiset (Sym2 (End ν)))
    (hG : G.wires = s(.name x, p) ::ₘ s(.name x, q) ::ₘ W) (hH : H.wires = s(p, q) ::ₘ W)
    (hc : H.cells = G.cells) (hl : H.loops = G.loops) : Contract G H := by
  obtain ⟨C, WG, n⟩ := G
  obtain ⟨C', WH, n'⟩ := H
  simp only at hG hH hc hl
  subst hG hH hc hl
  exact .join x p q _ W _

omit [DecidableEq ν] in
/-- `Contract.loop` with the graphs given by their fields (page 71). -/
theorem loop_of {G H : Graph S ν} (x : ν) (W : Multiset (Sym2 (End ν)))
    (hG : G.wires = s(.name x, .name x) ::ₘ W) (hH : H.wires = W)
    (hc : H.cells = G.cells) (hl : H.loops = G.loops + 1) : Contract G H := by
  obtain ⟨C, WG, n⟩ := G
  obtain ⟨C', WH, n'⟩ := H
  simp only at hG hH hc hl
  subst hG hH hc hl
  exact .loop x _ _ _

/-- `r = con(x, x)`, with `r = 0` and `x = 1`: the name `1` is a wire between the two auxiliary
ports. -/
def auxText : List (Term sig ℕ × Term sig ℕ) := [(.var 0, mkCon (.var 1) (.var 1))]

/-- Its raw graph: the name `1` ends two wires (page 71). -/
theorem raw_auxText : Graph.raw 0 auxText =
    ⟨{(0, Comb.con)},
      s(.name 0, .port 0 0) ::ₘ s(.port 0 1, .name 1) ::ₘ {s(.port 0 2, .name 1)}, 0⟩ := by
  simp [auxText, Graph.raw, Term.rawCells, Term.rawWires, Term.rootEnd, Term.size,
    Term.childBase, mkCon, sig, Fin.sum_univ_two]
  rfl

/-- Page 71: the graph of `r = con(x, x)` is `auxJoined`, the cell with its auxiliary ports
joined. -/
theorem hasGraph_auxText : (Net.ofList auxText).HasGraph auxJoined := by
  refine ⟨auxText, 0, rfl, .single (join_of 1 (.port 0 1) (.port 0 2) {s(.name 0, .port 0 0)}
    ?_ ?_ ?_ ?_), auxJoined_wf.name⟩ <;> (try rw [raw_auxText]) <;> first | decide | rfl

/-- The chain `x = y, y = z`, with names `0`, `1`, `2`. -/
def chainText : List (Term sig ℕ × Term sig ℕ) := [(.var 0, .var 1), (.var 1, .var 2)]

/-- The graph of the chain is one wire between the free ports `0` and `2` (page 71). -/
theorem hasGraph_chainText :
    (Net.ofList chainText).HasGraph (⟨0, {s(.name 0, .name 2)}, 0⟩ : Graph sig ℕ) := by
  refine ⟨chainText, 0, rfl, .single (join_of 1 (.name 0) (.name 2) 0 ?_ ?_ ?_ ?_),
    ((wf_iff _).2 (by decide)).name⟩ <;> first | decide | rfl

/-- The equation `x = x`. -/
def loopText : List (Term sig ℕ × Term sig ℕ) := [(.var 0, .var 0)]

/-- Page 71: the graph of `x = x` is one cyclic wire. -/
theorem hasGraph_loopText : (Net.ofList loopText).HasGraph cyclic :=
  ⟨loopText, 0, rfl, .single (loop_of 0 0 (by decide) (by decide) rfl rfl),
    cyclic_wf.name⟩

/-- `x = con(x, y)`, with `x = 0` and `y = 1`: a tree plugged into its own auxiliary port through
a name. -/
def selfText : List (Term sig ℕ × Term sig ℕ) := [(.var 0, mkCon (.var 0) (.var 1))]

/-- Its raw graph: the name `0` ends two wires (page 71). -/
theorem raw_selfText : Graph.raw 0 selfText =
    ⟨{(0, Comb.con)},
      s(.name 0, .port 0 0) ::ₘ s(.port 0 1, .name 0) ::ₘ {s(.port 0 2, .name 1)}, 0⟩ := by
  simp [selfText, Graph.raw, Term.rawCells, Term.rawWires, Term.rootEnd, Term.size,
    Term.childBase, mkCon, sig, Fin.sum_univ_two]
  rfl

/-- The graph of `x = con(x, y)`: the principal port of the cell joined to its first auxiliary
port, a vicious circle, the second auxiliary port on the free port `1`. -/
def selfGraph : Graph sig ℕ :=
  ⟨{(0, Comb.con)}, s(.port 0 0, .port 0 1) ::ₘ {s(.port 0 2, .name 1)}, 0⟩

/-- The graph of `x = con(x, y)` is the vicious circle `selfGraph`, and it is well formed
(page 71). -/
theorem hasGraph_selfText : (Net.ofList selfText).HasGraph selfGraph ∧ selfGraph.WF := by
  have hwf : selfGraph.WF := (wf_iff _).2 (by decide)
  refine ⟨⟨selfText, 0, rfl, .single (join_of 0 (.port 0 0) (.port 0 1) {s(.port 0 2, .name 1)}
    ?_ ?_ ?_ ?_), hwf.name⟩, hwf⟩ <;> (try rw [raw_selfText]) <;> first | decide | rfl

/-! ## A non-linear text has several graphs -/

/-- `x = a, x = b, x = c`, with `x = 0`: the name `0` occurs three times. -/
def threeText : List (Term sig ℕ × Term sig ℕ) :=
  [(.var 0, .var 1), (.var 0, .var 2), (.var 0, .var 3)]

/-- The text is not linear (page 71). -/
theorem not_linear_threeText : ¬ (Net.ofList threeText).Linear := fun h =>
  absurd (h 0) (by decide)

/-- Joining the first two occurrences of `0`. -/
def threeG1 : Graph sig ℕ := ⟨0, s(.name 1, .name 2) ::ₘ {s(.name 0, .name 3)}, 0⟩

/-- Joining the first and the third occurrence of `0`. -/
def threeG2 : Graph sig ℕ := ⟨0, s(.name 1, .name 3) ::ₘ {s(.name 0, .name 2)}, 0⟩

/-- On a non-linear text, `Net.HasGraph` holds of two graphs that are not isomorphic. The
uniqueness asked in `PLAN.md`, Stage C, needs the linearity of the net: in a text of a net of
page 71 a name is a free port or a wire, so it occurs at most twice. -/
theorem threeText_two_graphs : (Net.ofList threeText).HasGraph threeG1 ∧
    (Net.ofList threeText).HasGraph threeG2 ∧ threeG1.WF ∧ threeG2.WF ∧ ¬ Iso threeG1 threeG2 := by
  have h1 : threeG1.WF := (wf_iff _).2 (by decide)
  have h2 : threeG2.WF := (wf_iff _).2 (by decide)
  refine ⟨⟨threeText, 0, rfl, .single (join_of 0 (.name 1) (.name 2) {s(.name 0, .name 3)}
      (by decide) (by decide) rfl rfl), h1.name⟩,
    ⟨threeText, 0, rfl, .single (join_of 0 (.name 1) (.name 3) {s(.name 0, .name 2)}
      (by decide) (by decide) rfl rfl), h2.name⟩, h1, h2, ?_⟩
  rintro ⟨σ, -, -, hw, -⟩
  have hm : s(End.name 1, End.name 2) ∈ threeG2.wires := by
    rw [hw]; simp [threeG1, End.mapCell]
  simp [threeG2] at hm

/-! ## A well-formed graph without a text when names run out -/

/-- Two `con` cells in a vicious circle with no free port, the principal port of each on the
first auxiliary port of the other, their second auxiliary ports joined. Names are of type
`Empty`. -/
def viciousClosed : Graph sig Empty :=
  ⟨(0, Comb.con) ::ₘ {(1, Comb.con)},
    s(.port 0 0, .port 1 1) ::ₘ s(.port 1 0, .port 0 1) ::ₘ {s(.port 0 2, .port 1 2)}, 0⟩

/-- `viciousClosed` is well formed (page 71). -/
theorem viciousClosed_wf : viciousClosed.WF := (wf_iff _).2 (by decide)

/-- Without names, `viciousClosed` is the graph of no text: no name can be erased, and the wire of
the first equation would join two principal ports. So "every well-formed graph is the graph of a
net" (`PLAN.md`, Stage C, statement 4) needs enough names, for instance `ν = ℕ`: a cycle through
principal and auxiliary ports needs a name in a text (page 71). -/
theorem viciousClosed_no_text (N : Net sig Empty) : ¬ N.HasGraph viciousClosed := by
  rintro ⟨L, k, -, hc, -⟩
  have hr : Graph.raw k L = viciousClosed := by
    have hno : ∀ G H : Graph sig Empty, ¬ Contract G H := by
      intro G H h
      cases h with
      | join x => exact x.elim
      | loop x => exact x.elim
    rcases Relation.ReflTransGen.cases_tail hc with h | ⟨_, -, h⟩
    · exact h.symm
    · exact (hno _ _ h).elim
  cases L with
  | nil =>
    have := congrArg Graph.cells hr
    simp [Graph.raw, viciousClosed] at this
  | cons e L =>
    obtain ⟨a, b⟩ := e
    have hm := congrArg (s(a.rootEnd k, b.rootEnd (k + a.size)) ∈ ·.wires) hr
    simp only [Graph.raw, Multiset.mem_cons_self] at hm
    cases a with
    | var x => exact x.elim
    | app α ts =>
      cases b with
      | var x => exact x.elim
      | app β us => simp [Term.rootEnd, viciousClosed] at hm

end INet.GraphReview
