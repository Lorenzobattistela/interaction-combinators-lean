import InteractionCombinators.Lafont.GraphStep
import InteractionCombinators.Combinators
import Checks.GraphReview

/-!
# Check of `Lafont/GraphStep.lean`

Worked examples of `Graph.Interact` on the interaction combinators (Lafont 1997, Section 1.2,
page 73). In each, the two cells are `0` and `1`, `port c 0` is the principal port of `c` and
`port c (i + 1)` its `i`-th auxiliary port. Each interaction is proved by exhibiting the data of
`Interact.mk`: the graph of the rule (its raw graph, which needs no contraction), the identity
renumbering of its cells (it has none), the fresh names, and the contractions one by one.

* `conCon_free`: `con`–`con` with free auxiliary ports `0, 1 / 2, 3`. The result is the two wires
  `0–3` and `1–2` of `ruleConCon`: the auxiliary ports are exchanged.
* `dupDup_shared`: the graph of `dup(x, 1) = dup(x, 2)`. `ruleDupDup` joins the ports in order, so
  the result is the wire `1–2` and one cyclic wire, from the wire `x`.
* `conCon_closed`: the graph of `con(x, y) = con(x, y)`. The result is one cyclic wire.
* `not_interact_aux`: a principal port wired to an auxiliary port gives no interaction.
* `conCon_free_wf`: `Interact.wf` applied to the first example, so its hypotheses can hold.

The graphs before are the graphs of their texts (`conConFree_hasGraph`, `dupDupShared_hasGraph`,
`conConClosed_hasGraph`).
-/

namespace INet.GraphStepCheck

open Comb Graph GraphReview

/-! ## Tools for concrete contractions -/

/-- A joining of two wires, with the graphs given by their components. -/
theorem join_eq {G H : Graph sig ℕ} (x : ℕ) (p q : End ℕ) (W : Multiset (Sym2 (End ℕ)))
    (hG : G.wires = s(.name x, p) ::ₘ s(.name x, q) ::ₘ W) (hc : H.cells = G.cells)
    (hw : H.wires = s(p, q) ::ₘ W) (hl : H.loops = G.loops) : Contract G H := by
  obtain ⟨C, W', n⟩ := G
  obtain ⟨C', W'', n'⟩ := H
  simp only at hG hc hw hl
  subst hG hc hw hl
  exact Contract.join x p q _ _ _

/-- A closing of a cyclic wire, with the graphs given by their components. -/
theorem loop_eq {G H : Graph sig ℕ} (x : ℕ) (W : Multiset (Sym2 (End ℕ)))
    (hG : G.wires = s(.name x, .name x) ::ₘ W) (hc : H.cells = G.cells)
    (hw : H.wires = W) (hl : H.loops = G.loops + 1) : Contract G H := by
  obtain ⟨C, W', n⟩ := G
  obtain ⟨C', W'', n'⟩ := H
  simp only at hG hc hw hl
  subst hG hc hw hl
  exact Contract.loop x _ _ _

/-- Two graphs with the same components are equal. -/
theorem graph_eq {G H : Graph sig ℕ} (hc : G.cells = H.cells) (hw : G.wires = H.wires)
    (hl : G.loops = H.loops) : G = H := by
  obtain ⟨C, W, n⟩ := G
  obtain ⟨C', W', n'⟩ := H
  simp only at hc hw hl
  rw [hc, hw, hl]

/-- The names of the rule: auxiliary ports of the first cell, of the second, no internal wire. -/
abbrev RN : Type := Fin 2 ⊕ Fin 2 ⊕ Fin 0

/-- The `i`-th auxiliary port of the first cell, as an end of the graph of a rule. -/
abbrev lt (i : Fin 2) : Term sig RN := .var (.inl i)
/-- The `j`-th auxiliary port of the second cell, as an end of the graph of a rule. -/
abbrev rt (j : Fin 2) : Term sig RN := .var (.inr (.inl j))

/-- A text of `ruleConCon`: `l0 = r1, l1 = r0`. -/
def conConText : List (Term sig RN × Term sig RN) := [(lt 0, rt 1), (lt 1, rt 0)]

/-- A text of `ruleDupDup`: `l0 = r0, l1 = r1`. -/
def dupDupText : List (Term sig RN × Term sig RN) := [(lt 0, rt 0), (lt 1, rt 1)]

/-- The graph of `ruleConCon`: its raw graph, which has no cell and no name to contract. -/
theorem conCon_hasGraph : ruleConCon.net.HasGraph (raw 0 conConText) :=
  ⟨conConText, 0, rfl, .refl, by decide⟩

/-- The graph of `ruleDupDup`: its raw graph. -/
theorem dupDup_hasGraph : ruleDupDup.net.HasGraph (raw 0 dupDupText) :=
  ⟨dupDupText, 0, rfl, .refl, by decide⟩

/-- Fresh names for the four auxiliary ports: `k, k + 1` for the first cell, `k + 2, k + 3` for
the second. -/
def fresh (k : ℕ) : RN → ℕ := Sum.elim (fun i => k + i) (Sum.elim (fun j => k + 2 + j) fun _ => 0)

theorem fresh_injective (k : ℕ) : Function.Injective (fresh k) := by
  intro x y h
  rcases x with i | j | w <;> rcases y with i' | j' | w' <;>
    simp only [fresh, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg _ (Fin.ext (by omega))
  · omega
  · exact w'.elim0
  · omega
  · exact congrArg _ (congrArg _ (Fin.ext (by omega)))
  · exact w'.elim0
  · exact w.elim0
  · exact w.elim0
  · exact w.elim0

/-- Every name ends at most one wire, when the ends have no repetition. -/
theorem count_le_one_of_nodup {G : Graph sig ℕ} (h : G.ends.Nodup) (x : ℕ) :
    G.ends.count (.name x) ≤ 1 :=
  Multiset.nodup_iff_count_le_one.1 h _

/-! ## `con`–`con` with free auxiliary ports -/

/-- The wires of `conConFree` other than the one between the principal ports. -/
def conConFreeW : Multiset (Sym2 (End ℕ)) :=
  s(.port 0 1, .name 0) ::ₘ s(.port 0 2, .name 1) ::ₘ s(.port 1 1, .name 2) ::ₘ
    {s(.port 1 2, .name 3)}

/-- Two `con` cells `0`, `1` joined by their principal ports, the auxiliary ports of `0` free
under the names `0, 1`, those of `1` under `2, 3`: the graph of `con(0, 1) = con(2, 3)`. -/
def conConFree : Graph sig ℕ :=
  ⟨(0, Comb.con) ::ₘ (1, Comb.con) ::ₘ 0, s(.port 0 0, .port 1 0) ::ₘ conConFreeW, 0⟩

/-- The text `con(0, 1) = con(2, 3)`. -/
def conConFreeText : List (Term sig ℕ × Term sig ℕ) :=
  [(mkCon (.var 0) (.var 1), mkCon (.var 2) (.var 3))]

/-- `conConFree` is the graph of `con(0, 1) = con(2, 3)` (page 71): its raw graph, with nothing to
erase. -/
theorem conConFree_hasGraph : (Net.ofList conConFreeText).HasGraph conConFree := by
  refine ⟨conConFreeText, 0, rfl, ?_, count_le_one_of_nodup (by decide)⟩
  rw [graph_eq (H := conConFree) rfl (by decide) rfl]
  exact .refl

/-- Two wires, `0–3` and `1–2`. -/
def conConFreeAfter : Graph sig ℕ := ⟨0, s(.name 0, .name 3) ::ₘ {s(.name 1, .name 2)}, 0⟩

/-- **`con`–`con` with free auxiliary ports** (Lafont 1997, page 73). Before: cells `0 : con`,
`1 : con`, wires `port 0 0 – port 1 0`, `port 0 1 – 0`, `port 0 2 – 1`, `port 1 1 – 2`,
`port 1 2 – 3`. After: no cell, no cyclic wire, wires `0–3` and `1–2`, as in `ruleConCon`, where
the auxiliary ports are exchanged. The fresh names are `4, 5` (cell `0`) and `6, 7` (cell `1`);
the contractions erase `4, 7, 5, 6`. -/
theorem conCon_free : Interact system conConFree conConFreeAfter := by
  refine Interact.mk (I := system) 0 1 Comb.con Comb.con 0 conConFreeW 0 ruleConCon rfl
    (raw 0 conConText)
    conCon_hasGraph id (Set.injOn_id _) (by decide) (fresh 4) (fresh_injective 4) (by decide)
    conConFreeAfter ?_ (count_le_one_of_nodup (by decide))
  refine .head (join_eq (H := ⟨0, s(.name 0, .name 7) ::ₘ s(.name 5, .name 1) ::ₘ
      s(.name 6, .name 2) ::ₘ s(.name 7, .name 3) ::ₘ {s(.name 5, .name 6)}, 0⟩) 4 (.name 0)
      (.name 7) (s(.name 5, .name 1) ::ₘ s(.name 6, .name 2) ::ₘ s(.name 7, .name 3) ::ₘ
        {s(.name 5, .name 6)}) (by decide) rfl rfl rfl) ?_
  refine .head (join_eq (H := ⟨0, s(.name 0, .name 3) ::ₘ s(.name 5, .name 1) ::ₘ
      s(.name 6, .name 2) ::ₘ {s(.name 5, .name 6)}, 0⟩) 7 (.name 0) (.name 3)
      (s(.name 5, .name 1) ::ₘ s(.name 6, .name 2) ::ₘ {s(.name 5, .name 6)}) (by decide) rfl rfl
      rfl) ?_
  refine .head (join_eq (H := ⟨0, s(.name 1, .name 6) ::ₘ s(.name 0, .name 3) ::ₘ
      {s(.name 6, .name 2)}, 0⟩) 5 (.name 1) (.name 6) (s(.name 0, .name 3) ::ₘ
        {s(.name 6, .name 2)}) (by decide) rfl rfl rfl) ?_
  refine .single (join_eq 6 (.name 1) (.name 2) {s(.name 0, .name 3)} (by decide) rfl
    (by decide) rfl)

/-- `Interact.wf` applies to `conCon_free`: the graph before is well formed, so the graph after
is. -/
theorem conCon_free_wf : conConFreeAfter.WF :=
  conCon_free.wf ((wf_iff _).2 (by decide))

/-! ## `dup`–`dup` with a shared wire -/

/-- The wires of `dupDupShared` other than the one between the principal ports. -/
def dupDupSharedW : Multiset (Sym2 (End ℕ)) :=
  s(.port 0 1, .port 1 1) ::ₘ s(.port 0 2, .name 1) ::ₘ {s(.port 1 2, .name 2)}

/-- The graph of `dup(x, 1) = dup(x, 2)`: two `dup` cells joined by their principal ports, their
first auxiliary ports joined by the wire `x`, their second free under the names `1`, `2`. -/
def dupDupShared : Graph sig ℕ :=
  ⟨(0, Comb.dup) ::ₘ (1, Comb.dup) ::ₘ 0, s(.port 0 0, .port 1 0) ::ₘ dupDupSharedW, 0⟩

/-- One wire `1–2` and one cyclic wire. -/
def dupDupSharedAfter : Graph sig ℕ := ⟨0, {s(.name 1, .name 2)}, 1⟩

/-- The text `dup(x, 1) = dup(x, 2)`, with `x = 0`. -/
def dupDupText2 : List (Term sig ℕ × Term sig ℕ) :=
  [(mkDup (.var 0) (.var 1), mkDup (.var 0) (.var 2))]

/-- `dupDupShared` is the graph of `dup(x, 1) = dup(x, 2)` (page 71): erase `x` in its raw
graph. -/
theorem dupDupShared_hasGraph : (Net.ofList dupDupText2).HasGraph dupDupShared :=
  ⟨dupDupText2, 0, rfl, .single (join_eq 0 (.port 0 1) (.port 1 1)
    (s(.port 0 0, .port 1 0) ::ₘ s(.port 0 2, .name 1) ::ₘ {s(.port 1 2, .name 2)}) (by decide)
    rfl (by decide) rfl), count_le_one_of_nodup (by decide)⟩

/-- **`dup`–`dup` with a shared wire creates a cyclic wire** (Lafont 1997, page 73: "cyclic wires
may be created when such a rule is applied inside a net"). Before: cells `0 : dup`, `1 : dup`,
wires `port 0 0 – port 1 0`, `port 0 1 – port 1 1`, `port 0 2 – 1`, `port 1 2 – 2`. After: no
cell, the wire `1–2`, one cyclic wire. `ruleDupDup` joins the first auxiliary ports of the two
cells, which the wire `x` already joins: together they close a cycle. The fresh names are `3, 4`
and `5, 6`; the contractions erase `3`, close `5`, and erase `4, 6`. -/
theorem dupDup_shared : Interact system dupDupShared dupDupSharedAfter := by
  refine Interact.mk (I := system) 0 1 Comb.dup Comb.dup 0 dupDupSharedW 0 ruleDupDup rfl
    (raw 0 dupDupText)
    dupDup_hasGraph id (Set.injOn_id _) (by decide) (fresh 3) (fresh_injective 3) (by decide)
    dupDupSharedAfter ?_ (count_le_one_of_nodup (by decide))
  refine .head (join_eq (H := ⟨0, s(.name 5, .name 5) ::ₘ s(.name 4, .name 1) ::ₘ
      s(.name 6, .name 2) ::ₘ {s(.name 4, .name 6)}, 0⟩) 3 (.name 5) (.name 5)
      (s(.name 4, .name 1) ::ₘ s(.name 6, .name 2) ::ₘ {s(.name 4, .name 6)}) (by decide)
      rfl rfl rfl) ?_
  refine .head (loop_eq (H := ⟨0, s(.name 4, .name 1) ::ₘ s(.name 6, .name 2) ::ₘ
      {s(.name 4, .name 6)}, 1⟩) 5 _ rfl rfl rfl rfl) ?_
  refine .head (join_eq (H := ⟨0, s(.name 1, .name 6) ::ₘ {s(.name 6, .name 2)}, 1⟩) 4
      (.name 1) (.name 6) {s(.name 6, .name 2)} (by decide) rfl rfl rfl) ?_
  refine .single (join_eq 6 (.name 1) (.name 2) 0 (by decide) rfl rfl rfl)

/-! ## `con`–`con` with all auxiliary ports wired in pairs -/

/-- The wires of `conConClosed` other than the one between the principal ports. -/
def conConClosedW : Multiset (Sym2 (End ℕ)) :=
  s(.port 0 1, .port 1 1) ::ₘ {s(.port 0 2, .port 1 2)}

/-- The graph of `con(x, y) = con(x, y)`: two `con` cells joined by their principal ports, and
their auxiliary ports of the same rank joined. No free port. -/
def conConClosed : Graph sig ℕ :=
  ⟨(0, Comb.con) ::ₘ (1, Comb.con) ::ₘ 0, s(.port 0 0, .port 1 0) ::ₘ conConClosedW, 0⟩

/-- The text `con(x, y) = con(x, y)`, with `x, y = 0, 1`. -/
def conConClosedText : List (Term sig ℕ × Term sig ℕ) :=
  [(mkCon (.var 0) (.var 1), mkCon (.var 0) (.var 1))]

/-- `conConClosed` is the graph of `con(x, y) = con(x, y)` (page 71): erase `x`, then `y`, in its
raw graph. -/
theorem conConClosed_hasGraph : (Net.ofList conConClosedText).HasGraph conConClosed := by
  refine ⟨conConClosedText, 0, rfl, ?_, count_le_one_of_nodup (by decide)⟩
  refine .head (join_eq (H := ⟨(0, Comb.con) ::ₘ {(1, Comb.con)},
      s(.port 0 1, .port 1 1) ::ₘ s(.port 0 0, .port 1 0) ::ₘ s(.port 0 2, .name 1) ::ₘ
        {s(.port 1 2, .name 1)}, 0⟩) 0 (.port 0 1) (.port 1 1)
      (s(.port 0 0, .port 1 0) ::ₘ s(.port 0 2, .name 1) ::ₘ {s(.port 1 2, .name 1)}) (by decide)
      rfl rfl rfl) ?_
  exact .single (join_eq 1 (.port 0 2) (.port 1 2)
    (s(.port 0 1, .port 1 1) ::ₘ {s(.port 0 0, .port 1 0)}) (by decide) rfl (by decide) rfl)

/-- One cyclic wire and nothing else. -/
def conConClosedAfter : Graph sig ℕ := ⟨0, 0, 1⟩

/-- **`con`–`con` from `con(x, y) = con(x, y)` gives exactly one cyclic wire** (Lafont 1997,
page 73). Write `l0, l1` for the auxiliary ports of cell `0` and `r0, r1` for those of cell `1`.
The graph joins `l0–r0` and `l1–r1`, and `ruleConCon` joins `l0–r1` and `l1–r0`. Following the
wires, `l0 – r0 – l1 – r1 – l0` is a single cycle through all four ports, so one cyclic wire,
not two. (With `ruleDupDup`, which joins `l0–r0` and `l1–r1`, the same graph would give two.)
The fresh names are `2, 3` and `4, 5`; the contractions erase `2, 4, 5` and close `3`. -/
theorem conCon_closed : Interact system conConClosed conConClosedAfter := by
  refine Interact.mk (I := system) 0 1 Comb.con Comb.con 0 conConClosedW 0 ruleConCon rfl
    (raw 0 conConText)
    conCon_hasGraph id (Set.injOn_id _) (by decide) (fresh 2) (fresh_injective 2) (by decide)
    conConClosedAfter ?_ (count_le_one_of_nodup (by decide))
  refine .head (join_eq (H := ⟨0, s(.name 4, .name 5) ::ₘ s(.name 3, .name 5) ::ₘ
      {s(.name 3, .name 4)}, 0⟩) 2 (.name 4) (.name 5)
      (s(.name 3, .name 5) ::ₘ {s(.name 3, .name 4)}) (by decide) rfl rfl rfl) ?_
  refine .head (join_eq (H := ⟨0, s(.name 5, .name 3) ::ₘ {s(.name 3, .name 5)}, 0⟩) 4
      (.name 5) (.name 3) {s(.name 3, .name 5)} (by decide) rfl rfl rfl) ?_
  refine .head (join_eq (H := ⟨0, {s(.name 3, .name 3)}, 0⟩) 5 (.name 3) (.name 3) 0
      (by decide) rfl rfl rfl) ?_
  refine .single (loop_eq 3 0 rfl rfl rfl rfl)

/-! ## A non-example -/

/-- The graph of `0 = con(con(2, 3), 1)`: the principal port of the `con` cell `1` is wired to
the first auxiliary port of the `con` cell `0`, not to its principal port. -/
def auxPrincipal : Graph sig ℕ :=
  ⟨(0, Comb.con) ::ₘ {(1, Comb.con)},
    s(.name 0, .port 0 0) ::ₘ s(.port 0 1, .port 1 0) ::ₘ s(.port 0 2, .name 1) ::ₘ
      s(.port 1 1, .name 2) ::ₘ {s(.port 1 2, .name 3)}, 0⟩

/-- **Cells interact only through their principal ports** (Lafont 1997, page 73). In
`auxPrincipal` no wire joins two principal ports, so it has no interaction, whatever the result
graph. -/
theorem not_interact_aux (H : Graph sig ℕ) : ¬ Interact system auxPrincipal H := by
  intro h
  obtain ⟨c, d, hm⟩ := h.principal
  simp [auxPrincipal] at hm

end INet.GraphStepCheck
