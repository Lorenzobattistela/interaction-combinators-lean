import InteractionCombinators.Lafont.Duplication

/-!
# Checks of `Lafont/Basic.lean` against the paper

A review (issue 7) compared `erase_tree`, `mux`, `muxStar` and `mux_muxStar` with Lafont 1997,
pages 82 to 85. This file records the cases worked by hand, as statements that Lean checks.

Ports are numbered as in the picture of page 82: on a cell drawn with its principal port down, the
left auxiliary port is 1 and the right one is 2; on a cell drawn with its principal port up, the
left one is 2 and the right one is 1. `mkCon a b` has `a` on port 1 and `b` on port 2.

* `mux_shapes`, `muxStar_shapes` — the trees for `n = 0, 1, 2, 3`. Read with the numbering above,
  they are the nets of Fig. 4 (page 83), including the side of the nesting.
* `dupFree_mux`, `dupFree_muxStar` — the multiplexors contain no `dup` (page 83).
* `mux_muxStar_two`, `mux_muxStar_three`, `mux_muxStar_figure` — the property of page 82 for
  `n = 2` and `n = 3`: port `i` of `M_n` is joined to port `i` of `M_n*`.
* `mux_mux_two` — `M_2` against itself joins the ports crosswise, so the reversal in `muxStar` is
  what compensates for the exchange of ports by `con`–`con`.
* `erase_tree_multiplicity`, `erase_tree_no_leaf` — Lemma 2 (i) (page 85) on a tree where a name
  occurs twice, and on a tree without leaves.
-/

namespace INet.Comb.BasicCheck

open Term

variable (t₁ t₂ t₃ u₁ u₂ u₃ : Term sig ℕ) (Δ : CNet)

/-- `M_0`, `M_1`, `M_2`, `M_3` of Fig. 4 (page 83): an eraser, a wire, one `con`, and a `con` with
a `con` on its port 2. -/
theorem mux_shapes :
    mux ([] : List (Term sig ℕ)) = mkEra ∧ mux [t₁] = t₁ ∧ mux [t₁, t₂] = mkCon t₁ t₂ ∧
      mux [t₁, t₂, t₃] = mkCon t₁ (mkCon t₂ t₃) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `M_0*`, `M_1*`, `M_2*`, `M_3*` of Fig. 4 (page 83): an eraser, a wire, one `con` with its ports
in the reverse order, and a `con` with a `con` on its port 1. -/
theorem muxStar_shapes :
    muxStar ([] : List (Term sig ℕ)) = mkEra ∧ muxStar [u₁] = u₁ ∧
      muxStar [u₁, u₂] = mkCon u₂ u₁ ∧ muxStar [u₁, u₂, u₃] = mkCon (mkCon u₃ u₂) u₁ :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `M_n` does not use `dup` (page 83: "it will be essential that our implementation of the
multiplexors does not use `δ`"). -/
theorem dupFree_mux : ∀ ts : List (Term sig ℕ), (∀ t ∈ ts, DupFree t) → DupFree (mux ts)
  | [], _ => trivial
  | [t], h => h t (by simp)
  | t :: t' :: ts, h =>
    dupFree_mkCon.2 ⟨h t (by simp),
      dupFree_mux (t' :: ts) fun s hs => h s (List.mem_cons_of_mem _ hs)⟩

/-- `M_n*` does not use `dup` (page 83). -/
theorem dupFree_muxStar : ∀ us : List (Term sig ℕ), (∀ u ∈ us, DupFree u) → DupFree (muxStar us)
  | [], _ => trivial
  | [u], h => h u (by simp)
  | u :: u' :: us, h =>
    dupFree_mkCon.2 ⟨dupFree_muxStar (u' :: us) fun s hs => h s (List.mem_cons_of_mem _ hs),
      h u (by simp)⟩

/-- The multiplexor property (page 82) for `n = 2`, on the trees written out. -/
theorem mux_muxStar_two :
    Red (s(mkCon t₁ t₂, mkCon u₂ u₁) ::ₘ Δ) (s(t₁, u₁) ::ₘ s(t₂, u₂) ::ₘ Δ) := by
  have h := mux_muxStar [t₁, t₂] [u₁, u₂] Δ rfl
  refine h.cast rfl ?_
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, ← Multiset.cons_coe,
    Multiset.coe_nil]
  ms

/-- The multiplexor property (page 82) for `n = 3`, on the trees written out. -/
theorem mux_muxStar_three :
    Red (s(mkCon t₁ (mkCon t₂ t₃), mkCon (mkCon u₃ u₂) u₁) ::ₘ Δ)
      (s(t₁, u₁) ::ₘ s(t₂, u₂) ::ₘ s(t₃, u₃) ::ₘ Δ) := by
  have h := mux_muxStar [t₁, t₂, t₃] [u₁, u₂, u₃] Δ rfl
  refine h.cast rfl ?_
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, ← Multiset.cons_coe,
    Multiset.coe_nil]
  ms

/-- The picture of page 82 for `n = 3`: `M_3` with free ports `0, 1, 2` against `M_3*` with free
ports `3, 4, 5`, alone, reduces to the three wires `0–3`, `1–4`, `2–5`. -/
theorem mux_muxStar_figure :
    Red {s(mux [var 0, var 1, var 2], muxStar [var 3, var 4, var 5])}
      (s(var 0, var 3) ::ₘ s(var 1, var 4) ::ₘ {s(var 2, var 5)}) :=
  mux_muxStar_three (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) 0

/-- `M_2` against `M_2` joins port 1 to port 2 and port 2 to port 1 (page 82: `γγ` exchanges the
ports). The dual `M_2*` is `M_2` with its ports in the reverse order for this reason. -/
theorem mux_mux_two :
    Step system (s(mux [t₁, t₂], mux [u₁, u₂]) ::ₘ Δ) (s(t₁, u₂) ::ₘ s(t₂, u₁) ::ₘ Δ) :=
  step_con_con t₁ t₂ u₁ u₂ Δ

/-- Lemma 2 (i) (page 85) on a tree in which the name `0` occurs twice: one eraser per leaf, so
two erasers on `0`. The `era` inside the tree leaves nothing. -/
theorem erase_tree_multiplicity :
    Red {s(mkEra, mkCon (var 0) (mkDup (var 0) mkEra))}
      (s(mkEra, var 0) ::ₘ {s(mkEra, var 0)}) := by
  have h := erase_tree (mkCon (var 0) (mkDup (var 0) mkEra)) 0
  refine h.cast rfl ?_
  simp

/-- Lemma 2 (i) (page 85) on a tree without leaves: nothing is left. -/
theorem erase_tree_no_leaf : Red {s(mkEra, mkCon mkEra (mkDup mkEra mkEra))} 0 := by
  have h := erase_tree (mkCon mkEra (mkDup mkEra mkEra)) 0
  refine h.cast rfl ?_
  simp

end INet.Comb.BasicCheck
