import InteractionCombinators.Lafont.AutoMux

/-!
# Checks of `Lafont/AutoMux.lean` against the paper

A review (issue 21) compared `autoMux` and `autoMux_autoMux` with Lafont 1997, page 83 (Fig. 5 and
the picture above it). This file records the cases worked by hand, as statements that Lean checks.

Ports are numbered as in `BasicCheck.lean`: on a cell drawn with its principal port down, the left
auxiliary port is 1 and the right one is 2; `mkDup a b` has `a` on port 1 and `b` on port 2. Both
copies of `T_n` in the picture of page 83 are drawn with their principal port down, so their ports
are numbered `1, …, n` from left to right on both sides, and the picture joins port `i` of the left
copy to port `i` of the right copy.

* `autoMux_shapes` — the trees for `n = 0, 1, 2, 3`: they are the nets of Fig. 5, including the side
  of the nesting (the upper `dup` of `T_3` sits on port 2 of the lower one).
* `autoMux_autoMux_two`, `autoMux_autoMux_three` — the property for `n = 2, 3`, proved by hand with
  the rule `δδ` alone, without `autoMux_autoMux`; `autoMux_autoMux_three'` gets the same from
  `autoMux_autoMux`.
* `autoMux_autoMux_figure` — the picture of page 83 for `n = 3`, on free ports: the hypotheses of
  `autoMux_autoMux` hold on the net of the figure.
* `autoMux_autoMux_zero` — `T_0` against `T_0` uses `εε` and leaves nothing.
* `conMux_conMux_two`, `conMux_conMux_three`, `conMux_conMux_three_stuck` — the same nets built
  with `con` do not work (page 83: "`γ` is not suitable"): for `n = 2` the ports are joined
  crosswise, for `n = 3` one step leaves two equations between a name and a `con` cell, and then
  no step applies.
* `no_step_of_var`, `autoMux_autoMux_length_needed` — the hypothesis `ts.length = us.length` is
  needed: `T_1` against `T_2` is stuck and does not give the wire the conclusion would give.
-/

namespace INet.Comb.AutoMuxCheck

open Term

variable (t₁ t₂ t₃ u₁ u₂ u₃ : Term sig ℕ) (Δ : CNet)

/-- `T_0`, `T_1`, `T_2`, `T_3` of Fig. 5 (page 83): an eraser, a wire, one `dup`, and a `dup` with
a `dup` on its port 2. -/
theorem autoMux_shapes :
    autoMux ([] : List (Term sig ℕ)) = mkEra ∧ autoMux [t₁] = t₁ ∧
      autoMux [t₁, t₂] = mkDup t₁ t₂ ∧ autoMux [t₁, t₂, t₃] = mkDup t₁ (mkDup t₂ t₃) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The property of the autodual multiplexor (page 83) for `n = 0`: one `εε` step. -/
theorem autoMux_autoMux_zero : Red (s(autoMux [], autoMux []) ::ₘ Δ) Δ :=
  Steps.single (step_era_era Δ)

/-- The property of the autodual multiplexor (page 83) for `n = 2`: one `δδ` step joins port `i`
of one copy to port `i` of the other, without reversal. -/
theorem autoMux_autoMux_two :
    Step system (s(autoMux [t₁, t₂], autoMux [u₁, u₂]) ::ₘ Δ) (s(t₁, u₁) ::ₘ s(t₂, u₂) ::ₘ Δ) :=
  step_dup_dup t₁ t₂ u₁ u₂ Δ

/-- The property of the autodual multiplexor (page 83) for `n = 3`, by hand: two `δδ` steps. -/
theorem autoMux_autoMux_three :
    Red (s(autoMux [t₁, t₂, t₃], autoMux [u₁, u₂, u₃]) ::ₘ Δ)
      (s(t₁, u₁) ::ₘ s(t₂, u₂) ::ₘ s(t₃, u₃) ::ₘ Δ) := by
  refine Relation.ReflTransGen.head (step_dup_dup t₁ (mkDup t₂ t₃) u₁ (mkDup u₂ u₃) Δ) ?_
  have h := Steps.single (step_dup_dup t₂ t₃ u₂ u₃ (s(t₁, u₁) ::ₘ Δ))
  refine h.cast (Multiset.cons_swap _ _ _) ?_
  ms

/-- `autoMux_autoMux` gives the same result as the computation by hand for `n = 3`. -/
theorem autoMux_autoMux_three' :
    Red (s(autoMux [t₁, t₂, t₃], autoMux [u₁, u₂, u₃]) ::ₘ Δ)
      (s(t₁, u₁) ::ₘ s(t₂, u₂) ::ₘ s(t₃, u₃) ::ₘ Δ) := by
  have h := autoMux_autoMux [t₁, t₂, t₃] [u₁, u₂, u₃] Δ rfl
  refine h.cast rfl ?_
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, ← Multiset.cons_coe,
    Multiset.coe_nil]
  ms

/-- The picture of page 83 for `n = 3`: `T_3` with free ports `0, 1, 2` against `T_3` with free
ports `3, 4, 5`, alone, reduces to the three wires `0–3`, `1–4`, `2–5`. -/
theorem autoMux_autoMux_figure :
    Red {s(autoMux [var 0, var 1, var 2], autoMux [var 3, var 4, var 5])}
      (s(var 0, var 3) ::ₘ s(var 1, var 4) ::ₘ {s(var 2, var 5)}) :=
  autoMux_autoMux_three (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) 0

/-- `γ` is not suitable (page 83), `n = 2`: a `con` against a `con` joins port 1 to port 2 and
port 2 to port 1, not port `i` to port `i`. -/
theorem conMux_conMux_two :
    Step system (s(mkCon t₁ t₂, mkCon u₁ u₂) ::ₘ Δ) (s(t₁, u₂) ::ₘ s(t₂, u₁) ::ₘ Δ) :=
  step_con_con t₁ t₂ u₁ u₂ Δ

/-- `γ` is not suitable (page 83), `n = 3`: `T_3` built with `con`, against itself, gives after
one step the equations `0 = con 4 5` and `con 1 2 = 3`. These are not wires between ports, and no
interaction is left: the two `con` cells face free ports. -/
theorem conMux_conMux_three :
    Step system {s(mkCon (var 0) (mkCon (var 1) (var 2)), mkCon (var 3) (mkCon (var 4) (var 5)))}
      (s(var 0, mkCon (var 4) (var 5)) ::ₘ {s(mkCon (var 1) (var 2), var 3)}) :=
  step_con_con _ _ _ _ 0

/-- A net in which every equation has a name on one side has no active pair: no step applies. -/
theorem no_step_of_var (N M : CNet) (hN : ∀ e ∈ N, ∃ x, Term.var x ∈ e) :
    ¬ Step system N M := by
  intro h
  cases h with
  | mk α β r hr as bs Δ f hf hfresh =>
    obtain ⟨x, hx⟩ := hN _ (Multiset.mem_cons_self _ _)
    rcases Sym2.mem_iff.1 hx with h0 | h0 <;> cases h0

/-- After its one step, `T_3` built with `con` against itself is stuck (page 83, "`γ` is not
suitable"). -/
theorem conMux_conMux_three_stuck (M : CNet) :
    ¬ Step system (s(var 0, mkCon (var 4) (var 5)) ::ₘ {s(mkCon (var 1) (var 2), var 3)}) M :=
  no_step_of_var _ M (by simp)

/-- The hypothesis `ts.length = us.length` of `autoMux_autoMux` is needed: `T_1` against `T_2`, with
free ports `0` and `1, 2`, does not reduce to the wire `0–1`, which is what the conclusion would
give (`List.zipWith` stops at the shorter list). -/
theorem autoMux_autoMux_length_needed :
    ¬ Red {s(autoMux [var 0], autoMux [var 1, var 2])} {s(var 0, var 1)} := by
  intro h
  rcases Relation.ReflTransGen.cases_head h with h | ⟨M, hstep, _⟩
  · have hmem : s(var 0, var 1) ∈ ({s(autoMux [var 0], autoMux [var 1, var 2])} : CNet) := by
      rw [h]; simp
    rw [Multiset.mem_singleton, Sym2.eq_iff] at hmem
    rcases hmem with ⟨_, h1⟩ | ⟨h1, _⟩ <;> cases h1
  · exact no_step_of_var _ M (by simp [autoMux]) hstep

end INet.Comb.AutoMuxCheck
