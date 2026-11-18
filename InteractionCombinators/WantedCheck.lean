import InteractionCombinators.Wanted
import InteractionCombinators.Rename
import InteractionCombinators.Combinators

/-!
# Checks of the statements of `Wanted.lean` on concrete nets

`Wanted.lean` states `Equiv.add_right`, `StepsE.add_right` and `Translation.NetTr.equiv` without
proof. This file does not prove them. It records what a review found when trying to refute them
(issue 9): small nets on which the hypotheses hold, and nets showing that a hypothesis or a part of
a conclusion cannot be dropped.

* `equiv_add_right_needs_linear_right`, `equiv_add_right_needs_linear_left` — in
  `Equiv.add_right`, neither linearity hypothesis follows from the other, and without either one
  the conclusion fails.
* `equiv_add_right_shared_port` — the conclusion of `Equiv.add_right` on a net where the context
  shares a free port with the net.
* `stepsE_add_right_must_rename` — in `StepsE.add_right`, the result `M'` cannot always be `M`
  itself: a reduction may create a wire whose name is used by the context.
* `netTr_two_translations` — the hypotheses of `Translation.NetTr.equiv` hold for two different
  translations of one net, and its conclusion holds for them.
-/

namespace INet.WantedCheck

open Term

/-- Linearity, or a count of names, of a net written out with numerals. -/
local macro "names" : tactic =>
  `(tactic| (simp [Multiset.count_cons, Multiset.count_singleton] <;> (try split_ifs) <;> omega))

section Equiv

variable {S : Signature}

/-- A wire with free ports `1` and `2`. -/
def short : Net S ℕ := {s(var 1, var 2)}

/-- The same wire, spelled with an internal name `0`. -/
def long : Net S ℕ := s(var 0, var 1) ::ₘ {s(var 0, var 2)}

/-- A cyclic wire named `0`. -/
def loop : Net S ℕ := {s(var 0, var 0)}

theorem wire_long_short : Wire (long : Net S ℕ) short := by
  have h := Wire.mk (S := S) 0 (var 1) (var 0) (var 2) 0 (by intro y; names) (by simp)
  simpa [Term.subst, long, short] using h

theorem equiv_short_long : Equiv (short : Net S ℕ) long := wire_long_short.equiv.symm

theorem short_loop_linear : ((short : Net S ℕ) + loop).Linear := by
  intro y; simp only [short, loop]; names

theorem long_loop_not_linear : ¬ ((long : Net S ℕ) + loop).Linear := by
  intro h
  have := h 0
  simp [long, loop] at this

/-- In `Equiv.add_right` (page 72: a net is a graph), the hypothesis `hM` cannot be dropped: here
`N` and `M` are equivalent and `N + Γ` is linear, but `M + Γ` is not linear, and the two larger
nets are not equivalent. The context `Γ` uses the name of an internal wire of `M`. -/
theorem equiv_add_right_needs_linear_right :
    ∃ N M Γ : Net S ℕ, Equiv N M ∧ (N + Γ).Linear ∧ ¬ Equiv (N + Γ) (M + Γ) :=
  ⟨short, long, loop, equiv_short_long, short_loop_linear,
    fun h => long_loop_not_linear (h.linear short_loop_linear)⟩

/-- In `Equiv.add_right`, the hypothesis `hN` cannot be dropped either. -/
theorem equiv_add_right_needs_linear_left :
    ∃ N M Γ : Net S ℕ, Equiv N M ∧ (M + Γ).Linear ∧ ¬ Equiv (N + Γ) (M + Γ) :=
  ⟨long, short, loop, equiv_short_long.symm, short_loop_linear,
    fun h => long_loop_not_linear (h.symm.linear short_loop_linear)⟩

/-- The conclusion of `Equiv.add_right` on a net where the context shares the free port `1` with
the net: both hypotheses hold and the two larger nets are equivalent. -/
theorem equiv_add_right_shared_port :
    Equiv (short : Net S ℕ) long ∧ ((short : Net S ℕ) + {s(var 1, var 3)}).Linear ∧
      ((long : Net S ℕ) + {s(var 1, var 3)}).Linear ∧
      Equiv ((short : Net S ℕ) + {s(var 1, var 3)}) (long + {s(var 1, var 3)}) := by
  have hl : ((long : Net S ℕ) + {s(var 1, var 3)}).Linear := by
    intro y; simp only [long]; names
  exact ⟨equiv_short_long, (wire_long_short.add_right _ hl).linear_right, hl,
    (wire_long_short.add_right _ hl).equiv.symm⟩

end Equiv

section Steps

open Comb

/-- A `con` and a `dup` plugged by their principal ports. -/
def cut : CNet := {s(mkCon (var 0) (var 1), mkDup (var 2) (var 3))}

/-- The result of their interaction, with the four new wires named `4`, `5`, `6`, `7`. -/
def cutResult : CNet :=
  s(var 0, mkDup (var 4) (var 5)) ::ₘ s(var 1, mkDup (var 6) (var 7)) ::ₘ
    s(var 2, mkCon (var 4) (var 6)) ::ₘ {s(var 3, mkCon (var 5) (var 7))}

/-- A context that uses the name `4`. -/
def ctx : CNet := {s(var 4, var 4)}

/-- In `StepsE.add_right` the result is `M` only up to equivalence, and this cannot be improved:
here `N` reduces to `M` and `N + Γ` is linear, but `M + Γ` is not linear, so `M' = M` does not
satisfy the conclusion. The interaction creates a wire named `4`, which `Γ` uses. -/
theorem stepsE_add_right_must_rename :
    StepsE system cut cutResult ∧ (cut + ctx).Linear ∧ ¬ (cutResult + ctx).Linear := by
  refine ⟨?_, ?_, ?_⟩
  · have h := step_con_dup (var 0) (var 1) (var 2) (var 3) 0 4 5 6 7 (by decide) (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> simp)
    exact (Steps.single h).stepsE
  · intro y; simp only [cut, ctx]; names
  · intro h
    have := h 4
    simp [cutResult, ctx] at this

end Steps

section Translation

open Comb

/-- A signature with one symbol, without auxiliary port. -/
def unitSig : Signature := ⟨Unit, fun _ => 0⟩

/-- The symbol is translated to a `con` whose auxiliary ports are joined by an internal wire. -/
def tr : Translation unitSig sig where
  net _ :=
    { internal := 1
      tree := mkCon (var (.inr 0)) (var (.inr 0))
      port_count := fun i => i.elim0
      internal_count := fun w => by fin_cases w; simp }

/-- One cell on the free port `0`. -/
def source : Net unitSig ℕ := {s(.app () fun i => i.elim0, var 0)}

/-- Its translation, with the internal wire named `k`. -/
def target (k : ℕ) : CNet := {s(mkCon (var k) (var k), var 0)}

theorem netTr_target {k : ℕ} (hk : k ≠ 0) : tr.NetTr source (target k) := by
  constructor
  · have h := Translation.TermTr.app (Φ := tr) () (fun i => i.elim0) (fun i => i.elim0)
      (fun _ => k) (fun i => i.elim0)
    have e : (tr.net ()).inst (fun i => i.elim0) (fun _ => k) = mkCon (var k) (var k) := by
      simp [PNet.inst, tr]
    rw [e] at h
    exact Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, h, Translation.TermTr.var 0⟩ Multiset.Rel.zero
  · intro y
    have : (0 : ℕ) ≠ k := fun h => hk h.symm
    simp only [target]; names

/-- The hypotheses of `Translation.NetTr.equiv` (page 80: a translation extends to nets) hold for
two different nets, which differ by the name of an internal wire of an instance, and the
conclusion holds for them. -/
theorem netTr_two_translations :
    tr.NetTr source (target 1) ∧ tr.NetTr source (target 2) ∧ target 1 ≠ target 2 ∧
      Equiv (target 1) (target 2) := by
  refine ⟨netTr_target (by decide), netTr_target (by decide), ?_, ?_⟩
  · intro h
    have := congrArg (fun N : CNet => N.vars.count 1) h
    simp [target] at this
  · have h := Net.equiv_rename (N := target 1) (netTr_target (by decide)).linear (x := 1) (y := 2)
      (by simp [target]) (by simp [target])
    have e : (target 1).rename 1 2 = target 2 := by
      simp [target, Net.rename, Term.subst]
    rwa [e] at h

end Translation

end INet.WantedCheck
