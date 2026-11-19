import InteractionCombinators.Lafont.ReducedClosed
import InteractionCombinators.Combinators
import Checks.ViciousReview

/-!
# Checks for "a reduced net with no free port is empty" (page 80)

`Net.IsReduced.eq_zero_of_closed` has three hypotheses besides the net: linear, reduced (no cut,
no vicious circle) and no free port. This file shows that they can hold together (for `0`) and
that dropping any one of the conditions "no cut", "no vicious circle", "no free port" makes the
conclusion false, on nets of combinators that are linear:

* `cutNet` — `con(0, 1) = con(1, 0)`: no free port, no vicious circle, a cut, not empty.
* `viciousNet` — `0 = con(0, 1), 1 = era`: no free port, no cut, a vicious circle, not empty.
* `freeNet` — `0 = era`: reduced, a free port, not empty.
* `wireCycle` — `0 = 1, 1 = 0`, a cycle of wires with no cell: no free port, not reduced.
-/

namespace INet.ReducedClosedCheck

open Term Comb Vicious

/-- Non-vacuity: the empty net satisfies every hypothesis of `Net.IsReduced.eq_zero_of_closed`
(Lafont 1997, page 80). -/
theorem zero_hyps : (0 : Net sig ℕ).Linear ∧ (0 : Net sig ℕ).IsReduced ∧
    ∀ x, (0 : Net sig ℕ).vars.count x ≠ 1 :=
  ⟨fun x => by simp, Net.isReduced_zero, fun x => by simp⟩

/-! ## No cut is needed -/

/-- `con(0, 1) = con(1, 0)`: two cells joined principal to principal, their auxiliary ports
joined (Lafont 1997, page 80: a cut). -/
def cutNet : Net sig ℕ := s(mkCon (var 0) (var 1), mkCon (var 1) (var 0)) ::ₘ 0

/-- `cutNet` is linear. -/
theorem cutNet_linear : cutNet.Linear := by
  intro y
  simp only [cutNet, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_mkCon,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- `cutNet` has no free port: `0` and `1` occur twice. -/
theorem cutNet_closed : ∀ x, cutNet.vars.count x ≠ 1 := by
  intro y
  simp only [cutNet, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_mkCon,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- `cutNet` has a cut (Lafont 1997, page 80). -/
theorem cutNet_hasCut : cutNet.HasCut :=
  Net.hasCut_of_mem (Multiset.mem_cons_self _ _)

/-- `cutNet` has no vicious circle: a circle needs an equation `x = t` with a name on one side,
and the only equation of `cutNet` joins two cells. -/
theorem cutNet_not_hasVicious : ¬ cutNet.HasVicious := by
  intro hv
  obtain ⟨K, D, ⟨x, y, t, C, -, -, rfl⟩, h⟩ := hv.chainVicious
  have hm : s(var x, t) ∈ cutNet := h ▸ Multiset.mem_add.2 (.inl (Multiset.mem_cons_self _ _))
  simp [cutNet, mkCon] at hm

/-- Without "no cut" the conclusion fails: `cutNet` is linear, has no free port and no vicious
circle, yet it is not empty. -/
theorem cutNet_ne_zero : cutNet ≠ 0 := Multiset.cons_ne_zero

/-! ## No vicious circle is needed -/

/-- `0 = con(0, 1), 1 = era`: the principal port of `con` on its own auxiliary port, a vicious
circle of length 1 (Lafont 1997, page 79); every name occurs twice. -/
def viciousNet : Net sig ℕ := s(var 0, mkCon (var 0) (var 1)) ::ₘ s(var 1, mkEra) ::ₘ 0

/-- `viciousNet` is linear. -/
theorem viciousNet_linear : viciousNet.Linear := by
  intro y
  simp only [viciousNet, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_mkCon,
    vars_mkEra, Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- `viciousNet` has no free port. -/
theorem viciousNet_closed : ∀ x, viciousNet.vars.count x ≠ 1 := by
  intro y
  simp only [viciousNet, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_mkCon,
    vars_mkEra, Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- `viciousNet` has a vicious circle: `0` is a leaf of `con(0, 1)` (page 79). -/
theorem viciousNet_hasVicious : viciousNet.HasVicious :=
  Net.hasVicious_of_mem (by simp) (Multiset.mem_cons_self _ _)

/-- `viciousNet` has no cut: no equation joins two cells, and a chain of wires from a cell would
need a second equation on the name next to that cell, which neither `0` nor `1` has. -/
theorem viciousNet_not_hasCut : ¬ viciousNet.HasCut := by
  intro hc
  obtain ⟨a, b, xs, D, ⟨α, ts, rfl⟩, ⟨β, us, rfl⟩, h⟩ := hc.chainCut
  match xs, h with
  | [], h =>
    have hm : s(app α ts, app β us) ∈ viciousNet := by rw [h]; simp
    simp [viciousNet] at hm
  | y :: ys, h =>
    have h2 : ∃ c D', s(app α ts, var y) ::ₘ s(var y, c) ::ₘ D' = viciousNet := by
      cases ys with
      | nil => exact ⟨app β us, D, by rw [h, Cut.chain_cons, Cut.chain_nil, Multiset.cons_add,
          Multiset.singleton_add]⟩
      | cons z zs => exact ⟨var z, Cut.chain (var z) zs (app β us) + D, by
          rw [h, Cut.chain_cons, Cut.chain_cons, Multiset.cons_add, Multiset.cons_add]⟩
    obtain ⟨c, D', h2⟩ := h2
    have hD : D' = 0 := by
      have := congrArg Multiset.card h2
      simp only [viciousNet, Multiset.card_cons, Multiset.card_zero] at this
      exact Multiset.card_eq_zero.1 (by omega)
    subst hD
    rw [viciousNet, Multiset.cons_zero] at h2
    clear h
    rcases ViciousReview.pair_eq_cons_cons h2.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Sym2.eq_iff, var.injEq, reduceCtorEq, false_and, or_false, false_or,
        mkCon, mkEra] at h1 h2 <;>
      obtain ⟨-, rfl⟩ := h1 <;>
      simp at h2

/-- Without "no vicious circle" the conclusion fails: `viciousNet` is linear, has no free port and
no cut, yet it is not empty. -/
theorem viciousNet_ne_zero : viciousNet ≠ 0 := Multiset.cons_ne_zero

/-! ## No free port is needed -/

/-- `0 = era`: an eraser on the free port `0`. -/
def freeNet : Net sig ℕ := s(var 0, mkEra) ::ₘ 0

/-- `freeNet` is linear. -/
theorem freeNet_linear : freeNet.Linear := by
  intro y
  simp only [freeNet, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var, vars_mkEra,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- `freeNet` is reduced: a tree on a free port (`Net.isReduced_tree`, page 79). -/
theorem freeNet_isReduced : freeNet.IsReduced :=
  Net.isReduced_tree (x := 0) (t := mkEra) (by simp)

/-- `0` is a free port of `freeNet`: it occurs once. -/
theorem freeNet_free : freeNet.vars.count 0 = 1 := by
  simp [freeNet]

/-- Without "no free port" the conclusion fails: `freeNet` is linear and reduced, yet it is
not empty. -/
theorem freeNet_ne_zero : freeNet ≠ 0 := Multiset.cons_ne_zero

/-! ## A cycle of wires is not reduced -/

/-- `0 = 1, 1 = 0`: a cycle of two wires and no cell. -/
def wireCycle : Net sig ℕ := s(var 0, var 1) ::ₘ s(var 1, var 0) ::ₘ 0

/-- `wireCycle` is linear. -/
theorem wireCycle_linear : wireCycle.Linear := by
  intro y
  simp only [wireCycle, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- `wireCycle` has no free port. -/
theorem wireCycle_closed : ∀ x, wireCycle.vars.count x ≠ 1 := by
  intro y
  simp only [wireCycle, Net.vars_cons, Net.vars_zero, eqVars_mk, vars_var,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- A cycle of wires is a vicious circle (Lafont 1997, page 79: "a cyclic wire can be considered
as a vicious circle of length 0"), so `wireCycle` is not reduced. -/
theorem wireCycle_not_isReduced : ¬ wireCycle.IsReduced := by
  intro h
  refine h.2 (Net.ChainVicious.hasVicious ?_ wireCycle_linear)
  refine ⟨wireCycle, 0, ⟨0, 1, var 1, s(var 1, var 0) ::ₘ 0, by simp,
    .cons (by simp) (.nil 0), rfl⟩, by simp⟩

/-- The theorem applied to `wireCycle` would give `wireCycle = 0`; it is not, which is
consistent only because `wireCycle` is not reduced. -/
theorem wireCycle_ne_zero : wireCycle ≠ 0 := Multiset.cons_ne_zero

end INet.ReducedClosedCheck
