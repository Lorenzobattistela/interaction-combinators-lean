import InteractionCombinators.Lafont.PackageDecomp

/-!
# Review of `decomp` and `package_decomp` (Lafont 1997, page 88)

Checks for the review issue #63. The picture of page 88 cuts the `n` `dup` cells out of a package
`π`; `π'` is the rest. Here:

* the five shapes the issue asks for (no `dup`, one, two nested, two side by side, a wire joining
  the two auxiliary ports of one `dup`), computed by `rfl` and compared with the decomposition
  worked by hand;
* for each hypothesis of `package_decomp` (package, linear, bound on the names), an instance where
  only that hypothesis fails and a conclusion of `package_decomp` is false.
-/

namespace INet.Comb

open Term

/-! ## The five shapes -/

/-- No `dup`, page 88 with `n = 0`: nothing is cut, `π' = π`. -/
example : decomp 0 (mkCon mkEra mkEra : Term sig ℕ) = ⟨mkCon mkEra mkEra, [], 2⟩ := rfl

/-- One `dup`, `dup(0, con(0, ε))`, new names from `1`: the cell is cut at `1`, `τ` is the wire `1`
from the root to its principal port, `l₀ = 0`, `r₀ = con(0, ε)`. -/
example : decomp 1 (mkDup (var 0) (mkCon (var 0) mkEra) : Term sig ℕ) =
    ⟨var 1, [(1, var 0, mkCon (var 0) mkEra)], 6⟩ := rfl

/-- Two nested `dup` cells, the inner one on the right auxiliary port of the outer one:
`con(dup(0, dup(0, 1)), 1)`, new names from `2`. The outer cell is cut at `4`, the inner one at
`7`; the right auxiliary tree of the outer cell is the name `7`. Cells are listed outer first. -/
example : decomp 2 (mkCon (mkDup (var 0) (mkDup (var 0) (var 1))) (var 1) : Term sig ℕ) =
    ⟨mkCon (var 4) (var 1), [(4, var 0, var 7), (7, var 0, var 1)], 10⟩ := rfl

/-- Two `dup` cells side by side, `con(dup(0, 1), dup(0, 1))`, new names from `2`: the left one is
cut at `4`, the right one at `7`, and listed in this order. -/
example : decomp 2 (mkCon (mkDup (var 0) (var 1)) (mkDup (var 0) (var 1)) : Term sig ℕ) =
    ⟨mkCon (var 4) (var 7), [(4, var 0, var 1), (7, var 0, var 1)], 10⟩ := rfl

/-- A wire joining the two auxiliary ports of one `dup`, `dup(0, 0)`, new names from `1`: `π'` is
two wires, the wire `1` from the root to the principal port and the wire `0` between the two
auxiliary ports. -/
example : decomp 1 (mkDup (var 0) (var 0) : Term sig ℕ) = ⟨var 1, [(1, var 0, var 0)], 4⟩ := rfl

/-- `dup(0, 0)` is a package. -/
theorem isPackage_dup00 : (mkDup (var 0) (var 0) : Term sig ℕ).IsPackage := by
  intro x hx
  simp only [vars_mkDup, vars_var, Multiset.mem_add, Multiset.mem_singleton, or_self] at hx
  subst hx
  simp [vars_mkDup]

/-- `package_decomp` on the side-by-side shape: its hypotheses hold, and the net it gives is the
one worked by hand. -/
example : Equiv ({s(var 9, mkCon (mkDup (var 0) (var 1)) (mkDup (var 0) (var 1)))} : CNet)
    {s(var 9, mkCon (var 12) (var 15)), s(var 12, mkDup (var 0) (var 1)),
      s(var 15, mkDup (var 0) (var 1))} := by
  have hπ : (mkCon (mkDup (var 0) (var 1)) (mkDup (var 0) (var 1)) : Term sig ℕ).IsPackage := by
    intro x hx
    simp only [vars_mkDup, vars_mkCon, vars_var, Multiset.mem_add, Multiset.mem_singleton] at hx
    simp only [vars_mkDup, vars_mkCon, vars_var, Multiset.count_add, Multiset.count_singleton]
    rcases hx with ((rfl | rfl) | (rfl | rfl)) <;> simp
  have h := (package_decomp _ hπ (var 9) 0 10
    (by
      intro y
      simp only [Net.vars_cons, Net.vars_zero, eqVars_mk, vars_mkDup, vars_mkCon, vars_var,
        add_zero, Multiset.count_add, Multiset.count_singleton]
      split_ifs <;> omega)
    (by simp [Net.Below])).1
  have e : decomp 10 (mkCon (mkDup (var 0) (var 1)) (mkDup (var 0) (var 1)) : Term sig ℕ) =
      ⟨mkCon (var 12) (var 15), [(12, var 0, var 1), (15, var 0, var 1)], 18⟩ := rfl
  rw [e] at h
  simp only [Decomp.net, Decomp.cellEq, List.map_cons, List.map_nil, add_zero] at h
  exact h

/-! ## Each hypothesis is needed -/

/-- A net that is not linear is `Equiv` to itself only: no wire substitution applies to it, since
`Wire` needs a linear net on the left and gives one on the right. -/
theorem Equiv.eq_of_not_linear {N M : CNet} (h : Equiv N M) :
    (¬ N.Linear → N = M) ∧ (¬ M.Linear → N = M) := by
  induction h with
  | rel _ _ h => exact ⟨fun hn => absurd h.linear_left hn, fun hn => absurd h.linear_right hn⟩
  | refl _ => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | symm _ _ _ ih => exact ⟨fun hn => (ih.2 hn).symm, fun hn => (ih.1 hn).symm⟩
  | trans _ M _ _ _ ih ih' =>
    refine ⟨fun hn => ?_, fun hn => ?_⟩
    · have e := ih.1 hn
      exact e.trans (ih'.1 (e ▸ hn))
    · have e := ih'.2 hn
      exact (ih.2 (e ▸ hn)).trans e

/-- **Linearity is needed** (page 88; nets are linear by definition, page 70). `s(0, dup(0, 0))`:
the tree is a package, the names are below `1`, but the name `0` occurs three times. The net
`package_decomp` would give has two equations, the given one has one, and a net that is not linear
is `Equiv` to no other net, so the first conclusion of `package_decomp` fails. -/
theorem package_decomp_needs_linear :
    (mkDup (var 0) (var 0) : Term sig ℕ).IsPackage ∧
      Net.Below 1 ({s(var 0, mkDup (var 0) (var 0))} : CNet) ∧
      ¬ Net.Linear ({s(var 0, mkDup (var 0) (var 0))} : CNet) ∧
      ¬ Equiv ({s(var 0, mkDup (var 0) (var 0))} : CNet)
        (s(var 0, (decomp 1 (mkDup (var 0) (var 0))).τ) ::ₘ
          ((decomp 1 (mkDup (var 0) (var 0))).net + 0)) := by
  have hnl : ¬ Net.Linear ({s(var 0, mkDup (var 0) (var 0))} : CNet) := fun h => by
    have := h 0
    simp [eqVars_mk, vars_mkDup] at this
  refine ⟨isPackage_dup00, by simp [Net.Below, vars_mkDup], hnl, fun h => ?_⟩
  have e := congrArg Multiset.card ((Equiv.eq_of_not_linear h).1 hnl)
  simp [Decomp.net, decomp_mkDup, decomp_var] at e

/-- **The package hypothesis is needed** for the free ports of `π'` (page 88: `3n + 1` free
ports). `dup(0, 1)` under an eraser is linear with names below `2`, but it is not a package: its
leaves `0`, `1` are free. They stay free in `π'`, so the free names of `π'` are not only the cut
name `2`. (The `Equiv` of `package_decomp` does not use this hypothesis: `decomp_equiv`.) -/
theorem package_decomp_needs_package :
    ¬ (mkDup (var 0) (var 1) : Term sig ℕ).IsPackage ∧
      Net.Linear ({s(mkEra, mkDup (var 0) (var 1))} : CNet) ∧
      Net.Below 2 ({s(mkEra, mkDup (var 0) (var 1))} : CNet) ∧
      ¬ (∀ y, (decomp 2 (mkDup (var 0) (var 1) : Term sig ℕ)).vars'.count y = 1 ↔
        y ∈ (decomp 2 (mkDup (var 0) (var 1) : Term sig ℕ)).ports) := by
  refine ⟨fun h => ?_, fun y => ?_, by simp [Net.Below, vars_mkDup], fun h => ?_⟩
  · have := h 0 (by simp [vars_mkDup])
    simp [vars_mkDup] at this
  · simp only [Net.vars_singleton, eqVars_mk, vars_mkEra, vars_mkDup, vars_var,
      zero_add, Multiset.count_add, Multiset.count_singleton]
    split_ifs <;> omega
  · have := (h 0).1
    simp [Decomp.vars', Decomp.auxVars, Decomp.ports, decomp_mkDup, decomp_var] at this

/-- **The bound on the names is needed.** `dup(0, 0)` under an eraser is a package in a linear net,
but its names are not below `0`. Then `decomp 0` cuts the cell at the name `0`, which the net
already uses: the cut name is not new, it occurs three times in `π'`, and the net `package_decomp`
would give is not linear, hence not `Equiv` to the given one. -/
theorem package_decomp_needs_below :
    (mkDup (var 0) (var 0) : Term sig ℕ).IsPackage ∧
      Net.Linear ({s(mkEra, mkDup (var 0) (var 0))} : CNet) ∧
      ¬ Net.Below 0 ({s(mkEra, mkDup (var 0) (var 0))} : CNet) ∧
      (decomp 0 (mkDup (var 0) (var 0) : Term sig ℕ)).vars'.count 0 = 3 ∧
      0 ∈ (decomp 0 (mkDup (var 0) (var 0) : Term sig ℕ)).ports ∧
      0 ∈ Net.vars ({s(mkEra, mkDup (var 0) (var 0))} : CNet) ∧
      ¬ Equiv ({s(mkEra, mkDup (var 0) (var 0))} : CNet)
        (s(mkEra, (decomp 0 (mkDup (var 0) (var 0))).τ) ::ₘ
          ((decomp 0 (mkDup (var 0) (var 0))).net + 0)) := by
  have hlin : Net.Linear ({s(mkEra, mkDup (var 0) (var 0))} : CNet) := fun y => by
    simp only [Net.vars_singleton, eqVars_mk, vars_mkEra, vars_mkDup, vars_var,
      zero_add, Multiset.count_add, Multiset.count_singleton]
    split_ifs <;> omega
  refine ⟨isPackage_dup00, hlin, fun h => ?_, ?_, ?_, ?_, fun h => ?_⟩
  · exact absurd (h 0 (by simp [eqVars_mk, vars_mkDup])) (by omega)
  · simp [Decomp.vars', Decomp.auxVars, decomp_mkDup, decomp_var]
  · simp [Decomp.ports, decomp_mkDup]
  · simp [eqVars_mk, vars_mkDup]
  · have := h.linear hlin 0
    simp [Decomp.net, Decomp.cellEq, decomp_mkDup, decomp_var, Net.vars_cons, eqVars_mk, vars_mkDup,
      vars_mkEra] at this

end INet.Comb
