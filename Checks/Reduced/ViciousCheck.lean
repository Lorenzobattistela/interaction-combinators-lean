import InteractionCombinators.Reduced.Vicious
import Checks.Reduced.CutCheck

/-!
# Checks of vicious circles and reduced nets (pages 79–80)

The signature of `Checks/Reduced/CutCheck.lean`: a symbol `o` with no auxiliary port, a symbol `w`
with one, and the non-strict translation `Φ` that keeps `o` and turns `w` into a wire.

* `Net.HasVicious` is not vacuous: the cyclic wire `x = x`, the circle `w(x) = x` of length 1, and
  the circle `x₀ = w(x₁), x₁ = w(x₀)` of length 2, written with two equations, have one.
* It is not trivial: the linear net `x₀ = w(x₁), x₁ = w(o)` is reduced (it is the tree `w(w(o))`
  plugged into the free port `x₀`).
* Page 80: "the translation may create cyclic wires". `Φ` translates `x = w(x)` to `x = x`, and the
  fourth point of Proposition 3 finds the cyclic wire.
* Page 80: "it may happen that `Φ(N)` contains a vicious circle, and `N` contains no vicious
  circle, but a cut". The net `w(x) = w(x)` is such an `N`: its translation is `x = x`.
-/

namespace INet.ViciousCheck

open Term CutCheck

/-! ## Nets with a vicious circle -/

/-- The leaves of `w(t)` are those of `t`. -/
@[simp] theorem vars_w (t : Term sig ℕ) : (w t).vars = t.vars := by
  show (∑ _i : Fin 1, t.vars) = t.vars
  simp

/-- The cyclic wire `x₀ = x₀`, a vicious circle of length 0 (page 79). -/
theorem cyclic_hasVicious : Net.HasVicious ({s(var 0, var 0)} : Net sig ℕ) :=
  Net.hasVicious_of_mem (by simp) (Multiset.mem_singleton_self _)

/-- The cyclic wire is linear: the hypothesis of `cyclic_hasVicious` is not a degenerate net. -/
theorem cyclic_linear : Net.Linear ({s(var 0, var 0)} : Net sig ℕ) := by
  intro y
  simp only [Net.vars_singleton, eqVars_mk, vars_var, Multiset.count_add,
    Multiset.count_singleton]
  split_ifs <;> omega

/-- `w(x₀) = x₀`: the principal port of `w` on its own auxiliary port, a vicious circle of
length 1 (page 79). -/
theorem loop1_hasVicious : Net.HasVicious ({s(w (var 0), var 0)} : Net sig ℕ) := by
  rw [Sym2.eq_swap]
  exact Net.hasVicious_of_mem (by simp) (Multiset.mem_singleton_self _)

/-- `x₀ = w(x₁), x₁ = w(x₀)`: two cells, each with its principal port on the auxiliary port of the
other. -/
def loop2 : Net sig ℕ := s(var 0, w (var 1)) ::ₘ {s(var 1, w (var 0))}

/-- `loop2` is linear. -/
theorem loop2_linear : loop2.Linear := by
  intro y
  simp only [loop2, Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_var, vars_w,
    Multiset.count_add, Multiset.count_singleton]
  split_ifs <;> omega

/-- A vicious circle of length 2 written with two equations (page 79): no equation of `loop2` is a
circle on its own, the two together are. -/
theorem loop2_hasVicious : loop2.HasVicious := by
  refine Net.ChainVicious.hasVicious ⟨loop2, 0, ⟨0, 1, w (var 1), {s(var 1, w (var 0))},
    by simp, .cons (by simp) (.nil 0), rfl⟩, by simp⟩ loop2_linear

/-! ## A linear net with no vicious circle -/

/-- `x₀ = w(x₁), x₁ = w(o)`. -/
def chainNet : Net sig ℕ := s(var 0, w (var 1)) ::ₘ {s(var 1, w o)}

/-- `chainNet` is linear. -/
theorem chainNet_linear : chainNet.Linear := by
  intro y
  simp only [chainNet, Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_var, vars_w, vars_o,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- **A linear net with no cut and no vicious circle** (page 79): `chainNet` is the same graph as
the tree `w(w(o))` plugged into the free port `x₀`, which is reduced. -/
theorem chainNet_isReduced : chainNet.IsReduced := by
  have e : chainNet = s(var 1, w o) ::ₘ s(var 0, w (var 1)) ::ₘ 0 := Multiset.cons_swap _ _ _
  have W : Wire chainNet {s(var 0, w (w o))} := by
    refine (Wire.mk 1 (w o) (var 0) (w (var 1)) 0 (chainNet_linear.cast e) (by simp)).cast
      e.symm ?_
    rfl
  refine (Net.isReduced_tree ?_).of_equiv W.equiv.symm
  simp

/-! ## A non-strict translation creates a cyclic wire -/

/-- `Φ` translates `x₀ = w(x₀)` to the cyclic wire `x₀ = x₀`. -/
theorem netTr_loop1 : Φ.NetTr {s(var 0, w (var 0))} {s(var 0, var 0)} := by
  have ha : Φ.TermTr (w (var 0)) (var 0) :=
    Translation.TermTr.app (Φ := Φ) true (fun _ => var 0) (fun _ => var 0) (fun _ => 0)
      fun _ => .var 0
  exact ⟨Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, .var 0, ha⟩ Multiset.Rel.zero, cyclic_linear⟩

/-- The fourth point of Proposition 3 through a cell translated to a wire (page 80): the circle
`x₀ = w(x₀)` becomes the cyclic wire `x₀ = x₀`, which `Translation.NetTr.hasVicious` finds. -/
example : Net.HasVicious ({s(var 0, var 0)} : Net sig ℕ) :=
  netTr_loop1.hasVicious (Net.hasVicious_of_mem (by simp) (Multiset.mem_singleton_self _))

/-! ## A vicious circle of the translation can come from a cut -/

/-- `w(x₀) = w(x₀)`: a cut between two `w`, their auxiliary ports joined. -/
def cutLoop : Net sig ℕ := {s(w (var 0), w (var 0))}

/-- `w(x₀) = w(x₀)` is a cut (page 80). -/
theorem cutLoop_hasCut : cutLoop.HasCut := Net.hasCut_of_mem (Multiset.mem_singleton_self _)

/-- `w(x₀) = w(x₀)` has no vicious circle: its only equation joins two cells. -/
theorem cutLoop_not_hasVicious : ¬ cutLoop.HasVicious := by
  intro hv
  obtain ⟨K, D, ⟨x₀, y, t₀, C, -, -, rfl⟩, h⟩ := hv.chainVicious
  rw [cutLoop, Multiset.cons_add, Multiset.singleton_eq_cons_iff] at h
  rcases Sym2.eq_iff.1 h.1 with ⟨h', -⟩ | ⟨-, h'⟩ <;> simp [w] at h'

/-- `Φ` translates `w(x₀) = w(x₀)` to the cyclic wire `x₀ = x₀`. -/
theorem netTr_cutLoop : Φ.NetTr cutLoop {s(var 0, var 0)} := by
  have ha : Φ.TermTr (w (var 0)) (var 0) :=
    Translation.TermTr.app (Φ := Φ) true (fun _ => var 0) (fun _ => var 0) (fun _ => 0)
      fun _ => .var 0
  exact ⟨Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, ha, ha⟩ Multiset.Rel.zero, cyclic_linear⟩

/-- **The remark after Proposition 3** (page 80): "it may happen that `Φ(N)` contains a vicious
circle, and `N` contains no vicious circle, but a cut". With `N` the net `w(x₀) = w(x₀)` and `Φ`
turning `w` into a wire, `Φ(N)` is the cyclic wire `x₀ = x₀`. -/
theorem translation_circle_from_cut :
    cutLoop.HasCut ∧ ¬ cutLoop.HasVicious ∧ Φ.NetTr cutLoop {s(var 0, var 0)} ∧
      Net.HasVicious ({s(var 0, var 0)} : Net sig ℕ) :=
  ⟨cutLoop_hasCut, cutLoop_not_hasVicious, netTr_cutLoop, cyclic_hasVicious⟩

end INet.ViciousCheck
