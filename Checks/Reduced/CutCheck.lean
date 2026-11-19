import InteractionCombinators.Reduced.CutChain

/-!
# Checks of the cuts of Proposition 3 (page 80)

* A chain of two wires between two principal ports is a cut: `Net.HasCut` is not vacuous, and it
  sees more than the literal equations `α(…) = β(…)`.
* Without strictness a translation need not keep cuts. This is the remark at the end of the proof
  of Proposition 3, page 80: "it may happen that `N` contains a cut, and `Φ(N)` is reduced". The
  signature has a symbol `o` with no auxiliary port and a symbol `w` with one; `Φ` keeps `o` and
  translates `w` to a single wire. The net `w(x) = o` has a cut, its translation `x = o` has none.
* The first point through the same `Φ`: the translation `o = x, x = o` of `o = w(x), x = o` has a
  cut, and `Translation.NetTr.hasCut_reflect` finds the cut `o = w(x)` of the source.
-/

namespace INet.CutCheck

open Term

/-- Two symbols: `false` (written `o`) with no auxiliary port, `true` (written `w`) with one. -/
def sig : Signature := ⟨Bool, fun b => if b then 1 else 0⟩

/-- The cell `o`. -/
def o : Term sig ℕ := .app false (Fin.elim0 : Fin 0 → Term sig ℕ)

@[simp] theorem vars_o : o.vars = 0 := by simp [o, sig]

@[simp] theorem cells_o : o.cells = {false} := by
  simp [o, sig]
  rfl

/-- The cell `w(t)`. -/
def w (t : Term sig ℕ) : Term sig ℕ := .app true fun _ => t

/-- The principal net of arity one that is a single wire from its root to its port. -/
def wireNet : PNet sig 1 where
  internal := 0
  tree := .var (.inl 0)
  port_count i := by
    fin_cases i
    simp
  internal_count k := k.elim0

/-- `o` is kept, `w` becomes a wire. -/
def Φ : Translation sig sig := ⟨fun b => match b with
  | false => PNet.cell (S := sig) false
  | true => wireNet⟩

theorem not_strict : ¬ Φ.Strict := fun h => h true (.inl ⟨0, by simp [sig]⟩) rfl

/-! ## A chain of two wires is a cut -/

/-- `o = x₀, x₀ = x₁, x₁ = o`. -/
def chain2 : Net sig ℕ := s(o, var 0) ::ₘ s(var 0, var 1) ::ₘ {s(var 1, o)}

theorem chain2_linear : chain2.Linear := by
  intro y
  simp only [chain2, Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_o, vars_var,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- The two cells `o` joined by a chain of two wires make a cut. -/
theorem chain2_hasCut : chain2.HasCut := by
  refine Net.ChainCut.hasCut ⟨o, o, [0, 1], 0, ⟨false, _, rfl⟩, ⟨false, _, rfl⟩, ?_⟩ chain2_linear
  simp [chain2, Cut.chain]

/-- The chain has no literal cut: no equation of it is between two cells. -/
theorem chain2_no_literal : ∀ e ∈ chain2, ∀ (α β : sig.Sym) (ts : Fin (sig.arity α) → Term sig ℕ)
    (us : Fin (sig.arity β) → Term sig ℕ), e ≠ s(Term.app α ts, Term.app β us) := by
  intro e he α β ts us h
  simp only [chain2, Multiset.mem_cons, Multiset.mem_singleton] at he
  rcases he with rfl | rfl | rfl <;> simp [o] at h

/-! ## A non-strict translation can lose a cut -/

/-- `w(x₀) = o`: a cut. -/
def src : Net sig ℕ := {s(w (var 0), o)}

/-- `x₀ = o`: its translation. -/
def tgt : Net sig ℕ := {s(var 0, o)}

theorem src_hasCut : src.HasCut := Net.hasCut_of_mem (Multiset.mem_singleton_self _)

theorem netTr_src : Φ.NetTr src tgt := by
  have ha : Φ.TermTr (w (var 0)) (var 0) :=
    Translation.TermTr.app (Φ := Φ) true (fun _ => var 0) (fun _ => var 0) (fun _ => 0)
      fun _ => .var 0
  have hb : Φ.TermTr o o :=
    Translation.TermTr.app (Φ := Φ) false _ (Fin.elim0 : Fin 0 → Term sig ℕ) (fun _ => 0)
      fun i => i.elim0
  refine ⟨Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, ha, hb⟩ Multiset.Rel.zero, fun y => ?_⟩
  simp only [tgt, Net.vars_singleton, eqVars_mk, vars_o, vars_var, Multiset.count_add,
    Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

/-- The translation has no cut: it has a single cell, and equivalence keeps the cells. -/
theorem tgt_not_hasCut : ¬ tgt.HasCut := by
  rintro ⟨K, hE, α, β, ts, us, hm⟩
  obtain ⟨K', rfl⟩ := Multiset.exists_cons_of_mem hm
  have h := congrArg Multiset.card hE.cells_eq
  rw [Net.cells_cons, eqCells_mk, Term.cells_app, Term.cells_app] at h
  simp [tgt, Net.cells] at h
  erw [Multiset.card_singleton] at h
  omega

/-- **The converse of the second point fails without strictness** (Lafont 1997, page 80): a net
with a cut whose translation by a non-strict `Φ` has none. -/
theorem nonstrict_loses_cut :
    ¬ Φ.Strict ∧ src.HasCut ∧ Φ.NetTr src tgt ∧ ¬ tgt.HasCut :=
  ⟨not_strict, src_hasCut, netTr_src, tgt_not_hasCut⟩

/-! ## The first point through a cell translated to a wire -/

/-- `o = w(x₀), x₀ = o`. -/
def src2 : Net sig ℕ := s(o, w (var 0)) ::ₘ {s(var 0, o)}

/-- `o = x₀, x₀ = o`: its translation, a chain of one wire between two cells. -/
def tgt2 : Net sig ℕ := s(o, var 0) ::ₘ {s(var 0, o)}

theorem tgt2_linear : tgt2.Linear := by
  intro y
  simp only [tgt2, Net.vars_cons, Net.vars_singleton, eqVars_mk, vars_o, vars_var,
    Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
  split_ifs <;> omega

theorem netTr_src2 : Φ.NetTr src2 tgt2 := by
  have ha : Φ.TermTr (w (var 0)) (var 0) :=
    Translation.TermTr.app (Φ := Φ) true (fun _ => var 0) (fun _ => var 0) (fun _ => 0)
      fun _ => .var 0
  have hb : Φ.TermTr o o :=
    Translation.TermTr.app (Φ := Φ) false _ (Fin.elim0 : Fin 0 → Term sig ℕ) (fun _ => 0)
      fun i => i.elim0
  exact ⟨Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, hb, ha⟩
    (Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, .var 0, hb⟩ Multiset.Rel.zero), tgt2_linear⟩

theorem tgt2_hasCut : tgt2.HasCut := by
  refine Net.ChainCut.hasCut ⟨o, o, [0], 0, ⟨false, _, rfl⟩, ⟨false, _, rfl⟩, ?_⟩ tgt2_linear
  simp [tgt2, Cut.chain]

/-- The first point of the proof, through a cell translated to a wire (Lafont 1997, page 80): the
cut `o = x₀, x₀ = o` of the translation passes through the wire of `w`; in the source the chain
stops at the principal port of `w`, and `o = w(x₀)` is the cut. -/
example : src2.HasCut := netTr_src2.hasCut_reflect tgt2_hasCut

end INet.CutCheck
