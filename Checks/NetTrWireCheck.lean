import InteractionCombinators.NetTrWire
import Checks.NetTrEquivCheck

/-!
# Concrete checks of `Translation.NetTr.of_equiv`

Lafont 1997, Section 1.7, pages 79-80. The net `source3` is `NetTrEquivCheck.source2` with an
extra wire. Its translation is equivalent to a translation of `source2`.
-/

namespace INet.NetTrWireCheck

open Term Comb WantedCheck NetTrEquivCheck

/-- Linearity, or a count of names, of a net written out with numerals. -/
local macro "names" : tactic =>
  `(tactic| (simp [Multiset.count_cons, Multiset.count_singleton] <;> (try split_ifs) <;> omega))

/-- The cell of `unitSig`, which has no auxiliary port. -/
abbrev c : Term unitSig ℕ := .app () fun i => i.elim0

@[simp] theorem vars_c : c.vars = 0 := rfl

/-- `source2` spelled with an extra wire `2` between the first cell and the free port `0`. -/
def source3 : Net unitSig ℕ := s(var 2, c) ::ₘ s(var 2, var 0) ::ₘ {s(c, var 1)}

/-- One wire substitution takes `source3` to `source2`. -/
theorem wire_source3 : Wire source3 source2 := by
  have h := Wire.mk 2 c (var 2) (var 0) {s(c, var 1)} (by unfold Net.Linear; intro y; names)
    (by simp)
  exact h.cast rfl (by simp [Term.subst, source2])

/-- A translation of `source3`, with the internal wires named `a` and `b`. -/
def target3 (a b : ℕ) : CNet :=
  s(var 2, mkCon (var a) (var a)) ::ₘ s(var 2, var 0) ::ₘ {s(mkCon (var b) (var b), var 1)}

/-- `target3 5 6` is a translation of `source3` (Lafont 1997, Section 1.7, page 80). -/
theorem netTr_target3 : tr.NetTr source3 (target3 5 6) := by
  have inst : ∀ k : ℕ, tr.TermTr c (mkCon (var k) (var k)) := by
    intro k
    have h := Translation.TermTr.app (Φ := tr) () (fun i => i.elim0) (fun i => i.elim0)
      (fun _ => k) (fun i => i.elim0)
    have e : (tr.net ()).inst (fun i => i.elim0) (fun _ => k) = mkCon (var k) (var k) := by
      simp [PNet.inst, tr]
    rwa [e] at h
  constructor
  · exact Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, Translation.TermTr.var 2, inst 5⟩
      (Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, Translation.TermTr.var 2,
        Translation.TermTr.var 0⟩
        (Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, inst 6, Translation.TermTr.var 1⟩
          Multiset.Rel.zero))
  · intro y
    simp only [target3]; names

/-- `Translation.NetTr.of_equiv` is not vacuous: every hypothesis holds for the non-identity
translation `tr` and the wire substitution `wire_source3`, and the translation of `source2` it
gives is equivalent to `target3 5 6` (Lafont 1997, Section 1.7, page 80). -/
example : ∃ M', tr.NetTr source2 M' ∧ Equiv (target3 5 6) M' :=
  Translation.NetTr.of_equiv wire_source3.equiv netTr_target3

/-- Combined with `Translation.NetTr.equiv`: the translations `target3 5 6` of `source3` and
`target2 5 6` of `source2` are equivalent. -/
example : Equiv (target3 5 6) (target2 5 6) := by
  obtain ⟨M', hM', e⟩ := Translation.NetTr.of_equiv wire_source3.equiv netTr_target3
  exact e.trans (Translation.NetTr.equiv hM' (netTr_target2 (by decide) (by decide) (by decide)))

end INet.NetTrWireCheck
