import InteractionCombinators.Text.NetTrEquiv
import Checks.Misc.WantedCheck

/-!
# Concrete checks of `Translation.NetTr.equiv`

Lafont 1997, Section 1.7, page 80. Two concrete checks on translations whose principal net has an
internal wire: the theorem applies to the translations of the one-cell net `WantedCheck.source`,
and to two different translations of the two-cell net `source2`.
-/

namespace INet.NetTrEquivCheck

open Term Comb WantedCheck

/-- Linearity, or a count of names, of a net written out with numerals. -/
local macro "names" : tactic =>
  `(tactic| (simp [Multiset.count_cons, Multiset.count_singleton] <;> (try split_ifs) <;> omega))

/-- `Translation.NetTr.equiv` is not vacuous: the one-cell net `source` (the cell on the free port
`0`) has a translation for every name `k ≠ 0` of the internal wire of the instance, and any two of
them are equivalent. (Lafont 1997, Section 1.7, page 80.) -/
example {j k : ℕ} (hj : j ≠ 0) (hk : k ≠ 0) : Equiv (target j) (target k) :=
  Translation.NetTr.equiv (netTr_target hj) (netTr_target hk)

/-- Two cells of the same symbol, on the free ports `0` and `1`. The two equations of the net are
identical up to their free port. -/
def source2 : Net unitSig ℕ :=
  s(.app () fun i => i.elim0, var 0) ::ₘ {s(.app () fun i => i.elim0, var 1)}

/-- A translation of `source2` with the internal wires named `a` and `b`. -/
def target2 (a b : ℕ) : CNet :=
  s(mkCon (var a) (var a), var 0) ::ₘ {s(mkCon (var b) (var b), var 1)}

/-- `target2 a b` is a translation of `source2` (Lafont 1997, Section 1.7, page 80) whenever the
two internal wires have distinct names, different from the free ports `0` and `1`. -/
theorem netTr_target2 {a b : ℕ} (ha : 1 < a) (hb : 1 < b) (hab : a ≠ b) :
    tr.NetTr source2 (target2 a b) := by
  have inst : ∀ k : ℕ, tr.TermTr (.app () fun i => i.elim0) (mkCon (var k) (var k)) := by
    intro k
    have h := Translation.TermTr.app (Φ := tr) () (fun i => i.elim0) (fun i => i.elim0)
      (fun _ => k) (fun i => i.elim0)
    have e : (tr.net ()).inst (fun i => i.elim0) (fun _ => k) = mkCon (var k) (var k) := by
      simp [PNet.inst, tr]
    rwa [e] at h
  constructor
  · exact Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, inst a, Translation.TermTr.var 0⟩
      (Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, inst b, Translation.TermTr.var 1⟩ Multiset.Rel.zero)
  · intro y
    have : (0 : ℕ) ≠ a := by omega
    have : (0 : ℕ) ≠ b := by omega
    have : (1 : ℕ) ≠ a := by omega
    have : (1 : ℕ) ≠ b := by omega
    simp only [target2]; names

/-- Exchanging the names of the internal wires of the two instances gives an equivalent net. The
two translations of `source2` here are different nets (the wire on the port `0` is `5` in one and
`6` in the other). -/
example : target2 5 6 ≠ target2 6 5 ∧ Equiv (target2 5 6) (target2 6 5) := by
  refine ⟨fun h => ?_, Translation.NetTr.equiv (netTr_target2 (by decide) (by decide) (by decide))
    (netTr_target2 (by decide) (by decide) (by decide))⟩
  -- the number of equations with two occurrences of `5` and one of `0`
  have := congrArg
    (fun N : CNet => (N.map fun e => (eqVars e).count 5 + (eqVars e).count 0).count 3) h
  simp [target2] at this

end INet.NetTrEquivCheck
