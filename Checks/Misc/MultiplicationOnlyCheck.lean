import Demo.Multiplication
import Demo.Print

/-!
# `2 × 2 = 4` has no other answer (Lafont 1997, Fig. 1, page 78)

`Demo/Multiplication.lean` proves that the net of `n × m` reduces, up to wires, to the net of the
numeral `n * m`. A statement of that form would be weak if another numeral, or no computation at
all, also satisfied it. This file excludes both: the net of `2 × 2` is not the same graph as the
net of `4`, and the net of `n × m` reduces to the net of the numeral `k` only for `k = n * m`.
Written during the review of 20 November 2026.
-/

namespace INet.Demo.Mul.OnlyCheck

open Term Cut

/-- A successor adds one cell. -/
theorem cells_mkSucc (t : Term sig ℕ) : (mkSucc t).cells.card = t.cells.card + 1 := by
  rw [← Term.size_eq_card_cells, ← Term.size_eq_card_cells]
  change 1 + ∑ i : Fin 1, (![t] i).size = _
  rw [Fin.sum_univ_one]; simp; omega

/-- A multiplication cell adds one cell. -/
theorem cells_mkMul (y r : Term sig ℕ) :
    (mkMul y r).cells.card = y.cells.card + r.cells.card + 1 := by
  rw [← Term.size_eq_card_cells, ← Term.size_eq_card_cells, ← Term.size_eq_card_cells]
  change 1 + ∑ i : Fin 2, (![y, r] i).size = _
  rw [Fin.sum_univ_two]; simp; omega

/-- Zero is one cell. -/
theorem cells_mkZero : (mkZero : Term sig ℕ).cells.card = 1 := by
  rw [← Term.size_eq_card_cells]
  change 1 + ∑ i : Fin 0, ((![] : Fin 0 → Term sig ℕ) i).size = _
  rw [Fin.sum_univ_zero]
  rfl

/-- The numeral `n` has `n + 1` cells. -/
theorem cells_num (n : ℕ) : ((num n : Term sig ℕ).cells).card = n + 1 := by
  induction n with
  | zero => exact cells_mkZero
  | succ n ih => rw [num_succ, cells_mkSucc, ih]

/-- The net of the numeral `n` has `n + 1` cells. -/
theorem cells_numNet (n : ℕ) : (Net.cells (numNet n)).card = n + 1 := by
  change (Net.cells (s(var 0, num n) ::ₘ 0)).card = _
  rw [Net.cells_cons, eqCells_mk, Multiset.card_add, Multiset.card_add, cells_num]
  simp [Net.cells]

/-- The net of `n × m` has `n + m + 3` cells. -/
theorem cells_times (n m : ℕ) : (Net.cells (times n m)).card = n + m + 3 := by
  change (Net.cells (s(mkMul (num m) (var 0), num n) ::ₘ 0)).card = _
  rw [Net.cells_cons, eqCells_mk, Multiset.card_add, Multiset.card_add, cells_num, cells_mkMul,
    cells_num]
  simp [Net.cells]
  omega

/-- Zero steps cannot witness `two_times_two`: the net of `2 × 2` is not the same graph as the
net of `4`. -/
theorem not_equiv_start : ¬ Equiv twoTimesTwo four := by
  intro h
  have := congrArg Multiset.card h.cells_eq
  rw [twoTimesTwo, four, cells_times, cells_numNet] at this
  omega

/-- The net of a numeral has no cut. -/
theorem numNet_not_hasCut (n : ℕ) : ¬ Net.HasCut (numNet n) := by
  intro h
  obtain ⟨a, b, xs, D, ⟨α, ts, rfl⟩, ⟨β, us, rfl⟩, hN⟩ := h.chainCut
  have hc := congrArg Multiset.card hN
  rcases xs with _ | ⟨x, ys⟩
  · have : s(Term.app α ts, Term.app β us) ∈ numNet n := by rw [hN]; simp
    simp [numNet] at this
  · rcases ys with _ | ⟨y, zs⟩ <;>
      simp [numNet] at hc

/-- If `2 × 2` reduces, up to wires, to the net of the numeral `k`, then `k = 4`. -/
theorem only_four (k : ℕ) (h : ∃ M, StepsE system twoTimesTwo M ∧ Equiv M (numNet k)) :
    k = 4 := by
  obtain ⟨M, hM, eM⟩ := h
  obtain ⟨M4, h4, e4⟩ := two_times_two
  obtain ⟨n, hn⟩ := hM.exists_stepsEN
  obtain ⟨m, hm⟩ := h4.exists_stepsEN
  have nk : StepE.Normal system M :=
    (StepE.Normal.of_not_hasCut (numNet_not_hasCut k)).of_equiv eM.symm
  have n4 : StepE.Normal system M4 :=
    (StepE.Normal.of_not_hasCut (numNet_not_hasCut 4)).of_equiv e4.symm
  obtain ⟨-, E⟩ := StepsEN.normal_unique system_wellFormed (times_linear 2 2) nk n4 hn hm
  have E' : Equiv (numNet k) four := eM.symm.trans (E.trans e4)
  have := congrArg Multiset.card E'.cells_eq
  rw [four, cells_numNet, cells_numNet] at this
  omega

/-- **Only the product is an answer**: if the net of `n × m` reduces, up to wires, to the net of
the numeral `k`, then `k = n * m`. By uniqueness of normal forms (`StepsEN.normal_unique`). -/
theorem only_product (n m k : ℕ) (h : ∃ M, StepsE system (times n m) M ∧ Equiv M (numNet k)) :
    k = n * m := by
  obtain ⟨M, hM, eM⟩ := h
  obtain ⟨M4, h4, e4⟩ := times_reduces n m
  obtain ⟨a, hn⟩ := hM.exists_stepsEN
  obtain ⟨b, hm⟩ := h4.exists_stepsEN
  have nk : StepE.Normal system M :=
    (StepE.Normal.of_not_hasCut (numNet_not_hasCut k)).of_equiv eM.symm
  have n4 : StepE.Normal system M4 :=
    (StepE.Normal.of_not_hasCut (numNet_not_hasCut _)).of_equiv e4.symm
  obtain ⟨-, E⟩ := StepsEN.normal_unique system_wellFormed (times_linear n m) nk n4 hn hm
  have E' : Equiv (numNet k) (numNet (n * m)) := eM.symm.trans (E.trans e4)
  have := congrArg Multiset.card E'.cells_eq
  rw [cells_numNet, cells_numNet] at this
  omega

/-- The net of `2 × 2` is the first net of Fig. 1 (page 78), and `four` is the last. -/
example : twoTimesTwo =
    s(mkMul (mkSucc (mkSucc mkZero)) (.var 0), mkSucc (mkSucc mkZero)) ::ₘ 0 := rfl

example : four = s(.var 0, mkSucc (mkSucc (mkSucc (mkSucc mkZero)))) ::ₘ 0 := rfl

end INet.Demo.Mul.OnlyCheck
