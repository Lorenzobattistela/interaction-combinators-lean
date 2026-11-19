import InteractionCombinators.Lafont.CodeGammaMeet
import InteractionCombinators.Lafont.CodeGammaCheck
import InteractionCombinators.Lafont.CodeCellsMeetCheck

/-!
# Check of `codeGamma_meet` (pages 89–90)

The side `φ₀` of `GammaCheck` (`l₀ = w₀, m₀ = w₀, l₁ = w₁, m₁ = w₁`, `a = b = k = 2`, no cells),
three symbols numbered by `CodeGammaCheck.idx`, `σ = swap 0 1`, used for both `Γ_{α,β}` (names from
`10`) and `Γ_{β,α}` (names from `20`). The codes are the wires `7` and `8`, the trees on the ports
are `0, 1` and `2, 3`, the loop is `5`.

* `codeGamma_φ₀_gen` — `Γ` of `φ₀` from any `k₀`: `M*_4(ε, w₀, w₁, T_σ(w₀, w₁))`.
* `codeGamma_meet_φ₀` — the hypothesis of `codeGamma_meet` is proved, and the net it reaches is
  computed: both codes against erasers (`C_0`), `0 = 10, 1 = 11, 2 = 20, 3 = 21`, and, for the
  middle ports through `σ`, `10 = 21, 11 = 20`.
-/

namespace INet.Comb.CodeGammaMeetCheck

open Term Rule Translation GammaCheck CodeGammaCheck

/-- The trees of `⟨φ₀⟩` from `k₀`: the internal wires `k₀ + 0`, `k₀ + 1`. -/
theorem codePort_φ₀ (k₀ : ℕ) :
    codePort 3 idx φ₀ k₀ (.inl 0) = var (k₀ + 0) ∧ codePort 3 idx φ₀ k₀ (.inl 1) = var (k₀ + 1) ∧
      codePort 3 idx φ₀ k₀ (.inr 0) = var (k₀ + 0) ∧
      codePort 3 idx φ₀ k₀ (.inr 1) = var (k₀ + 1) := by
  obtain ⟨h0, h1, h2, h3⟩ := portTree_φ₀
  simp only [codePort, gammaTree, h0, h1, h2, h3]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `φ₀` has no cells: no trees on extra ports, so the copier is `C_0`, an eraser. -/
theorem codeGammaExtras_φ₀ (k₀ : ℕ) : codeGammaExtras 3 idx φ₀ k₀ = [] := by
  obtain ⟨h0, h1, h2, h3⟩ := portTree_φ₀
  have e : ∀ p, codePortExtras 3 idx φ₀ k₀ p = [] := by
    rintro (i | j)
    · revert i
      rw [Fin.forall_fin_two]
      exact ⟨by rw [codePortExtras, gammaTree, h0]; rfl, by rw [codePortExtras, gammaTree, h1]; rfl⟩
    · revert j
      rw [Fin.forall_fin_two]
      exact ⟨by rw [codePortExtras, gammaTree, h2]; rfl, by rw [codePortExtras, gammaTree, h3]; rfl⟩
  simp [codeGammaExtras, e]

/-- `Γ` of `φ₀` from any `k₀` (as `CodeGammaCheck.codeGamma_φ₀`, which is the case `k₀ = 10`). -/
theorem codeGamma_φ₀_gen (k₀ : ℕ) :
    codeGamma 3 idx φ₀ (Equiv.swap 0 1) hs k₀ =
      mkCon (mkCon (mkCon (mkCon (var (k₀ + 0)) (var (k₀ + 1))) (var (k₀ + 1))) (var (k₀ + 0)))
        mkEra := by
  obtain ⟨h0, h1, h2, h3⟩ := codePort_φ₀ k₀
  have hl : portList (Equiv.swap (0 : Fin 2) 1) = [0, 1] := by decide
  have hp : pairFst (Equiv.swap (0 : Fin 2) 1) = [0] := by decide
  simp only [codeGamma, codeGammaExtras_φ₀, transpositorPerm, hl, hp, List.ofFn_succ,
    List.ofFn_zero, List.map_cons, List.map_nil, Fin.succ_zero_eq_one, Fin.isValue, h0, h1, h2, h3]
  rfl

/-- The net of the last rows of the analogue of Fig. 7 for this instance. -/
noncomputable abbrev N0 : CNet :=
  s(mux (var 7 :: [var 0, var 1] ++ [var 5]), codeGamma 3 idx φ₀ (Equiv.swap 0 1) hs 10) ::ₘ
    s(mux (var 8 :: [var 2, var 3] ++ [var 5]), codeGamma 3 idx φ₀ (Equiv.swap 0 1) hs 20) ::ₘ 0

/-- The hypothesis of `codeGamma_meet` holds for this instance. -/
theorem N0_linear : Net.Linear N0 := by
  apply Net.linear_of_forall_mem
  rw [N0, codeGamma_φ₀_gen, codeGamma_φ₀_gen]
  decide

/-- **`codeGamma_meet` on `φ₀`** (Fig. 10, pages 89–90): its hypothesis holds, and the net it
reaches is the codes `7`, `8` against erasers and the six wires
`0 = 10, 1 = 11, 2 = 20, 3 = 21, 10 = 21, 11 = 20`. -/
theorem codeGamma_meet_φ₀ :
    ∃ M, StepsE system N0 M ∧
      Equiv M (s(var 7, mkEra) ::ₘ s(var 8, mkEra) ::ₘ s(var 0, var 10) ::ₘ s(var 1, var 11) ::ₘ
        s(var 2, var 20) ::ₘ s(var 3, var 21) ::ₘ s(var 10, var 21) ::ₘ {s(var 11, var 20)}) := by
  obtain ⟨M, hS, hE⟩ := codeGamma_meet 3 idx φ₀ φ₀ (Equiv.swap 0 1) hs 10 20 (var 7) (var 8)
    [var 0, var 1] [var 2, var 3] rfl rfl 5 0 N0_linear
  refine ⟨M, hS, hE.trans (Equiv.of_eq ?_)⟩
  obtain ⟨a0, a1, a2, a3⟩ := codePort_φ₀ 10
  obtain ⟨b0, b1, b2, b3⟩ := codePort_φ₀ 20
  simp only [Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, Fin.isValue,
    a0, a1, a2, a3, b0, b1, b2, b3, Equiv.swap_apply_left, Equiv.swap_apply_right,
    codeGammaExtras_φ₀]
  decide

/-! ## `codeCells_meet_end` on `[dup]` against `[dup]` -/

open CodeCellsMeetCheck RecursionFreeFig7Check in
/-- `[dup]` against `[dup]` of Fig. 10, ports `0, 1` and `2, 3`, internal wires from `4`. -/
noncomputable def netDupDup : CNet :=
  {s((codeNet sd Comb.dup).inst (fun i => .var (zeroOne i)) fromFour,
    (codeNet sd Comb.dup).inst (fun j => .var (twoThree j))
      (afterFour (codeNet sd Comb.dup).internal))}

open CodeCellsMeetCheck RecursionFreeFig7Check in
/-- The hypothesis of `codeCells_meet_end` holds for `[dup]` against `[dup]`. -/
theorem linear_netDupDup : netDupDup.Linear := by
  refine linear_blocks _ _ zeroOne twoThree ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [zeroOne]
  · intro j; fin_cases j <;> simp [twoThree]
  · intro z
    simp only [Fin.sum_univ_two, zeroOne, twoThree, Matrix.cons_val_zero, Matrix.cons_val_one]
    by_cases h0 : z = 0 <;> by_cases h1 : z = 1 <;> by_cases h2 : z = 2 <;>
      by_cases h3 : z = 3 <;> simp [h0, h1, h2, h3]

open CodeCellsMeetCheck RecursionFreeFig7Check in
/-- **`codeCells_meet_end` applies to `[dup]` against `[dup]`** (Fig. 10, pages 89–90). The full
system has a rule `dup`–`dup` (page 86), so the side `s` of `dup` against itself exists; it is the
side on both sides of the meeting, with its `k` middle ports and its involution. The linearity
hypothesis is proved (`linear_netDupDup`), and the net reaches, up to wires, the two codes against
the copiers of `Γ_{dup,dup}`, the ports `0, 1` and `2, 3` against the trees of `⟨φ⟩`, and the middle
ports of the two copies of `⟨φ⟩` against each other through `σ`. -/
theorem codeCells_meet_end_dupDup :
    ∃ s : ExpSide sig (sig.arity Comb.dup), sd Comb.dup Comb.dup = some s ∧
      ∃ (K K' : ℕ) (M : CNet), StepsE system netDupDup M ∧
        Equiv M
          (s((code (codeKey sd Comb.dup) (menu (codeMenus sd (codeMenuBase sd Comb.dup)))).bind
                (fun x => var (codeRen zeroOne K x)),
              copier (codeGammaExtras (Nat.card sig.Sym) (fun γ => symEnum sig γ) s.φ
                (K' + (2 + 1 + off (codeCellSizes sd Comb.dup) (symEnum sig Comb.dup))))) ::ₘ
            s((code (codeKey sd Comb.dup) (menu (codeMenus sd (codeMenuBase sd Comb.dup)))).bind
                (fun x => var (codeRen twoThree K' x)),
              copier (codeGammaExtras (Nat.card sig.Sym) (fun γ => symEnum sig γ) s.φ
                (K + (2 + 1 + off (codeCellSizes sd Comb.dup) (symEnum sig Comb.dup))))) ::ₘ
            ((Finset.univ.val.map fun p : Fin 2 =>
                s(var (zeroOne p), codePort (Nat.card sig.Sym) (fun γ => symEnum sig γ) s.φ
                  (K' + (2 + 1 + off (codeCellSizes sd Comb.dup) (symEnum sig Comb.dup)))
                  (.inl p))) +
              (Finset.univ.val.map fun q : Fin 2 =>
                s(var (twoThree q), codePort (Nat.card sig.Sym) (fun γ => symEnum sig γ) s.φ
                  (K + (2 + 1 + off (codeCellSizes sd Comb.dup) (symEnum sig Comb.dup)))
                  (.inl q))) +
              (Finset.univ.val.map fun l : Fin s.k =>
                s(codePort (Nat.card sig.Sym) (fun γ => symEnum sig γ) s.φ
                    (K' + (2 + 1 + off (codeCellSizes sd Comb.dup) (symEnum sig Comb.dup)))
                    (.inr l),
                  codePort (Nat.card sig.Sym) (fun γ => symEnum sig γ) s.φ
                    (K + (2 + 1 + off (codeCellSizes sd Comb.dup) (symEnum sig Comb.dup)))
                    (.inr (s.σ l)))) + 0)) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1
    ((System.DecData.side_isSome_iff (System.WellFormed.decData system_wellFormed)
      Comb.dup Comb.dup).2 (Or.inl ⟨_, rfl⟩))
  exact ⟨s, hs, codeCells_meet_end sd Comb.dup Comb.dup zeroOne twoThree _ _ 0 s.φ s.φ s.σ
    s.involutive s.linear s.expanded s.linear s.expanded hs hs linear_netDupDup⟩

end INet.Comb.CodeGammaMeetCheck
