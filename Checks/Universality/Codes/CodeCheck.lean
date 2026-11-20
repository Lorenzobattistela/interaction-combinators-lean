import InteractionCombinators.Text.NetLemmas
import InteractionCombinators.Universality.Codes.Code
import Checks.Universality.RecursionFree.DecompositionCheck

/-!
# Review of `Universality/Codes/Code.lean` against Fig. 8 (page 88) and Fig. 9 (page 89)

Checks of the code `!π` and the decoder `D`, all proved in Lean.

* **Hypotheses of `code_isPackage`.** Both are needed: without `hb` the cut names can clash with the
  names of `π` (`code_isPackage_needs_below`); without `hπ` the root tree `τ` carries the free
  name of `π` into the code (`code_isPackage_needs_isPackage`).
* **`decoder_free` is sharp.** If the free port `w` is `k` or `k + 1`, it occurs three times
  (`decoder_count_self`, `decoder_count_succ`).
* **Fig. 9 on a package with two different `dup` cells.** `π₂ = con(dup(0, con(1, ε)), dup(1, 0))`:
  the first cell has `l = 0`, `r = con(1, ε)`, the second `l = 1`, `r = 0`, so a swap of the trees
  on port 0 and on port 1 would show. `code_decoder_π₂` is the first stage of Fig. 9 on it: `M_2`
  faces the `dup` cell of the decoder, the `M_2*` on its port 0, `k = 12`, carries the trees `0, 1`
  on port 0, the one on its port 1, `k + 1 = 13`, the trees `con(1, ε), 0` on port 1. `decode_π₂`
  carries out the whole of Fig. 9 by hand: the `con`–`dup` commutation, the two annihilations of the
  copies of `M_2` with the `M_2*`, and the wires; what is left is `Equiv` to `π₂` on the free port.
-/

namespace INet.Comb.CodeCheck

open Term

/-! ## Helpers for concrete nets -/

/-- One wire substitution on a concrete net, with every side condition in decidable form. -/
theorem wire_of (x : ℕ) (t a b : Term sig ℕ) (Δ N M : CNet)
    (hN : N = s(var x, t) ::ₘ s(a, b) ::ₘ Δ) (hM : M = s(a.subst x t, b.subst x t) ::ₘ Δ)
    (hlin : ∀ y ∈ N.vars, N.vars.count y ≤ 2) (hx : x ∈ a.vars + b.vars) : Equiv N M := by
  subst hN hM
  exact (Wire.mk x t a b Δ (Net.linear_of_forall_mem hlin) hx).equiv

/-! ## The hypotheses of `code_isPackage` -/

/-- `hb` is needed in `code_isPackage` (page 88: the new names must be new). The package
`dup(0, 0)` with new names from `0`: the cell is cut at `0`, which is already a name of `π`, and
the code `M_4(0, 0, 0, 0)` has the name `0` four times. With new names from `1` it is a package. -/
theorem code_isPackage_needs_below :
    (mkDup (var 0) (var 0) : Term sig ℕ).IsPackage ∧
      ¬ (code 0 (mkDup (var 0) (var 0) : Term sig ℕ)).IsPackage ∧
      (code 1 (mkDup (var 0) (var 0) : Term sig ℕ)).IsPackage := by
  unfold Term.IsPackage; decide

/-- `hπ` is needed in `code_isPackage`: the code of the tree `var 0`, which is not a package, is
`M_4(ε, ε, ε, 0)`, which has the free name `0`, although the new names (from `1`) are fresh. -/
theorem code_isPackage_needs_isPackage :
    ¬ (var 0 : Term sig ℕ).IsPackage ∧ (var 0 : Term sig ℕ).Below 1 ∧
      ¬ (code 1 (var 0 : Term sig ℕ)).IsPackage := by
  unfold Term.IsPackage Term.Below; decide

/-! ## `decoder_free` is sharp -/

/-- If the free port of the decoder is the left wire `k` of its loop, it occurs three times. -/
theorem decoder_count_self (k : ℕ) : (decoder k k : Term sig ℕ).vars.count k = 3 := by
  rw [vars_decoder]
  simp [Multiset.insert_eq_cons]

/-- If the free port of the decoder is the right wire `k + 1` of its loop, it occurs three
times. -/
theorem decoder_count_succ (k : ℕ) : (decoder (k + 1) k : Term sig ℕ).vars.count (k + 1) = 3 := by
  rw [vars_decoder]
  simp [Multiset.insert_eq_cons]

/-! ## Fig. 9 on a package with two different `dup` cells -/

/-- A package with two `dup` cells whose left and right trees differ. -/
def π₂ : Term sig ℕ := mkCon (mkDup (var 0) (mkCon (var 1) mkEra)) (mkDup (var 1) (var 0))

/-- `π₂` is a package: `0` and `1` occur twice each (page 87). -/
theorem π₂_isPackage : π₂.IsPackage := by unfold Term.IsPackage; decide

/-- The decomposition of `π₂` with new names from `2` (page 88): the cells are cut at `4` and `9`;
the first has `l = 0`, `r = con(1, ε)`, the second `l = 1`, `r = 0`; `τ = con(4, 9)`. -/
theorem decomp_π₂ : decomp 2 π₂ =
    ⟨mkCon (var 4) (var 9), [(4, var 0, mkCon (var 1) mkEra), (9, var 1, var 0)], 12⟩ := rfl

/-- The code of `π₂` (Fig. 8): `M_4` of `M_2(4, 9)`, `M_2*` of the trees `0, 1` on port 0,
`M_2*` of the trees `con(1, ε), 0` on port 1, and `τ`. -/
theorem code_π₂ : code 2 π₂ = mux [mux [var 4, var 9], muxStar [var 0, var 1],
    muxStar [mkCon (var 1) mkEra, var 0], mkCon (var 4) (var 9)] := rfl

/-- The first stage of Fig. 9 (page 89) on `π₂`, decoder with free port `20` and loop `12`, `13`.
`M_2(4, 9) = con(4, 9)` faces the `dup` cell; `M_2*` of the trees on port 0, `con(1, 0)`, faces
port 0 of that cell, `12`; `M_2*` of the trees on port 1, `con(0, con(1, ε))`, faces its port 1,
`13`; `τ` comes out on `20`. -/
theorem code_decoder_π₂ : Red {s(code 2 π₂, decoder 20 12)}
    (s(mkCon (var 4) (var 9), mkDup (var 12) (var 13)) ::ₘ
      s(mkCon (var 1) (var 0), var 12) ::ₘ
      s(mkCon (var 0) (mkCon (var 1) mkEra), var 13) ::ₘ {s(mkCon (var 4) (var 9), var 20)}) :=
  code_decoder 2 π₂ 20 12 0

/-- Fig. 9 (page 89) carried out on `π₂`: the code against the decoder reduces to a net that is
`Equiv` to `π₂` on the free port. After the first stage, `con(4, 9)` against `dup(12, 13)` puts a
copy `con(14, 16)` of `M_2` on the left port `12` and a copy `con(15, 17)` on the right port `13`,
and the cells `4 = dup(14, 15)`, `9 = dup(16, 17)`. The left copy meets `M_2*` of the left trees
(`14 — 0`, `16 — 1`), the right one `M_2*` of the right trees (`15 — con(1, ε)`, `17 — 0`): each
new `dup` cell gets its own left tree on its left port and its own right tree on its right port. -/
theorem decode_π₂ : ∃ M, StepsE system {s(code 2 π₂, decoder 20 12)} M ∧
    Equiv M {s(π₂, var 20)} := by
  have h1 := code_decoder_π₂
  -- stage 2: `M_2` (here one `con`) against the `dup` cell of the decoder
  have h2 := step_con_dup (var 4) (var 9) (var 12) (var 13)
    (s(mkCon (var 1) (var 0), var 12) ::ₘ
        s(mkCon (var 0) (mkCon (var 1) mkEra), var 13) ::ₘ {s(mkCon (var 4) (var 9), var 20)})
    14 15 16 17 (by decide) (by decide)
  -- stage 3: the copy of `M_2` on the left port `12` against `M_2*` of the left trees
  have h3 : StepE system
      (s(var 4, mkDup (var 14) (var 15)) ::ₘ s(var 9, mkDup (var 16) (var 17)) ::ₘ
        s(var 12, mkCon (var 14) (var 16)) ::ₘ s(var 13, mkCon (var 15) (var 17)) ::ₘ
        s(mkCon (var 1) (var 0), var 12) ::ₘ
        s(mkCon (var 0) (mkCon (var 1) mkEra), var 13) ::ₘ {s(mkCon (var 4) (var 9), var 20)})
      (s(var 1, var 16) ::ₘ s(var 0, var 14) ::ₘ
        s(var 4, mkDup (var 14) (var 15)) ::ₘ s(var 9, mkDup (var 16) (var 17)) ::ₘ
        s(var 13, mkCon (var 15) (var 17)) ::ₘ s(mkCon (var 0) (mkCon (var 1) mkEra), var 13) ::ₘ
        {s(mkCon (var 4) (var 9), var 20)}) :=
    ⟨_, wire_of 12 (mkCon (var 14) (var 16)) (mkCon (var 1) (var 0)) (var 12)
        (s(var 4, mkDup (var 14) (var 15)) ::ₘ s(var 9, mkDup (var 16) (var 17)) ::ₘ
          s(var 13, mkCon (var 15) (var 17)) ::ₘ s(mkCon (var 0) (mkCon (var 1) mkEra), var 13) ::ₘ
          {s(mkCon (var 4) (var 9), var 20)}) _
        (s(mkCon (var 1) (var 0), mkCon (var 14) (var 16)) ::ₘ
          s(var 4, mkDup (var 14) (var 15)) ::ₘ s(var 9, mkDup (var 16) (var 17)) ::ₘ
          s(var 13, mkCon (var 15) (var 17)) ::ₘ s(mkCon (var 0) (mkCon (var 1) mkEra), var 13) ::ₘ
          {s(mkCon (var 4) (var 9), var 20)})
        (by decide) (by decide) (by decide) (by decide),
      step_con_con (var 1) (var 0) (var 14) (var 16) _⟩
  -- stage 3: the copy on the right port `13` against `M_2*` of the right trees
  have h4 : StepE system
      (s(var 1, var 16) ::ₘ s(var 0, var 14) ::ₘ
        s(var 4, mkDup (var 14) (var 15)) ::ₘ s(var 9, mkDup (var 16) (var 17)) ::ₘ
        s(var 13, mkCon (var 15) (var 17)) ::ₘ s(mkCon (var 0) (mkCon (var 1) mkEra), var 13) ::ₘ
        {s(mkCon (var 4) (var 9), var 20)})
      (s(var 0, var 17) ::ₘ s(mkCon (var 1) mkEra, var 15) ::ₘ
        s(var 1, var 16) ::ₘ s(var 0, var 14) ::ₘ
        s(var 4, mkDup (var 14) (var 15)) ::ₘ s(var 9, mkDup (var 16) (var 17)) ::ₘ
        {s(mkCon (var 4) (var 9), var 20)}) :=
    ⟨_, wire_of 13 (mkCon (var 15) (var 17)) (mkCon (var 0) (mkCon (var 1) mkEra)) (var 13)
        (s(var 1, var 16) ::ₘ s(var 0, var 14) ::ₘ
          s(var 4, mkDup (var 14) (var 15)) ::ₘ s(var 9, mkDup (var 16) (var 17)) ::ₘ
          {s(mkCon (var 4) (var 9), var 20)}) _
        (s(mkCon (var 0) (mkCon (var 1) mkEra), mkCon (var 15) (var 17)) ::ₘ
          s(var 1, var 16) ::ₘ s(var 0, var 14) ::ₘ
          s(var 4, mkDup (var 14) (var 15)) ::ₘ s(var 9, mkDup (var 16) (var 17)) ::ₘ
          {s(mkCon (var 4) (var 9), var 20)})
        (by decide) (by decide) (by decide) (by decide),
      step_con_con (var 0) (mkCon (var 1) mkEra) (var 15) (var 17) _⟩
  refine ⟨_, (h1.stepsE.tail h2.stepE).tail h3 |>.tail h4, ?_⟩
  -- the last net is `π₂` with its wires spelled out
  refine (wire_of 4 (mkDup (var 14) (var 15)) (mkCon (var 4) (var 9)) (var 20)
    (s(var 0, var 17) ::ₘ s(mkCon (var 1) mkEra, var 15) ::ₘ s(var 1, var 16) ::ₘ
      s(var 0, var 14) ::ₘ {s(var 9, mkDup (var 16) (var 17))}) _ _
    (by decide) rfl (by decide) (by decide)).trans ?_
  refine (wire_of 9 (mkDup (var 16) (var 17)) (mkCon (mkDup (var 14) (var 15)) (var 9)) (var 20)
    (s(var 0, var 17) ::ₘ s(mkCon (var 1) mkEra, var 15) ::ₘ s(var 1, var 16) ::ₘ
      {s(var 0, var 14)}) _ _
    (by decide) rfl (by decide) (by decide)).trans ?_
  refine (wire_of 15 (mkCon (var 1) mkEra)
    (mkCon (mkDup (var 14) (var 15)) (mkDup (var 16) (var 17))) (var 20)
    (s(var 0, var 17) ::ₘ s(var 1, var 16) ::ₘ {s(var 0, var 14)}) _ _
    (by decide) rfl (by decide) (by decide)).trans ?_
  refine (wire_of 16 (var 1)
    (mkCon (mkDup (var 14) (mkCon (var 1) mkEra)) (mkDup (var 16) (var 17))) (var 20)
    (s(var 0, var 17) ::ₘ {s(var 0, var 14)}) _ _
    (by decide) rfl (by decide) (by decide)).trans ?_
  refine (wire_of 14 (var 0)
    (mkCon (mkDup (var 14) (mkCon (var 1) mkEra)) (mkDup (var 1) (var 17))) (var 20)
    {s(var 0, var 17)} _ _
    (by decide) rfl (by decide) (by decide)).trans ?_
  exact wire_of 17 (var 0)
    (mkCon (mkDup (var 0) (mkCon (var 1) mkEra)) (mkDup (var 1) (var 17))) (var 20) 0 _ _
    (by decide) (by decide) (by decide) (by decide)

end INet.Comb.CodeCheck
