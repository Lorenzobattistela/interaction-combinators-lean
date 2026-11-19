import InteractionCombinators.Lafont.CodeGammaMeet
import InteractionCombinators.Lafont.CodeGammaExtractCheck
import InteractionCombinators.Lafont.CodeCellsMeetCheck
import InteractionCombinators.Lafont.CodeCellsPlug

/-!
# Review of the meeting lemmas of Fig. 10 (pages 89–90)

Lafont 1997, Fig. 10 (journal page 89, PDF page 21) and page 90. This file reviews
`codeCells_meet`, `codeCells_meet_gamma`, `codeGamma_meet`, `codeTerm_extract` and
`codeGamma_extract` against the figure. It is not imported by any library file.

What the figure shows, and the statements say:

* `[α_i]`: the multiplexor `M_{n_i+2}` has, from left to right, the code `!Γ`, the `n_i` ports and
  the loop, which goes to the right auxiliary port of `T_{1,1}`. In `codeCells_meet`, the code is
  the first leaf, the ports `xs` follow in order and the loop `K + n` is the last leaf.
* `Γ_{i,j}`: the leaves of `M*_{n_i+2}`, from left to right, are `C_{p_{i,j}}`, the trees of
  `⟨φ_{i,j}⟩` at the ports of `α_i`, and a wire that goes around to the root of `T_{σ_{i,j}}`.
  `codeGamma` has these leaves in this order, so `mux_muxStar` gives: code against `C_p`, port `i`
  against the tree at `.inl i`, loop against `T_σ`. This is `codeCells_meet_gamma`.
* The selector of `[α_i]` takes from the menu `Γ_j` of `[α_j]` its entry `i`, which is
  `Γ_{i,j}`, the package built from the side of `α_i` against `α_j`. `codeCells_meet` pairs the
  multiplexor of `[α]` with `codeGammaOpt … (side α β)` taken from the menu of `[β]`, and the other
  way round.
* In `codeGamma_meet` the middle port `l` of `⟨φ⟩` meets the port `σ l` of `⟨ψ⟩`. `σ` is
  involutive, so `σ = σ⁻¹` and the side on which `σ` is written does not matter
  (`Fig7EndReview.middle_symm`).

Below:

1. instances that are not degenerate: `codeTerm_extract` and `codeGamma_extract` with the real
   sides `sd` of the full system (the Check files only use `sideNone`, where every menu is an
   eraser), and `codeGamma_meet` with a side of four cells (the Check files only use sides without
   cells, so `C_p` was never more than an eraser);
2. how the lemmas compose: `codeCells_meet` → `codeCells_meet_gamma` (`meet_gamma_of_some`); the
   hypotheses that `codeGamma_extract` puts on the code are met by the code of `codeCells_meet`
   (`codeKey_bound`, `injOn_codeRen_code`); and the ports left by `codeGamma_meet` are in the form
   `∑ q, {s(P q, codePort … q)}` that `codeGamma_extract` asks for (`ports_sum_form`).
-/

namespace INet.Comb.CodeMeetReview

open Term Translation CodeTermExtractCheck CodeGammaExtractCheck CodeCellsMeetCheck

/-! ## 1. Instances that are not degenerate -/

/-- **`codeTerm_extract` with the sides of the full system** (Fig. 10, page 90): the tree
`con(dup(0, 1), 2)` with two cells, with the menus `Γ` built from the decomposition data `sd` of the
interaction combinators (the menus contain real packages `Γ_{i,j}`, not erasers). -/
theorem extract_conDup_sd :
    ∃ (K : ℕ) (fs : List (ℕ → ℕ)) (M : CNet) (t' : Term sig ℕ),
      StepsE system (s(var 3, codeTerm (Nat.card sig.Sym) (fun α => symEnum sig α) 4 tConDup) ::ₘ
          (codeCopies (code K (menu (codeMenus sd 0)))
            (codeExtras (Nat.card sig.Sym) (fun α => symEnum sig α) 4 tConDup) fs + 0)) M ∧
        Equiv M (s(var 3, t') ::ₘ 0) ∧ (codeTranslation sd).TermTr tConDup t' := by
  refine codeTerm_extract_of_nodup sd 0 tConDup 4 3 ?_ ?_
  · simp [tConDup]
  · intro x hx
    simp [tConDup] at hx
    omega

/-- **`codeGamma_extract` with the sides of the full system** (Fig. 10, pages 89–90): the side
`con`–`dup` with four cells and two middle ports, so `C_4` has four auxiliary ports, against a copy
of `!Γ` whose menus come from the decomposition data `sd`. -/
theorem gamma_extract_conDup_sd :
    ∃ (M : CNet) (t' : Fin 2 ⊕ Fin 2 → Term sig ℕ),
      StepsE system (s(copier (codeGammaExtras (Nat.card sig.Sym) (fun α => symEnum sig α)
          ruleConDup 0),
        (code (0 + ∑ i, codeMenuSizes sd i) (menu (codeMenus sd 0))).bind
          fun x => var (28 + x)) ::ₘ
        ((∑ q, {s(var (24 + (finSumFinEquiv q : ℕ)),
          codePort (Nat.card sig.Sym) (fun α => symEnum sig α) ruleConDup 0 q)}) + 0)) M ∧
      Equiv M ((∑ q, {s(var (24 + (finSumFinEquiv q : ℕ)), t' q)}) + 0) ∧
      ∀ q, (codeTranslation sd).TermTr (gammaTree ruleConDup 0 q) (t' q) := by
  set K := 0 + ∑ i, codeMenuSizes sd i
  have hC : (code K (menu (codeMenus sd 0))).IsPackage :=
    code_isPackage K _ (menu_codeMenus_isPackage sd 0) (menu_codeMenus_below sd 0)
  obtain ⟨hinj, hlin⟩ := codeGamma_extract_hyps (Nat.card sig.Sym) (fun α => symEnum sig α)
    ExpandTrReview.ruleConDup_expanded ruleConDup_linear 0 _ hC
  have e : (0 : ℕ) + codeGammaSize ruleConDup = 24 := by
    rw [CodeGammaCheck.codeGammaSize_conDup]
  simp only [e, show (24 : ℕ) + (2 + 2) = 28 from rfl] at hinj hlin
  exact codeGamma_extract sd ruleConDup 0 0 K le_rfl _ hinj _ 0 hlin

open CodeGammaCheck GammaCheck in
/-- The net for `codeGamma_meet` with the side `con`–`dup` (four cells, `C_4` not an eraser) on
both sides, `σ = swap 0 1`, the packages on `[0, 24)` and `[24, 48)`, codes `54`, `55`, ports
`50, 51` and `52, 53`, loop `56`, is linear. -/
theorem linear_conDup_meet :
    Net.Linear (s(mux (var 54 :: [var 50, var 51] ++ [var 56]),
        codeGamma 3 idx ruleConDup (Equiv.swap 0 1) hs 0) ::ₘ
      s(mux (var 55 :: [var 52, var 53] ++ [var 56]),
        codeGamma 3 idx ruleConDup (Equiv.swap 0 1) hs 24) ::ₘ (0 : CNet)) := by
  intro y
  simp only [Net.vars_cons, Net.vars_zero, eqVars_mk, vars_mux,
    vars_codeGamma _ _ ExpandTrReview.ruleConDup_expanded ruleConDup_linear, codeGammaSize_conDup,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, vars_var, Multiset.count_add, Multiset.count_nsmul, count_Ico,
    Multiset.count_singleton, add_zero]
  split_ifs <;> omega

open CodeGammaCheck GammaCheck in
/-- **`codeGamma_meet` with a side of four cells** (Fig. 10, pages 89–90): with the linearity
proved, the copiers `C_4` of the two packages are not erasers, and two middle ports are exchanged
by `σ = swap 0 1`. -/
example := codeGamma_meet 3 idx ruleConDup ruleConDup (Equiv.swap 0 1) hs 0 24 (var 54) (var 55)
  [var 50, var 51] [var 52, var 53] rfl rfl 56 0 linear_conDup_meet

/-! ## 2. Composability -/

variable {S : Signature} [Finite S.Sym]
  (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **`codeCells_meet` → `codeCells_meet_gamma`.** When the side of `α` against `β` exists, the
equation `M_{n+2}` against `Γ_{α,β}` left by `codeCells_meet` (leaves `c`, the ports `xs`, the loop
`ℓ`; the package `codeGammaOpt … (side α β) B` renamed by `ρ`) is accepted as it is by
`codeCells_meet_gamma`, after `rw` with the side. The second equation of `codeCells_meet` is this
one with `α`, `β` exchanged. -/
theorem meet_gamma_of_some (α β : S.Sym) (s : ExpSide S (S.arity α)) (hs : side α β = some s)
    (B : ℕ) (ρ : ℕ → ℕ) (c : Term sig ℕ) (xs : Fin (S.arity α) → ℕ) (ℓ : ℕ) (Δ : CNet) :
    Red (s(mux (c :: List.ofFn (fun i => (var (xs i) : Term sig ℕ)) ++ [var ℓ]),
        (codeGammaOpt (Nat.card S.Sym) (fun γ => symEnum S γ) (side α β) B).bind
          fun x => var (ρ x)) ::ₘ Δ)
      (s(c, (copier (codeGammaExtras (Nat.card S.Sym) (fun γ => symEnum S γ) s.φ B)).bind
          fun x => var (ρ x)) ::ₘ
        s(var ℓ, transpositorPerm s.σ s.involutive fun j =>
          (codePort (Nat.card S.Sym) (fun γ => symEnum S γ) s.φ B (.inr j)).bind
            fun x => var (ρ x)) ::ₘ
        ((↑(List.ofFn fun i => s(var (xs i),
          (codePort (Nat.card S.Sym) (fun γ => symEnum S γ) s.φ B (.inl i)).bind
            fun x => var (ρ x))) : CNet) + Δ)) := by
  rw [hs]
  exact codeCells_meet_gamma _ _ s.φ s.σ s.involutive B ρ c xs ℓ Δ

-- `codeKey_bound`, `injOn_codeRen_code` and `ports_sum_form`, found by this review, are now in
-- the library file `CodeCellsPlug.lean`.

end INet.Comb.CodeMeetReview
