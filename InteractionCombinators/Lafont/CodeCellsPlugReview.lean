import InteractionCombinators.Lafont.CodeCellsPlug
import InteractionCombinators.Lafont.CodeDataSides
import InteractionCombinators.Lafont.PlugsNetTr
import InteractionCombinators.Lafont.CodeCellsMeetCheck
import InteractionCombinators.Lafont.DecompositionCheck

/-!
# Review of `sides_expand` and `codeCells_plug` (pages 85–86, 89–90)

Lafont 1997, page 85 (the decomposition of the right member of a rule, PDF page 17), page 86
(Fig. 7, PDF page 18), page 89 (Fig. 10, PDF page 21) and page 90 ("the analogue of Fig. 7 is
left to the reader").

What the figures say, against the statements:

* Page 85: the right member `ν_{i,j}` is `φ_{i,j}` on the `n_i` ports of `α_i`, `ψ_{i,j}` on the
  `n_j` ports of `α_j`, and `σ_{i,j}` below joining their middle ports. `sides_expand` gives
  `(⟨k, φ, ψ, σ⟩ : Decomposition S (S.arity α) (S.arity β)).Plugs r` with `φ` the side of `α`
  (`D.side α β`) and `ψ` the side of `β` (`D.side β α`): the decomposition of page 85, not its
  swap. `Rule.plug φ ψ σ` joins the middle wire `l` of `φ` to the middle wire `σ l` of `ψ`.
* Page 86, last row of Fig. 7: `[φ_{i,j}]` on the ports of `α_i`, `[φ_{j,i}]` on those of `α_j`,
  `T_{σ_{i,j}}` against `T_{σ_{j,i}}`, giving `σ_{i,j}` between them. `plugTermTarget σ tφ tψ xs ys`
  puts `xs` against the trees of `φ` (the side of `α`), `ys` against those of `ψ` (the side of
  `β`), and `tφ (.inr l)` against `tψ (.inr (σ l))`, the same joining as `Rule.plug φ ψ σ`. Since
  `σ_{j,i} = σ_{i,j}` is involutive (page 86), which side's `σ` is used does not matter
  (`middle_reindex`).

The checks below:

* `codeCells_plug_conDup` — a non-degenerate instance of `codeCells_plug`: `[con]` against
  `[dup]` with the sides of `decData system_wellFormed`, obtained from `sides_expand`; the linearity
  hypothesis is `linear_netConDup`. Here `k = 4`, the side of `con` has the two `dup` cells and the
  side of `dup` the two `con` cells (page 85), so each copier `C_p` has two auxiliary ports: it is
  a `dup` cell, not an eraser.
* `compatible_of_codeCells_plug` — `codeCells_plug` with `Δ = 0`, `netTr_plug_termTr` and
  `Decomposition.Plugs.netTr_inst_of_sides` fit together into `Translation.Compatible` for the
  translation of Fig. 10 with the sides of `decData`, with no further glue.
-/

namespace INet.Comb.CodeCellsPlugReview

open Term Translation CodeCellsMeetCheck RecursionFreeFig7Check

/-- **`codeCells_plug` on `[con]` against `[dup]`, with `k > 0` and copiers that are not erasers**
(Fig. 10, pages 89–90; the decomposition of `con`–`dup`, page 85). The sides are those of
`sides_expand` for the rule `con`–`dup`: `k = 4` middle wires, the side of `con` has the cells
`dup, dup` and the side of `dup` the cells `con, con`, so both copiers have two auxiliary ports
(`length_codeGammaExtras`). Every hypothesis of `codeCells_plug` is proved. -/
theorem codeCells_plug_conDup :
    ∃ (k : ℕ) (φ : Rule sig 2 k) (ψ : Rule sig 2 k) (σ : Equiv.Perm (Fin k)),
      k = 4 ∧ φ.net.cells = {Comb.dup, Comb.dup} ∧ ψ.net.cells = {Comb.con, Comb.con} ∧
      (⟨k, φ, ψ, σ⟩ : Decomposition sig 2 2).Plugs ruleConDup ∧
      (∀ k₀, (codeGammaExtras (Nat.card sig.Sym) (fun γ => symEnum sig γ) φ k₀).length = 2) ∧
      (∀ k₁, (codeGammaExtras (Nat.card sig.Sym) (fun γ => symEnum sig γ) ψ k₁).length = 2) ∧
      ∃ (k₀ k₁ : ℕ) (M : CNet) (tφ : Fin 2 ⊕ Fin k → Term sig ℕ)
        (tψ : Fin 2 ⊕ Fin k → Term sig ℕ),
        StepsE system netConDup M ∧
        Equiv M (plugTermTarget σ tφ tψ zeroOne twoThree + 0) ∧
        (∀ p, (codeTranslation sd).TermTr (gammaTree φ k₀ p) (tφ p)) ∧
        (∀ q, (codeTranslation sd).TermTr (gammaTree ψ k₁ q) (tψ q)) := by
  obtain ⟨k, φ, ψ, σ, hσ, hl, he, hl', he', hs, hs', hP⟩ :=
    (System.WellFormed.decData system_wellFormed).sides_expand system_wellFormed
      (α := Comb.con) (β := Comb.dup) (r := ruleConDup) rfl
  have hne : (Comb.con : sig.Sym) ≠ Comb.dup := by decide
  have h0 : sd Comb.con Comb.dup = some ((System.WellFormed.decData system_wellFormed).rawφ
      Comb.con Comb.dup ruleConDup rfl).expand :=
    congrArg (Option.map RawSide.expand)
      (System.DecData.rawSide_of_rule (System.WellFormed.decData system_wellFormed)
        (α := (Comb.con : sig.Sym)) (β := Comb.dup) (r := ruleConDup) rfl)
  have h1 : sd Comb.dup Comb.con = some ((System.WellFormed.decData system_wellFormed).rawψ
      Comb.dup Comb.con ruleConDup rfl).expand :=
    congrArg (Option.map RawSide.expand)
      (System.DecData.rawSide_swap_of_rule (System.WellFormed.decData system_wellFormed)
        system_wellFormed (α := (Comb.con : sig.Sym)) (β := Comb.dup) (r := ruleConDup) rfl)
  have e0 := Option.some.inj (hs.symm.trans h0)
  have e1 := Option.some.inj (hs'.symm.trans h1)
  have hdec : (System.WellFormed.decData system_wellFormed).dec Comb.con Comb.dup ruleConDup rfl =
      ruleConDup.decompose.absorb :=
    congrFun (congrFun (System.WellFormed.normDecomp_ne system_wellFormed hne) ruleConDup) rfl
  have hk : k = 4 :=
    (congrArg ExpSide.k e0).trans ((congrArg Decomposition.k hdec).trans
      DecompositionCheck.conDup_k)
  have hc : φ.net.cells = {Comb.dup, Comb.dup} :=
    (congrArg (fun s : ExpSide sig (sig.arity (Comb.con : sig.Sym)) => s.φ.net.cells) e0).trans
      ((RawSide.cells_expand _).trans
        ((congrArg (fun D : Decomposition sig (sig.arity (Comb.con : sig.Sym))
            (sig.arity (Comb.dup : sig.Sym)) => D.φ.net.cells) hdec).trans
          ((Decomposition.absorb_cells _).trans DecompositionCheck.conDup_cells.1)))
  have hc' : ψ.net.cells = {Comb.con, Comb.con} :=
    (congrArg (fun s : ExpSide sig (sig.arity (Comb.dup : sig.Sym)) => s.φ.net.cells) e1).trans
      ((RawSide.cells_expand _).trans
        ((congrArg (fun D : Decomposition sig (sig.arity (Comb.con : sig.Sym))
            (sig.arity (Comb.dup : sig.Sym)) => D.ψ.net.cells) hdec).trans
          DecompositionCheck.conDup_cells.2))
  refine ⟨k, φ, ψ, σ, hk, hc, hc', hP, fun k₀ => ?_, fun k₁ => ?_,
    codeCells_plug sd Comb.con Comb.dup zeroOne twoThree _ _ 0 φ ψ σ hσ hl he hl' he' hs hs'
      linear_netConDup⟩
  · exact (length_codeGammaExtras _ _ he hl k₀).trans (congrArg Multiset.card hc)
  · exact (length_codeGammaExtras _ _ he' hl' k₁).trans (congrArg Multiset.card hc')

/-- **`codeCells_plug` gives `Translation.Compatible` with the existing glue** (Fig. 10, pages
89–90; the analogue of Fig. 7, page 86; the decomposition, page 85). For a well-formed system
over a finite alphabet, the translation of Fig. 10 with the sides of `decData` is compatible with
reduction: `sides_expand` gives the sides and `Plugs r`, `codeCells_plug` with `Δ = 0` reduces the
two cells to `plugTermTarget`, `netTr_plug_termTr` makes it a translation of an instance of
`Rule.plug φ ψ σ`, and `Decomposition.Plugs.netTr_inst_of_sides` turns that into a translation of
an instance of `r`. -/
theorem compatible_of_codeCells_plug {S : Signature} [Finite S.Sym] (I : System S)
    (hI : I.WellFormed) : (codeTranslation hI.decData.side).Compatible I system := by
  intro α β r h xs ys f g hlin
  obtain ⟨k, φ, ψ, σ, hσ, hl, he, hl', he', hs, hs', hP⟩ := hI.decData.sides_expand hI h
  obtain ⟨k₀, k₁, M, tφ, tψ, hS, hE, htφ, htψ⟩ :=
    codeCells_plug hI.decData.side α β xs ys f g 0 φ ψ σ hσ hl he hl' he' hs hs' hlin
  rw [add_zero] at hE
  have hL : Net.Linear (plugTermTarget σ tφ tψ xs ys) :=
    hE.linear (hS.linear system_wellFormed.linear hlin)
  obtain ⟨h', N', hN, hE'⟩ := netTr_plug_termTr (codeTranslation hI.decData.side) he hl he' hl'
    σ k₀ k₁ tφ tψ htφ htψ xs ys hL
  obtain ⟨h'', N'', hN'', hE''⟩ :=
    Decomposition.Plugs.netTr_inst_of_sides (D := ⟨k, φ, ψ, σ⟩) hP hl hl' xs ys h' hN
  exact ⟨M, N'', h'', hS, hE.trans (hE'.symm.trans hE''), hN''⟩

end INet.Comb.CodeCellsPlugReview
