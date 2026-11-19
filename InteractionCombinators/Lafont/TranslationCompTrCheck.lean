import InteractionCombinators.Lafont.TranslationCompReview
import InteractionCombinators.Lafont.TranslationCompTr

/-!
# A concrete check of `Translation.NetTr.comp` (page 80)

Lafont 1997, Section 1.7, page 80: "composition of translations is defined in the obvious way".
`Φ = permTr (0 1)` exchanges the two auxiliary ports of the symbol of `sigN 2`; `Ψ = twoCellsTr`
sends that symbol to the two cells `β(γ(x₀), x₁)` (`TranslationCompReview.lean`). Neither is the
identity. The net `N` is one cut between two cells, joined by the internal wire `1`, with free
ports `0` and `2`. Its translations `N'` by `Φ` and `N''` by `Ψ` are written out, and `N''` is a
translation of `N` by `Ψ ∘ Φ`: the hypotheses of `NetTr.comp` are satisfiable by non-trivial
translations.
-/

namespace INet.TranslationCompTrCheck

open Term Translation TranslationCompReview

/-- The exchange of the two auxiliary ports. -/
abbrev σ : _root_.Equiv.Perm (Fin 2) := _root_.Equiv.swap 0 1

/-- The cell `star(a, b)` of `sigN 2`. -/
abbrev cell2 (a b : ℕ) : Term (sigN 2) ℕ := .app (star 2) ![var a, var b]

/-- The cell `β(γ(a), b)` of `sigBG`. -/
abbrev cellBG (a b : ℕ) : Term sigBG ℕ := .app symB ![.app symG ![var a], var b]

/-- One cut between two cells, the internal wire `1` between them, the free ports `0` and `2`. -/
def N : Net (sigN 2) ℕ := s(cell2 0 1, cell2 1 2) ::ₘ 0

/-- `N` with the auxiliary ports of both cells exchanged. -/
def N' : Net (sigN 2) ℕ := s(cell2 1 0, cell2 2 1) ::ₘ 0

/-- `N'` with each cell replaced by `β(γ(x₀), x₁)`. -/
def N'' : Net sigBG ℕ := s(cellBG 1 0, cellBG 2 1) ::ₘ 0

/-- The names of `cell2 a b`. -/
theorem vars_cell2 (a b : ℕ) : (cell2 a b).vars = a ::ₘ b ::ₘ 0 := by
  show (∑ i : Fin 2, _) = _
  rw [Fin.sum_univ_two]
  simp [Multiset.singleton_add]

/-- The names of `cellBG a b`. -/
theorem vars_cellBG (a b : ℕ) : (cellBG a b).vars = a ::ₘ b ::ₘ 0 := by
  show (∑ i : Fin 2, _) = _
  rw [Fin.sum_univ_two]
  have h : (Term.app symG ![var a] : Term sigBG ℕ).vars = {a} := by
    show (∑ i : Fin 1, _) = _
    simp
  simp [h, Multiset.singleton_add]

/-- `N` has an internal wire, the name `1`, and its one equation is a cut. -/
theorem N_wire_cut : N.vars.count 1 = 2 ∧ ∃ a b, N = s(cell2 0 a, cell2 a b) ::ₘ 0 :=
  ⟨by simp [N, vars_cell2], 1, 2, rfl⟩

/-- `Φ` exchanges the ports of a cell. -/
theorem termTr_perm (a b : ℕ) : (permTr σ).TermTr (cell2 a b) (cell2 b a) := by
  have h := TermTr.app (Φ := permTr σ) (star 2) ![var a, var b] ![var a, var b] Fin.elim0
    (fun i => by fin_cases i <;> exact .var _)
  convert h using 1
  unfold cell2
  congr 1
  funext i
  fin_cases i <;> rfl

/-- `Ψ` replaces a cell by `β(γ(x₀), x₁)`. -/
theorem termTr_two (a b : ℕ) : twoCellsTr.TermTr (cell2 a b) (cellBG a b) := by
  have h := TermTr.app (Φ := twoCellsTr) (star 2) ![var a, var b] ![var a, var b] Fin.elim0
    (fun i => by fin_cases i <;> exact .var _)
  convert h using 1
  unfold cellBG
  congr 1
  funext i
  fin_cases i
  · change Term.app _ _ = Term.app _ _
    congr 1
    funext j
    fin_cases j
    rfl
  · rfl

/-- `N'` is a translation of `N` by `Φ` (page 80). -/
theorem netTr_N' : (permTr σ).NetTr N N' := by
  refine ⟨Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, termTr_perm 0 1, termTr_perm 1 2⟩
    Multiset.Rel.zero, ?_⟩
  unfold Net.Linear
  intro y
  simp [N', vars_cell2, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- `N''` is a translation of `N'` by `Ψ` (page 80). -/
theorem netTr_N'' : twoCellsTr.NetTr N' N'' := by
  refine ⟨Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, termTr_two 1 0, termTr_two 2 1⟩
    Multiset.Rel.zero, ?_⟩
  unfold Net.Linear
  intro y
  simp [N'', vars_cellBG, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- **The composite translates `N` to `N''`** (page 80): by `NetTr.comp`, `N''` is a translation
of `N` by `twoCellsTr ∘ permTr (0 1)`. -/
theorem netTr_comp : (twoCellsTr.comp (permTr σ)).NetTr N N'' :=
  netTr_N'.comp netTr_N''

end INet.TranslationCompTrCheck
