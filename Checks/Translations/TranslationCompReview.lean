import InteractionCombinators.Translations.TranslationCompBasic

/-!
# Review of `Translation.comp`, `PNet.Iso` and `Translation.Invertible` (pages 80–81)

Lafont 1997, page 80, last paragraph, and page 81, top: "Composition of translations is defined in
the obvious way. One says that `Φ` is invertible if there is a translation `Φ⁻¹` of `Σ'` into `Σ`
such that `Φ⁻¹ ∘ Φ = id_Σ` and `Φ ∘ Φ⁻¹ = id_Σ'`. In that case, it is easy to see that each
`Φ(α)` is necessarily of the following form [a cell `α'` under a permutation `σ` of its auxiliary
ports]".

The general lemmas on the tree of `Ψ(p)` over `ℕ` (`Translation.natTree_trPNet`,
`Translation.cells_trPNet`, …) are in
`InteractionCombinators/Translations/TranslationCompBasic.lean`.

* `permTr σ` — the translation of a symbol of arity `k` to itself with its auxiliary ports
  permuted by `σ`, the form of the figure of page 81. `comp_permTr`: `permTr τ ∘ permTr σ` is
  `permTr (τ.trans σ)`, so composition composes the permutations, in the right order
  (`comp_permTr_order`); `permTr_invertible`: every `permTr σ` is invertible;
  `permTr_rot_comp_self_not_iso`: a 3-cycle is not its own inverse.
* `twoCells_not_invertible` — the translation `α ↦ β(γ(x₀), x₁)`, two cells, is not invertible.
-/

namespace INet

open Term

namespace TranslationCompReview

open Translation PNet

/-! ## Permutations of the auxiliary ports (figure of page 81) -/

/-- One symbol, of arity `k`. -/
def sigN (k : ℕ) : Signature := ⟨Unit, fun _ => k⟩

/-- The symbol of `sigN k`. -/
def star (k : ℕ) : (sigN k).Sym := ()

/-- The cell of `sigN k` with its auxiliary ports permuted by `σ`: its auxiliary port `i` is the
port `σ i` of the net. This is the form `α' ∘ σ` of the figure of page 81. -/
def permNet {k : ℕ} (σ : _root_.Equiv.Perm (Fin k)) : PNet (sigN k) k where
  internal := 0
  tree := .app (star k) fun i => .var (.inl (σ i))
  port_count i := by
    rw [Term.vars_app, Multiset.count_sum']
    simp only [Term.vars_var, Multiset.count_singleton, Sum.inl.injEq]
    exact (show (∑ x : Fin k, if i = σ x then (1 : ℕ) else 0) = 1 by
      rw [← _root_.Equiv.sum_comp σ.symm]
      simp)
  internal_count w := w.elim0

/-- The identity permutation gives the cell itself. -/
theorem permNet_refl (k : ℕ) :
    permNet (_root_.Equiv.refl (Fin k)) = PNet.cell (S := sigN k) (star k) :=
  rfl

/-- The translation of the symbol of `sigN k` to itself with its ports permuted by `σ`. -/
def permTr {k : ℕ} (σ : _root_.Equiv.Perm (Fin k)) : Translation (sigN k) (sigN k) :=
  ⟨fun _ => permNet σ⟩

/-- `permNet σ` and `permNet τ` are the same graph only if `σ = τ`: `Iso` fixes the ports, so it
sees the permutation. -/
theorem permNet_iso {k : ℕ} {σ τ : _root_.Equiv.Perm (Fin k)} (h : (permNet σ).Iso (permNet τ)) :
    σ = τ := by
  obtain ⟨e, he⟩ := h
  have he' : (Term.app (star k) fun i => Term.var (Sum.map id e (.inl (σ i)))) =
      Term.app (star k) fun i => Term.var (.inl (τ i)) := he
  simp only [Term.app.injEq, heq_eq_eq, true_and] at he'
  ext i
  have h3 := congrFun he' i
  simp only [Term.var.injEq, Sum.map_inl, id, Sum.inl.injEq] at h3
  rw [h3]

/-- **Composition composes the permutations** (page 80): `permTr τ ∘ permTr σ` sends the symbol
to the cell with its ports permuted by `τ.trans σ`, that is `σ ∘ τ`: the auxiliary port `j` of
the cell is the port `σ (τ j)`. -/
theorem comp_permTr {k : ℕ} (τ σ : _root_.Equiv.Perm (Fin k)) :
    (((permTr τ).comp (permTr σ)).net (star k)).Iso (permNet (τ.trans σ)) := by
  have hs : (permTr τ).size (permNet σ).natTree = 0 := by
    show (permTr τ).size (Term.app (star k) fun i => Term.var (σ i : ℕ)) = 0
    simp [Translation.size, permTr, permNet]
  have hm : (permNet (τ.trans σ)).internal = 0 + (permTr τ).size (permNet σ).natTree := by
    rw [hs]
    rfl
  have hy := (permTr τ).trPNet_hyps ((permTr σ).net (star k))
  exact iso_ofNat (permNet (τ.trans σ)) (finCongr hm) hy.1 hy.2.1 hy.2.2 rfl

/-- **Every port permutation is invertible** (page 81): `permTr σ⁻¹` is an inverse of
`permTr σ`. -/
theorem permTr_invertible {k : ℕ} (σ : _root_.Equiv.Perm (Fin k)) : (permTr σ).Invertible := by
  refine ⟨permTr σ.symm, fun _ => ?_, fun _ => ?_⟩
  · have h := comp_permTr σ.symm σ
    rw [_root_.Equiv.symm_trans_self, permNet_refl] at h
    exact h
  · have h := comp_permTr σ σ.symm
    rw [_root_.Equiv.self_trans_symm, permNet_refl] at h
    exact h

/-- **Composition is in the right order** (page 80): with the transpositions `σ = (0 1)` and
`τ = (1 2)` of `Fin 3`, `permTr τ ∘ permTr σ` is not `permTr (σ.trans τ)`; it is
`permTr (τ.trans σ)` by `comp_permTr`. An error in the port order of `enc` or `ofNat`, or in the
order of `comp`, would make one of the two statements fail. -/
theorem comp_permTr_order :
    ¬ (((permTr (_root_.Equiv.swap (1 : Fin 3) 2)).comp
        (permTr (_root_.Equiv.swap (0 : Fin 3) 1))).net (star 3)).Iso
      (permNet ((_root_.Equiv.swap (0 : Fin 3) 1).trans (_root_.Equiv.swap 1 2))) := by
  intro h
  have hst := congrArg (fun f : _root_.Equiv.Perm (Fin 3) => f 0)
    (permNet_iso ((comp_permTr _ _).symm.trans h))
  revert hst
  decide

/-- **A 3-cycle is not its own inverse** (page 81): for the rotation `ρ` of the three ports,
`permTr ρ ∘ permTr ρ` is not the identity, although `permTr ρ` is invertible. -/
theorem permTr_rot_comp_self_not_iso :
    ¬ (((permTr (finRotate 3)).comp (permTr (finRotate 3))).net (star 3)).Iso
      ((Translation.id (sigN 3)).net (star 3)) := by
  intro h
  have h' : (permNet ((finRotate 3).trans (finRotate 3))).Iso
      (permNet (_root_.Equiv.refl (Fin 3))) := by
    rw [permNet_refl]
    exact (comp_permTr _ _).symm.trans h
  have hst := congrArg (fun f : _root_.Equiv.Perm (Fin 3) => f 0) (permNet_iso h')
  revert hst
  decide

/-! ## A translation with two cells is not invertible -/

/-- Two symbols: `true` of arity `2` (Lafont's `β` in this check) and `false` of arity `1`
(`γ`). -/
def sigBG : Signature := ⟨Bool, fun b => match b with | true => 2 | false => 1⟩

/-- The symbol `β` of `sigBG`, of arity `2`. -/
def symB : sigBG.Sym := true

/-- The symbol `γ` of `sigBG`, of arity `1`. -/
def symG : sigBG.Sym := false

/-- The principal net `β(γ(x₀), x₁)`: two cells. -/
def twoCells : PNet sigBG 2 where
  internal := 0
  tree := .app symB ![.app symG ![.var (.inl 0)], .var (.inl 1)]
  port_count i := by
    fin_cases i <;> rfl
  internal_count w := w.elim0

/-- The translation of the symbol of arity `2` of `sigN 2` to `β(γ(x₀), x₁)`. -/
def twoCellsTr : Translation (sigN 2) sigBG := ⟨fun _ => twoCells⟩

/-- The translation by `twoCellsTr` of a tree is either a wire or has a cell `γ`, so its cells
are never the single cell `β`. -/
theorem cells_trTerm_twoCells (k : ℕ) (t : Term (sigN 2) ℕ) :
    (twoCellsTr.trTerm k t).cells ≠ {symB} := by
  cases t with
  | var x => exact (Multiset.singleton_ne_zero _).symm
  | app a ts =>
    intro h
    have hf : symG ∈ (twoCellsTr.trTerm k (.app a ts)).cells := by
      have key : ∀ (u : Fin (sigBG.arity symG) → Term sigBG ℕ) (v : Term sigBG ℕ),
          symG ∈ (Term.app symB ![Term.app symG u, v]).cells := by
        intro u v
        exact Multiset.mem_cons_of_mem
          (Multiset.mem_sum.2 ⟨(0 : Fin 2), Finset.mem_univ _, Multiset.mem_cons_self _ _⟩)
      exact key _ _
    rw [h, Multiset.mem_singleton] at hf
    cases hf

/-- **A translation with two cells is not invertible** (page 81): `twoCellsTr`, which sends the
symbol of arity `2` to `β(γ(x₀), x₁)`, has no inverse. If `Ψ` were one, `twoCellsTr(Ψ(β))` would
be the single cell `β` up to the names of internal wires; but the translation of any principal
net by `twoCellsTr` is a wire or contains a cell `γ`. This is the content of the figure of page
81 in a case where `Φ(α)` is not a single cell. -/
theorem twoCells_not_invertible : ¬ twoCellsTr.Invertible := by
  rintro ⟨Ψ, -, h⟩
  have hc : (twoCellsTr.trPNet (Ψ.net symB)).tree.cells =
      (PNet.cell (S := sigBG) symB).tree.cells := (h symB).cells_eq
  rw [cells_trPNet] at hc
  exact cells_trTerm_twoCells _ _ (hc.trans (by simp [PNet.cell]))

end TranslationCompReview

end INet
