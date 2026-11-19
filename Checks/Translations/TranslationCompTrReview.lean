import Checks.Translations.TranslationCompReview
import InteractionCombinators.Translations.TranslationCompTr

/-!
# Review of `Translation.NetTr.comp` with internal wires on both sides (page 80)

Lafont 1997, Section 1.7, journal page 80, last paragraph: "Composition of translations is defined
in the obvious way." The check of `TranslationCompTrCheck.lean` uses two translations without
internal wires. Here both translations have one: `wTr` sends the symbol of arity `3` of `sigN 3`
to the two cells `star(x₀, w, star(w, x₁, x₂))`, joined by the internal wire `w`.

* `comp_natTree` — the principal net of `wTr ∘ wTr`, written out over `ℕ`: four cells, three
  internal wires, `3` from `Φ(α)` and `4, 5` from the two instances of `Ψ` inside it, in that
  order.
* `netTr_N'`, `netTr_N''`, `netTr_comp` — a cut with an internal wire, its translation by `Φ`, the
  translation of that by `Ψ`, and `NetTr.comp`.
* `inst_comp`, `left_eq_inst`, `left_ne_inst_swap`, `termTr_comp_left` — the left side of `N''`
  is the instance of `Ψ(Φ(α))` whose internal wires are named, in order, by the wire of the `Φ`
  instance (`10`) and then by those of the two `Ψ` instances (`20`, `21`); exchanging the first
  two names gives a different tree.
-/

namespace INet.TranslationCompTrReview

open Term Translation TranslationCompReview

/-- The cell `star(a, b, c)` of `sigN 3`. -/
abbrev cell3 (a b c : Term (sigN 3) ℕ) : Term (sigN 3) ℕ := .app (star 3) ![a, b, c]

/-- Two cells joined by the wire `w`: `star(a, w, star(w, b, c))`. -/
abbrev cellW (a : Term (sigN 3) ℕ) (w : ℕ) (b c : Term (sigN 3) ℕ) : Term (sigN 3) ℕ :=
  cell3 a (var w) (cell3 (var w) b c)

/-- The principal net `star(x₀, w, star(w, x₁, x₂))`: two cells, one internal wire `w`. -/
def twoNet : PNet (sigN 3) 3 where
  internal := 1
  tree := .app (star 3) ![.var (.inl 0), .var (.inr 0),
    .app (star 3) ![.var (.inr 0), .var (.inl 1), .var (.inl 2)]]
  port_count i := by
    fin_cases i <;> rfl
  internal_count w := by
    fin_cases w
    rfl

/-- The translation of the symbol of `sigN 3` to two cells joined by an internal wire. -/
def wTr : Translation (sigN 3) (sigN 3) := ⟨fun _ => twoNet⟩

/-- The composite has three internal wires: one from `Φ`, two from `Ψ`. -/
theorem comp_internal : ((wTr.comp wTr).net (star 3)).internal = 3 := rfl

/-- `wTr` replaces a cell by two cells joined by the wire `w`. -/
theorem termTr_w {a b c a' b' c' : Term (sigN 3) ℕ} (w : ℕ) (ha : wTr.TermTr a a')
    (hb : wTr.TermTr b b') (hc : wTr.TermTr c c') :
    wTr.TermTr (cell3 a b c) (cellW a' w b' c') := by
  have h := TermTr.app (Φ := wTr) (star 3) ![a, b, c] ![a', b', c'] ![w]
    (fun i => by fin_cases i <;> assumption)
  convert h using 1
  unfold cellW cell3
  congr 1
  funext i
  fin_cases i
  · rfl
  · rfl
  · change Term.app _ _ = Term.app _ _
    congr 1
    funext j
    fin_cases j <;> rfl

/-- One cut between two cells, the internal wire `1` between them, the free ports `0, 2, 3, 4`. -/
def N : Net (sigN 3) ℕ := s(cell3 (var 0) (var 1) (var 2), cell3 (var 1) (var 3) (var 4)) ::ₘ 0

/-- `N` translated by `Φ = wTr`, the new wires `10` and `11`. -/
def N' : Net (sigN 3) ℕ :=
  s(cellW (var 0) 10 (var 1) (var 2), cellW (var 1) 11 (var 3) (var 4)) ::ₘ 0

/-- The left side of `N''`: `Ψ` applied to `cellW 0 10 1 2`, the new wires `20` and `21`. -/
abbrev left'' : Term (sigN 3) ℕ := cellW (var 0) 20 (var 10) (cellW (var 10) 21 (var 1) (var 2))

/-- The right side of `N''`, the new wires `22` and `23`. -/
abbrev right'' : Term (sigN 3) ℕ := cellW (var 1) 22 (var 11) (cellW (var 11) 23 (var 3) (var 4))

/-- `N'` translated by `Ψ = wTr`: eight cells. -/
def N'' : Net (sigN 3) ℕ := s(left'', right'') ::ₘ 0

/-- The names of `cell3`. -/
theorem vars_cell3 (a b c : Term (sigN 3) ℕ) : (cell3 a b c).vars = a.vars + b.vars + c.vars := by
  change (∑ i : Fin 3, _) = _
  rw [Fin.sum_univ_three]
  rfl

/-- `N` has an internal wire, the name `1`, and its one equation is a cut. -/
theorem N_wire_cut : N.vars.count 1 = 2 ∧
    ∃ a b c d e, N = s(cell3 (var a) (var b) (var c), cell3 (var b) (var d) (var e)) ::ₘ 0 :=
  ⟨by simp [N, vars_cell3], 0, 1, 2, 3, 4, rfl⟩

/-- `N'` is a translation of `N` by `Φ` (page 80). -/
theorem netTr_N' : wTr.NetTr N N' := by
  refine ⟨Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl,
    termTr_w 10 (.var _) (.var _) (.var _), termTr_w 11 (.var _) (.var _) (.var _)⟩
    Multiset.Rel.zero, ?_⟩
  unfold Net.Linear
  intro y
  simp [N', vars_cell3, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- `N''` is a translation of `N'` by `Ψ` (page 80). -/
theorem netTr_N'' : wTr.NetTr N' N'' := by
  refine ⟨Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl,
    termTr_w 20 (.var _) (.var _) (termTr_w 21 (.var _) (.var _) (.var _)),
    termTr_w 22 (.var _) (.var _) (termTr_w 23 (.var _) (.var _) (.var _))⟩
    Multiset.Rel.zero, ?_⟩
  unfold Net.Linear
  intro y
  simp [N'', vars_cell3, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- **The composite translates `N` to `N''`** (page 80): by `NetTr.comp`, `N''`, eight cells and
six new wires, is a translation of `N` by `wTr ∘ wTr`. -/
theorem netTr_comp : (wTr.comp wTr).NetTr N N'' :=
  netTr_N'.comp netTr_N''

/-! ## The principal net of the composite, written out -/

/-- Substituting in a cell substitutes in its three subtrees. -/
theorem bind_cell3 (σ : ℕ → Term (sigN 3) ℕ) (a b c : Term (sigN 3) ℕ) :
    (cell3 a b c).bind σ = cell3 (a.bind σ) (b.bind σ) (c.bind σ) := by
  change Term.app _ _ = Term.app _ _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- An instance of `twoNet`: two cells joined by the wire `f 0`. -/
theorem inst_twoNet (args : Fin 3 → Term (sigN 3) ℕ) (f : Fin 1 → ℕ) :
    twoNet.inst args f = cellW (args 0) (f 0) (args 1) (args 2) := by
  change Term.app _ _ = Term.app _ _
  congr 1
  funext i
  fin_cases i
  · rfl
  · rfl
  · change Term.app _ _ = Term.app _ _
    congr 1
    funext j
    fin_cases j <;> rfl

/-- The translation of a cell by `wTr`, its wire numbered `k`: the subtrees take the next blocks
of names, in order. -/
theorem trTerm_cell3 (k : ℕ) (a b c : Term (sigN 3) ℕ) :
    wTr.trTerm k (cell3 a b c) =
      cellW (wTr.trTerm (k + 1) a) k (wTr.trTerm (k + 1 + wTr.size a) b)
        (wTr.trTerm (k + 1 + (wTr.size a + wTr.size b)) c) := by
  refine (inst_twoNet _ _).trans ?_
  have h1 : (wTr.net (star 3)).internal = 1 := rfl
  simp only [h1, off]
  rfl

/-- The tree of `twoNet` over `ℕ`: ports `0, 1, 2`, internal wire `3`. -/
theorem natTree_twoNet : twoNet.natTree = cellW (var 0) 3 (var 1) (var 2) := by
  change Term.app _ _ = Term.app _ _
  congr 1
  funext i
  fin_cases i
  · rfl
  · rfl
  · change Term.app _ _ = Term.app _ _
    congr 1
    funext j
    fin_cases j <;> rfl

/-- **The principal net of `wTr ∘ wTr`** (page 80), over `ℕ`: the ports are `0, 1, 2`, the wire
of `Φ(α)` is `3`, the wires of the instance of `Ψ` at the root and of the inner one are `4` and
`5`. Four cells, three internal wires. -/
theorem comp_natTree :
    ((wTr.comp wTr).net (star 3)).natTree =
      cellW (var 0) 4 (var 3) (cellW (var 3) 5 (var 1) (var 2)) := by
  refine (natTree_trPNet wTr twoNet).trans ?_
  rw [natTree_twoNet, trTerm_cell3, trTerm_cell3]
  rfl

/-- An instance of a principal net is its tree over `ℕ` with the names decoded: `σ` sends the
port `i` to `args i` and the internal wire `w`, named `n + w`, to `g w`. -/
theorem inst_eq_bind_natTree {S : Signature} {n : ℕ} (p : PNet S n) (args : Fin n → Term S ℕ)
    (g : Fin p.internal → ℕ) (σ : ℕ → Term S ℕ)
    (hσ : ∀ x, σ (p.enc x) = Sum.elim args (fun w => var (g w)) x) :
    p.inst args g = p.natTree.bind σ := by
  unfold PNet.inst PNet.natTree
  rw [Term.bind_bind]
  exact Term.bind_congr fun x _ => (hσ x).symm

/-- **An instance of `wTr ∘ wTr`** (page 80): the internal wire `0` of the composite is the wire
of `Φ(α)`, the wires `1` and `2` those of the instances of `Ψ` at the root and inside. -/
theorem inst_comp (xs : Fin 3 → ℕ) (g : Fin 3 → ℕ) :
    ((wTr.comp wTr).net (star 3)).inst (fun i => var (xs i)) g =
      cellW (var (xs 0)) (g 1) (var (g 0)) (cellW (var (g 0)) (g 2) (var (xs 1)) (var (xs 2))) := by
  let σ : ℕ → Term (sigN 3) ℕ := fun x =>
    var (if h : x < 6 then ![xs 0, xs 1, xs 2, g 0, g 1, g 2] ⟨x, h⟩ else 0)
  refine (inst_eq_bind_natTree ((wTr.comp wTr).net (star 3)) _ g σ ?_).trans ?_
  · rintro (i | w)
    · fin_cases i <;> rfl
    · fin_cases w <;> rfl
  · rw [comp_natTree]
    simp only [bind_cell3, bind_var]
    rfl

/-- **The left side of `N''` is an instance of `Ψ(Φ(α))`** (page 80): its ports are `0, 1, 2`,
and its internal wires are `10`, the wire of the instance of `Φ`, then `20` and `21`, those of
the instances of `Ψ`. -/
theorem left_eq_inst : left'' = ((wTr.comp wTr).net (star 3)).inst
    (fun i => var (![0, 1, 2] i)) ![10, 20, 21] :=
  (inst_comp ![0, 1, 2] ![10, 20, 21]).symm

/-- **The order of the blocks matters** (page 80): naming the internal wires of `Ψ(Φ(α))` by
`20, 10, 21`, the wire of `Φ` and the root wire of `Ψ` exchanged, does not give the left side of
`N''`. -/
theorem left_ne_inst_swap : left'' ≠ ((wTr.comp wTr).net (star 3)).inst
    (fun i => var (![0, 1, 2] i)) ![20, 10, 21] := by
  intro h
  have h := h.trans (inst_comp ![0, 1, 2] ![20, 10, 21])
  have h1 := congrFun (eq_of_heq (Term.app.inj h).2) ⟨1, by decide⟩
  simp at h1

/-- **The left side of `N''` is a translation by the composite, directly** (page 80): it is the
instance of `Ψ(Φ(α))` with the ports `0, 1, 2` and the internal wires `10, 20, 21`, the names that
`NetTr.comp` finds without stating them. -/
theorem termTr_comp_left : (wTr.comp wTr).TermTr (cell3 (var 0) (var 1) (var 2)) left'' := by
  refine left_eq_inst ▸ ?_
  have h := TermTr.app (Φ := wTr.comp wTr) (star 3) ![var 0, var 1, var 2]
    (fun i => var (![0, 1, 2] i)) ![10, 20, 21] (fun i => by fin_cases i <;> exact .var _)
  exact h

end INet.TranslationCompTrReview
