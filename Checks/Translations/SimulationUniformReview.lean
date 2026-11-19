import InteractionCombinators.Translations.SimulationUniform
import InteractionCombinators.Universality.RecursionFree.DecompositionLemmas

/-!
# Review of the uniform bounds `L`, `M` (page 81)

Review of `Lafont/SimulationUniform.lean` (issue #233). Lafont 1997, page 81: "let `L` (resp.
`M`) be the minimal (resp. the maximal) length of all those reductions".

* **Degenerate cases.**
  - `exists_distinct_linear_naming`: every pair `Φ(α)(xs) = Φ(β)(ys)` has a linear naming with
    pairwise distinct names. So the branch of `Translation.Compatible.exists_length` that picks
    `k = 0` for want of such a naming never applies to a pair with a rule, and `len_spec` shows
    that `Compatible.len h (α, β)` is the length of an actual reduction for every rule.
  - `ruleLens_eq_empty`, `compatibleWithin_of_no_rules`: a system without rules has no lengths,
    `sInf ∅ = sSup ∅ = 0`, and every translation is compatible within any bounds. The statement
    `compatibleWithin_len` stays true there, and says nothing, as the paper does.
* **A system with two rules of different lengths.** The source has two symbols `z`, `c` without
  auxiliary ports and the rules `z z ↦ ∅`, `c c ↦ ∅`. The target has `z` without auxiliary port
  and `e` with one, and the rules `z z ↦ ∅`, `e e ↦ {x = y}`. The translation keeps `z` and
  sends `c` to the tree `e(z)`. The rule of `z` is simulated in one interaction, the rule of `c`
  in two. Every rule of the target removes two cells and creates none, so the number of cells
  fixes the length of every reduction (`card_cells_stepsEN`). It follows that `Φ` is compatible
  within `L` and `M` exactly when `L ≤ 1` and `2 ≤ M` (`compatibleWithin_iff`), and that
  `compatibleWithin_len` gives `L = 1`, `M = 2` (`sInf_ruleLens`, `sSup_ruleLens`).
-/

namespace INet.SimulationUniformReview

open Term Translation SimulationUniform

/-! ## Degenerate cases -/

section General

variable {S S' : Signature}

/-- An injective renaming of the leaves of a principal net: every name occurs at most twice. -/
theorem count_map_le_two {n : ℕ} (p : PNet S' n) (ν : Fin n ⊕ Fin p.internal → ℕ)
    (hν : Function.Injective ν) (y : ℕ) : (p.tree.vars.map ν).count y ≤ 2 := by
  classical
  by_cases h : ∃ x, ν x = y
  · obtain ⟨x, rfl⟩ := h
    rw [Multiset.count_map_eq_count' _ _ hν]
    rcases x with i | w
    · rw [p.port_count i]; omega
    · rw [p.internal_count w]
  · rw [Multiset.count_eq_zero_of_notMem]
    · omega
    · intro hy
      obtain ⟨x, -, hx⟩ := Multiset.mem_map.1 hy
      exact h ⟨x, hx⟩

/-- **Every pair has a linear naming with distinct names** (Lafont 1997, page 80: the two cells of
a rule have distinct ports). For any translation and any symbols `α`, `β`, the names
`xs i = 4 i`, `ys j = 4 j + 1`, `f w = 4 w + 2`, `g w = 4 w + 3` are pairwise distinct and make
the pair `Φ(α)(xs) = Φ(β)(ys)` linear. Hence the case of `Compatible.exists_length` in which no
such naming exists, and `k` is arbitrary, never happens. -/
theorem exists_distinct_linear_naming (Φ : Translation S S') (α β : S.Sym) :
    ∃ (xs : Fin (S.arity α) → ℕ) (ys : Fin (S.arity β) → ℕ)
      (f : Fin (Φ.net α).internal → ℕ) (g : Fin (Φ.net β).internal → ℕ),
      Function.Injective xs ∧ Function.Injective ys ∧ (∀ i j, xs i ≠ ys j) ∧
      Net.Linear ({s((Φ.net α).inst (fun i => .var (xs i)) f,
        (Φ.net β).inst (fun j => .var (ys j)) g)} : Net S' ℕ) := by
  classical
  let xs : Fin (S.arity α) → ℕ := fun i => 4 * i
  let ys : Fin (S.arity β) → ℕ := fun j => 4 * j + 1
  let f : Fin (Φ.net α).internal → ℕ := fun w => 4 * w + 2
  let g : Fin (Φ.net β).internal → ℕ := fun w => 4 * w + 3
  refine ⟨xs, ys, f, g, fun i j h => Fin.ext (by simp only [xs] at h; omega),
    fun i j h => Fin.ext (by simp only [ys] at h; omega),
    fun i j h => by simp only [xs, ys] at h; omega, fun y => ?_⟩
  rw [Net.vars_singleton, eqVars_mk, vars_inst, vars_inst, Multiset.count_add]
  have hA := count_map_le_two (Φ.net α) (Sum.elim xs f)
    (by
      rintro (i | i) (j | j) h <;> simp only [Sum.elim_inl, Sum.elim_inr, xs, f] at h
      all_goals first | (congr 1; exact Fin.ext (by omega)) | omega) y
  have hB := count_map_le_two (Φ.net β) (Sum.elim ys g)
    (by
      rintro (i | i) (j | j) h <;> simp only [Sum.elim_inl, Sum.elim_inr, ys, g] at h
      all_goals first | (congr 1; exact Fin.ext (by omega)) | omega) y
  have mA : y ∈ (Φ.net α).tree.vars.map (Sum.elim xs f) → y % 4 = 0 ∨ y % 4 = 2 := by
    intro hy
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 hy
    rcases x with i | w <;> simp only [Sum.elim_inl, Sum.elim_inr, xs, f] <;> omega
  have mB : y ∈ (Φ.net β).tree.vars.map (Sum.elim ys g) → y % 4 = 1 ∨ y % 4 = 3 := by
    intro hy
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 hy
    rcases x with i | w <;> simp only [Sum.elim_inl, Sum.elim_inr, ys, g] <;> omega
  by_cases h0 : ((Φ.net α).tree.vars.map (Sum.elim xs f)).count y = 0
  · omega
  · have h1 := mA (Multiset.count_ne_zero.1 h0)
    have h2 : ((Φ.net β).tree.vars.map (Sum.elim ys g)).count y = 0 :=
      Multiset.count_eq_zero.2 fun hy => by have := mB hy; omega
    omega

/-- **The length of a rule is the length of a reduction** (Lafont 1997, page 81). For a compatible
`Φ` and a rule `r` of `α`–`β`, some linear naming of the pair with distinct names reduces in
exactly `Compatible.len h (α, β)` interactions to a translation of an instance of `r`. So `L` and
`M` of `compatibleWithin_len` are lengths of reductions, not arbitrary numbers. -/
theorem len_spec {Φ : Translation S S'} {I : System S} {I' : System S'} (h : Φ.Compatible I I')
    {α β : S.Sym} {r : Rule S (S.arity α) (S.arity β)} (hr : I.rule α β = some r) :
    ∃ (xs : Fin (S.arity α) → ℕ) (ys : Fin (S.arity β) → ℕ)
      (f : Fin (Φ.net α).internal → ℕ) (g : Fin (Φ.net β).internal → ℕ)
      (M N' : Net S' ℕ) (h' : Fin r.internal → ℕ),
      StepsEN I' (h.len (α, β)) (s((Φ.net α).inst (fun i => .var (xs i)) f,
        (Φ.net β).inst (fun j => .var (ys j)) g) ::ₘ 0) M ∧
      Equiv M N' ∧ Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h') N' := by
  obtain ⟨xs, ys, f, g, hx, hy, hxy, hl⟩ := exists_distinct_linear_naming Φ α β
  exact ⟨xs, ys, f, g, (h.exists_length α β).choose_spec r hr xs ys f g hx hy hxy hl⟩

/-- A system without rules has no lengths: `ruleLens` is empty, and `L = sInf ∅ = 0`,
`M = sSup ∅ = 0` in `compatibleWithin_len` (Lafont 1997, page 81). -/
theorem ruleLens_eq_empty {I : System S} (hI : ∀ α β, I.rule α β = none) (K : S.Sym × S.Sym → ℕ) :
    ruleLens (I := I) K = ∅ ∧ sInf (ruleLens (I := I) K) = 0 ∧ sSup (ruleLens (I := I) K) = 0 := by
  have e : ruleLens (I := I) K = ∅ := by
    ext n
    simp [ruleLens, hI]
  exact ⟨e, by rw [e, Nat.sInf_empty], by rw [e, csSup_empty]; rfl⟩

/-- A system without rules: every translation is compatible within any bounds, in particular
within `0` and `0`. The conclusion of `compatibleWithin_len` holds there and carries no
information, as in the paper, where `L` and `M` are then undefined. -/
theorem compatibleWithin_of_no_rules (Φ : Translation S S') {I : System S} (I' : System S')
    (hI : ∀ α β, I.rule α β = none) (L M : ℕ) : Φ.CompatibleWithin I I' L M := by
  intro α β r hr
  rw [hI] at hr
  cases hr

end General

/-! ## Two rules of different lengths -/

/-- Source symbols: `z` and `c`, both without auxiliary ports. -/
inductive USym : Type
  | z | c
  deriving DecidableEq

/-- The source signature: every symbol has arity `0`. -/
def usig : Signature where
  Sym := USym
  arity _ := 0

instance : Finite usig.Sym :=
  Finite.of_surjective (fun b : Bool => if b then USym.z else USym.c) fun x => by
    cases x
    exacts [⟨true, rfl⟩, ⟨false, rfl⟩]

/-- Target symbols: `z` without auxiliary port, `e` with one. -/
inductive VSym : Type
  | z | e
  deriving DecidableEq

/-- The target signature. -/
def vsig : Signature where
  Sym := VSym
  arity
    | .z => 0
    | .e => 1

instance : DecidableEq vsig.Sym := inferInstanceAs (DecidableEq VSym)

/-- The source symbol `z`, typed as a symbol of `usig`. -/
abbrev uz : usig.Sym := USym.z

/-- The source symbol `c`, typed as a symbol of `usig`. -/
abbrev uc : usig.Sym := USym.c

/-- The target symbol `z`, typed as a symbol of `vsig`. -/
abbrev vz : vsig.Sym := VSym.z

/-- The target symbol `e`, typed as a symbol of `vsig`. -/
abbrev ve : vsig.Sym := VSym.e

instance {ν : Type} [DecidableEq ν] : DecidableEq (Term vsig ν) :=
  Comb.DecompositionCheck.termDecEq

/-- The target cell `z`. -/
def zT {ν : Type} : Term vsig ν := .app vz Fin.elim0

/-- The target cell `e` with a tree on its auxiliary port. -/
def eT {ν : Type} (t : Term vsig ν) : Term vsig ν := .app ve fun _ => t

/-- The source rules `z z ↦ ∅` and `c c ↦ ∅`. -/
def usys : System usig where
  rule
    | .z, .z => some ⟨0, 0⟩
    | .c, .c => some ⟨0, 0⟩
    | _, _ => none

/-- `e e ↦ {x = y}`: the auxiliary ports of the two cells are joined. -/
def ruleEE : Rule vsig 1 1 := ⟨0, s(.var (.inl 0), .var (.inr (.inl 0))) ::ₘ 0⟩

/-- The target rules `z z ↦ ∅` and `e e ↦ {x = y}`. -/
def vsys : System vsig where
  rule
    | .z, .z => some ⟨0, 0⟩
    | .e, .e => some ruleEE
    | _, _ => none

/-- `usys` is an interaction system in the sense of Lafont (page 72). -/
theorem usys_wellFormed : usys.WellFormed where
  linear := by
    intro α β r h
    cases α <;> cases β <;> cases h <;> exact ⟨fun i => i.elim0, fun i => i.elim0, fun w => w.elim0⟩
  reduced := by
    intro α β r h
    cases α <;> cases β <;> cases h <;> exact fun e he => by cases he
  unique := by
    intro α β hne h
    cases α <;> cases β <;> first | exact absurd rfl hne | rfl
  symm := by
    refine fun α r h => Rule.symm_of_equiv ?_
    revert α r h
    intro α r h
    cases α <;> cases h <;> exact Equiv.refl _

/-- `vsys` is an interaction system in the sense of Lafont (page 72). -/
theorem vsys_wellFormed : vsys.WellFormed where
  linear := by
    intro α β r h
    cases α <;> cases β <;> cases h
    · exact ⟨fun i => i.elim0, fun i => i.elim0, fun w => w.elim0⟩
    · exact ⟨by decide, by decide, fun w => w.elim0⟩
  reduced := by
    intro α β r h
    cases α <;> cases β <;> cases h
    · exact fun e he => by cases he
    · intro e he
      rcases Multiset.mem_cons.1 (show e ∈ _ ::ₘ 0 from he) with rfl | h
      · exact ⟨_, _, rfl, fun w h => by cases h⟩
      · cases h
  unique := by
    intro α β hne h
    cases α <;> cases β <;> first | exact absurd rfl hne | rfl
  symm := by
    refine fun α r h => Rule.symm_of_equiv ?_
    revert α r h
    intro α r h
    cases α <;> cases h
    · exact Equiv.refl _
    · refine Equiv.of_eq ?_
      exact congrArg (· ::ₘ 0) Sym2.eq_swap

/-- The principal net `z`. -/
def zNet : PNet vsig 0 where
  internal := 0
  tree := zT
  port_count i := i.elim0
  internal_count w := w.elim0

/-- The principal net `e(z)`: an `e` cell whose auxiliary port holds a `z` cell. -/
def ezNet : PNet vsig 0 where
  internal := 0
  tree := eT zT
  port_count i := i.elim0
  internal_count w := w.elim0

/-- The translation: `z ↦ z`, `c ↦ e(z)`. It is strict and is not the identity. -/
def Φ : Translation usig vsig where
  net
    | .z => zNet
    | .c => ezNet

/-- `Φ` is strict (Lafont 1997, page 80). -/
theorem Φ_strict : Φ.Strict := by
  intro α x h
  cases α <;> cases h

/-- `z` has no name, so a substitution leaves it unchanged. -/
theorem zT_bind{ν μ : Type} (σ : ν → Term vsig μ) : (zT : Term vsig ν).bind σ = zT := by
  change Term.app vz _ = Term.app vz _
  congr 1
  funext i
  exact i.elim0

/-- The instance of `Φ(z)`: names play no role. -/
theorem inst_z (xs : Fin (usig.arity uz) → Term vsig ℕ) (f : Fin (Φ.net uz).internal → ℕ) :
    (Φ.net uz).inst xs f = zT :=
  zT_bind _

/-- The instance of `Φ(c)` is `e(z)`. -/
theorem inst_c (xs : Fin (usig.arity uc) → Term vsig ℕ) (f : Fin (Φ.net uc).internal → ℕ) :
    (Φ.net uc).inst xs f = eT zT := by
  change Term.app ve _ = Term.app ve _
  congr 1
  funext i
  exact zT_bind _

/-- `z = z` interacts and leaves the empty net. -/
theorem step_zz (Δ : Net vsig ℕ) : Step vsys (s(zT, zT) ::ₘ Δ) Δ := by
  have h := Step.mk (I := vsys) vz vz ⟨0, 0⟩ rfl Fin.elim0 Fin.elim0 Δ Fin.elim0
    (fun i => i.elim0) (fun i => i.elim0)
  simpa only [zero_add] using (show Step vsys (s(zT, zT) ::ₘ Δ) (0 + Δ) from h)

/-- `e(z) = e(z)` interacts and leaves `z = z`. -/
theorem step_ee : Step vsys (s(eT zT, eT zT) ::ₘ 0) (s(zT, zT) ::ₘ 0) := by
  have := Step.mk (I := vsys) ve ve ruleEE rfl (fun _ => zT) (fun _ => zT) 0 Fin.elim0
    (fun i => i.elim0) (fun i => i.elim0)
  rw [add_zero] at this
  exact this

/-- The translation of the empty net is the empty net. -/
theorem netTr_zero : Φ.NetTr 0 0 := ⟨Multiset.Rel.zero, fun _ => by simp⟩

/-- **`Φ` simulates `z z` in one interaction and `c c` in two**: `Φ` is compatible within `1`
and `2` (Lafont 1997, page 81). -/
theorem Φ_compatibleWithin : Φ.CompatibleWithin usys vsys 1 2 := by
  intro α β r hr xs ys f g hlin
  cases α <;> cases β <;> cases hr
  · refine ⟨0, 0, Fin.elim0, ⟨1, le_rfl, by omega, ?_⟩, Equiv.refl _, netTr_zero⟩
    rw [inst_z, inst_z]
    exact StepsEN.single (step_zz 0).stepE
  · refine ⟨0, 0, Fin.elim0, ⟨2, by omega, le_rfl, ?_⟩, Equiv.refl _, netTr_zero⟩
    rw [inst_c, inst_c]
    exact (StepsEN.single step_ee.stepE).tail (step_zz 0).stepE

/-- `Φ` is a translation of interaction systems (Lafont 1997, page 80). -/
theorem Φ_compatible : Φ.Compatible usys vsys := Φ_compatibleWithin.compatible

/-! ### Counting cells -/

/-- The cells of a `z` cell. -/
theorem cells_vz (as : Fin (vsig.arity vz) → Term vsig ℕ) : (Term.app vz as).cells = {vz} := by
  change vz ::ₘ ∑ i : Fin 0, (as i).cells = _
  simp

/-- The auxiliary port of `e`. -/
abbrev e0 : Fin (vsig.arity ve) := ⟨0, Nat.one_pos⟩

/-- The cells of an `e` cell with a tree on its auxiliary port. -/
theorem cells_ve (as : Fin (vsig.arity ve) → Term vsig ℕ) :
    (Term.app ve as).cells = ve ::ₘ (as e0).cells := by
  change ve ::ₘ ∑ i : Fin 1, (as i).cells = _
  rw [Fin.sum_univ_one]
  rfl

/-- The cells of `z`. -/
theorem cells_zT : (zT : Term vsig ℕ).cells = {vz} := cells_vz _

/-- The cells of `e(z)`. -/
theorem cells_ezT : (eT zT : Term vsig ℕ).cells = {ve, vz} := by
  rw [eT, cells_ve]
  exact congrArg (ve ::ₘ ·) cells_zT

/-- The cells of a sum of nets. -/
theorem cells_add (A B : Net vsig ℕ) : Net.cells (A + B) = A.cells + B.cells := by
  simp [Net.cells]

/-- **Every interaction of `vsys` removes two cells.** The rules `z z ↦ ∅` and `e e ↦ {x = y}`
replace the two cells by no cell, and the trees on the auxiliary ports are kept. Wire substitution
keeps the cells (`Equiv.cells_eq`). -/
theorem card_cells_stepE {N M : Net vsig ℕ} (h : StepE vsys N M) :
    Multiset.card (Net.cells N) = Multiset.card (Net.cells M) + 2 := by
  obtain ⟨N', hE, hs⟩ := h
  rw [hE.cells_eq]
  obtain ⟨α, β, r, hr, as, bs, Δ, f, -, -⟩ := hs
  cases α <;> cases β <;> cases hr
  · show Multiset.card (Net.cells (s(Term.app vz as, Term.app vz bs) ::ₘ Δ)) =
      Multiset.card (Net.cells (0 + Δ)) + 2
    rw [Net.cells_cons, eqCells_mk, cells_vz, cells_vz, zero_add]
    simp only [Multiset.card_add, Multiset.card_singleton]
    omega
  · show Multiset.card (Net.cells (s(Term.app ve as, Term.app ve bs) ::ₘ Δ)) =
      Multiset.card (Net.cells ((s(as e0, bs e0) ::ₘ 0) + Δ)) + 2
    rw [Net.cells_cons, eqCells_mk, cells_ve, cells_ve, cells_add, Net.cells_cons, eqCells_mk]
    simp only [Multiset.card_add, Multiset.card_cons]
    have : Multiset.card (Net.cells (0 : Net vsig ℕ)) = 0 := rfl
    omega

/-- The number of cells fixes the length of a reduction in `vsys`. -/
theorem card_cells_stepsEN {n : ℕ} {N M : Net vsig ℕ} (h : StepsEN vsys n N M) :
    Multiset.card (Net.cells N) = Multiset.card (Net.cells M) + 2 * n := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [ih, card_cells_stepE hs]; ring

/-- A net that is the same graph as a translation of the empty net has no cell. -/
theorem card_cells_of_netTr_zero {M N' : Net vsig ℕ} (hE : Equiv M N') (hT : Φ.NetTr 0 N') :
    Multiset.card (Net.cells M) = 0 := by
  have : N' = 0 := Multiset.rel_zero_left.1 hT.rel
  subst this
  rw [hE.cells_eq]
  rfl

/-- **The length of a reduction of `z = z`** to a translation of the right member is `1`. -/
theorem length_z {k : ℕ} {M N' : Net vsig ℕ}
    (h : StepsEN vsys k (s(zT, zT) ::ₘ 0) M) (hE : Equiv M N') (hT : Φ.NetTr 0 N') : k = 1 := by
  have := card_cells_stepsEN h
  rw [card_cells_of_netTr_zero hE hT, Net.cells_cons, eqCells_mk, cells_zT] at this
  simp only [Multiset.card_add, Multiset.card_singleton] at this
  have : Multiset.card (Net.cells (0 : Net vsig ℕ)) = 0 := rfl
  omega

/-- **The length of a reduction of `e(z) = e(z)`** to a translation of the right member is `2`. -/
theorem length_c {k : ℕ} {M N' : Net vsig ℕ}
    (h : StepsEN vsys k (s(eT zT, eT zT) ::ₘ 0) M) (hE : Equiv M N') (hT : Φ.NetTr 0 N') :
    k = 2 := by
  have := card_cells_stepsEN h
  rw [card_cells_of_netTr_zero hE hT, Net.cells_cons, eqCells_mk, cells_ezT] at this
  simp only [Multiset.card_add, Multiset.insert_eq_cons, Multiset.card_cons,
    Multiset.card_singleton] at this
  have : Multiset.card (Net.cells (0 : Net vsig ℕ)) = 0 := rfl
  omega

/-- `z` has no name. -/
theorem vars_zT : (zT : Term vsig ℕ).vars = 0 := by
  change (∑ i : Fin 0, _ : Multiset ℕ) = 0
  simp

/-- `e(z)` has no name. -/
theorem vars_ezT: (eT zT : Term vsig ℕ).vars = 0 := by
  change (∑ _i : Fin 1, (zT : Term vsig ℕ).vars) = 0
  simp [vars_zT]

/-- The pair `z = z` is linear. -/
theorem linear_z : Net.Linear (s(zT, zT) ::ₘ 0 : Net vsig ℕ) := by
  intro y
  simp [vars_zT]

/-- The pair `e(z) = e(z)` is linear. -/
theorem linear_c : Net.Linear (s(eT zT, eT zT) ::ₘ 0 : Net vsig ℕ) := by
  intro y
  simp [vars_ezT]

/-- The source symbols have no auxiliary port. -/
theorem noPort {α : usig.Sym} (i : Fin (usig.arity α)) : False := i.elim0

/-- The translated pair of `z z`, for any names: `z = z`. -/
theorem pair_z (xs ys : Fin (usig.arity uz) → ℕ) (f g : Fin (Φ.net uz).internal → ℕ) :
    ({s((Φ.net uz).inst (fun i => .var (xs i)) f, (Φ.net uz).inst (fun j => .var (ys j)) g)} :
      Net vsig ℕ) = s(zT, zT) ::ₘ 0 := by
  rw [inst_z, inst_z]
  rfl

/-- The translated pair of `c c`, for any names: `e(z) = e(z)`. -/
theorem pair_c (xs ys : Fin (usig.arity uc) → ℕ) (f g : Fin (Φ.net uc).internal → ℕ) :
    ({s((Φ.net uc).inst (fun i => .var (xs i)) f, (Φ.net uc).inst (fun j => .var (ys j)) g)} :
      Net vsig ℕ) = s(eT zT, eT zT) ::ₘ 0 := by
  rw [inst_c, inst_c]
  rfl

/-- **The bounds of `Φ` are exactly `L ≤ 1` and `2 ≤ M`** (Lafont 1997, page 81). `Φ` is
compatible within `L` and `M` if and only if `L ≤ 1 ≤ 2 ≤ M`: one rule needs one interaction,
the other two, and no other length is possible. -/
theorem compatibleWithin_iff (L M : ℕ) : Φ.CompatibleWithin usys vsys L M ↔ L ≤ 1 ∧ 2 ≤ M := by
  constructor
  · intro h
    obtain ⟨M₁, N₁, h₁, ⟨k₁, hL₁, hM₁, hk₁⟩, hE₁, hT₁⟩ :=
      h uz uz ⟨0, 0⟩ rfl (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
        (linear_z.cast (pair_z _ _ _ _).symm)
    obtain ⟨M₂, N₂, h₂, ⟨k₂, hL₂, hM₂, hk₂⟩, hE₂, hT₂⟩ :=
      h uc uc ⟨0, 0⟩ rfl (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
        (linear_c.cast (pair_c _ _ _ _).symm)
    rw [pair_z] at hk₁
    rw [pair_c] at hk₂
    have e₁ := length_z hk₁ hE₁ hT₁
    have e₂ := length_c hk₂ hE₂ hT₂
    omega
  · rintro ⟨hL, hM⟩ α β r hr xs ys f g hlin
    obtain ⟨M₁, N', h', ⟨k, hLk, hkM, hk⟩, hE, hT⟩ := Φ_compatibleWithin α β r hr xs ys f g hlin
    exact ⟨M₁, N', h', ⟨k, by omega, by omega, hk⟩, hE, hT⟩

/-- The length chosen by `Compatible.len` for `z z` is `1`. -/
theorem len_z : Φ_compatible.len (uz, uz) = 1 := by
  obtain ⟨M, N', h', hS, hE, hT⟩ := (Φ_compatible.exists_length uz uz).choose_spec
    ⟨0, 0⟩ rfl (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun i => (noPort i).elim)
    (fun i => (noPort i).elim) (fun i => (noPort i).elim) (linear_z.cast (pair_z _ _ _ _).symm)
  rw [pair_z] at hS
  exact length_z hS hE hT

/-- The length chosen by `Compatible.len` for `c c` is `2`. -/
theorem len_c : Φ_compatible.len (uc, uc) = 2 := by
  obtain ⟨M, N', h', hS, hE, hT⟩ := (Φ_compatible.exists_length uc uc).choose_spec
    ⟨0, 0⟩ rfl (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun i => (noPort i).elim)
    (fun i => (noPort i).elim) (fun i => (noPort i).elim) (linear_c.cast (pair_c _ _ _ _).symm)
  rw [pair_c] at hS
  exact length_c hS hE hT

/-- The lengths of the rules of `usys` are `1` and `2`. -/
theorem ruleLens_eq : ruleLens (I := usys) Φ_compatible.len = {1, 2} := by
  ext n
  simp only [ruleLens, Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨α, β⟩, hs, rfl⟩
    cases α <;> cases β <;> simp [usys] at hs
    · exact .inl len_z
    · exact .inr len_c
  · rintro (rfl | rfl)
    · exact ⟨(uz, uz), rfl, len_z⟩
    · exact ⟨(uc, uc), rfl, len_c⟩

/-- **`compatibleWithin_len` gives `L = 1`** for `Φ`: the minimal length of the rules (Lafont
1997, page 81). -/
theorem sInf_ruleLens : sInf (ruleLens (I := usys) Φ_compatible.len) = 1 := by
  rw [ruleLens_eq]
  apply le_antisymm (Nat.sInf_le (by simp))
  exact le_csInf ⟨1, by simp⟩ (by simp)

/-- **`compatibleWithin_len` gives `M = 2`** for `Φ`: the maximal length of the rules (Lafont
1997, page 81). So `L < M` here, and both bounds are optimal (`compatibleWithin_iff`). -/
theorem sSup_ruleLens : sSup (ruleLens (I := usys) Φ_compatible.len) = 2 := by
  rw [ruleLens_eq]
  apply le_antisymm (csSup_le ⟨1, by simp⟩ (by simp))
  exact le_csSup (Set.toFinite _).bddAbove (by simp)

/-- `compatibleWithin_len`, applied to `Φ`: it gives the bounds `1` and `2`. -/
example : Φ.CompatibleWithin usys vsys 1 2 := by
  have := Φ_compatible.compatibleWithin_len (Φ := Φ) usys_wellFormed vsys_wellFormed.linear
  rwa [sInf_ruleLens, sSup_ruleLens] at this

end INet.SimulationUniformReview
