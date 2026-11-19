import InteractionCombinators.Lafont.CodeTr

/-!
# Renaming the pieces of Fig. 10, and the cell `[β]` it extracts (pages 89–90)

Lafont 1997, Fig. 10 (journal page 89, PDF page 21) and the text of page 90.

The extraction of page 90 (`codeCell_code_codeMenus`) leaves, at a cell `⟨β⟩`, the tree of `[β]`
with a copy of the menu `Γ_β` and a copy of `!Γ`, renamed by some functions `g` and `g'`. The copy
of `!Γ` comes from another cell, whose names start elsewhere. This file shows that the result is an
instance of the principal net `[β]` of `codeTranslation` (`CodeTr.lean`), so that the
translation relation `TermTr` holds.

* `codeTerm_shift`, `codeExtras_shift`, `codeGamma_shift`, `menu_codeCellMenu_shift`,
  `menu_codeMenus_shift` — the pieces of Fig. 10 numbered from `k₀` are those numbered from
  `k₀'`, renamed by any `g` with `g (k₀ + i) = k₀' + i`.
* `treePNet_inst_bind` — an instance of `treePNet` is the tree with the ports plugged and the other
  names renamed.
* `codeNet_inst_eq` — the tree left by the extraction is an instance of `[β]`.
-/

namespace INet.Comb

open Term Translation

variable {S : Signature} {a k : ℕ}

/-! ## Shifting the pieces of Fig. 10 -/

/-- Renaming goes through the tree on the extra port of `⟨α_i⟩` (page 89). -/
theorem bind_codeExtra (g : ℕ → ℕ) (m i y u k₀ : ℕ) (hg : g (k₀ + 1) = g k₀ + 1) :
    (codeExtra m i y u k₀).bind (fun x => var (g x)) = codeExtra m i (g y) (g u) (g k₀) := by
  simp [codeExtra, copier, bind_autoMux, bind_muxStar, selector_eq_cellSel, bind_cellSel, hg]

variable (m : ℕ) (idx : S.Sym → ℕ)

/-- **Shifting `⟨t⟩`** (Fig. 10, page 89): renaming `⟨t⟩`, numbered from `b`, by a `g` that sends
`b + i` to `b' + i` gives `⟨t⟩` of the renamed tree, numbered from `b'`. -/
theorem codeTerm_shift (g : ℕ → ℕ) (t : Term S ℕ) :
    ∀ (b b' : ℕ), (∀ i, g (b + i) = b' + i) →
      (codeTerm m idx b t).bind (fun x => var (g x)) =
        codeTerm m idx b' (t.bind fun x => var (g x)) := by
  induction t with
  | var x => intro b b' _; rfl
  | app α ts ih =>
    intro b b' hg
    have h0 : g b = b' := by simpa using hg 0
    rw [codeTerm, bind_cellSkel, bind_app, codeTerm]
    simp only [bind_var, List.map_cons, List.map_ofFn, Function.comp_def, codeSize_bind_var, h0,
      hg 1, hg 2]
    congr 2
    exact List.ofFn_inj.2 (funext fun i =>
      ih i _ _ fun j => by rw [add_assoc, add_assoc, hg, add_assoc, add_assoc])

/-- **Shifting the trees on the extra ports of `⟨t⟩`** (Fig. 10, page 89). -/
theorem codeExtras_shift (g : ℕ → ℕ) (t : Term S ℕ) :
    ∀ (b b' : ℕ), (∀ i, g (b + i) = b' + i) →
      (codeExtras m idx b t).map (·.bind fun x => var (g x)) =
        codeExtras m idx b' (t.bind fun x => var (g x)) := by
  induction t with
  | var x => intro b b' _; rfl
  | app α ts ih =>
    intro b b' hg
    rw [codeExtras, bind_app, codeExtras, List.map_cons, bind_codeExtra _ _ _ _ _ _
      (by rw [hg 3, show b + 3 + 1 = b + 4 by omega, hg 4]), hg 1, hg 2, hg 3, List.map_flatten,
      List.map_ofFn]
    simp only [Function.comp_def, codeSize_bind_var]
    congr 2
    exact List.ofFn_inj.2 (funext fun i =>
      ih i _ _ fun j => by rw [add_assoc, add_assoc, hg, add_assoc, add_assoc])

/-- **Shifting `Γ_{i,j}`** (Fig. 10, page 89): the package numbered from `k₀`, renamed by a `g`
that sends `k₀ + i` to `k₀' + i`, is the package numbered from `k₀'`. -/
theorem codeGamma_shift (φ : Rule S a k) (σ : Equiv.Perm (Fin k)) (hσ : Function.Involutive σ)
    (g : ℕ → ℕ) (k₀ k₀' : ℕ) (hg : ∀ i, g (k₀ + i) = k₀' + i) :
    (codeGamma m idx φ σ hσ k₀).bind (fun x => var (g x)) = codeGamma m idx φ σ hσ k₀' := by
  have hb : ∀ p i, g (codeBase φ k₀ p + i) = codeBase φ k₀' p + i := fun p i => by
    simp only [codeBase, add_assoc]; exact hg _
  have hp : ∀ p, (codePort m idx φ k₀ p).bind (fun x => var (g x)) = codePort m idx φ k₀' p :=
    fun p => by
      rw [codePort, codeTerm_shift m idx g _ _ _ (hb p), gammaTree_shift φ g k₀ k₀' hg]; rfl
  have hx : ∀ p, (codePortExtras m idx φ k₀ p).map (·.bind fun x => var (g x)) =
      codePortExtras m idx φ k₀' p := fun p => by
    rw [codePortExtras, codeExtras_shift m idx g _ _ _ (hb p), gammaTree_shift φ g k₀ k₀' hg]; rfl
  rw [codeGamma, bind_muxStar, List.map_cons, copier, bind_autoMux, codeGammaExtras,
    List.map_flatten, List.map_ofFn, List.map_append, List.map_ofFn, List.map_cons, List.map_nil,
    bind_transpositorPerm]
  simp only [Function.comp_def, hp, hx]
  rfl

/-- Shifting `codeGammaOpt` (page 89). -/
theorem codeGammaOpt_shift (o : Option (ExpSide S a)) (g : ℕ → ℕ) (k₀ k₀' : ℕ)
    (hg : ∀ i, g (k₀ + i) = k₀' + i) :
    (codeGammaOpt m idx o k₀).bind (fun x => var (g x)) = codeGammaOpt m idx o k₀' := by
  cases o with
  | none => simp [codeGammaOpt]
  | some s => exact codeGamma_shift m idx s.φ s.σ s.involutive g k₀ k₀' hg

variable [Finite S.Sym] (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **Shifting the menu `Γ_β`** (Fig. 10, page 89). -/
theorem menu_codeCellMenu_shift (β : S.Sym) (g : ℕ → ℕ) (k₀ k₀' : ℕ)
    (hg : ∀ i, g (k₀ + i) = k₀' + i) :
    (menu (codeCellMenu side β k₀)).bind (fun x => var (g x)) = menu (codeCellMenu side β k₀') := by
  rw [menu, bind_mux, codeCellMenu_eq, codeCellMenu_eq, List.map_ofFn, menu]
  congr 2
  funext j
  exact codeGammaOpt_shift _ _ _ g _ _ fun i => by rw [add_assoc, hg, add_assoc]

/-- **Shifting the menu `Γ = Γ_0 & ⋯ & Γ_{m-1}`** (Fig. 10, page 89). -/
theorem menu_codeMenus_shift (g : ℕ → ℕ) (k₀ k₀' : ℕ) (hg : ∀ i, g (k₀ + i) = k₀' + i) :
    (menu (codeMenus side k₀)).bind (fun x => var (g x)) = menu (codeMenus side k₀') := by
  rw [menu, bind_mux, codeMenus_eq, codeMenus_eq, List.map_ofFn, menu]
  congr 2
  funext i
  exact menu_codeCellMenu_shift side _ g _ _ fun j => by rw [add_assoc, hg, add_assoc]

/-! ## The tree left by the extraction is an instance of `[β]` -/

/-- **An instance of `treePNet`** (page 80): with the tree `args i` on the port `i` and the internal
wire of name `x` named `h x`, the instance is `t` with each port `i < n` replaced by `args i` and
every other name `x` by `h x`. -/
theorem treePNet_inst_bind (n : ℕ) (t : Term sig ℕ) (hp : ∀ i < n, t.vars.count i = 1)
    (hw : ∀ x ∈ t.vars, n ≤ x → t.vars.count x = 2) (args : Fin n → Term sig ℕ) (h : ℕ → ℕ) :
    (treePNet n t hp hw).inst args (fun w => h ((wireNum n t).symm w).1) =
      t.bind fun x => if hx : x < n then args ⟨x, hx⟩ else var (h x) := by
  show (t.bind (treeLeaf n t)).bind (Sum.elim args
    fun w : Fin (wireSet n t).card => var (h ((wireNum n t).symm w).1)) = _
  rw [Term.bind_bind]
  refine Term.bind_congr fun x hx => ?_
  unfold treeLeaf
  by_cases h1 : x < n
  · simp [h1]
  · have h2 : x ∈ wireSet n t :=
      Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hx, not_lt.1 h1⟩
    simp [h1, h2]

/-- Plugging trees into the names of the cell `[αᵢ]` of Fig. 6 (page 86), when the loop is renamed
to a name. -/
theorem bind_cellSkel_of (f : ℕ → Term sig ℕ) (Γ : Term sig ℕ) (m i : ℕ) (ts : List (Term sig ℕ))
    (ℓ ℓ' : ℕ) (hℓ : f ℓ = var ℓ') :
    (cellSkel Γ m i ts ℓ).bind f = cellSkel (Γ.bind f) m i (ts.map (·.bind f)) ℓ' := by
  simp [cellSkel, bind_transpositor, bind_cellSel, bind_mux, hℓ]

/-- **The extracted tree is an instance of `[β]`** (Fig. 10, pages 89–90). The tree of `[β]` with
a copy of the menu `Γ_β` (numbered from any `B`, renamed by `g`), a copy of the code `!Γ` of
`Γ = codeMenus side k₀` (cut names from `K`, renamed by `g'`), the trees `args` on the ports and the
loop `ℓ` is the principal net `[β]` of `codeTranslation side` with `args` on its ports and its
internal wires named by some `F`. -/
theorem codeNet_inst_eq (β : S.Sym) (B k₀ K : ℕ)
    (g g' : ℕ → ℕ) (ℓ : ℕ) (args : Fin (S.arity β) → Term sig ℕ) :
    ∃ F, (codeNet side β).inst args F =
      cellSkel ((menu (codeCellMenu side β B)).bind fun x => var (g x)) (Nat.card S.Sym)
        (symEnum S β) (((code K (menu (codeMenus side k₀))).bind fun x => var (g' x)) ::
          List.ofFn args) ℓ := by
  set MB := codeMenuBase side β
  set KB := codeKey side β
  -- the shift of the menu `Γ_β` from `S.arity β + 1` to `B`, and that of `Γ` from `MB` to `k₀`
  set s₁ : ℕ → ℕ := fun x => B + (x - (S.arity β + 1))
  set s₂ : ℕ → ℕ := fun x => k₀ + (x - MB)
  set ρ : ℕ → ℕ := fun x => if x < KB then s₂ x else K + (x - KB)
  set h : ℕ → ℕ := fun x => if x = S.arity β then ℓ else if x < MB then g (s₁ x) else g' (ρ x)
  refine ⟨fun w => h ((wireNum (S.arity β) (codeTree side β)).symm w).1, ?_⟩
  have hMB : S.arity β + 1 ≤ MB := Nat.le_add_right _ _
  have hKB : MB ≤ KB := Nat.le_add_right _ _
  have hΓv : ∀ x ∈ (menu (codeCellMenu side β (S.arity β + 1))).vars, S.arity β + 1 ≤ x ∧ x < MB := fun x hx => by
    rw [vars_menu_codeCellMenu, Multiset.mem_nsmul_of_ne_zero (by omega), Multiset.mem_Ico] at hx
    exact hx
  have hGv : ∀ x ∈ (menu (codeMenus side MB)).vars, MB ≤ x ∧ x < KB := fun x hx => by
    rw [vars_menu_codeMenus, Multiset.mem_nsmul_of_ne_zero (by omega), Multiset.mem_Ico] at hx
    exact hx
  have hCv : ∀ x ∈ (code KB (menu (codeMenus side MB))).vars, MB ≤ x := fun x hx => by
    rw [vars_code] at hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · rcases Multiset.mem_add.1 hx with hx | hx
      · exact (hGv x hx).1
      · exact hKB.trans ((decomp_ports _ KB).2.1 x hx).1
    · exact hKB.trans ((decomp_ports _ KB).2.1 x hx).1
  -- the menu `Γ_β`
  have eΓ : (menu (codeCellMenu side β (S.arity β + 1))).bind (fun x => var (h x)) =
      (menu (codeCellMenu side β B)).bind fun x => var (g x) := by
    rw [← menu_codeCellMenu_shift side β s₁ (S.arity β + 1) B (fun i => by simp [s₁]), Term.bind_bind]
    refine Term.bind_congr fun x hx => ?_
    obtain ⟨h1, h2⟩ := hΓv x hx
    simp [h, show x ≠ S.arity β by omega, h2]
  -- the code `!Γ`
  have eC : (code KB (menu (codeMenus side MB))).bind (fun x => var (h x)) =
      (code K (menu (codeMenus side k₀))).bind fun x => var (g' x) := by
    have eρ : (menu (codeMenus side MB)).bind (fun x => var (s₂ x)) =
        (menu (codeMenus side MB)).bind (fun x => var (ρ x)) :=
      Term.bind_congr fun x hx => by simp [ρ, (hGv x hx).2]
    rw [← menu_codeMenus_shift side s₂ MB k₀ (fun i => by simp [s₂]), eρ,
      code_bind_var _ ρ KB K (fun i => by simp [ρ]), Term.bind_bind]
    refine Term.bind_congr fun x hx => ?_
    have := hCv x hx
    simp [h, show x ≠ S.arity β by omega, show ¬ x < MB by omega]
  refine (treePNet_inst_bind _ (codeTree side β) _ _ args h).trans ?_
  rw [codeTree_eq, bind_cellSkel_of _ _ _ _ _ _ ℓ (by simp [h])]
  have hΓ : (menu (codeCellMenu side β (S.arity β + 1))).bind
      (fun x => if hx : x < S.arity β then args ⟨x, hx⟩ else var (h x)) =
      (menu (codeCellMenu side β (S.arity β + 1))).bind (fun x => var (h x)) :=
    Term.bind_congr fun x hx => by simp [show ¬ x < S.arity β by have := (hΓv x hx).1; omega]
  have hC : (code KB (menu (codeMenus side MB))).bind
      (fun x => if hx : x < S.arity β then args ⟨x, hx⟩ else var (h x)) =
      (code KB (menu (codeMenus side MB))).bind (fun x => var (h x)) :=
    Term.bind_congr fun x hx => by simp [show ¬ x < S.arity β by have := hCv x hx; omega]
  have hA : (fun j : Fin (S.arity β) => (var (j : ℕ) : Term sig ℕ).bind
      (fun x => if hx : x < S.arity β then args ⟨x, hx⟩ else var (h x))) = args :=
    funext fun j => by simp [j.isLt]
  simp only [List.map_cons, List.map_ofFn, Function.comp_def, hΓ, eΓ, hA]
  exact congrArg (fun c => cellSkel _ _ _ (c :: List.ofFn args) ℓ) (hC.trans eC)

end INet.Comb
