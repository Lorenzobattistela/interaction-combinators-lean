import InteractionCombinators.Lafont.CodeGammaExtract
import Checks.CodeTermExtractCheck
import Checks.CodeGammaCheck

/-!
# Checks for `codeGamma_extract` (Fig. 10, pages 89–90)

* `vars_codeGamma_parts` — the names of the trees on the extra ports and of the trees at the ports
  of `⟨φ⟩` are both ends of each name of `[k₀, k₀ + codeGammaSize φ)`.
* `codeGamma_extract_hyps` — the hypothesis of `codeGamma_extract` holds for a linear side in
  expanded form, the partners `P q` fresh wires above `Γ_{i,j}` and the copy of `!Γ` renamed into
  a block above those wires.
* `gamma_extract_conDup` — the rule `con`–`dup` of the interaction combinators (four cells), read as a
  side, with no rule for the menus (`sideNone`): `C_4` against `!Γ` and the four trees `⟨φ⟩`
  reduce to translations of the four trees of the side.
-/

namespace INet.Comb.CodeGammaExtractCheck

open Term Translation CodeTermExtractCheck

variable {S : Signature} {a k : ℕ} (m : ℕ) (idx : S.Sym → ℕ)

/-- **The names of the parts of `Γ_{i,j}`** (Fig. 10, page 89): for a linear side in expanded
form, the trees on the extra ports of `⟨φ⟩` and the trees of `⟨φ⟩` at its ports use both ends of
each name of `[k₀, k₀ + codeGammaSize φ)`. -/
theorem vars_codeGamma_parts {φ : Rule S a k} (he : φ.Expanded) (hl : φ.Linear) (k₀ : ℕ) :
    ((codeGammaExtras m idx φ k₀).map Term.vars).sum + ∑ p, (codePort m idx φ k₀ p).vars =
      2 • Multiset.Ico k₀ (k₀ + codeGammaSize φ) := by
  set s := codeSizes φ
  set B := k₀ + φ.internal
  have hport : ∀ p, (codePort m idx φ k₀ p).vars +
      ((codePortExtras m idx φ k₀ p).map Term.vars).sum = (gammaTree φ k₀ p).vars +
      2 • Multiset.Ico (B + off s (finSumFinEquiv p))
        (B + off s (finSumFinEquiv p) + s (finSumFinEquiv p)) := fun p => by
    rw [codePort, codePortExtras, vars_codeTerm_add, gammaTree, Rule.portTreeC_eq_portTree he hl,
      codeSize_bind_var]
    simp [s, codeSizes, codeBase, B]
  rw [codeGammaExtras, sum_vars_flatten_ofFn,
    Equiv.sum_comp finSumFinEquiv.symm (fun p => ((codePortExtras m idx φ k₀ p).map
      Term.vars).sum), add_comm, ← Finset.sum_add_distrib]
  simp only [hport]
  rw [Finset.sum_add_distrib, sum_vars_gammaTree he hl,
    Equiv.sum_comp finSumFinEquiv (fun q => 2 • Multiset.Ico (B + off s q) (B + off s q + s q)),
    ← Finset.smul_sum, sum_Ico_off, ← nsmul_add, codeGammaSize,
    Multiset.Ico_add_Ico_eq_Ico (by omega) (by omega), add_assoc]

/-- **The hypothesis of `codeGamma_extract` can be met** (Fig. 10, pages 89–90): for a linear side
`φ` in expanded form, with `N₀ = k₀ + codeGammaSize φ` above the names of `Γ_{i,j}`, the partner
of the port `q` the fresh wire `N₀ + q` (ports numbered by `finSumFinEquiv`), and the package `C`
(for instance `!Γ`) renamed by `x ↦ N₀ + (a + k) + x`, the net is linear, and the renaming is
injective. -/
theorem codeGamma_extract_hyps {φ : Rule S a k} (he : φ.Expanded) (hl : φ.Linear) (k₀ : ℕ)
    (C : Term sig ℕ) (hC : C.IsPackage) :
    Set.InjOn (fun x => k₀ + codeGammaSize φ + (a + k) + x) {x | x ∈ C.vars} ∧
    Net.Linear (s(copier (codeGammaExtras m idx φ k₀),
      C.bind fun x => var (k₀ + codeGammaSize φ + (a + k) + x)) ::ₘ
      ((∑ q, {s(var (k₀ + codeGammaSize φ + (finSumFinEquiv q : ℕ)), codePort m idx φ k₀ q)}) +
        0)) := by
  set N₀ := k₀ + codeGammaSize φ
  refine ⟨fun x _ x' _ h => by simpa using h, fun y => ?_⟩
  set Zs : Multiset ℕ := ∑ q : Fin a ⊕ Fin k, ({N₀ + (finSumFinEquiv q : ℕ)} : Multiset ℕ)
  have hvP : Net.vars (∑ q : Fin a ⊕ Fin k,
      ({s(var (N₀ + (finSumFinEquiv q : ℕ)), codePort m idx φ k₀ q)} : CNet)) =
      Zs + ∑ p, (codePort m idx φ k₀ p).vars := by
    have h := map_sum (⟨⟨Net.vars, by simp [Net.vars]⟩, Net.vars_add⟩ : CNet →+ Multiset ℕ)
      (fun q : Fin a ⊕ Fin k =>
        ({s(var (N₀ + (finSumFinEquiv q : ℕ)), codePort m idx φ k₀ q)} : CNet)) Finset.univ
    refine h.trans ?_
    show ∑ q : Fin a ⊕ Fin k, Net.vars
      ({s(var (N₀ + (finSumFinEquiv q : ℕ)), codePort m idx φ k₀ q)} : CNet) = _
    simp only [Net.vars_singleton, eqVars_mk, vars_var, Finset.sum_add_distrib, Zs]
  have hv : Net.vars (s(copier (codeGammaExtras m idx φ k₀),
      C.bind fun x => var (N₀ + (a + k) + x)) ::ₘ
      ((∑ q, {s(var (N₀ + (finSumFinEquiv q : ℕ)), codePort m idx φ k₀ q)}) + 0)) =
      2 • Multiset.Ico k₀ N₀ + Zs + C.vars.map fun x => N₀ + (a + k) + x := by
    rw [add_zero, Net.vars_cons, eqVars_mk, copier, vars_autoMux, vars_bind_var, hvP, ← vars_codeGamma_parts m idx he hl]
    abel
  rw [hv, Multiset.count_add, Multiset.count_add, Multiset.count_nsmul, count_map_add]
  have hZs : Zs = Finset.univ.val.map fun q : Fin a ⊕ Fin k => N₀ + (finSumFinEquiv q : ℕ) := by
    simp only [Zs, Finset.sum_eq_multiset_sum]
    rw [show (fun q : Fin a ⊕ Fin k => ({N₀ + (finSumFinEquiv q : ℕ)} : Multiset ℕ)) =
      (fun x => {x}) ∘ (fun q => N₀ + (finSumFinEquiv q : ℕ)) from rfl, ← Multiset.map_map,
      Multiset.sum_map_singleton]
  have hZ1 : Zs.count y ≤ 1 := by
    refine Multiset.nodup_iff_count_le_one.1 ?_ y
    rw [hZs]
    refine (Multiset.nodup_map_iff_of_injective fun q q' h => ?_).2 Finset.univ.nodup
    exact finSumFinEquiv.injective (Fin.ext (by simpa using h))
  have hZ0 : ¬ (N₀ ≤ y ∧ y < N₀ + (a + k)) → Zs.count y = 0 := fun hy => by
    refine Multiset.count_eq_zero.2 fun hm => hy ?_
    rw [hZs] at hm
    obtain ⟨q, -, rfl⟩ := Multiset.mem_map.1 hm
    exact ⟨by omega, by have := (finSumFinEquiv q).isLt; omega⟩
  have hI : (Multiset.Ico k₀ N₀).count y ≤ 1 :=
    Multiset.nodup_iff_count_le_one.1 Multiset.nodup_Ico y
  have hI0 : N₀ ≤ y → (Multiset.Ico k₀ N₀).count y = 0 := fun hy =>
    Multiset.count_eq_zero.2 fun hm => by rw [Multiset.mem_Ico] at hm; omega
  have hC2 : ∀ x, C.vars.count x ≤ 2 := fun x => by
    by_cases hx : x ∈ C.vars
    · exact (hC x hx).le
    · rw [Multiset.count_eq_zero.2 hx]; omega
  split_ifs with hy
  · rw [hI0 (by omega), hZ0 (by omega)]
    have := hC2 (y - (N₀ + (a + k)))
    omega
  · by_cases hy' : N₀ ≤ y
    · rw [hI0 hy']; omega
    · rw [hZ0 (by omega)]; omega

/-! ## The rule `con`–`dup`, four cells -/

/-- **`C_4` against `!Γ` and the four trees `⟨φ⟩` of the rule `con`–`dup`** (Fig. 10, pages 89–90):
the rule `con`–`dup` of the interaction combinators, read as a side with four cells (`k₀ = 0`, so
`Γ_{i,j}` uses the names `[0, 24)`), its four ports facing the fresh wires `24`, …, `27`, and the
copy of `!Γ` (with no rule for the menus, `sideNone`) renamed above `28`. The hypothesis of
`codeGamma_extract` holds (`codeGamma_extract_hyps`), so the net reduces to the four equations
`24 + q = t' q`, each `t' q` a translation of the tree of the side at the port `q`. -/
theorem gamma_extract_conDup :
    Multiset.card ruleConDup.net.cells = 4 ∧
    ∃ (M : CNet) (t' : Fin 2 ⊕ Fin 2 → Term sig ℕ),
      StepsE system (s(copier (codeGammaExtras (Nat.card sig.Sym) (fun α => symEnum sig α)
          ruleConDup 0),
        (code (0 + ∑ i, codeMenuSizes sideNone i) (menu (codeMenus sideNone 0))).bind
          fun x => var (28 + x)) ::ₘ
        ((∑ q, {s(var (24 + (finSumFinEquiv q : ℕ)),
          codePort (Nat.card sig.Sym) (fun α => symEnum sig α) ruleConDup 0 q)}) + 0)) M ∧
      Equiv M ((∑ q, {s(var (24 + (finSumFinEquiv q : ℕ)), t' q)}) + 0) ∧
      ∀ q, (codeTranslation sideNone).TermTr (gammaTree ruleConDup 0 q) (t' q) := by
  refine ⟨CodeGammaCheck.card_cells_conDup, ?_⟩
  set K := 0 + ∑ i, codeMenuSizes sideNone i
  have hb : (menu (codeMenus sideNone 0)).Below K := menu_codeMenus_below sideNone 0
  have hC : (code K (menu (codeMenus sideNone 0))).IsPackage :=
    code_isPackage K _ (menu_codeMenus_isPackage sideNone 0) hb
  obtain ⟨hinj, hlin⟩ := codeGamma_extract_hyps (Nat.card sig.Sym) (fun α => symEnum sig α)
    ExpandTrReview.ruleConDup_expanded ruleConDup_linear 0 _ hC
  have e : (0 : ℕ) + codeGammaSize ruleConDup = 24 := by
    rw [CodeGammaCheck.codeGammaSize_conDup]
  simp only [e, show (24 : ℕ) + (2 + 2) = 28 from rfl] at hinj hlin
  exact codeGamma_extract sideNone ruleConDup 0 0 K le_rfl _ hinj _ 0 hlin

end INet.Comb.CodeGammaExtractCheck
