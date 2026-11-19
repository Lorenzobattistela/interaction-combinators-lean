import InteractionCombinators.Universality.General.CodeTermExtract

/-!
# Checks for `codeTerm_extract` (Fig. 10, page 90)

The hypotheses of `codeTerm_extract` can be met, for every choice `side` of expanded sides and
every tree whose names are distinct:

* `vars_codeCopies`, `count_map_add`, `code_below` — the names of the copies of `!Γ`.
* `codeTerm_extract_hyps` — with a fresh name `p` on the principal port and the copies of a package
  `C` shifted to disjoint blocks of names above everything else, the net of `codeTerm_extract` is
  linear, and each renaming is injective.
* `codeTerm_extract_of_nodup` — so `codeTerm_extract` applies to every such tree, for every `side`.
* `extract_conDup` — the tree `con(dup(0, 1), 2)` of the interaction combinators (two cells),
  with no rule (`sideNone`): `⟨t⟩` with its two copies of `!Γ` reduces to a translation of `t`.
-/

namespace INet.Comb.CodeTermExtractCheck

open Term Translation

/-! ## The names of the copies -/

/-- The names of the copies `e = C_f` (page 89): those of the trees `e`, and the images of the
names of `C` by each `f`. -/
theorem vars_codeCopies (C : Term sig ℕ) :
    ∀ (es : List (Term sig ℕ)) (fs : List (ℕ → ℕ)), fs.length = es.length →
      Net.vars (codeCopies C es fs) = (es.map Term.vars).sum + (fs.map fun f => C.vars.map f).sum
  | [], [], _ => by simp [codeCopies]
  | e :: es, f :: fs, h => by
    rw [codeCopies_cons, Net.vars_cons, eqVars_mk, vars_codeCopies C es fs (by simpa using h),
      vars_bind_var]
    simp only [List.map_cons, List.sum_cons]
    abel
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- A shifted multiset of names. -/
theorem count_map_add (c y : ℕ) (M : Multiset ℕ) :
    (M.map fun x => c + x).count y = if c ≤ y then M.count (y - c) else 0 := by
  split_ifs with h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left]
    exact Multiset.count_map_eq_count' _ _ (fun a b hab => by simpa using hab) d
  · refine Multiset.count_eq_zero.2 fun hm => ?_
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 hm
    omega

/-- The names of the code `!Γ` (page 88) are below the next unused name of its decomposition. -/
theorem code_below (K : ℕ) (Γ : Term sig ℕ) (hΓ : Γ.Below K) :
    (code K Γ).Below (decomp K Γ).k := by
  obtain ⟨-, hr, hk⟩ := decomp_ports Γ K
  intro x hx
  rw [vars_code] at hx
  rcases Multiset.mem_add.1 hx with hx | hx
  · rcases Multiset.mem_add.1 hx with hx | hx
    · exact (hΓ x hx).trans_le hk
    · exact (hr x hx).2
  · exact (hr x hx).2

/-! ## The hypotheses can be met -/

variable {S : Signature}

/-- **The hypotheses of `codeTerm_extract` hold** for a tree `t` whose names are distinct, with a
fresh name `p` on the principal port, `b` above `p` and the names of `t`, and the `j`-th copy of the
package `C` shifted by `W * (j + 1)`, where `W` is above the new names of `⟨t⟩` and the names
of `C`. -/
theorem codeTerm_extract_hyps (m : ℕ) (idx : S.Sym → ℕ) (C : Term sig ℕ) (hC : C.IsPackage)
    (W : ℕ) (hCW : C.Below W) (t : Term S ℕ) (b p : ℕ) (hnd : (p ::ₘ t.vars).Nodup)
    (hb : ∀ x ∈ p ::ₘ t.vars, x < b) (hW : b + codeSize t ≤ W) :
    (List.ofFn fun j : Fin (codeExtras m idx b t).length => fun x => W * (j + 1) + x).length =
        (codeExtras m idx b t).length ∧
      (∀ f ∈ List.ofFn (fun j : Fin (codeExtras m idx b t).length => fun x => W * (j + 1) + x),
        Set.InjOn f {x | x ∈ C.vars}) ∧
      Net.Linear (s(var p, codeTerm m idx b t) ::ₘ (codeCopies C (codeExtras m idx b t)
        (List.ofFn fun j : Fin (codeExtras m idx b t).length => fun x => W * (j + 1) + x) + 0)) := by
  set n := (codeExtras m idx b t).length
  set F : Fin n → ℕ → ℕ := fun j x => W * (j + 1) + x
  refine ⟨List.length_ofFn, fun f hf => ?_, fun y => ?_⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hf
    intro x _ x' _ h
    simpa [F] using h
  have hpb : p < b := hb p (Multiset.mem_cons_self _ _)
  have hW0 : 0 < W := by omega
  -- the names of the net
  have hv : Net.vars (s(var p, codeTerm m idx b t) ::ₘ (codeCopies C (codeExtras m idx b t)
      (List.ofFn F) + 0)) = (p ::ₘ t.vars) + 2 • Multiset.Ico b (b + codeSize t) +
        ∑ j, C.vars.map (F j) := by
    rw [add_zero, Net.vars_cons, eqVars_mk, vars_var, vars_codeCopies C _ _ List.length_ofFn,
      List.map_ofFn, List.sum_ofFn, ← Multiset.singleton_add]
    simp only [Function.comp_def]
    have h := vars_codeTerm_add m idx b t
    calc _ = {p} + ((codeTerm m idx b t).vars + ((codeExtras m idx b t).map Term.vars).sum) +
          ∑ j, C.vars.map (F j) := by abel
      _ = _ := by rw [h]; abel
  rw [hv, Multiset.count_add, Multiset.count_add, Multiset.count_nsmul, Multiset.count_sum']
  have hC2 : ∀ x, C.vars.count x ≤ 2 := fun x => by
    by_cases hx : x ∈ C.vars
    · exact (hC x hx).le
    · rw [Multiset.count_eq_zero.2 hx]; omega
  have h1 : (p ::ₘ t.vars).count y ≤ 1 := Multiset.nodup_iff_count_le_one.1 hnd y
  have hI : (Multiset.Ico b (b + codeSize t)).count y ≤ 1 :=
    Multiset.nodup_iff_count_le_one.1 Multiset.nodup_Ico y
  by_cases hy : y < W
  · -- below `W`: no copy
    have h0 : ∑ j : Fin n, (C.vars.map (F j)).count y = 0 := Finset.sum_eq_zero fun j _ => by
      have : W ≤ W * (j + 1) := Nat.le_mul_of_pos_right W (Nat.succ_pos _)
      rw [count_map_add]
      split_ifs <;> omega
    rw [h0]
    by_cases hyb : b ≤ y
    · have : (p ::ₘ t.vars).count y = 0 :=
        Multiset.count_eq_zero.2 fun hm => by have := hb y hm; omega
      omega
    · have : (Multiset.Ico b (b + codeSize t)).count y = 0 :=
        Multiset.count_eq_zero.2 fun hm => by rw [Multiset.mem_Ico] at hm; omega
      omega
  · -- above `W`: at most one copy, a package
    have h0 : (p ::ₘ t.vars).count y = 0 :=
      Multiset.count_eq_zero.2 fun hm => by have := hb y hm; omega
    have h0' : (Multiset.Ico b (b + codeSize t)).count y = 0 :=
      Multiset.count_eq_zero.2 fun hm => by rw [Multiset.mem_Ico] at hm; omega
    rw [h0, h0']
    have hblock : ∀ j : Fin n, (C.vars.map (F j)).count y ≠ 0 → y / W = j + 1 := fun j hj => by
      rw [count_map_add] at hj
      split_ifs at hj with hle
      · have hm : y - W * (j + 1) ∈ C.vars := Multiset.count_ne_zero.1 hj
        have := hCW _ hm
        refine Nat.div_eq_of_lt_le (by rw [mul_comm]; exact hle) ?_
        rw [mul_comm, Nat.mul_succ]
        omega
      · exact absurd rfl hj
    by_cases hex : ∃ j : Fin n, (C.vars.map (F j)).count y ≠ 0
    · obtain ⟨j₀, hj₀⟩ := hex
      rw [Finset.sum_eq_single j₀ (fun j _ hj => by
        by_contra hne
        exact hj (Fin.ext (by have := hblock j hne; have := hblock j₀ hj₀; omega)))
        (by simp)]
      rw [count_map_add]
      split_ifs
      · have := hC2 (y - W * (j₀ + 1)); omega
      · omega
    · simp only [not_exists, not_not] at hex
      rw [Finset.sum_eq_zero fun j _ => hex j]
      omega

variable [Finite S.Sym] (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **`codeTerm_extract` applies to every tree whose names are distinct** (Fig. 10, page 90), for
every choice `side` of expanded sides: with `!Γ` numbered from the end of `Γ`, a fresh name `p` on
the principal port and the copies of `!Γ` on disjoint blocks of names, `⟨t⟩` reduces to a
translation of `t`. -/
theorem codeTerm_extract_of_nodup (k₀ : ℕ) (t : Term S ℕ) (b p : ℕ)
    (hnd : (p ::ₘ t.vars).Nodup) (hb : ∀ x ∈ p ::ₘ t.vars, x < b) :
    ∃ (K : ℕ) (fs : List (ℕ → ℕ)) (M : CNet) (t' : Term sig ℕ),
      StepsE system (s(var p, codeTerm (Nat.card S.Sym) (fun α => symEnum S α) b t) ::ₘ
          (codeCopies (code K (menu (codeMenus side k₀)))
            (codeExtras (Nat.card S.Sym) (fun α => symEnum S α) b t) fs + 0)) M ∧
        Equiv M (s(var p, t') ::ₘ 0) ∧ (codeTranslation side).TermTr t t' := by
  set K := k₀ + ∑ i, codeMenuSizes side i
  set Γ := menu (codeMenus side k₀)
  have hΓK : Γ.Below K := menu_codeMenus_below side k₀
  set W := (decomp K Γ).k + b + codeSize t
  have hC : (code K Γ).IsPackage := code_isPackage K Γ (menu_codeMenus_isPackage side k₀) hΓK
  have hCW : (code K Γ).Below W := fun x hx => by
    have := code_below K Γ hΓK x hx; omega
  obtain ⟨h1, h2, h3⟩ := codeTerm_extract_hyps (Nat.card S.Sym) (fun α => symEnum S α) (code K Γ)
    hC W hCW t b p hnd hb (by omega)
  obtain ⟨M, t', hS, hE, hT⟩ := codeTerm_extract side k₀ K le_rfl t b (var p) _ 0 h1 h2 h3
  exact ⟨K, _, M, t', hS, hE, hT⟩

/-! ## A tree with two cells -/

/-- No rule: every pair of symbols of the combinators gets no side. -/
def sideNone : ∀ α : sig.Sym, sig.Sym → Option (ExpSide sig (sig.arity α)) := fun _ _ => none

/-- The tree `con(dup(0, 1), 2)`. -/
def tConDup : Term sig ℕ := mkCon (mkDup (var 0) (var 1)) (var 2)

/-- It has two cells. -/
theorem card_cells_tConDup : Multiset.card tConDup.cells = 2 := by
  simp [tConDup, cells_mkCon, cells_mkDup]
  rfl

/-- **The tree `con(dup(0, 1), 2)` of two cells** (Fig. 10, page 90): `⟨t⟩` (new names from `4`),
with the fresh name `3` on its principal port and a copy of `!Γ` on each of its two extra ports,
reduces to a net that is `Equiv` to `3 = t'` with `t'` a translation of `t` by `[α]` of Fig. 10. -/
theorem extract_conDup :
    ∃ (K : ℕ) (fs : List (ℕ → ℕ)) (M : CNet) (t' : Term sig ℕ),
      StepsE system (s(var 3, codeTerm (Nat.card sig.Sym) (fun α => symEnum sig α) 4 tConDup) ::ₘ
          (codeCopies (code K (menu (codeMenus sideNone 0)))
            (codeExtras (Nat.card sig.Sym) (fun α => symEnum sig α) 4 tConDup) fs + 0)) M ∧
        Equiv M (s(var 3, t') ::ₘ 0) ∧ (codeTranslation sideNone).TermTr tConDup t' := by
  refine codeTerm_extract_of_nodup sideNone 0 tConDup 4 3 ?_ ?_
  · simp [tConDup]
  · intro x hx
    simp [tConDup] at hx
    omega

end INet.Comb.CodeTermExtractCheck
