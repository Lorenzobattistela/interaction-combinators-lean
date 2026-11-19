import InteractionCombinators.Lafont.DecodeCopy

/-!
# Review of `code_decoder_copy` and `Decomp.rename` (Figs. 9 and 10, pages 89 and 90)

Checks recorded by the review of issue #105.

* `copy_of_copy`, `copier_decoder_copy`: in Fig. 10 (page 89, the translation `⟨α_k⟩`) the code
  `!Γ` reaches the decoder `D` only after two copiers. `C_{p_{i,j}}` in `Γ_{i,j}` makes a copy, and
  `C_2` in `⟨α_k⟩` copies that copy again. A copy of a copy is still of the form
  `(code k π).bind (var ∘ f)` with `f` injective on the names of the code. `copier_decoder_copy`
  chains `C_2` (`copier_package`) with `code_decoder_copy`, with every hypothesis taken from the
  first copier. So the form of `code_decoder_copy` is what Fig. 10 needs.
* `decode_copy_adversarial`: the hypotheses of `code_decoder_copy` all hold at once, with `f`
  non-monotone (it puts the two cut names in reverse order and sends `1` below `0`). The decoder
  has free port `4` and loop `0, 1` (names *below* those of the copy, and two of them names of the
  original code). The context is not empty and uses the original cut names `3`, `6`, which the
  copy no longer uses.
* `copier_decoder_instance`: `copier_decoder_copy` on a concrete copy, with a non-empty context.
* `decomp_rename_instance`, `decomp_rename_needs_shift`: `decomp_bind_var` on a concrete
  instance. It also needs its hypothesis: a renaming that does not shift the counter gives
  different cut names from the ones `decomp` chooses.
-/

namespace INet.Comb.DecodeCopyReview

open Term CodeCheck DecodeReview

/-! ## A copy of a copy is a copy (Fig. 10) -/

/-- A copy of a copy is a copy (page 89, Fig. 10: `!Γ` passes through `C_{p_{i,j}}`, then `C_2`).
Renaming `t` by `f`, injective on the names of `t`, and then by `g`, injective on the names of the
renamed tree, is renaming `t` by `g ∘ f`, which is injective on the names of `t`. -/
theorem copy_of_copy (t : Term sig ℕ) (f g : ℕ → ℕ) (hf : Set.InjOn f {x | x ∈ t.vars})
    (hg : Set.InjOn g {x | x ∈ (t.bind fun x => var (f x)).vars}) :
    ((t.bind fun x => var (f x)).bind fun x => var (g x)) = t.bind (fun x => var (g (f x))) ∧
      Set.InjOn (fun x => g (f x)) {x | x ∈ t.vars} := by
  refine ⟨?_, fun x hx y hy h => hf hx hy (hg ?_ ?_ h)⟩
  · rw [Term.bind_bind]
    exact Term.bind_congr fun x _ => by rw [bind_var]
  · show f x ∈ (t.bind fun x => var (f x)).vars
    rw [vars_bind_var]; exact Multiset.mem_map_of_mem f hx
  · show f y ∈ (t.bind fun x => var (f x)).vars
    rw [vars_bind_var]; exact Multiset.mem_map_of_mem f hy

/-- **The translation `⟨α_k⟩` of Fig. 10 (page 89) against a copy of `!Γ`, then the extraction of
page 90.** A copy `(code k π).bind (var ∘ f)`, as `copier_code` leaves it (`f` injective on the
names of the code), meets the copier `C_2` whose first auxiliary port carries the decoder `D`
(free port `w`, loop `k₀, k₀ + 1`) and whose second carries `u` (the extra port of `⟨α_k⟩`). This
reduces, in any context `Δ`, to a net that is `Equiv` to the package `π` renamed by some injective
`g` on `w`, next to a new copy of the code on `u`. The only hypotheses are those of
`copier_code`, together with `f` and linearity. -/
theorem copier_decoder_copy (π : Term sig ℕ) (hπ : π.IsPackage) (k : ℕ) (hb : π.Below k)
    (f : ℕ → ℕ) (hf : Set.InjOn f {x | x ∈ (code k π).vars}) (w k₀ : ℕ) (u : Term sig ℕ)
    (Δ : CNet)
    (hlin : Net.Linear
      (s(copier [decoder w k₀, u], (code k π).bind (fun x => var (f x))) ::ₘ Δ)) :
    ∃ (g g' : ℕ → ℕ) (M : CNet), Set.InjOn g {x | x ∈ (code k π).vars} ∧
      Set.InjOn g' {x | x ∈ (code k π).vars} ∧
      StepsE system
        (s(copier [decoder w k₀, u], (code k π).bind (fun x => var (f x))) ::ₘ Δ) M ∧
      Equiv M (s(var w, π.bind (fun x => var (g x))) ::ₘ
        s(u, (code k π).bind (fun x => var (g' x))) ::ₘ Δ) := by
  set C := (code k π).bind (fun x => var (f x)) with hC
  have hCp : C.IsPackage := IsPackage.bind_var (code_isPackage k π hπ hb) f hf
  have hCd : DupFree C := DupFree.bind_var (code_dupFree k π) f
  obtain ⟨fs, N, hlen, hinj, hS, hE⟩ := copier_package C hCp hCd [decoder w k₀, u] Δ hlin
  obtain ⟨g₁, g₂, rfl⟩ := List.length_eq_two.1 hlen
  obtain ⟨e₁, i₁⟩ := copy_of_copy (code k π) f g₁ hf (hinj g₁ (by simp))
  obtain ⟨e₂, i₂⟩ := copy_of_copy (code k π) f g₂ hf (hinj g₂ (by simp))
  set N₁ : CNet := s((code k π).bind (fun x => var (g₁ (f x))), decoder w k₀) ::ₘ
    (s(u, (code k π).bind (fun x => var (g₂ (f x)))) ::ₘ Δ) with hN₁
  have hE₁ : Equiv N N₁ := by
    have e : ((List.zipWith (fun u g => s(u, C.bind (fun x => var (g x)))) [decoder w k₀, u]
        [g₁, g₂] : CNet) + Δ) = N₁ := by
      simp only [List.zipWith_cons_cons, List.zipWith_nil_left, ← Multiset.cons_coe,
        Multiset.coe_nil, Multiset.cons_add, zero_add, hN₁, hC, e₁, e₂, Sym2.eq_swap]
    exact e ▸ hE
  have hlinN : N.Linear := StepsE.linear system_wellFormed.linear hS hlin
  have hlin₁ : N₁.Linear := hE₁.linear hlinN
  obtain ⟨M, hS₁, hEM⟩ := code_decoder_copy π hπ k hb (fun x => g₁ (f x)) i₁ w k₀ _ hlin₁
  obtain ⟨M', hS', hE'⟩ := stepsE_of_equiv hE₁ hS₁
  exact ⟨_, _, M', i₁, i₂, hS.trans hS', hE'.trans hEM⟩

/-! ## The hypotheses of `code_decoder_copy` hold together on adversarial instances -/

/-- A non-monotone renaming of the names `0, 1, 3, 6` of `code 3 πn`: `0 ↦ 7`, `1 ↦ 2`,
`3 ↦ 9`, `6 ↦ 5`. It reverses the order of the two cut names `3 < 6` and of `0 < 1`. -/
def rev (x : ℕ) : ℕ :=
  if x = 0 then 7 else if x = 1 then 2 else if x = 3 then 9 else if x = 6 then 5 else x

/-- The copy written out: `M_n` on the cut names `9, 5`, in this order. -/
theorem copy_rev_eq : (code 3 πn).bind (fun x => var (rev x)) =
    mux [mux [var 9, var 5], muxStar [mkCon (var 7) (var 2), var 2], muxStar [var 5, var 7],
      var 9] := by decide

/-- `code_decoder_copy` (pages 89 and 90) with every hypothesis proved and nothing chosen to suit
it. The renaming `rev` is not monotone. The decoder has free port `4` and loop `0, 1`, which are
below the names of the copy (and `0`, `1` are names of the original code). The context
`3 = 6` is not empty and joins the two original cut names, which the copy no longer uses. The
package comes out renamed, `dup(dup(7, 2), con(7, 2))`, on `4`. -/
theorem decode_copy_adversarial : ∃ M, StepsE system
    (s((code 3 πn).bind (fun x => var (rev x)), decoder 4 0) ::ₘ {s(var 3, var 6)}) M ∧
    Equiv M (s(var 4, mkDup (mkDup (var 7) (var 2)) (mkCon (var 7) (var 2))) ::ₘ
      {s(var 3, var 6)}) := by
  have hinj : ∀ x ∈ (code 3 πn).vars, ∀ y ∈ (code 3 πn).vars, rev x = rev y → x = y := by decide
  have hπ : πn.bind (fun x => var (rev x)) =
      mkDup (mkDup (var 7) (var 2)) (mkCon (var 7) (var 2)) := by decide
  have h := code_decoder_copy πn (by unfold Term.IsPackage; decide) 3
    (by unfold Term.Below; decide) rev (fun x hx y hy hxy => hinj x hx y hy hxy) 4 0
    {s(var 3, var 6)} (linear_of_forall_mem _ (by decide))
  rw [hπ] at h
  exact h

/-- `copier_decoder_copy` (page 89, Fig. 10) on the copy by `rev`: `C_2` with the decoder (free
port `4`, loop `0, 1`) on its first auxiliary port and the extra port `8` on its second, in the
context `3 = 6`. Every hypothesis is proved. -/
theorem copier_decoder_instance : ∃ (g g' : ℕ → ℕ) (M : CNet),
    Set.InjOn g {x | x ∈ (code 3 πn).vars} ∧ Set.InjOn g' {x | x ∈ (code 3 πn).vars} ∧
    StepsE system (s(copier [decoder 4 0, var 8], (code 3 πn).bind (fun x => var (rev x))) ::ₘ
      {s(var 3, var 6)}) M ∧
    Equiv M (s(var 4, πn.bind (fun x => var (g x))) ::ₘ
      s(var 8, (code 3 πn).bind (fun x => var (g' x))) ::ₘ {s(var 3, var 6)}) := by
  have hinj : ∀ x ∈ (code 3 πn).vars, ∀ y ∈ (code 3 πn).vars, rev x = rev y → x = y := by decide
  exact copier_decoder_copy πn (by unfold Term.IsPackage; decide) 3
    (by unfold Term.Below; decide) rev (fun x hx y hy hxy => hinj x hx y hy hxy) 4 0 (var 8)
    {s(var 3, var 6)} (linear_of_forall_mem _ (by decide))

/-! ## `Decomp.rename` -/

/-- `decomp_bind_var` (page 88) on `πn` renamed by `rev` on its names and shifted from `3` to
`10`: the cut names are `10`, `13`, the images of `3`, `6`, and the auxiliary trees are renamed
by `rev`. -/
theorem decomp_rename_instance :
    (decomp 10 (πn.bind fun x => var (if x < 3 then rev x else x + 7))).cells.map (·.1) = [10, 13] ∧
    ((decomp 3 πn).rename (fun x => if x < 3 then rev x else x + 7) 0).cells.map (·.1) =
      [10, 13] ∧
    (decomp 10 (πn.bind fun x => var (if x < 3 then rev x else x + 7))).cells.map (·.2) =
      ((decomp 3 πn).rename (fun x => if x < 3 then rev x else x + 7) 0).cells.map (·.2) := by
  decide

/-- The hypothesis of `decomp_bind_var` is needed (page 88): renaming by `rev`, which does not
send `3 + i` to `K + i`, renames the cut names `3, 6` to `9, 5`. Decomposing the renamed package
from `3` still cuts at `3, 6`. -/
theorem decomp_rename_needs_shift :
    (decomp 3 (πn.bind fun x => var (rev x))).cells.map (·.1) = [3, 6] ∧
    ((decomp 3 πn).rename rev 0).cells.map (·.1) = [9, 5] := by
  decide

end INet.Comb.DecodeCopyReview
