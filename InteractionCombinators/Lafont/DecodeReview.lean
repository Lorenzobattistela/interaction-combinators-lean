import InteractionCombinators.Lafont.DecodeCheck
import InteractionCombinators.RenameMany

/-!
# Review of `code_decoder_package` (Fig. 9, page 89)

Checks recorded by the review of issue #86.

* `decode_nestedRight`: a package with a `dup` nested in the **right** auxiliary tree of another
  `dup`, itself under a `con` (so `τ` is not a wire), in a context that is not empty.
* `decode_tree_shared`: `code_decoder_tree` on a tree that is not a package, whose free name `0`
  is shared with the context `Δ`.
* `decode_renamedCopy`: the instance that Fig. 10 (page 90) needs. There the decoder meets a
  **copy** of `!π` made by the copier (`copier_code`), whose names are renamed: it is not of the
  form `code k π`. The copy is `Equiv` to `code k π` (`equiv_bind_var`), and the theorem applies
  through `stepsE_of_equiv`. Here this is done on a concrete copy whose cut names are not the ones
  `decomp` would choose.
-/

namespace INet.Comb.DecodeReview

open Term CodeCheck

/-- A package with a `dup` nested in the right auxiliary tree of another `dup`:
`con(dup(2, con(dup(0, 1), 2)), con(0, 1))`. -/
def πr : Term sig ℕ :=
  mkCon (mkDup (var 2) (mkCon (mkDup (var 0) (var 1)) (var 2))) (mkCon (var 0) (var 1))

/-- `πr` is a package (page 88): every name occurs twice. -/
theorem πr_isPackage : πr.IsPackage := by unfold Term.IsPackage; decide

/-- Fig. 9 (page 89) on `πr`, plugged into `3`, next to the equation `4 = 5`; new names of the code
from `6`, loop of the decoder at `(decomp 6 πr).k`. -/
theorem decode_nestedRight : ∃ M, StepsE system
    {s(code 6 πr, decoder 3 (decomp 6 πr).k), s(var 4, var 5)} M ∧
    Equiv M {s(var 3, πr), s(var 4, var 5)} :=
  code_decoder_package πr πr_isPackage 6 3 _ {s(var 4, var 5)}
    (linear_of_forall_mem _ (by decide)) (by unfold Net.Below; decide) le_rfl

/-- `code_decoder_tree` (page 89) on the tree `dup(0, dup(1, 1))`, which is not a package: its name
`0` is free, and the context `0 = ε` shares it. -/
theorem decode_tree_shared : ∃ M, StepsE system
    {s(code 3 (mkDup (var 0) (mkDup (var 1) (var 1))), decoder 2 20), s(var 0, mkEra)} M ∧
    Equiv M {s(var 2, mkDup (var 0) (mkDup (var 1) (var 1))), s(var 0, mkEra)} :=
  code_decoder_tree _ 3 2 20 {s(var 0, mkEra)}
    (linear_of_forall_mem _ (by decide)) (by unfold Net.Below; decide) (by decide)

/-- The package of `CodeCheck`, `dup(dup(0, 1), con(0, 1))`, two nested `dup` cells. -/
def πn : Term sig ℕ := mkDup (mkDup (var 0) (var 1)) (mkCon (var 0) (var 1))

/-- Its code with new names from `3` has the names `0, 1, 3, 6` (cut at `3` and `6`). -/
theorem code_πn : code 3 πn =
    mux [mux [var 3, var 6], muxStar [mkCon (var 0) (var 1), var 1], muxStar [var 6, var 0],
      var 3] := rfl

/-- The renaming of the copy: `0 ↦ 40`, `1 ↦ 41`, `3 ↦ 50`, `6 ↦ 47`, the identity elsewhere. -/
def fwd (x : ℕ) : ℕ :=
  if x = 0 then 40 else if x = 1 then 41 else if x = 3 then 50 else if x = 6 then 47 else x

/-- A copy of `code 3 πn` as the copier of Fig. 10 leaves it, renamed injectively by `fwd`. It is
not `code k π` for any `k`, `π`: `decomp k` cuts the outer cell before the inner one at `k` and
`k + 3`, while here the outer cut name `50` is above the inner one `47`. -/
def copy : Term sig ℕ := (code 3 πn).bind fun x => var (fwd x)

/-- The renaming back: `fwd` followed by its inverse on the four names, as one involution
exchanging `0 ↔ 40`, `1 ↔ 41`, `3 ↔ 50`, `6 ↔ 47`. -/
def back (x : ℕ) : ℕ :=
  if x = 40 then 0 else if x = 41 then 1 else if x = 50 then 3 else if x = 47 then 6 else
  if x = 0 then 40 else if x = 1 then 41 else if x = 3 then 50 else if x = 6 then 47 else x

/-- The copy written out: `M_n` on the cut names `50, 47`, in this order. -/
theorem copy_eq : copy =
    mux [mux [var 50, var 47], muxStar [mkCon (var 40) (var 41), var 41], muxStar [var 47, var 40],
      var 50] := by decide

/-- The net of Fig. 10 around the decoder: the copy against the decoder, free port `2`, loop at
`30`. -/
def N₁ : CNet := {s(copy, decoder 2 30)}

/-- `N₁` renamed by `back` is `code 3 πn` against the same decoder. -/
theorem N₁_back : Net.bind (fun x => (var (back x) : Term sig ℕ)) N₁ =
    {s(code 3 πn, decoder 2 30)} := by decide

/-- The copy against the decoder is the same graph as `code 3 πn` against it (page 70: the names of
internal wires do not matter). -/
theorem N₁_equiv : Equiv N₁ {s(code 3 πn, decoder 2 30)} := by
  have hlin : N₁.Linear := linear_of_forall_mem _ (by decide)
  have hinj : ∀ x ∈ Net.vars N₁, ∀ y ∈ Net.vars N₁, back x = back y → x = y := by decide
  have hfree : ∀ x ∈ Net.vars N₁, (Net.vars N₁).count x = 1 → back x = x := by decide
  rw [← N₁_back]
  exact Net.equiv_bind_var hlin back (fun x hx y hy h => hinj x hx y hy h)
    (fun x hx => hfree x (Multiset.one_le_count_iff_mem.1 (by omega)) hx)

/-- Fig. 9 on a renamed copy of the code (the instance needed by Fig. 10, page 90): the decoder
extracts `πn` from the copy, through `N₁_equiv` and `code_decoder_package`. -/
theorem decode_renamedCopy : ∃ M, StepsE system N₁ M ∧ Equiv M {s(var 2, πn)} := by
  obtain ⟨M, hS, hE⟩ := code_decoder_package πn (by unfold Term.IsPackage; decide) 3 2 30 0
    (linear_of_forall_mem _ (by decide)) (by unfold Net.Below; decide) (by decide)
  obtain ⟨M', hS', hE'⟩ := stepsE_of_equiv N₁_equiv hS
  exact ⟨M', hS', hE'.trans hE⟩

end INet.Comb.DecodeReview
