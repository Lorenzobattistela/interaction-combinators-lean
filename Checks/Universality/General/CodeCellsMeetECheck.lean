import Checks.Universality.Codes.CodeMenusECheck
import InteractionCombinators.Universality.General.CodeShift
import InteractionCombinators.Universality.General.CodeCellsMeet

/-!
# Check: the principal net `[α]` of Fig. 10 and the meeting of two cells, for `combEnum`

`codeNetE e side α` (`Lafont/CodeTr.lean`) is the principal net `[α]` of Fig. 10 (page 89) with the
symbols numbered by `e`, and `codeCells_meetE` (`Lafont/CodeCellsMeet.lean`) the analogue of
Fig. 7, rows 1–2, for any `e`. Here they are used at the hand-written numbering
`con, dup, era ↦ 0, 1, 2` (`combEnum`) with the side `sideConDup`, without `symEnum`.

The internal wires of `[α]` are its names other than the ports, each of which occurs twice
(`Checks/CodeTreeECheck.lean`): `(82 - 2) / 2 = 40` for `con`, `(130 - 2) / 2 = 64` for `dup`,
`80 / 2 = 40` for `era`.
-/

namespace INet.Comb.CodeCellsMeetECheck

open Term Translation CodeGammaReview CodeMenusECheck

-- The compiler evaluates `[α]` (it is not `noncomputable`): its numbers of internal wires.
#guard [(codeNetE combEnum sideConDup (Comb.con : sig.Sym)).internal,
  (codeNetE combEnum sideConDup (Comb.dup : sig.Sym)).internal,
  (codeNetE combEnum sideConDup (Comb.era : sig.Sym)).internal] == [40, 64, 40]

-- The wire names given by `codeWiresE` are computed too: the first wire of `[con]`, shifted by
-- `100`, is the loop `2` of `[con]` shifted, `102`.
#guard (List.finRange (codeNetE combEnum sideConDup (Comb.con : sig.Sym)).internal).head?.map
  (codeWiresE combEnum sideConDup (Comb.con : sig.Sym) 100) == some 102

/-- `codeNetE_inst` at `combEnum` (page 89): each `[α]` with its ports named `0, 1, …` and its
wires named back is the tree of Fig. 10. (Stated for a variable `α`: for a concrete symbol the
elaborator unfolds the number of wires and exceeds the recursion depth.) -/
example (α : sig.Sym) : (codeNetE combEnum sideConDup α).inst (fun i => var (i : ℕ))
      (fun w => ((wireNum (sig.arity α) (codeTreeE combEnum sideConDup α)).symm w).1) =
    codeTreeE combEnum sideConDup α :=
  codeNetE_inst combEnum sideConDup α

/-- `[con]` is strict at `combEnum` (definition page 80). -/
example : (codeNetE combEnum sideConDup (Comb.con : sig.Sym)).Strict :=
  codeNetE_strict combEnum sideConDup _

/-- The entry of the menu `Γ_dup` at the number `0` of `con` is `Γ_{con,dup}`, built from the
side of `con` against `dup` (Fig. 10, page 89), at `combEnum`. -/
example (k₀ : ℕ) (h : (combEnum (Comb.con : sig.Sym) : ℕ) <
      (codeCellMenuE combEnum sideConDup (Comb.dup : sig.Sym) k₀).length) :
    (codeCellMenuE combEnum sideConDup (Comb.dup : sig.Sym) k₀)[(combEnum Comb.con : ℕ)]'h =
      codeGammaOpt 3 (fun γ => combEnum γ) (sideConDup Comb.con Comb.dup)
        (k₀ + off (codeCellSizesE combEnum sideConDup Comb.dup) (combEnum Comb.con)) :=
  getElem_codeCellMenuE combEnum sideConDup _ _ k₀ h

/-- **`codeCells_meetE` at `combEnum`** (Fig. 10, pages 89–90; Fig. 7, rows 1–2): `[con]` and
`[dup]` plugged by their roots, with any names on their ports and wires, in a linear context,
reduce to the two multiplexors against `Γ_{con,dup}` and `Γ_{dup,con}`. -/
example (xs : Fin (sig.arity (Comb.con : sig.Sym)) → ℕ)
    (ys : Fin (sig.arity (Comb.dup : sig.Sym)) → ℕ)
    (f : Fin (codeNetE combEnum sideConDup (Comb.con : sig.Sym)).internal → ℕ)
    (g : Fin (codeNetE combEnum sideConDup (Comb.dup : sig.Sym)).internal → ℕ) (Δ : CNet)
    (hlin : Net.Linear (s((codeNetE combEnum sideConDup (Comb.con : sig.Sym)).inst
        (fun i => var (xs i)) f,
      (codeNetE combEnum sideConDup (Comb.dup : sig.Sym)).inst (fun j => var (ys j)) g) ::ₘ Δ)) :
    ∃ (K K' : ℕ) (M : CNet),
      StepsE system (s((codeNetE combEnum sideConDup (Comb.con : sig.Sym)).inst
          (fun i => var (xs i)) f,
        (codeNetE combEnum sideConDup (Comb.dup : sig.Sym)).inst (fun j => var (ys j)) g) ::ₘ Δ)
        M ∧
      Equiv M
        (s(mux ((code (codeKeyE combEnum sideConDup (Comb.con : sig.Sym))
                (menu (codeMenusE combEnum sideConDup
                  (codeMenuBaseE combEnum sideConDup Comb.con)))).bind
                (fun x => var (codeRen xs K x)) ::
              List.ofFn (fun i => (var (xs i) : Term sig ℕ)) ++
                [var (K + sig.arity (Comb.con : sig.Sym))]),
            (codeGammaOpt 3 (fun γ => combEnum γ) (sideConDup Comb.con Comb.dup)
              (sig.arity (Comb.dup : sig.Sym) + 1 +
                off (codeCellSizesE combEnum sideConDup Comb.dup)
                (combEnum Comb.con))).bind
                (fun x => var (codeRen ys K' x))) ::ₘ
          s(mux ((code (codeKeyE combEnum sideConDup (Comb.dup : sig.Sym))
                (menu (codeMenusE combEnum sideConDup
                  (codeMenuBaseE combEnum sideConDup Comb.dup)))).bind
                (fun x => var (codeRen ys K' x)) ::
              List.ofFn (fun j => (var (ys j) : Term sig ℕ)) ++
                [var (K + sig.arity (Comb.con : sig.Sym))]),
            (codeGammaOpt 3 (fun γ => combEnum γ) (sideConDup Comb.dup Comb.con)
              (sig.arity (Comb.con : sig.Sym) + 1 +
                off (codeCellSizesE combEnum sideConDup Comb.con)
                (combEnum Comb.dup))).bind
                (fun x => var (codeRen xs K x))) ::ₘ Δ) :=
  codeCells_meetE combEnum sideConDup (Comb.con : sig.Sym) (Comb.dup : sig.Sym) xs ys f g Δ hlin

end INet.Comb.CodeCellsMeetECheck
