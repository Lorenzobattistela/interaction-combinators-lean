import InteractionCombinators.Universality.General.CodeTr

/-!
# Checks for the principal net `[α]` of Fig. 10 (pages 89–90)

A system with one symbol `α` of arity one and no rule. Every side is absent, so `Γ_{α,α}` is an
eraser, the menu `Γ_α = Γ_{α,α}` is an eraser, `Γ = Γ_α` is an eraser, and its code `!Γ` is
`M_4(ε, ε, ε, ε)` (no `dup` cell, `code_of_dupFree`). So `[α]` is the tree of Fig. 10 with these
pieces: `T_{1,1}(ε, S^0_1(M_3(!Γ, 0, 1)), 1)`, the port `0` and the loop `1`.
-/

namespace INet.Comb

open Term

/-- A signature with one symbol of arity one. -/
def sigOne : Signature := ⟨Unit, fun _ => 1⟩

instance : Unique sigOne.Sym := inferInstanceAs (Unique Unit)

instance : Finite sigOne.Sym := inferInstanceAs (Finite Unit)

/-- No rule: every side is absent. -/
def sideNone : ∀ α : sigOne.Sym, sigOne.Sym → Option (ExpSide sigOne (sigOne.arity α)) :=
  fun _ _ => none

theorem card_sigOne : Nat.card sigOne.Sym = 1 := Nat.card_unique

theorem codeCellMenu_sideNone (β : sigOne.Sym) (k : ℕ) : codeCellMenu sideNone β k = [mkEra] := by
  rw [codeCellMenu_eq]
  simp only [sideNone, codeGammaOpt, List.ofFn_const, card_sigOne]
  rfl

theorem codeMenus_sideNone (k : ℕ) : codeMenus sideNone k = [mkEra] := by
  rw [codeMenus_eq]
  simp only [codeCellMenu_sideNone, List.ofFn_const, card_sigOne]
  rfl

theorem symEnum_sigOne (α : sigOne.Sym) : (symEnum sigOne α : ℕ) = 0 := by
  have h1 : Nat.card sigOne.Sym = 1 := card_sigOne
  have h2 : (symEnum sigOne α : ℕ) < Nat.card sigOne.Sym := (symEnum sigOne α).isLt
  omega

/-- **`[α]` for a one-symbol system without rules** (Fig. 10, page 89): the transpositor `T_{1,1}`
carrying the eraser `Γ_α` and the selector `S^0_1` on `M_3` of the code `!Γ = M_4(ε, ε, ε, ε)`, the
port `0` and the loop `1`. -/
theorem codeTree_sigOne (α : sigOne.Sym) :
    codeTree sideNone α = cellSkel mkEra 1 0 [mux [mkEra, mkEra, mkEra, mkEra], var 0] 1 := by
  rw [codeTree_eq, codeCellMenu_sideNone, codeMenus_sideNone, symEnum_sigOne, card_sigOne,
    show menu [mkEra] = (mkEra : Term sig ℕ) from rfl, code_of_dupFree _ _ (by trivial)]
  rfl

/-- The names of this `[α]` (page 89): the port `0` once and the loop `1` twice. -/
example (α : sigOne.Sym) : (codeTree sideNone α).vars = {0} + {1} + {1} := by
  rw [codeTree_sigOne, vars_cellSkel]
  simp [mux]

/-- This `[α]` has one internal wire, the loop (page 89). -/
example (α : sigOne.Sym) : (codeNet sideNone α).internal = 1 := by
  show (wireSet 1 (codeTree sideNone α)).card = 1
  rw [wireSet, codeTree_sigOne, vars_cellSkel]
  simp [mux]
  decide

/-- This `[α]` is strict (page 80). -/
example : (codeTranslation sideNone).Strict := codeTranslation_strict sideNone

end INet.Comb
