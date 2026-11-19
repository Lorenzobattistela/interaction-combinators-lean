import InteractionCombinators.Lafont.RecursionFreeTr

/-!
# Review: the translation `[α]` of a recursion-free system against Fig. 6 (page 86)

Lafont 1997, Section 2.4, journal page 86 (PDF page 18), Fig. 6, and page 87 ("`[φ_{i,j}]` stands
for the net obtained by replacing each `α_k` by `[α_k]` in `φ_{i,j}`. If `φ_{i,j}` happens to be
undefined, which means that there is no rule for `α_i, α_j`, then `Γ_{i,j}` can be fixed
arbitrarily"). Checks of `RecursionFreeSide.lean` and `RecursionFreeTr.lean`.

* `cellMenu_getElem`, `cellMenu_of_side`, `cellMenu_of_no_rule` — entry `i` of the menu of `[α]`
  is `Γ_{α_i,α}`, built from the side of `α_i` (arity of `α_i`) against `α`; an eraser when there
  is no rule between them.
* `lowerTr_translation` — the call for `α` sees the final translation on every symbol below `α`.
* `rawSide_pair`, `rawSide_self` — **the two-rule case**: in a well-formed system the sides
  `φ_{α,β}` and `φ_{β,α}` (and their `σ`) come from one and the same decomposition.
* `con_menu_noConDup` — an instance of two symbols of different rank where a package of `[con]`
  contains a cell `era`, of lower rank.
-/

namespace INet

open Term

namespace Comb

open Translation

variable {S : Signature} [Finite S.Sym] {I : System S}

/-- The menu of `[α]` has one entry per symbol (Fig. 6, `Γ_{1,α} & … & Γ_{m,α}`). -/
theorem cellMenu_length (Φ : Translation S sig) (D : I.RecursionFreeData) (α : S.Sym) :
    (cellMenu Φ D α).length = Nat.card S.Sym := by
  simp [cellMenu]

/-- **Entry `i` of the menu of `[α]` is `Γ_{α_i,α}`** (Fig. 6, right, page 86): it is built from
the side of `α_i` against `α`, which lives on the ports of `α_i`. -/
theorem cellMenu_getElem (Φ : Translation S sig) (D : I.RecursionFreeData) (α : S.Sym)
    (i : Fin (Nat.card S.Sym)) :
    (cellMenu Φ D α)[(i : ℕ)]'(by rw [cellMenu_length]; exact i.isLt) =
      gammaOpt Φ (D.side ((symEnum S).symm i) α) (S.arity α + 1 + off (cellSizes Φ D α) i) := by
  simp [cellMenu]

/-- With a side `s` of `β` against `α` (a rule `β`–`α` or `α`–`β`), the entry of number
`symEnum S β` of the menu of `[α]` is the package `gamma` of `s` (Fig. 6, page 86). The selector of
`[β]` is `S^{symEnum S β}` (`cellNet`), so the numbering of the menu and of the selectors is the
same. -/
theorem cellMenu_of_side (Φ : Translation S sig) (D : I.RecursionFreeData) {α β : S.Sym}
    {s : ExpSide S (S.arity β)} (hs : D.side β α = some s) :
    (cellMenu Φ D α)[(symEnum S β : ℕ)]'(by rw [cellMenu_length]; exact (symEnum S β).isLt) =
      gamma Φ s.φ s.σ s.involutive (S.arity α + 1 + off (cellSizes Φ D α) (symEnum S β)) := by
  rw [cellMenu_getElem, Equiv.symm_apply_apply, hs]
  rfl

/-- Without a rule between `β` and `α`, the entry of number `symEnum S β` of the menu of `[α]` is
an eraser (page 87: "`Γ_{i,j}` can be fixed arbitrarily"). -/
theorem cellMenu_of_no_rule (Φ : Translation S sig) (D : I.RecursionFreeData) {α β : S.Sym}
    (h₀ : I.rule β α = none) (h₁ : I.rule α β = none) :
    (cellMenu Φ D α)[(symEnum S β : ℕ)]'(by rw [cellMenu_length]; exact (symEnum S β).isLt) =
      mkEra := by
  rw [cellMenu_getElem, Equiv.symm_apply_apply, D.side_eq, D.rawSide_eq_none h₀ h₁]
  rfl

/-- **The recursion sees the final translation below `α`** (page 87, "defined inductively"): the
translation passed to the call for `α`, built from the final translation, agrees with it on every
symbol smaller than `α`. With `cellNet_congr`, this is why `translation_net` holds. -/
theorem lowerTr_translation (D : I.RecursionFreeData) (α γ : S.Sym)
    (hγ : D.rank γ < D.rank α) :
    (D.lowerTr α fun β _ => (D.translation : Translation S sig).net β).net γ = D.translation.net γ := by
  show (if h : D.rank γ < D.rank α then _ else _) = _
  rw [dite_eq_left_of_eq_true (eq_true hγ)]

end Comb

namespace System.RecursionFreeData

variable {S : Signature} {I : System S} (D : I.RecursionFreeData)

/-- **The two-rule case cannot occur in a well-formed system** (page 86, `φ_{j,i} = ψ_{i,j}`,
`σ_{j,i} = σ_{i,j}`). For `α ≠ β` with a rule `α`–`β`, `System.WellFormed.unique` excludes a rule
`β`–`α`, so the side of `α` against `β` is the `φ` and the side of `β` against `α` the `ψ` of the
same decomposition `D.dec α β r h`; both carry its `σ`. This is what Fig. 7 needs. -/
theorem rawSide_pair (hI : I.WellFormed) {α β : S.Sym} (hne : α ≠ β)
    {r : Rule S (S.arity α) (S.arity β)} (h : I.rule α β = some r) :
    D.rawSide α β = some (D.rawφ α β r h) ∧ D.rawSide β α = some (D.rawψ β α r h) ∧
      (D.rawφ α β r h).σ = (D.dec α β r h).σ ∧ (D.rawψ β α r h).σ = (D.dec α β r h).σ :=
  ⟨D.rawSide_of_rule h,
    D.rawSide_of_rule_swap (hI.unique α β hne (by rw [h]; rfl)) h, rfl, rfl⟩

/-- **The rule of a symbol with itself** (page 86, `i = j`): the side of `α` against `α` is the `φ`
of the one decomposition of `α`–`α`, which is also its `ψ` (`RecursionFreeData.self`), with its
involutive `σ`. -/
theorem rawSide_self {α : S.Sym} {r : Rule S (S.arity α) (S.arity α)} (h : I.rule α α = some r) :
    D.rawSide α α = some (D.rawφ α α r h) ∧ (D.rawφ α α r h).φ = (D.dec α α r h).ψ ∧
      (D.rawφ α α r h).σ = (D.dec α α r h).σ :=
  ⟨D.rawSide_of_rule h, (D.self α r h).symm, rfl⟩

end System.RecursionFreeData

namespace Comb

open Translation

/-- The side of `era` against `con` in `systemNoConDup` is the non-canonical `eraSide` of page 87,
the `φ` of the rule `era`–`con`. -/
theorem rawSide_era_con :
    recursionFreeDataNoConDup.rawSide Comb.era Comb.con =
      some (recursionFreeDataNoConDup.rawφ Comb.era Comb.con ruleEraBin rfl) :=
  recursionFreeDataNoConDup.rawSide_of_rule rfl

/-- `eraSide` has a cell `era`. -/
theorem era_mem_cells_eraSide : (Comb.era : sig.Sym) ∈ eraSide.net.cells := by
  show (Comb.era : sig.Sym) ∈ Net.cells (show Net sig (Fin 0 ⊕ Fin 2 ⊕ Fin 0) from eraSide.net)
  refine Multiset.mem_bind.2 ⟨s(mkEra, .var (.inr (.inl 0))), by decide, ?_⟩
  rw [eqCells_mk]
  exact Multiset.mem_add.2 (Or.inl (Multiset.mem_cons.2 (Or.inl rfl)))

/-- `con` as a symbol of `sig`. -/
abbrev sCon : sig.Sym := Comb.con
/-- `dup` as a symbol of `sig`. -/
abbrev sDup : sig.Sym := Comb.dup
/-- `era` as a symbol of `sig`. -/
abbrev sEra : sig.Sym := Comb.era

/-- The number of a symbol is an index of the menu. -/
theorem symEnum_lt_length (Φ : Translation sig sig) (β : sig.Sym) :
    (symEnum sig β : ℕ) < (cellMenu Φ recursionFreeDataNoConDup sCon).length :=
  Nat.lt_of_lt_of_eq (symEnum sig β).isLt (cellMenu_length Φ _ _).symm

/-- **An instance: `[con]` in `systemNoConDup`** (pages 86–87), with `era < con` (ranks `0 < 1`).
The menu of `[con]` has three entries:

* the entry of `con` is `gamma` of the side of `con` against `con` (the rule `con`–`con`);
* the entry of `era` is `gamma` of a side `s` of `era` against `con` (the rule `era`–`con`),
  and `s` has a cell `era`: `[con]` contains the translation `Φ.net era` of a lower symbol;
* the entry of `dup` is `mkEra`: there is no rule `con`–`dup` nor `dup`–`con`. -/
theorem con_menu_noConDup (Φ : Translation sig sig) :
    recursionFreeDataNoConDup.rank sEra < recursionFreeDataNoConDup.rank sCon ∧
    (∃ s, recursionFreeDataNoConDup.side sCon sCon = some s ∧
      (cellMenu Φ recursionFreeDataNoConDup sCon)[(symEnum sig sCon : ℕ)]'(symEnum_lt_length Φ _) =
        gamma Φ s.φ s.σ s.involutive (sig.arity sCon + 1 +
          off (cellSizes Φ recursionFreeDataNoConDup sCon) (symEnum sig sCon))) ∧
    (∃ s, recursionFreeDataNoConDup.side sEra sCon = some s ∧ sEra ∈ s.φ.net.cells ∧
      (cellMenu Φ recursionFreeDataNoConDup sCon)[(symEnum sig sEra : ℕ)]'(symEnum_lt_length Φ _) =
        gamma Φ s.φ s.σ s.involutive (sig.arity sCon + 1 +
          off (cellSizes Φ recursionFreeDataNoConDup sCon) (symEnum sig sEra))) ∧
    (cellMenu Φ recursionFreeDataNoConDup sCon)[(symEnum sig sDup : ℕ)]'(symEnum_lt_length Φ _) =
      mkEra := by
  refine ⟨by decide, ?_, ?_, cellMenu_of_no_rule Φ _ rfl rfl⟩
  · have hs : recursionFreeDataNoConDup.side sCon sCon = some
        (recursionFreeDataNoConDup.rawφ sCon sCon ruleConCon rfl).expand := by
      rw [System.RecursionFreeData.side_eq, recursionFreeDataNoConDup.rawSide_of_rule]
      rfl
    exact ⟨_, hs, cellMenu_of_side Φ _ hs⟩
  · have hs : recursionFreeDataNoConDup.side sEra sCon = some
        (recursionFreeDataNoConDup.rawφ sEra sCon ruleEraBin rfl).expand := by
      rw [System.RecursionFreeData.side_eq, recursionFreeDataNoConDup.rawSide_of_rule]
      rfl
    refine ⟨_, hs, ?_, cellMenu_of_side Φ _ hs⟩
    rw [show (recursionFreeDataNoConDup.rawφ sEra sCon ruleEraBin rfl).expand.φ.net.cells = _ from
      RawSide.cells_expand _]
    exact era_mem_cells_eraSide

end Comb

end INet
