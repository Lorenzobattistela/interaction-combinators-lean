import InteractionCombinators.Lafont.RecursionFreeSide
import InteractionCombinators.Lafont.DecompositionAbsorb

/-!
# Decomposition data without an order, and the side `φ_{α,β}` it chooses (pages 85–86, 90)

Lafont 1997, Section 2.4, journal pages 85–86 (PDF pages 17–18), and Section 3, journal page 90
(PDF page 22). Every rule `α_i`–`α_j` decomposes (page 85) into `φ_{i,j}` on the ports of `α_i`,
`ψ_{i,j}` on the ports of `α_j`, and a permutation `σ_{i,j}` of the middle wires, and page 86
normalises the decomposition: "one can assume that in all cases, `φ_{j,i} = ψ_{i,j}`,
`σ_{j,i} = σ_{i,j}`, and `σ_{i,j}` is involutive", with `σ_{i,j}` an identity for `i ≠ j`.

Stage 5 (`System.RecursionFreeData`) asks in addition for an order on the alphabet. The general
translation of Section 2.5 and Fig. 10 (pages 88–90, "in the general case") uses the same sides
`φ_{i,j}` and permutations `σ_{i,j}`, but no order. This file gives the data of page 86 without
the order.

* `System.DecData` — the fields of `RecursionFreeData` without `rank`, `rank_φ`, `rank_ψ`;
  `RecursionFreeData.toDecData` forgets the order.
* `System.WellFormed.decData`, `System.exists_decData` — every well-formed system has such data:
  the canonical decomposition `Rule.decompose` with `σ` moved into `φ` (`Decomposition.absorb`) for
  `α ≠ β`, the symmetric decomposition (`System.WellFormed.symmDec`) for `α`–`α`. No order and no
  recursion-freeness are needed.
* `System.DecData.rawSide`, `.side` — the side `φ_{α,β}` of `α` against `β`, as in
  `RecursionFreeSide.lean`, with `rawSide_of_rule`, `rawSide_of_rule_swap`, `rawSide_eq_none`,
  `side_eq`; `RecursionFreeData.rawSide_toDecData`, `side_toDecData`: stage 5 is a special case.
-/

namespace INet

variable {S : Signature}

open Term

/-- The decomposition data of an interaction system (Lafont 1997, pages 85–86), without an order
(page 90): a decomposition of every rule, normalised as on page 86 — its sides linear and
reduced, `σ` involutive, `ψ = φ` for a rule `α`–`α`, `σ = 1` for a rule `α`–`β` with
`α ≠ β`. -/
structure System.DecData (I : System S) where
  /-- The decomposition chosen for each rule. -/
  dec : ∀ α β (r : Rule S (S.arity α) (S.arity β)), I.rule α β = some r →
    Decomposition S (S.arity α) (S.arity β)
  /-- Plugging the sides gives back the rule (page 85). -/
  plug : ∀ α β r (h : I.rule α β = some r), (dec α β r h).Plugs r
  /-- The sides are linear. -/
  linear : ∀ α β r (h : I.rule α β = some r), (dec α β r h).φ.Linear ∧ (dec α β r h).ψ.Linear
  /-- The sides are reduced nets (page 85). -/
  reduced : ∀ α β r (h : I.rule α β = some r),
    (dec α β r h).φ.Reduced ∧ (dec α β r h).ψ.Reduced
  /-- `σ_{i,j}` is involutive (page 86). -/
  involutive : ∀ α β r (h : I.rule α β = some r), Function.Involutive (dec α β r h).σ
  /-- For a rule `α_i`–`α_i`, `φ_{i,i} = ψ_{i,i}` (page 86, `φ_{j,i} = ψ_{i,j}` with `i = j`). -/
  self : ∀ α r (h : I.rule α α = some r), (dec α α r h).ψ = (dec α α r h).φ
  /-- For a rule `α_i`–`α_j` with `i ≠ j`, `σ_{i,j}` is an identity (page 86). -/
  ne : ∀ α β r (h : I.rule α β = some r), α ≠ β → (dec α β r h).σ = 1

/-- The decomposition data of a recursion-free system (page 86) with its order forgotten
(page 90). -/
def System.RecursionFreeData.toDecData {I : System S} (D : I.RecursionFreeData) : I.DecData where
  dec := D.dec
  plug := D.plug
  linear := D.linear
  reduced := D.reduced
  involutive := D.involutive
  self := D.self
  ne := D.ne

/-! ### Existence for every well-formed system (pages 85–86, 90) -/

namespace System.WellFormed

variable {I : System S}

open Classical in
/-- The normalised decomposition of a rule of a well-formed system (page 86): the symmetric
decomposition for a rule `α`–`α`, the canonical decomposition (page 85) with `σ` moved into `φ`
for `α ≠ β`. -/
noncomputable def normDecomp (hI : I.WellFormed) (α β : S.Sym) :
    ∀ r : Rule S (S.arity α) (S.arity β), I.rule α β = some r →
      Decomposition S (S.arity α) (S.arity β) :=
  if hab : α = β then hab ▸ fun r h => hI.symmDec α r h
  else fun r _ => r.decompose.absorb

theorem normDecomp_self (hI : I.WellFormed) (α : S.Sym) :
    hI.normDecomp α α = fun r h => hI.symmDec α r h := by
  unfold normDecomp
  split_ifs with hab
  · rfl
  · exact absurd rfl hab

theorem normDecomp_ne (hI : I.WellFormed) {α β : S.Sym} (hab : α ≠ β) :
    hI.normDecomp α β = fun r _ => r.decompose.absorb := by
  unfold normDecomp
  split_ifs with h
  · exact absurd h hab
  · rfl

/-- **Page 86, "one can assume", without an order (page 90).** Every well-formed system has
normalised decomposition data: the symmetric decomposition (`Rule.exists_symm_decomposition`) of
a rule `α`–`α`, and the canonical decomposition `Rule.decompose` with `σ` moved into `φ`
(`Decomposition.absorb`) of a rule `α`–`β` with `α ≠ β`. -/
noncomputable def decData (hI : I.WellFormed) : I.DecData where
  dec := hI.normDecomp
  plug α β r h := by
    by_cases hab : α = β
    · subst hab
      rw [normDecomp_self]
      exact (hI.symmDec_spec α r h).2.2.2.2
    · rw [normDecomp_ne hI hab]
      exact r.decompose.absorb_plugs (r.plug_decompose (hI.linear α β r h))
  linear α β r h := by
    by_cases hab : α = β
    · subst hab
      rw [normDecomp_self]
      obtain ⟨hψ, -, hl, -, -⟩ := hI.symmDec_spec α r h
      show (hI.symmDec α r h).φ.Linear ∧ (hI.symmDec α r h).ψ.Linear
      rw [hψ]
      exact ⟨hl, hl⟩
    · rw [normDecomp_ne hI hab]
      have hd := r.decompose_linear (hI.linear α β r h)
      exact ⟨r.decompose.absorb_linear hd.1, hd.2⟩
  reduced α β r h := by
    by_cases hab : α = β
    · subst hab
      rw [normDecomp_self]
      obtain ⟨hψ, -, -, hr, -⟩ := hI.symmDec_spec α r h
      show (hI.symmDec α r h).φ.Reduced ∧ (hI.symmDec α r h).ψ.Reduced
      rw [hψ]
      exact ⟨hr, hr⟩
    · rw [normDecomp_ne hI hab]
      have hd := r.decompose_reduced (hI.reduced α β r h)
      exact ⟨r.decompose.absorb_reduced hd.1, hd.2⟩
  involutive α β r h := by
    by_cases hab : α = β
    · subst hab
      rw [normDecomp_self]
      exact (hI.symmDec_spec α r h).2.1
    · rw [normDecomp_ne hI hab]
      exact fun _ => rfl
  self α r h := by
    rw [normDecomp_self]
    exact (hI.symmDec_spec α r h).1
  ne α β r h hne := by
    rw [normDecomp_ne hI hne]
    rfl

end System.WellFormed

/-- **Pages 86 and 90.** Every well-formed interaction system has normalised decomposition data,
with no order on its alphabet and no recursion-freeness. -/
theorem System.exists_decData {I : System S} (hI : I.WellFormed) : Nonempty I.DecData :=
  ⟨hI.decData⟩

/-! ### The side `φ_{α,β}` (page 86) -/

namespace System.DecData

variable {I : System S} (D : I.DecData)

/-- The side `φ` of the decomposition of a rule `α`–`β`, on the ports of `α` (page 86). -/
def rawφ (α β : S.Sym) (r : Rule S (S.arity α) (S.arity β)) (h : I.rule α β = some r) :
    RawSide S (S.arity α) :=
  ⟨_, (D.dec α β r h).φ, (D.dec α β r h).σ, (D.linear α β r h).1, (D.reduced α β r h).1,
    D.involutive α β r h⟩

/-- The side `ψ` of the decomposition of a rule `β`–`α`, on the ports of `α`: the side `φ_{α,β}`
read from the rule `β`–`α` (page 86, `φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}`). -/
def rawψ (α β : S.Sym) (r : Rule S (S.arity β) (S.arity α)) (h : I.rule β α = some r) :
    RawSide S (S.arity α) :=
  ⟨_, (D.dec β α r h).ψ, (D.dec β α r h).σ, (D.linear β α r h).2, (D.reduced β α r h).2,
    D.involutive β α r h⟩

open Classical in
/-- The side `φ_{α,β}` of `α` against `β` (page 86): the `φ` of the rule `α`–`β` if it exists,
otherwise the `ψ` of the rule `β`–`α` if it exists, otherwise nothing. -/
noncomputable def rawSide (α β : S.Sym) : Option (RawSide S (S.arity α)) :=
  if h : ∃ r, I.rule α β = some r then some (D.rawφ α β h.choose h.choose_spec)
  else if h' : ∃ r, I.rule β α = some r then some (D.rawψ α β h'.choose h'.choose_spec)
  else none

/-- The side `φ_{α,β}` in expanded form (page 86), the input of Fig. 10 (page 90). -/
noncomputable def side (α β : S.Sym) : Option (ExpSide S (S.arity α)) :=
  (D.rawSide α β).map RawSide.expand

/-- With a rule `α`–`β`, the side of `α` against `β` is the `φ` of its decomposition
(page 86). -/
theorem rawSide_of_rule {α β : S.Sym} {r : Rule S (S.arity α) (S.arity β)}
    (h : I.rule α β = some r) : D.rawSide α β = some (D.rawφ α β r h) := by
  have hc : ∃ r, I.rule α β = some r := ⟨r, h⟩
  have e : hc.choose = r := Option.some.inj (hc.choose_spec.symm.trans h)
  rw [rawSide, dite_eq_left_of_eq_true (eq_true hc)]
  subst e
  rfl

/-- Without a rule `α`–`β` but with a rule `β`–`α`, the side of `α` against `β` is the `ψ` of the
decomposition of `β`–`α` (page 86, `φ_{j,i} = ψ_{i,j}`). -/
theorem rawSide_of_rule_swap {α β : S.Sym} (h₀ : I.rule α β = none)
    {r : Rule S (S.arity β) (S.arity α)} (h : I.rule β α = some r) :
    D.rawSide α β = some (D.rawψ α β r h) := by
  have hn : ¬ ∃ r, I.rule α β = some r := by rintro ⟨r', h'⟩; rw [h₀] at h'; cases h'
  have hc : ∃ r, I.rule β α = some r := ⟨r, h⟩
  have e : hc.choose = r := Option.some.inj (hc.choose_spec.symm.trans h)
  rw [rawSide, dite_eq_right_of_eq_false (eq_false hn), dite_eq_left_of_eq_true (eq_true hc)]
  subst e
  rfl

/-- Without a rule between `α` and `β`, there is no side (page 86). -/
theorem rawSide_eq_none {α β : S.Sym} (h₀ : I.rule α β = none) (h₁ : I.rule β α = none) :
    D.rawSide α β = none := by
  have hn : ¬ ∃ r, I.rule α β = some r := by rintro ⟨r', h'⟩; rw [h₀] at h'; cases h'
  have hn' : ¬ ∃ r, I.rule β α = some r := by rintro ⟨r', h'⟩; rw [h₁] at h'; cases h'
  rw [rawSide, dite_eq_right_of_eq_false (eq_false hn), dite_eq_right_of_eq_false (eq_false hn')]

/-- The side chosen for `α` against `β` is the expanded form of `rawSide` (page 86). -/
theorem side_eq (α β : S.Sym) : D.side α β = (D.rawSide α β).map RawSide.expand := rfl

/-- There is a side of `α` against `β` exactly when there is a rule `α`–`β` or a rule `β`–`α`
(page 86). -/
theorem side_isSome_iff (α β : S.Sym) :
    (D.side α β).isSome ↔ (∃ r, I.rule α β = some r) ∨ ∃ r, I.rule β α = some r := by
  rw [side_eq, Option.isSome_map, rawSide]
  split_ifs with h h'
  · exact iff_of_true rfl (Or.inl h)
  · exact iff_of_true rfl (Or.inr h')
  · exact iff_of_false (by simp) (by rintro (h₁ | h₁) <;> contradiction)

end System.DecData

namespace System.RecursionFreeData

variable {I : System S} (D : I.RecursionFreeData)

/-- The sides of a recursion-free system (page 86) are those of its data with the order
forgotten (page 90). -/
theorem rawSide_toDecData : D.toDecData.rawSide = D.rawSide := rfl

/-- The expanded sides of a recursion-free system (page 86) are those of its data with the order
forgotten (page 90): stage 5 is a special case. -/
theorem side_toDecData : D.toDecData.side = D.side := rfl

end System.RecursionFreeData

end INet
