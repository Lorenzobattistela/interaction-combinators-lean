import InteractionCombinators.Universality.RecursionFree.RecursionFreeSide
import InteractionCombinators.Text.RenameMany
import InteractionCombinators.Text.RenameStep
import InteractionCombinators.Text.NetLemmas

/-!
# `Decomposition.Plugs` survives replacing the sides by their expanded forms (pages 85–86)

Lafont 1997, page 85 (a decomposition `φ, ψ, σ` of the right member of a rule) and page 86 (the
sides normalised). The translation of a recursion-free system (Fig. 6) is built from the expanded
forms `RawSide.expand` of the sides, which are the sides up to `Equiv` and an injective renaming of
their internal wires (`RawSide.expand_spec`). This file shows that plugging the expanded sides
still gives back the rule.

* `Equiv.bind_var_add` — an `Equiv`, renamed by an injective map, holds beside a context `Δ` that
  meets the renamed net only in its free ports.
* `Rule.plugIota` — the internal wires of `Rule.plug φ ψ σ` sent to those of `Rule.plug φ' ψ' σ`:
  the middle wires fixed, `ι₁` on the block of `φ`, `ι₂` on the block of `ψ`.
* `Rule.plug_equiv_rename`, `Rule.plug_rename` — **plugging respects side-wise renaming up to
  `Equiv`**, for linear sides `φ`, `ψ`.
* `Decomposition.Plugs.of_expand` — a decomposition that plugs `r` still plugs `r` after its sides
  are replaced by sides related to them as in `Rule.plug_rename`.
* `System.RecursionFreeData.plugs_expand` — the instance for a recursion-free system: the
  expanded sides chosen by `RawSide.expand` plug the rule.

## The linearity of the sides

`Rule.plug_rename` assumes that the sides `φ` and `ψ` are linear (`Rule.Linear`). The sides of a
decomposition are nets on page 85, and `System.RecursionFreeData.linear` supplies this, so the
instance `plugs_expand` has no hypothesis beyond the recursion-free data. Without it the statement
is false: `plug_rename_needs_linear` gives two sides, each `Net.Linear`, whose middle wire occurs
twice, so that their plug is not linear and is `Equiv` only to itself, while a wire substitution
inside `φ` changes the plug.
-/

namespace INet

variable {S : Signature}

open Term

/-! ### An `Equiv` beside a context -/

/-- **An `Equiv` renamed by an injective map holds beside a context** (Lafont 1997, Section 1.2,
page 71: a net is a graph). Let `K` be linear and `Equiv K L`. Rename by an injective `f` and add
a context `Δ` that is linear, that meets each renamed name at most once, and that does not meet the
renamed names that are not free ports of `K`. Then the two larger nets are equivalent. -/
theorem Equiv.bind_var_add {ν μ : Type} [DecidableEq ν] [DecidableEq μ] {K L : Net S ν}
    (h : Equiv K L) (f : ν → μ) (hf : Function.Injective f) (Δ : Net S μ) (hK : K.Linear)
    (hΔ : Δ.Linear) (hfree : ∀ y, Δ.vars.count (f y) ≤ 1)
    (hint : ∀ y, K.vars.count y ≠ 1 → Δ.vars.count (f y) = 0) :
    Equiv ((K.bind fun y => var (f y)) + Δ) ((L.bind fun y => var (f y)) + Δ) := by
  have hgood : ∀ K' : Net S ν, K'.Linear → (∀ y, K'.vars.count y = 1 ↔ K.vars.count y = 1) →
      ((K'.bind fun y => var (f y)) + Δ).Linear := by
    intro K' hK' hfr z
    rw [Net.vars_add, Multiset.count_add, Net.vars_bind_var]
    by_cases hz : ∃ y, f y = z
    · obtain ⟨y, rfl⟩ := hz
      rw [Multiset.count_map_eq_count' f _ hf y]
      by_cases h1 : K.vars.count y = 1
      · have := (hfr y).2 h1
        have := hfree y
        omega
      · rw [hint y h1]
        have := hK' y
        omega
    · rw [Multiset.count_map_eq_zero (fun y hy => hz ⟨y, hy⟩)]
      have := hΔ z
      omega
  have key : ∀ K₁ L₁ : Net S ν, Equiv K₁ L₁ → K₁.Linear →
      (∀ y, K₁.vars.count y = 1 ↔ K.vars.count y = 1) →
      Equiv ((K₁.bind fun y => var (f y)) + Δ) ((L₁.bind fun y => var (f y)) + Δ) := by
    intro K₁ L₁ h₁
    induction h₁ with
    | rel K L h => exact fun hK hfr => ((h.bind_var f hf).add_right Δ (hgood K hK hfr)).equiv
    | refl _ => exact fun _ _ => Equiv.refl _
    | symm K L h ih =>
      intro hL hfr
      exact (ih (Equiv.linear (Equiv.symm h) hL) fun y => (Equiv.free_iff h y).trans (hfr y)).symm
    | trans K M L h₁ _ ih₁ ih₂ =>
      intro hK hfr
      exact (ih₁ hK hfr).trans
        (ih₂ (Equiv.linear h₁ hK) fun y => (Equiv.free_iff h₁ y).symm.trans (hfr y))
  exact key K L h hK fun _ => Iff.rfl

namespace Rule

variable {a b k m n m' n' : ℕ}

/-! ### Plugging respects side-wise renaming -/

/-- The internal wires of a plugged rule sent to those of another (page 85): the `k` middle wires
are fixed, the block of `φ` is renamed by `ι₁`, the block of `ψ` by `ι₂`. -/
def plugIota (ι₁ : Fin m → Fin m') (ι₂ : Fin n → Fin n') : Fin (k + m + n) → Fin (k + m' + n') :=
  Fin.addCases
    (fun u : Fin (k + m) => Fin.castAdd n'
      (Fin.addCases (fun l : Fin k => Fin.castAdd m' l) (fun j => Fin.natAdd k (ι₁ j)) u))
    (fun j => Fin.natAdd (k + m') (ι₂ j))

theorem plugIota_injective {ι₁ : Fin m → Fin m'} {ι₂ : Fin n → Fin n'}
    (h₁ : Function.Injective ι₁) (h₂ : Function.Injective ι₂) :
    Function.Injective (plugIota (k := k) ι₁ ι₂) := by
  intro x y hxy
  induction x using Fin.addCases with
  | left u =>
    induction u using Fin.addCases with
    | left l =>
      induction y using Fin.addCases with
      | left v =>
        induction v using Fin.addCases with
        | left l' => simp [plugIota, Fin.ext_iff] at hxy ⊢; omega
        | right j' => simp [plugIota, Fin.ext_iff] at hxy; omega
      | right j' => simp [plugIota, Fin.ext_iff] at hxy; omega
    | right j =>
      induction y using Fin.addCases with
      | left v =>
        induction v using Fin.addCases with
        | left l' => simp [plugIota, Fin.ext_iff] at hxy; omega
        | right j' =>
          have e : ι₁ j = ι₁ j' := by simpa [plugIota, Fin.ext_iff] using hxy
          rw [h₁ e]
      | right j' => simp [plugIota, Fin.ext_iff] at hxy; omega
  | right j =>
    induction y using Fin.addCases with
    | left v =>
      induction v using Fin.addCases with
      | left l' => simp [plugIota, Fin.ext_iff] at hxy; omega
      | right j' => simp [plugIota, Fin.ext_iff] at hxy; omega
    | right j' =>
      have e : ι₂ j = ι₂ j' := by simpa [plugIota, Fin.ext_iff] using hxy
      rw [h₂ e]

theorem plugIota_plugL {ι₁ : Fin m → Fin m'} {ι₂ : Fin n → Fin n'} (x : Fin a ⊕ Fin k ⊕ Fin m) :
    Sum.map id (Sum.map id (plugIota ι₁ ι₂)) (plugL (b := b) (n := n) x) =
      plugL (n := n') (Sum.map id (Sum.map id ι₁) x) := by
  rcases x with i | l | j <;> simp [plugL, plugIota]

theorem plugIota_plugR {ι₁ : Fin m → Fin m'} {ι₂ : Fin n → Fin n'} (σ : Equiv.Perm (Fin k))
    (x : Fin b ⊕ Fin k ⊕ Fin n) :
    Sum.map id (Sum.map id (plugIota ι₁ ι₂)) (plugR (a := a) (m := m) σ x) =
      plugR (m := m') σ (Sum.map id (Sum.map id ι₂) x) := by
  rcases x with i | l | j <;> simp [plugR, plugIota]

theorem sumMap_injective {p q : ℕ} {ι : Fin m → Fin m'} (h : Function.Injective ι) :
    Function.Injective (Sum.map id (Sum.map id ι) : Fin p ⊕ Fin q ⊕ Fin m → Fin p ⊕ Fin q ⊕ Fin m') :=
  Function.injective_id.sumMap (Function.injective_id.sumMap h)

/-- In a linear side renamed by an injective `ι`, each middle wire occurs once. -/
theorem count_side_rename {p q : ℕ} {φ : Rule S p q} (hφ : φ.Linear) {ι : Fin φ.internal → Fin m'}
    (hι : Function.Injective ι) (l : Fin q) :
    (φ.net.bind fun x => var (Sum.map id (Sum.map id ι) x)).vars.count (.inr (.inl l)) = 1 :=
  (Net.count_vars_bind_var _ (sumMap_injective hι) _ (.inr (.inl l))).trans (hφ.right l)

/-- **Plugging respects side-wise renaming up to `Equiv`** (Lafont 1997, pages 85–86), with the
renaming `plugIota ι₁ ι₂` of the internal wires: if `φ'` is `φ` renamed by `ι₁` up to `Equiv` and
`ψ'` is `ψ` renamed by `ι₂`, then the plug of `φ'` and `ψ'` through `σ` is the plug of `φ` and
`ψ` renamed by `plugIota ι₁ ι₂`. The sides `φ`, `ψ` are linear. -/
theorem plug_equiv_rename {φ : Rule S a k} {φ' : Rule S a k} {ψ : Rule S b k} {ψ' : Rule S b k}
    (σ : Equiv.Perm (Fin k)) (hφ : φ.Linear) (hψ : ψ.Linear)
    {ι₁ : Fin φ.internal → Fin φ'.internal} (hι₁ : Function.Injective ι₁)
    {ι₂ : Fin ψ.internal → Fin ψ'.internal} (hι₂ : Function.Injective ι₂)
    (h₁ : Equiv φ'.net (φ.net.bind fun x => var (Sum.map id (Sum.map id ι₁) x)))
    (h₂ : Equiv ψ'.net (ψ.net.bind fun x => var (Sum.map id (Sum.map id ι₂) x))) :
    Equiv (Rule.plug φ' ψ' σ).net ((Rule.plug φ ψ σ).net.bind
      fun x => var (Sum.map id (Sum.map id (plugIota (k := k) ι₁ ι₂)) x)) := by
  set Lφ := φ.net.bind fun x => var (Sum.map id (Sum.map id ι₁) x) with hLφ
  set Lψ := ψ.net.bind fun x => var (Sum.map id (Sum.map id ι₂) x) with hLψ
  have cφ := count_side_rename hφ hι₁
  have cψ := count_side_rename hψ hι₂
  have linφ : Lφ.Linear := (hφ.net_linear).bind_var _ (sumMap_injective hι₁)
  have linψ : Lψ.Linear := (hψ.net_linear).bind_var _ (sumMap_injective hι₂)
  have linφ' : φ'.net.Linear := (Equiv.symm h₁).linear linφ
  have linψ' : ψ'.net.Linear := (Equiv.symm h₂).linear linψ
  -- the free ports of `φ'`, `ψ'` are those of the renamed sides
  have fφ' : ∀ l, φ'.net.vars.count (.inr (.inl l)) = 1 := fun l =>
    (h₁.free_iff _).2 (cφ l)
  have fψ' : ∀ l, ψ'.net.vars.count (.inr (.inl l)) = 1 := fun l =>
    (h₂.free_iff _).2 (cψ l)
  -- the target, side by side
  have htarget : ((Rule.plug φ ψ σ).net.bind
      fun x => var (Sum.map id (Sum.map id (plugIota (k := k) ι₁ ι₂)) x)) =
      (Lφ.bind fun x => var (plugL (b := b) (n := ψ'.internal) x)) +
        (Lψ.bind fun x => var (plugR (a := a) (m := φ'.internal) σ x)) := by
    show Net.bind _ (φ.net.bind (fun x => var (plugL x)) + ψ.net.bind (fun x => var (plugR σ x)))
      = _
    rw [Net.bind_add, Net.bind_bind, Net.bind_bind, hLφ, hLψ, Net.bind_bind, Net.bind_bind]
    simp only [Term.bind_var, plugIota_plugL, plugIota_plugR]
  -- the count of a name of the `φ'` block or of the `ψ'` block in the other side
  have dR : ∀ (N : Net S (Fin b ⊕ Fin k ⊕ Fin ψ'.internal)) (y : Fin a ⊕ Fin k ⊕ Fin φ'.internal),
      (N.bind fun x => var (plugR (a := a) (m := φ'.internal) σ x)).vars.count
        (plugL (b := b) (n := ψ'.internal) y) =
      match y with
      | .inl _ => 0
      | .inr (.inl l) => N.vars.count (.inr (.inl (σ l)))
      | .inr (.inr _) => 0 := by
    intro N y
    rcases y with i | l | j
    · rw [Net.vars_bind_var]
      exact Multiset.count_map_eq_zero fun x hx => by
        rcases x with i' | l' | j' <;> simp [plugR, plugL] at hx
    · have e : (plugL (b := b) (n := ψ'.internal) (.inr (.inl l)) :
          Fin a ⊕ Fin b ⊕ Fin (k + φ'.internal + ψ'.internal)) =
          plugR (a := a) (m := φ'.internal) σ (.inr (.inl (σ l))) := by
        simp [plugL, plugR]
      rw [e]
      exact Net.count_vars_bind_var _ (plugR_injective σ) _ _
    · rw [Net.vars_bind_var]
      exact Multiset.count_map_eq_zero fun x hx => by
        rcases x with i' | l' | j' <;> simp [plugR, plugL, Fin.ext_iff] at hx <;> omega
  have dL : ∀ (N : Net S (Fin a ⊕ Fin k ⊕ Fin φ'.internal)) (y : Fin b ⊕ Fin k ⊕ Fin ψ'.internal),
      (N.bind fun x => var (plugL (b := b) (n := ψ'.internal) x)).vars.count
        (plugR (a := a) (m := φ'.internal) σ y) =
      match y with
      | .inl _ => 0
      | .inr (.inl l) => N.vars.count (.inr (.inl (σ.symm l)))
      | .inr (.inr _) => 0 := by
    intro N y
    rcases y with i | l | j
    · rw [Net.vars_bind_var]
      exact Multiset.count_map_eq_zero fun x hx => by
        rcases x with i' | l' | j' <;> simp [plugR, plugL] at hx
    · have e : (plugR (a := a) (m := φ'.internal) σ (.inr (.inl l)) :
          Fin a ⊕ Fin b ⊕ Fin (k + φ'.internal + ψ'.internal)) =
          plugL (b := b) (n := ψ'.internal) (.inr (.inl (σ.symm l))) := by
        simp [plugL, plugR]
      rw [e]
      exact Net.count_vars_bind_var _ plugL_injective _ _
    · rw [Net.vars_bind_var]
      exact Multiset.count_map_eq_zero fun x hx => by
        rcases x with i' | l' | j' <;> simp [plugR, plugL, Fin.ext_iff] at hx <;> omega
  -- first replace `φ'` by `Lφ`, beside `ψ'`
  have E₁ := Equiv.bind_var_add (Equiv.symm h₁) (plugL (b := b) (n := ψ'.internal))
    plugL_injective (ψ'.net.bind fun x => var (plugR (a := a) (m := φ'.internal) σ x)) linφ
    (linψ'.bind_var _ (plugR_injective σ))
    (fun y => by
      rw [dR]
      rcases y with i | l | j
      · exact Nat.zero_le _
      · exact (fψ' (σ l)).le
      · exact Nat.zero_le _)
    (fun y hy => by
      rw [dR]
      rcases y with i | l | j
      · rfl
      · exact absurd (cφ l) hy
      · rfl)
  -- then replace `ψ'` by `Lψ`, beside `Lφ`
  have E₂ := Equiv.bind_var_add (Equiv.symm h₂) (plugR (a := a) (m := φ'.internal) σ)
    (plugR_injective σ) (Lφ.bind fun x => var (plugL (b := b) (n := ψ'.internal) x)) linψ
    (linφ.bind_var _ plugL_injective)
    (fun y => by
      rw [dL]
      rcases y with i | l | j
      · exact Nat.zero_le _
      · exact (cφ (σ.symm l)).le
      · exact Nat.zero_le _)
    (fun y hy => by
      rw [dL]
      rcases y with i | l | j
      · rfl
      · exact absurd (cψ l) hy
      · rfl)
  rw [add_comm (Lψ.bind _), add_comm (ψ'.net.bind _)] at E₂
  exact ((Equiv.symm E₁).trans (Equiv.symm E₂)).trans (Equiv.of_eq htarget.symm)

/-- **Plugging respects side-wise renaming up to `Equiv`** (Lafont 1997, pages 85–86): for linear
sides `φ`, `ψ`, and `φ'`, `ψ'` equal to them up to `Equiv` and injective renamings `ι₁`, `ι₂` of
their internal wires, the plug of `φ'` and `ψ'` through `σ` is the plug of `φ` and `ψ` up to
`Equiv` and an injective renaming of its internal wires. -/
theorem plug_rename {φ : Rule S a k} {φ' : Rule S a k} {ψ : Rule S b k} {ψ' : Rule S b k}
    (σ : Equiv.Perm (Fin k)) (hφ : φ.Linear) (hψ : ψ.Linear)
    {ι₁ : Fin φ.internal → Fin φ'.internal} (hι₁ : Function.Injective ι₁)
    {ι₂ : Fin ψ.internal → Fin ψ'.internal} (hι₂ : Function.Injective ι₂)
    (h₁ : Equiv φ'.net (φ.net.bind fun x => var (Sum.map id (Sum.map id ι₁) x)))
    (h₂ : Equiv ψ'.net (ψ.net.bind fun x => var (Sum.map id (Sum.map id ι₂) x))) :
    ∃ ι : Fin (Rule.plug φ ψ σ).internal → Fin (Rule.plug φ' ψ' σ).internal,
      Function.Injective ι ∧
      Equiv (Rule.plug φ' ψ' σ).net
        ((Rule.plug φ ψ σ).net.bind fun x => var (Sum.map id (Sum.map id ι) x)) :=
  ⟨plugIota ι₁ ι₂, plugIota_injective hι₁ hι₂, plug_equiv_rename σ hφ hψ hι₁ hι₂ h₁ h₂⟩

end Rule

/-! ### `Plugs` for the expanded sides -/

/-- **A decomposition still plugs its rule after its sides are renamed** (Lafont 1997, pages
85–86): if `D` plugs `r`, its sides are linear, and `φ'`, `ψ'` are `D.φ`, `D.ψ` up to `Equiv` and
injective renamings of their internal wires, then `⟨D.k, φ', ψ', D.σ⟩` plugs `r`. -/
theorem Decomposition.Plugs.of_expand {a b : ℕ} {D : Decomposition S a b} {r : Rule S a b}
    (hD : D.Plugs r) (hφ : D.φ.Linear) (hψ : D.ψ.Linear) {φ' : Rule S a D.k}
    {ψ' : Rule S b D.k} {ι₁ : Fin D.φ.internal → Fin φ'.internal} (hι₁ : Function.Injective ι₁)
    {ι₂ : Fin D.ψ.internal → Fin ψ'.internal} (hι₂ : Function.Injective ι₂)
    (h₁ : Equiv φ'.net (D.φ.net.bind fun x => var (Sum.map id (Sum.map id ι₁) x)))
    (h₂ : Equiv ψ'.net (D.ψ.net.bind fun x => var (Sum.map id (Sum.map id ι₂) x))) :
    Decomposition.Plugs ⟨D.k, φ', ψ', D.σ⟩ r := by
  obtain ⟨ι₀, hι₀, hE⟩ := hD
  obtain ⟨ι, hι, hE'⟩ := Rule.plug_rename D.σ hφ hψ hι₁ hι₂ h₁ h₂
  refine ⟨ι ∘ ι₀, hι.comp hι₀, ?_⟩
  have h := hE.bind_var _ (Rule.sumMap_injective hι)
  rw [Net.bind_bind] at h
  simp only [Term.bind_var, Sum.map_map, Sum.map_comp_map, Function.comp_id] at h
  exact hE'.trans h

namespace System.RecursionFreeData

variable {I : System S}

/-- **The expanded sides plug the rule** (Lafont 1997, pages 85–86). For a recursion-free system
and a rule `α`–`β`, the decomposition made of the expanded side `φ` of `α` against `β`
(`(D.rawφ α β r h).expand`), the expanded side `ψ` read from `β` (`(D.rawψ β α r h).expand`) and
the permutation `σ` of the decomposition plugs the rule. -/
theorem plugs_expand (D : I.RecursionFreeData) {α β : S.Sym} {r : Rule S (S.arity α) (S.arity β)}
    (h : I.rule α β = some r) :
    Decomposition.Plugs ⟨(D.dec α β r h).k, (D.rawφ α β r h).expand.φ,
      (D.rawψ β α r h).expand.φ, (D.dec α β r h).σ⟩ r := by
  obtain ⟨ι₁, hι₁, h₁⟩ := (D.rawφ α β r h).expand_spec
  obtain ⟨ι₂, hι₂, h₂⟩ := (D.rawψ β α r h).expand_spec
  exact Decomposition.Plugs.of_expand (D := D.dec α β r h) (D.plug α β r h)
    (D.linear α β r h).1 (D.linear α β r h).2 hι₁ hι₂ h₁ h₂

end System.RecursionFreeData

/-! ### Checks -/

/-- Renaming the internal wires by the identity changes nothing. -/
theorem Net.bind_sumMap_id {p q m : ℕ} (N : Net S (Fin p ⊕ Fin q ⊕ Fin m)) :
    (N.bind fun x => var (Sum.map id (Sum.map id (id : Fin m → Fin m)) x)) = N := by
  simp only [Sum.map_id_id, id_eq]
  exact Net.bind_var_self N

namespace Comb

open DecompositionReview

/-- Non-vacuity of `Decomposition.Plugs.of_expand`: applied to `decConCon_plugs` with the sides
unchanged and the identity renamings, it gives back that `decConCon` plugs `ruleConCon`. -/
theorem decConCon_plugs_of_expand : Decomposition.Plugs
    ⟨decConCon.k, decConCon.φ, decConCon.ψ, decConCon.σ⟩ ruleConCon :=
  Decomposition.Plugs.of_expand decConCon_plugs idSide_linear idSide_linear
    (ι₁ := id) Function.injective_id (ι₂ := id) Function.injective_id
    (Equiv.of_eq (Net.bind_sumMap_id _).symm) (Equiv.of_eq (Net.bind_sumMap_id _).symm)

/-- A side with one middle wire `m` and one internal wire `w`: `w = m, w = m`. It is `Net.Linear`
but not `Rule.Linear`: the middle wire occurs twice. -/
def badSide : Rule sig 0 1 := ⟨1, s(pw 0, pr 0) ::ₘ {s(pw 0, pr 0)}⟩

/-- `badSide` after the wire substitution of `w`: `m = m`, with the internal wire unused. -/
def badSide' : Rule sig 0 1 := ⟨1, {s(pr 0, pr 0)}⟩

/-- The other side: `m = m`, no internal wire. -/
def badLoop : Rule sig 0 1 := ⟨0, {s(pr 0, pr 0)}⟩

/-- **`Rule.plug_rename` needs linear sides** (pages 85–86). `badSide'` is `badSide` up to
`Equiv` (with the identity renaming), and `badLoop` is itself, yet the plug of `badSide'` and
`badLoop` is not, up to `Equiv`, the plug of `badSide` and `badLoop` renamed by any `ι`: the
latter is not linear (its middle wire occurs four times), so it is `Equiv` only to itself, and it
has three equations where the former has two. -/
theorem plug_rename_needs_linear :
    Equiv badSide'.net (badSide.net.bind fun x => var (Sum.map id (Sum.map id id) x)) ∧
    Equiv badLoop.net (badLoop.net.bind fun x => var (Sum.map id (Sum.map id id) x)) ∧
    ¬ ∃ ι : Fin (Rule.plug badSide badLoop 1).internal →
        Fin (Rule.plug badSide' badLoop 1).internal,
      Function.Injective ι ∧
      Equiv (Rule.plug badSide' badLoop 1).net
        ((Rule.plug badSide badLoop 1).net.bind fun x => var (Sum.map id (Sum.map id ι) x)) := by
  refine ⟨?_, Equiv.of_eq (Net.bind_sumMap_id _).symm, ?_⟩
  · have hW : Wire ((s(pw 0, pr 0) ::ₘ s(pw 0, pr 0) ::ₘ 0 : Net sig (Fin 0 ⊕ Fin 1 ⊕ Fin 1)))
        (s((pw 0 : Term sig (Fin 0 ⊕ Fin 1 ⊕ Fin 1)).subst (.inr (.inr 0)) (pr 0),
          (pr 0 : Term sig (Fin 0 ⊕ Fin 1 ⊕ Fin 1)).subst (.inr (.inr 0)) (pr 0)) ::ₘ 0) :=
      Wire.mk (.inr (.inr 0)) (pr 0) (pw 0) (pr 0) 0 (by unfold Net.Linear; decide) (by decide)
    have e : (s((pw 0 : Term sig (Fin 0 ⊕ Fin 1 ⊕ Fin 1)).subst (.inr (.inr 0)) (pr 0),
        (pr 0 : Term sig (Fin 0 ⊕ Fin 1 ⊕ Fin 1)).subst (.inr (.inr 0)) (pr 0)) ::ₘ 0 :
        Net sig (Fin 0 ⊕ Fin 1 ⊕ Fin 1)) = {s(pr 0, pr 0)} := by decide
    rw [e] at hW
    exact hW.equiv.symm.trans (Equiv.of_eq (Net.bind_sumMap_id (m := 1) _).symm)
  · rintro ⟨ι, hι, hE⟩
    have hnl : ¬ ((Rule.plug badSide badLoop 1).net.bind
        fun x => var (Sum.map id (Sum.map id ι) x)).Linear := by
      intro hl
      have h4 := hl (Sum.map id (Sum.map id ι) (.inr (.inr ⟨0, by decide⟩)))
      rw [Net.count_vars_bind_var _ (Rule.sumMap_injective hι)] at h4
      revert h4
      decide
    have e := (Equiv.symm hE).eq_of_not_linear_any hnl
    have hc := congrArg Multiset.card e
    simp only [Net.bind, Multiset.card_map] at hc
    revert hc
    decide

end Comb

end INet
