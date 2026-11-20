import InteractionCombinators.Universality.RecursionFree.DecompositionAbsorb

/-!
# Review of `System.RecursionFreeData` (pages 85–87)

Checks produced by the review of
`InteractionCombinators/Universality/RecursionFree/RecursionFree.lean` against Lafont 1997, pages
85–87 (PDF pages 17–19, Fig. 6 and Fig. 7).

## The normalisations of page 86 cost nothing

The paper defines recursion-free by the order condition *after* saying that "one can assume"
`φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}`, `σ_{i,j}` involutive, and `σ_{i,j} = 1` for `i ≠ j`.
The structure asks for these normalisations together with the order condition. They do not make
the definition stronger:

* `Decomposition.absorb`: for `α ≠ β`, the permutation is moved into `φ` by renumbering its
  middle wires. The cells, linearity, reducedness and `Plugs` are kept, and `σ` becomes `1`.
* `Decomposition.Plugs.cells`, `rankBound_transfer`: any decomposition that plugs `r` splits the
  cells of `r` between `φ` and `ψ`. So for a rule `α`–`α`, where both sides are bounded by
  `rank α`, the order condition holds for one decomposition iff it holds for every one, in
  particular for the symmetric decomposition `Rule.exists_symm_decomposition_of_symmPerm` (#77).
* `RecursionFreeDataRaw.recursionFree`: for a well-formed system, the order condition with
  *arbitrary* decompositions (no `involutive`, no `self`, no `ne`) already gives
  `System.RecursionFree`.

## The order

`exists_rank_of_strictOrder`: on a finite alphabet, any strict order is given by a rank into `ℕ`
(the number of smaller symbols). So `rank : S.Sym → ℕ` is no stronger than "the alphabet can be
ordered", for the finite alphabets of the paper.

## The port order

`eraBin_canonical_not`, `eraBin_canonical_mutant`: the canonical decomposition of `era`–`con`
puts both erasers into `ψ`. Under the definition it fails for every order, and under the mutant
that exchanges `α` and `β` in `rank_φ`, `rank_ψ` it succeeds with `era < con`. The paper says
(page 87) that this example needs a *non-canonical* decomposition, which is true only of the
definition as written: the port order agrees with the paper.

## `Plugs` is not vacuous

* `decDupDup_not_plugs_conCon`, `decConCon_not_plugs_dupDup`: the decompositions of `con`–`con`
  and `dup`–`dup` differ only by `σ`, and each plugs only its own rule. The injective renaming of
  `Plugs` does not let a wrong wiring through.
* `conDup_needs_plug`: without the field `plug`, the identity sides with `σ = 1` would satisfy
  every other field for `con`–`dup`, for every order, and the full system would be recursion-free.
-/

namespace INet

variable {S : Signature}

open Term

/-! ### `Plugs` keeps the cells -/

/-- A decomposition that plugs `r` splits the cells of `r` between its two sides (page 85). -/
theorem Decomposition.Plugs.cells {a b : ℕ} {D : Decomposition S a b} {r : Rule S a b}
    (h : D.Plugs r) : D.φ.net.cells + D.ψ.net.cells = r.net.cells := by
  obtain ⟨ι, -, hE⟩ := h
  have hc := hE.cells_eq
  rw [Rule.cells_plug, Net.cells_bind_var] at hc
  exact hc

/-- For a decomposition that plugs `r`, both sides contain only symbols of rank `< ρ` iff `r`
does. For a rule `α`–`α` (page 86, both sides bounded by `α`) the order condition does not depend
on the decomposition chosen. -/
theorem rankBound_iff_of_plugs {a b : ℕ} {D : Decomposition S a b} {r : Rule S a b}
    (h : D.Plugs r) (rank : S.Sym → ℕ) (ρ : ℕ) :
    ((∀ γ ∈ D.φ.net.cells, rank γ < ρ) ∧ (∀ γ ∈ D.ψ.net.cells, rank γ < ρ)) ↔
      ∀ γ ∈ r.net.cells, rank γ < ρ := by
  rw [← h.cells]
  simp only [Multiset.mem_add]
  exact ⟨fun ⟨h₁, h₂⟩ γ hγ => hγ.elim (h₁ γ) (h₂ γ),
    fun h' => ⟨fun γ hγ => h' γ (Or.inl hγ), fun γ hγ => h' γ (Or.inr hγ)⟩⟩

/-- **Page 86, rule `α`–`α`.** If one decomposition of `r` has all its cells of rank
`< rank α`, so has every other decomposition of `r`, in particular a symmetric one. -/
theorem rankBound_transfer {a b : ℕ} {D D' : Decomposition S a b} {r : Rule S a b}
    (h : D.Plugs r) (h' : D'.Plugs r) (rank : S.Sym → ℕ) (ρ : ℕ)
    (hφ : ∀ γ ∈ D.φ.net.cells, rank γ < ρ) (hψ : ∀ γ ∈ D.ψ.net.cells, rank γ < ρ) :
    (∀ γ ∈ D'.φ.net.cells, rank γ < ρ) ∧ (∀ γ ∈ D'.ψ.net.cells, rank γ < ρ) :=
  (rankBound_iff_of_plugs h' rank ρ).2 ((rankBound_iff_of_plugs h rank ρ).1 ⟨hφ, hψ⟩)

/-! ### The normalisations are free -/

/-- The order condition of page 86 on decompositions that are *not* normalised: no `involutive`,
no `self` (`ψ = φ` for `α`–`α`), no `ne` (`σ = 1` for `α ≠ β`). -/
structure RecursionFreeDataRaw (I : System S) where
  /-- The order on the alphabet. -/
  rank : S.Sym → ℕ
  /-- The decomposition chosen for each rule. -/
  dec : ∀ α β (r : Rule S (S.arity α) (S.arity β)), I.rule α β = some r →
    Decomposition S (S.arity α) (S.arity β)
  /-- Plugging the sides gives back the rule. -/
  plug : ∀ α β r (h : I.rule α β = some r), (dec α β r h).Plugs r
  /-- The sides are linear. -/
  linear : ∀ α β r (h : I.rule α β = some r), (dec α β r h).φ.Linear ∧ (dec α β r h).ψ.Linear
  /-- The sides are reduced. -/
  reduced : ∀ α β r (h : I.rule α β = some r),
    (dec α β r h).φ.Reduced ∧ (dec α β r h).ψ.Reduced
  /-- `φ` contains only symbols smaller than `β`. -/
  rank_φ : ∀ α β r (h : I.rule α β = some r), ∀ γ ∈ (dec α β r h).φ.net.cells, rank γ < rank β
  /-- `ψ` contains only symbols smaller than `α`. -/
  rank_ψ : ∀ α β r (h : I.rule α β = some r), ∀ γ ∈ (dec α β r h).ψ.net.cells, rank γ < rank α

namespace RecursionFreeDataRaw

variable {I : System S}

/-- The symmetric decomposition of a rule `α`–`α` of a well-formed system
(`Rule.exists_symm_decomposition_of_symmPerm`, page 86); now `System.WellFormed.symmDec` in
`DecompositionAbsorb.lean`. -/
noncomputable def symmDec (hI : I.WellFormed) (α : S.Sym) (r : Rule S (S.arity α) (S.arity α))
    (h : I.rule α α = some r) : Decomposition S (S.arity α) (S.arity α) :=
  hI.symmDec α r h

/-- The symmetric decomposition is normalised and plugs back the rule (page 86). -/
theorem symmDec_spec (hI : I.WellFormed) (α : S.Sym) (r : Rule S (S.arity α) (S.arity α))
    (h : I.rule α α = some r) :
    (symmDec hI α r h).ψ = (symmDec hI α r h).φ ∧
      Function.Involutive (symmDec hI α r h).σ ∧ (symmDec hI α r h).φ.Linear ∧
      (symmDec hI α r h).φ.Reduced ∧ (symmDec hI α r h).Plugs r :=
  hI.symmDec_spec α r h

open Classical in
/-- The normalised decomposition: the symmetric one for a rule `α`–`α`, the given one with `σ`
moved into `φ` for `α ≠ β`. -/
noncomputable def normDec (R : RecursionFreeDataRaw I) (hI : I.WellFormed) (α β : S.Sym) :
    ∀ r : Rule S (S.arity α) (S.arity β), I.rule α β = some r →
      Decomposition S (S.arity α) (S.arity β) :=
  if hab : α = β then hab ▸ fun r h => symmDec hI α r h
  else fun r h => (R.dec α β r h).absorb

theorem normDec_self (R : RecursionFreeDataRaw I) (hI : I.WellFormed) (α : S.Sym) :
    R.normDec hI α α = fun r h => symmDec hI α r h := by
  unfold normDec
  split_ifs with hab
  · rfl
  · exact absurd rfl hab

theorem normDec_ne (R : RecursionFreeDataRaw I) (hI : I.WellFormed) {α β : S.Sym}
    (hab : α ≠ β) : R.normDec hI α β = fun r h => (R.dec α β r h).absorb := by
  unfold normDec
  split_ifs with h
  · exact absurd h hab
  · rfl

/-- **Page 86, "one can assume".** For a well-formed system, the order condition on arbitrary
decompositions gives a `System.RecursionFreeData` with the same order: the symmetric
decomposition of a rule `α`–`α` keeps the order condition (`rankBound_transfer`), and moving `σ`
into `φ` for `α ≠ β` adds no cell (`Decomposition.absorb`). -/
noncomputable def toData (R : RecursionFreeDataRaw I) (hI : I.WellFormed) :
    I.RecursionFreeData where
  rank := R.rank
  dec := R.normDec hI
  plug α β r h := by
    by_cases hab : α = β
    · subst hab
      rw [normDec_self]
      exact (symmDec_spec hI α r h).2.2.2.2
    · rw [normDec_ne R hI hab]
      exact (R.dec α β r h).absorb_plugs (R.plug α β r h)
  linear α β r h := by
    by_cases hab : α = β
    · subst hab
      rw [normDec_self]
      obtain ⟨hψ, -, hl, -, -⟩ := symmDec_spec hI α r h
      show (symmDec hI α r h).φ.Linear ∧ (symmDec hI α r h).ψ.Linear
      rw [hψ]
      exact ⟨hl, hl⟩
    · rw [normDec_ne R hI hab]
      exact ⟨(R.dec α β r h).absorb_linear (R.linear α β r h).1, (R.linear α β r h).2⟩
  reduced α β r h := by
    by_cases hab : α = β
    · subst hab
      rw [normDec_self]
      obtain ⟨hψ, -, -, hr, -⟩ := symmDec_spec hI α r h
      show (symmDec hI α r h).φ.Reduced ∧ (symmDec hI α r h).ψ.Reduced
      rw [hψ]
      exact ⟨hr, hr⟩
    · rw [normDec_ne R hI hab]
      exact ⟨(R.dec α β r h).absorb_reduced (R.reduced α β r h).1, (R.reduced α β r h).2⟩
  involutive α β r h := by
    by_cases hab : α = β
    · subst hab
      rw [normDec_self]
      exact (symmDec_spec hI α r h).2.1
    · rw [normDec_ne R hI hab]
      exact fun _ => rfl
  self α r h := by
    rw [normDec_self]
    exact (symmDec_spec hI α r h).1
  ne α β r h hne := by
    rw [normDec_ne R hI hne]
    rfl
  rank_φ α β r h := by
    by_cases hab : α = β
    · subst hab
      rw [normDec_self]
      exact (rankBound_transfer (R.plug α α r h) (symmDec_spec hI α r h).2.2.2.2 R.rank
        (R.rank α) (R.rank_φ α α r h) (R.rank_ψ α α r h)).1
    · rw [normDec_ne R hI hab]
      show ∀ γ ∈ (R.dec α β r h).absorb.φ.net.cells, R.rank γ < R.rank β
      rw [Decomposition.absorb_cells]
      exact R.rank_φ α β r h
  rank_ψ α β r h := by
    by_cases hab : α = β
    · subst hab
      rw [normDec_self]
      exact (rankBound_transfer (R.plug α α r h) (symmDec_spec hI α r h).2.2.2.2 R.rank
        (R.rank α) (R.rank_φ α α r h) (R.rank_ψ α α r h)).2
    · rw [normDec_ne R hI hab]
      exact R.rank_ψ α β r h

/-- **Page 86.** A well-formed system that satisfies the order condition with arbitrary
decompositions is recursion-free. -/
theorem recursionFree (R : RecursionFreeDataRaw I) (hI : I.WellFormed) : I.RecursionFree :=
  ⟨R.toData hI⟩

end RecursionFreeDataRaw

/-- **Page 86.** For a well-formed system, `System.RecursionFree` is equivalent to the order
condition on arbitrary decompositions: the normalisations `involutive`, `self` and `ne` of
`System.RecursionFreeData` make the definition no stronger. -/
theorem recursionFree_iff_raw {I : System S} (hI : I.WellFormed) :
    I.RecursionFree ↔ Nonempty (RecursionFreeDataRaw I) :=
  ⟨fun ⟨R⟩ => ⟨⟨R.rank, R.dec, R.plug, R.linear, R.reduced, R.rank_φ, R.rank_ψ⟩⟩,
    fun ⟨R⟩ => R.recursionFree hI⟩

/-! ### The order: a rank into `ℕ` is no loss on a finite alphabet -/

/-- On a finite alphabet (page 85: `m` symbols), every strict order is given by a rank into `ℕ`:
the number of smaller symbols. So `rank : S.Sym → ℕ` says no more than "the alphabet can be
ordered" (page 86). -/
theorem exists_rank_of_strictOrder {α : Type} [Fintype α] (lt : α → α → Prop)
    (irrefl : ∀ a, ¬ lt a a) (trans : ∀ a b c, lt a b → lt b c → lt a c) :
    ∃ rank : α → ℕ, ∀ a b, lt a b → rank a < rank b := by
  classical
  refine ⟨fun a => (Finset.univ.filter fun c => lt c a).card, fun a b hab =>
    Finset.card_lt_card (Finset.ssubset_def.2 ⟨fun c hc => ?_, fun hsub => ?_⟩)⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact trans _ _ _ hc hab
  · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ a, hab⟩)
    exact irrefl a (Finset.mem_filter.1 this).2

namespace Comb

open DecompositionReview

/-! ### The port order: the canonical decomposition of `era`–`con` -/

/-- The canonical decomposition of `era`–`con` has an eraser in `ψ`, the side on the ports of
`con`. -/
theorem era_mem_eraBin_decompose_ψ :
    (Comb.era : sig.Sym) ∈ ruleEraBin.decompose.ψ.net.cells := by
  show (Comb.era : sig.Sym) ∈ Net.cells
    (show Net sig (Fin 2 ⊕ Fin 0 ⊕ Fin 0) from ruleEraBin.decompose.ψ.net)
  rw [eraBin_decompose.2.2]
  refine Multiset.mem_bind.2 ⟨s(.var (.inl 0), mkEra), Multiset.mem_cons_self _ _, ?_⟩
  rw [eqCells_mk]
  exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_self _ _))

/-- **Page 87, "a non-canonical decomposition for `γε` and `δε`".** Under `rank_ψ`, the canonical
decomposition of `era`–`con` fails for every order: its `ψ` holds an eraser, which would have to
be smaller than the eraser. -/
theorem eraBin_canonical_not (rank : sig.Sym → ℕ) :
    ¬ ∀ γ ∈ ruleEraBin.decompose.ψ.net.cells, rank γ < rank Comb.era :=
  fun h => lt_irrefl _ (h _ era_mem_eraBin_decompose_ψ)

/-- The mutant that exchanges `α` and `β` in `rank_φ` and `rank_ψ` (`φ` bounded by the first
cell, `ψ` by the second) accepts the canonical decomposition of `era`–`con` with `era < con`.
Under the mutant, the remark of page 87 that this example needs a non-canonical decomposition
would be false; under the definition it is true (`eraBin_canonical_not`). -/
theorem eraBin_canonical_mutant :
    (∀ γ ∈ ruleEraBin.decompose.φ.net.cells, rankNoConDup γ < rankNoConDup Comb.era) ∧
      ∀ γ ∈ ruleEraBin.decompose.ψ.net.cells, rankNoConDup γ < rankNoConDup Comb.con := by
  constructor
  · intro γ hγ
    have h0 : (show Net sig (Fin 0 ⊕ Fin 0 ⊕ Fin 0) from ruleEraBin.decompose.φ.net) = 0 :=
      eraBin_decompose.2.1
    have hγ' : γ ∈ Net.cells
        (show Net sig (Fin 0 ⊕ Fin 0 ⊕ Fin 0) from ruleEraBin.decompose.φ.net) := hγ
    rw [h0] at hγ'
    simp [Net.cells] at hγ'
  · intro γ hγ
    have hγ' : γ ∈ Net.cells
        (show Net sig (Fin 2 ⊕ Fin 0 ⊕ Fin 0) from ruleEraBin.decompose.ψ.net) := hγ
    rw [eraBin_decompose.2.2] at hγ'
    clear hγ
    revert γ
    decide

/-! ### `Plugs` is not vacuous -/

/-- The sides of `con`–`con` plugged with `σ = 1` (which is `decDupDup`) do not give `con`–`con`,
for any renaming: the port `0` of the first cell would meet the port `0` of the second, not the
port `1`. -/
theorem decDupDup_not_plugs_conCon : ¬ decDupDup.Plugs ruleConCon := by
  rintro ⟨ι, -, hE⟩
  let s : Fin 2 ⊕ Fin 2 ⊕ Fin (Rule.plug decDupDup.φ decDupDup.ψ decDupDup.σ).internal →
      Term sig (Fin 2) :=
    Sum.elim (fun i => var i) (Sum.elim (fun j => var j.rev) fun _ => var 0)
  have hN : Net.Sol (ruleConCon.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) s := by
    refine ⟨s, ?_, fun _ _ => rfl⟩
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.1 he
    have key : ∀ e ∈ ruleConCon.net, e ∈ [s(pl 0, pr 1), s(pl 1, pr 0)] := by decide
    have h := key e₀ he₀
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> rfl
  obtain ⟨s', hs, hp⟩ := (hE.sol_iff s).2 hN
  have h1 := hs s(var (.inl 0), var (.inr (.inr ⟨0, by decide⟩))) (by decide)
  have h2 := hs s(var (.inr (.inl 0)), var (.inr (.inr ⟨0, by decide⟩))) (by decide)
  have p1 := hp (.inl 0) (by decide)
  have p2 := hp (.inr (.inl 0)) (by decide)
  simp only [Sym2.lift_mk, Term.bind_var] at h1 h2
  rw [p1] at h1
  rw [p2, ← h1] at h2
  exact absurd h2 (by decide)

/-- The sides of `dup`–`dup` plugged through the exchange (which is `decConCon`) do not give
`dup`–`dup`, for any renaming. -/
theorem decConCon_not_plugs_dupDup : ¬ decConCon.Plugs ruleDupDup := by
  rintro ⟨ι, -, hE⟩
  let s : Fin 2 ⊕ Fin 2 ⊕ Fin (Rule.plug decConCon.φ decConCon.ψ decConCon.σ).internal →
      Term sig (Fin 2) :=
    Sum.elim (fun i => var i) (Sum.elim (fun j => var j) fun _ => var 0)
  have hN : Net.Sol (ruleDupDup.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) s := by
    refine ⟨s, ?_, fun _ _ => rfl⟩
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.1 he
    have key : ∀ e ∈ ruleDupDup.net, e ∈ [s(pl 0, pr 0), s(pl 1, pr 1)] := by decide
    have h := key e₀ he₀
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> rfl
  obtain ⟨s', hs, hp⟩ := (hE.sol_iff s).2 hN
  have h1 := hs s(var (.inl 0), var (.inr (.inr ⟨0, by decide⟩))) (by decide)
  have h2 := hs s(var (.inr (.inl 1)), var (.inr (.inr ⟨0, by decide⟩))) (by decide)
  have p1 := hp (.inl 0) (by decide)
  have p2 := hp (.inr (.inl 1)) (by decide)
  simp only [Sym2.lift_mk, Term.bind_var] at h1 h2
  rw [p1] at h1
  rw [p2, ← h1] at h2
  exact absurd h2 (by decide)

/-- `idSide` has no cell. -/
theorem idSide_cells : idSide.net.cells = 0 := by
  show Net.cells (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0) from idSide.net) = 0
  have : DecidableEq sig.Sym := inferInstanceAs (DecidableEq Comb)
  decide

/-- The field `plug` is what makes `system` not recursion-free: for `con`–`con`'s identity sides
with `σ = 1` (`decDupDup`, of arities `2`, `2` like `con`–`dup`), every other field holds for
`con`–`dup` and for every order (the sides have no cell), but they do not plug `ruleConDup`. -/
theorem conDup_needs_plug (rank : sig.Sym → ℕ) :
    (decDupDup.φ.Linear ∧ decDupDup.ψ.Linear) ∧ (decDupDup.φ.Reduced ∧ decDupDup.ψ.Reduced) ∧
      Function.Involutive decDupDup.σ ∧ decDupDup.σ = 1 ∧
      (∀ γ ∈ decDupDup.φ.net.cells, rank γ < rank Comb.dup) ∧
      (∀ γ ∈ decDupDup.ψ.net.cells, rank γ < rank Comb.con) ∧
      ¬ decDupDup.Plugs ruleConDup := by
  refine ⟨⟨idSide_linear, idSide_linear⟩, ⟨idSide_reduced, idSide_reduced⟩, fun _ => rfl, rfl,
    fun γ hγ => ?_, fun γ hγ => ?_, fun h => ?_⟩
  · exact absurd (idSide_cells ▸ hγ : γ ∈ (0 : Multiset sig.Sym)) (Multiset.notMem_zero γ)
  · exact absurd (idSide_cells ▸ hγ : γ ∈ (0 : Multiset sig.Sym)) (Multiset.notMem_zero γ)
  · have hc := h.cells
    have h0 : decDupDup.φ.net.cells + decDupDup.ψ.net.cells = 0 := by
      show idSide.net.cells + idSide.net.cells = 0
      rw [idSide_cells, add_zero]
    rw [h0] at hc
    exact Multiset.notMem_zero _ (hc ▸ dup_mem_cells_conDup)

end Comb

end INet
