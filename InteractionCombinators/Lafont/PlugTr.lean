import InteractionCombinators.Lafont.Fig7End
import InteractionCombinators.Lafont.Decomposition
import InteractionCombinators.NetTrWire

/-!
# The net reached by Fig. 7 is a translation of the plugged rule (page 86)

Lafont 1997, Section 2.4, journal page 86 (PDF page 18), end of Fig. 7. After the two `T_σ`
annihilate, what is left is `[φ_{i,j}]` and `[φ_{j,i}]` joined through `σ`: "a translation of the
right-hand side". Here the right-hand side is the plugged rule `Rule.plug φ ψ σ` of page 85, in
which the middle wire `l` of `φ` is joined to the middle wire `σ l` of `ψ`.

* `plugTarget Φ φ ψ σ k₀ k₁ xs ys` — the net reached at the end of Fig. 7 (the conclusion of
  `mux_gamma_mux_gamma` with the names `xs`, `ys` on the auxiliary ports and an empty context).
* `equiv_contract_map` — several wires `P = x`, `x = t` removed at once.
* `netTr_plug_gamma` — **`plugTarget` is, up to wires, a translation of an instance of
  `Rule.plug φ ψ σ`**, for linear sides in expanded form.
* `mux_gamma_mux_gamma_ofFn` — the conclusion net of `mux_gamma_mux_gamma` with
  `ts = List.ofFn (var ∘ xs)`, `us = List.ofFn (var ∘ ys)` and `Δ = 0` is `plugTarget`.
* `mux_gamma_mux_gamma_netTr` — the two together: the last rows of Fig. 7 reduce to a net
  equivalent to a translation of an instance of `Rule.plug φ ψ σ`.
-/

namespace INet.Comb

open Term Translation ExpandedIso

variable {S : Signature}

/-- **The net at the end of Fig. 7** (Lafont 1997, page 86): the name `xs p` against the tree of
`[φ]` at its port `p`, the name `ys q` against the tree of `[ψ]` at its port `q`, and the tree of
`[φ]` at the middle port `l` against the tree of `[ψ]` at the middle port `σ l`. -/
noncomputable def plugTarget (Φ : Translation S sig) {a b k : ℕ} (φ : Rule S a k)
    (ψ : Rule S b k) (σ : Equiv.Perm (Fin k)) (k₀ k₁ : ℕ) (xs : Fin a → ℕ) (ys : Fin b → ℕ) :
    CNet :=
  (Finset.univ.val.map fun p : Fin a => s(var (xs p), gammaPort Φ φ k₀ (.inl p))) +
    (Finset.univ.val.map fun q : Fin b => s(var (ys q), gammaPort Φ ψ k₁ (.inl q))) +
    (Finset.univ.val.map fun l : Fin k =>
      s(gammaPort Φ φ k₀ (.inr l), gammaPort Φ ψ k₁ (.inr (σ l))))

/-- Several wires removed at once (page 70): the equations `P i = x i` and `x i = t i`, for `i`
in `L`, are the equations `P i = t i`. -/
theorem equiv_contract_map {ι : Type} (L : Multiset ι) (x : ι → ℕ) (P t : ι → Term sig ℕ)
    (R : CNet)
    (hlin : Net.Linear (L.map (fun i => s(P i, var (x i))) +
      L.map (fun i => s(var (x i), t i)) + R)) :
    Equiv (L.map (fun i => s(P i, var (x i))) + L.map (fun i => s(var (x i), t i)) + R)
      (L.map (fun i => s(P i, t i)) + R) := by
  induction L using Multiset.induction_on generalizing R with
  | empty =>
    simp only [Multiset.map_zero, zero_add]
    exact Equiv.refl R
  | cons i L ih =>
    have e1 : ((i ::ₘ L).map (fun i => s(P i, var (x i))) +
        (i ::ₘ L).map (fun i => s(var (x i), t i)) + R : CNet) =
        s(P i, var (x i)) ::ₘ s(var (x i), t i) ::ₘ (L.map (fun i => s(P i, var (x i))) +
          L.map (fun i => s(var (x i), t i)) + R) := by
      simp only [Multiset.map_cons]
      ms
    rw [e1] at hlin ⊢
    have E1 := equiv_contract (P i) (t i) (x i) _ hlin
    have e2 : (s(P i, t i) ::ₘ (L.map (fun i => s(P i, var (x i))) +
        L.map (fun i => s(var (x i), t i)) + R) : CNet) =
        L.map (fun i => s(P i, var (x i))) + L.map (fun i => s(var (x i), t i)) +
          (s(P i, t i) ::ₘ R) := by
      ms
    have E2 := ih (s(P i, t i) ::ₘ R) ((E1.linear hlin).cast e2)
    refine E1.trans ((Equiv.of_eq e2).trans (E2.trans (Equiv.of_eq ?_)))
    simp only [Multiset.map_cons]
    ms

/-- The names of a net given as a map. -/
theorem vars_map_net {ι : Type} (L : Multiset ι) (f : ι → Sym2 (Term sig ℕ)) :
    Net.vars (L.map f) = L.bind fun i => eqVars (f i) := by
  simp [Net.vars, Multiset.bind_map]

/-- A map over `α ⊕ β` splits into the two maps. -/
theorem map_univ_sum {α β γ : Type} [Fintype α] [Fintype β] (f : α ⊕ β → γ) :
    (Finset.univ.val.map f) =
      Finset.univ.val.map (fun x => f (.inl x)) + Finset.univ.val.map (fun y => f (.inr y)) := by
  rw [← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.map_disjSum]

/-- A linear side in expanded form, with its ports named by `M` and its internal wire `w` named
`k₀ + w` (by `g`), is the equations `M p = gammaTree φ k₀ p` (pages 85–86). -/
theorem bind_expanded {a k : ℕ} {φ : Rule S a k} (he : φ.Expanded) (hl : φ.Linear)
    (g : Fin a ⊕ Fin k ⊕ Fin φ.internal → Term S ℕ) (M : Fin a ⊕ Fin k → ℕ) (k₀ : ℕ)
    (hM : ∀ p, g (port p) = var (M p))
    (hw : ∀ w : Fin φ.internal, g (.inr (.inr w)) = var (k₀ + w)) :
    φ.net.bind g = Finset.univ.val.map fun p => s(var (M p), gammaTree φ k₀ p) := by
  obtain ⟨hN, hT⟩ := he.net_eq_portTree hl
  rw [hN]
  unfold Net.bind
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun p _ => ?_
  simp only [Function.comp_apply, Sym2.map_mk]
  rw [gammaTree_eq_portTree he hl]
  congr 1
  · exact hM p
  refine Term.bind_congr fun x hx => ?_
  obtain ⟨w, rfl⟩ := hT p x hx
  rw [hw]
  rfl

/-- **The net at the end of Fig. 7 is a translation of the plugged rule** (Lafont 1997, page 86;
the plugged rule, page 85). For linear sides `φ`, `ψ` in expanded form and any permutation `σ` of
the middle wires, if `plugTarget` is linear then it is, up to wires, a translation of an instance
of `Rule.plug φ ψ σ` with the names `xs` on the ports of `φ` and `ys` on those of `ψ`.

The internal wire `w` of `φ` is named `k₀ + w`, that of `ψ` is named `k₁ + w`, as in `gammaPort`,
and the middle wire `l` gets a fresh name `B + l`. The translation is taken equation by equation;
the fresh middle wires are then removed (`equiv_contract_map`). -/
theorem netTr_plug_gamma (Φ : Translation S sig) {a b k : ℕ} {φ : Rule S a k}
    {ψ : Rule S b k} (hφe : φ.Expanded) (hφl : φ.Linear) (hψe : ψ.Expanded)
    (hψl : ψ.Linear) (σ : Equiv.Perm (Fin k)) (k₀ k₁ : ℕ)
    (xs : Fin a → ℕ) (ys : Fin b → ℕ)
    (hlin : Net.Linear (plugTarget Φ φ ψ σ k₀ k₁ xs ys)) :
    ∃ (h : Fin (Rule.plug φ ψ σ).internal → ℕ) (N' : CNet),
      Φ.NetTr ((Rule.plug φ ψ σ).inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N' ∧
      Equiv N' (plugTarget Φ φ ψ σ k₀ k₁ xs ys) := by
  set B := (plugTarget Φ φ ψ σ k₀ k₁ xs ys).vars.sup + 1 with hB
  let h : Fin (k + φ.internal + ψ.internal) → ℕ := fun i =>
    if (i : ℕ) < k then B + i else if (i : ℕ) < k + φ.internal then k₀ + (i - k)
    else k₁ + (i - (k + φ.internal))
  let Mφ : Fin a ⊕ Fin k → ℕ := Sum.elim xs fun l => B + l
  let Mψ : Fin b ⊕ Fin k → ℕ := Sum.elim ys fun l => B + (σ.symm l : ℕ)
  let G : Fin a ⊕ Fin b ⊕ Fin (k + φ.internal + ψ.internal) → Term S ℕ :=
    Sum.elim (fun i => .var (xs i)) (Sum.elim (fun j => .var (ys j)) fun i => .var (h i))
  -- the instance, equation by equation
  have hinst : (Rule.plug φ ψ σ).inst (fun i => .var (xs i)) (fun j => .var (ys j)) h =
      (Finset.univ.val.map fun p => s(var (Mφ p), gammaTree φ k₀ p)) +
        (Finset.univ.val.map fun q => s(var (Mψ q), gammaTree ψ k₁ q)) := by
    change Net.bind G (φ.net.bind (fun x => var (Rule.plugL x)) +
      ψ.net.bind (fun x => var (Rule.plugR σ x))) = _
    rw [show ∀ A C : Net S (Fin a ⊕ Fin b ⊕ Fin (k + φ.internal + ψ.internal)),
        Net.bind G (A + C) = Net.bind G A + Net.bind G C from
        fun A C => Multiset.map_add _ _ _, Net.bind_bind, Net.bind_bind]
    congr 1
    · refine bind_expanded hφe hφl _ Mφ k₀ ?_ ?_
      · rintro (i | l)
        · rfl
        · simp [port, Rule.plugL, G, h, Mφ]
      · intro w
        simp only [Rule.plugL, Term.bind, G, Sum.elim_inr, h, Fin.val_castAdd, Fin.val_natAdd]
        split_ifs <;> first | omega | (congr 1; omega)
    · refine bind_expanded hψe hψl _ Mψ k₁ ?_ ?_
      · rintro (j | l)
        · rfl
        · simp [port, Rule.plugR, G, h, Mψ]
      · intro w
        simp only [Rule.plugR, Term.bind, G, Sum.elim_inr, h, Fin.val_natAdd]
        split_ifs <;> first | omega | (congr 1; omega)
  have hrel : Multiset.Rel Φ.EqTr
      ((Rule.plug φ ψ σ).inst (fun i => .var (xs i)) (fun j => .var (ys j)) h)
      ((Finset.univ.val.map fun p => s(var (Mφ p), gammaPort Φ φ k₀ p)) +
        (Finset.univ.val.map fun q => s(var (Mψ q), gammaPort Φ ψ k₁ q))) := by
    rw [hinst]
    refine Multiset.Rel.add ?_ ?_ <;>
    · refine Multiset.rel_map.2 (Multiset.rel_refl_of_refl_on fun p _ => ?_)
      exact ⟨_, _, _, _, rfl, rfl, TermTr.var _, Φ.termTr_trTerm _ _⟩
  -- the same net, arranged for the removal of the middle wires
  have hT : (Finset.univ.val.map fun p => s(var (Mφ p), gammaPort Φ φ k₀ p)) +
      (Finset.univ.val.map fun q => s(var (Mψ q), gammaPort Φ ψ k₁ q)) =
      (Finset.univ.val.map fun l : Fin k => s(gammaPort Φ φ k₀ (.inr l), var (B + (l : ℕ)))) +
        (Finset.univ.val.map fun l : Fin k =>
          s(var (B + (l : ℕ)), gammaPort Φ ψ k₁ (.inr (σ l)))) +
        ((Finset.univ.val.map fun p : Fin a => s(var (xs p), gammaPort Φ φ k₀ (.inl p))) +
          (Finset.univ.val.map fun q : Fin b => s(var (ys q), gammaPort Φ ψ k₁ (.inl q)))) := by
    have h1 : (Finset.univ.val.map fun p => s(var (Mφ p), gammaPort Φ φ k₀ p)) =
        (Finset.univ.val.map fun p : Fin a => s(var (xs p), gammaPort Φ φ k₀ (.inl p))) +
          Finset.univ.val.map fun l : Fin k => s(gammaPort Φ φ k₀ (.inr l), var (B + (l : ℕ))) := by
      rw [map_univ_sum]
      congr 1
      exact Multiset.map_congr rfl fun l _ => Sym2.eq_swap
    have h2 : (Finset.univ.val.map fun q => s(var (Mψ q), gammaPort Φ ψ k₁ q)) =
        (Finset.univ.val.map fun q : Fin b => s(var (ys q), gammaPort Φ ψ k₁ (.inl q))) +
          Finset.univ.val.map fun l : Fin k =>
            s(var (B + (l : ℕ)), gammaPort Φ ψ k₁ (.inr (σ l))) := by
      rw [map_univ_sum]
      congr 1
      conv_lhs => rw [← Multiset.map_univ_val_equiv σ]
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun l _ => ?_
      simp [Mψ]
    rw [h1, h2]
    ms
  -- linearity: the middle wires are fresh
  have hlin' : Net.Linear
      ((Finset.univ.val.map fun l : Fin k => s(gammaPort Φ φ k₀ (.inr l), var (B + (l : ℕ)))) +
        (Finset.univ.val.map fun l : Fin k =>
          s(var (B + (l : ℕ)), gammaPort Φ ψ k₁ (.inr (σ l)))) +
        ((Finset.univ.val.map fun p : Fin a => s(var (xs p), gammaPort Φ φ k₀ (.inl p))) +
          (Finset.univ.val.map fun q : Fin b => s(var (ys q), gammaPort Φ ψ k₁ (.inl q))))) := by
    refine hlin.add_fresh (Finset.univ.val.map fun l : Fin k => B + (l : ℕ)) ?_ ?_ ?_
    · exact Finset.univ.nodup.map fun x y hxy => Fin.ext (by simpa using hxy)
    · intro x hx hmem
      obtain ⟨l, -, rfl⟩ := Multiset.mem_map.1 hx
      have := Multiset.le_sup hmem
      omega
    · simp only [plugTarget, Net.vars_add, vars_map_net, eqVars_mk, vars_var, Multiset.bind_add,
        Multiset.bind_singleton]
      abel
  have E := equiv_contract_map Finset.univ.val (fun l : Fin k => B + (l : ℕ))
    (fun l => gammaPort Φ φ k₀ (.inr l)) (fun l => gammaPort Φ ψ k₁ (.inr (σ l))) _ hlin'
  refine ⟨h, _, ⟨hrel, hlin'.cast hT.symm⟩, (Equiv.of_eq hT).trans (E.trans (Equiv.of_eq ?_))⟩
  simp only [plugTarget]
  ms

/-- **The bridge to `Fig7End`** (page 86): the net reached by `mux_gamma_mux_gamma` with the names
`xs` and `ys` on the auxiliary ports of the two cells and an empty context is `plugTarget`. -/
theorem mux_gamma_mux_gamma_ofFn (Φ : Translation S sig) {a b k : ℕ} (φ : Rule S a k)
    (ψ : Rule S b k) (σ : Equiv.Perm (Fin k)) (k₀ k₁ : ℕ) (xs : Fin a → ℕ) (ys : Fin b → ℕ) :
    (Finset.univ.val.map fun p : Fin a =>
        s((List.ofFn fun p => (var (xs p) : Term sig ℕ))[(p : ℕ)]'(by simp),
          gammaPort Φ φ k₀ (.inl p))) +
      (Finset.univ.val.map fun q : Fin b =>
        s((List.ofFn fun q => (var (ys q) : Term sig ℕ))[(q : ℕ)]'(by simp),
          gammaPort Φ ψ k₁ (.inl q))) +
      (Finset.univ.val.map fun l : Fin k =>
        s(gammaPort Φ φ k₀ (.inr l), gammaPort Φ ψ k₁ (.inr (σ l)))) + 0 =
      plugTarget Φ φ ψ σ k₀ k₁ xs ys := by
  simp [plugTarget]

/-- **The last rows of Fig. 7 reduce to a translation of the plugged rule** (Lafont 1997, page 86;
page 85 for `Rule.plug`). The multiplexors `M_{a+1}` with leaves `xs` and the loop `ℓ`, and
`M_{b+1}` with leaves `ys` and `ℓ`, against the packages `Γ` of linear sides `φ`, `ψ` in expanded
form with the involution `σ`, reduce up to wires to a translation of an instance of
`Rule.plug φ ψ σ` with the names `xs`, `ys` on its ports. It composes `mux_gamma_mux_gamma`,
`mux_gamma_mux_gamma_ofFn` and `netTr_plug_gamma`. -/
theorem mux_gamma_mux_gamma_netTr (Φ : Translation S sig) {a b k : ℕ} {φ : Rule S a k}
    {ψ : Rule S b k} (hφe : φ.Expanded) (hφl : φ.Linear) (hψe : ψ.Expanded)
    (hψl : ψ.Linear) (σ : Equiv.Perm (Fin k)) (hσ : Function.Involutive σ) (k₀ k₁ : ℕ)
    (xs : Fin a → ℕ) (ys : Fin b → ℕ) (ℓ : ℕ)
    (hlin : Net.Linear
      (s(mux (List.ofFn (fun p => (var (xs p) : Term sig ℕ)) ++ [var ℓ]), gamma Φ φ σ hσ k₀) ::ₘ
        s(mux (List.ofFn (fun q => (var (ys q) : Term sig ℕ)) ++ [var ℓ]), gamma Φ ψ σ hσ k₁) ::ₘ
          0)) :
    ∃ (M N' : CNet) (h : Fin (Rule.plug φ ψ σ).internal → ℕ),
      StepsE system
        (s(mux (List.ofFn (fun p => (var (xs p) : Term sig ℕ)) ++ [var ℓ]), gamma Φ φ σ hσ k₀) ::ₘ
          s(mux (List.ofFn (fun q => (var (ys q) : Term sig ℕ)) ++ [var ℓ]),
            gamma Φ ψ σ hσ k₁) ::ₘ 0) M ∧
      Equiv M N' ∧
      Φ.NetTr ((Rule.plug φ ψ σ).inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N' := by
  obtain ⟨M, hS, hE⟩ := mux_gamma_mux_gamma Φ φ ψ σ hσ k₀ k₁ _ _ (List.length_ofFn)
    (List.length_ofFn) ℓ 0 hlin
  rw [mux_gamma_mux_gamma_ofFn] at hE
  have L := hE.linear (hS.linear system_wellFormed.linear hlin)
  obtain ⟨h, N', hN', hE'⟩ := netTr_plug_gamma Φ hφe hφl hψe hψl σ k₀ k₁ xs ys L
  exact ⟨M, N', h, hS, hE.trans hE'.symm, hN'⟩

end INet.Comb
