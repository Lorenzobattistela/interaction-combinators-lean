import InteractionCombinators.Lafont.Gamma
import InteractionCombinators.Lafont.CellSkeleton

/-!
# Lafont, "Interaction Combinators" (1997): the end of Fig. 7 (page 86)

Page 86 (PDF page 18), Section 2.4, Fig. 7, last rows. After the first rows
(`cellSkel_cellSkel`), the multiplexor `M_{nᵢ+1}` of `[αᵢ]` faces the package `Γ_{i,j}` and
`M_{nⱼ+1}` of `[αⱼ]` faces `Γ_{j,i}`, the two multiplexors sharing the loop `ℓ`. Each `M_{n+1}`
annihilates with the dual multiplexor `M*_{n+1}` of its package (`mux_muxStar`): the auxiliary
trees of each cell meet the trees of `[φ]` at the ports on its side, and the loop `ℓ` joins the two
transpositors `T_σ`, which annihilate (`transpositorPerm_transpositorPerm`): the middle port `l`
of `[φ_{i,j}]` meets the middle port `σ l` of `[φ_{j,i}]`.

* `mux_gamma_mux_gamma` — the last rows of Fig. 7, at the level of trees, in a context `Δ`.
* `cellSkel_gamma_cellSkel_gamma` — the whole of Fig. 7: `[αᵢ] ⋈ [αⱼ]` reduces to the same net.
* `Fig7EndCheck.mux_gamma_mux_gamma_dupDup` and `Fig7EndCheck.cellSkel_dupDup` — instances on the
  side `φ₀` of `GammaCheck`, whose hypotheses are proved.

Relating the resulting net to the translation of `Rule.plug φ ψ σ` is not done here.
-/

namespace INet.Comb

open Term

/-- The equations between a list `ts` of length `a` and the leaves `f 0, …, f (a-1)`, as a
multiset indexed by `Fin a`. -/
theorem coe_zipWith_ofFn {a : ℕ} (ts : List (Term sig ℕ)) (hts : ts.length = a)
    (f : Fin a → Term sig ℕ) :
    ((List.zipWith (fun t u => s(t, u)) ts (List.ofFn f) : List _) : CNet) =
      Finset.univ.val.map fun p : Fin a => s(ts[(p : ℕ)]'(hts ▸ p.2), f p) := by
  subst hts
  rw [Fin.univ_val_map]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

/-- `M_{a+1}` against the package `Γ` of an `a`-port side: the first `a` trees meet the trees of
`[φ]` at the ports `.inl p`, and the last one, `var ℓ`, meets the transpositor `T_σ` (Fig. 7,
page 86). -/
theorem mux_gamma_loop (Φ : Translation S sig) {a k : ℕ} (φ : Rule S a k)
    (σ : Equiv.Perm (Fin k)) (hσ : Function.Involutive σ) (k₀ : ℕ) (ts : List (Term sig ℕ)) (hts : ts.length = a)
    (ℓ : ℕ) (Δ : CNet) :
    Red (s(mux (ts ++ [var ℓ]), gamma Φ φ σ hσ k₀) ::ₘ Δ)
      (s(var ℓ, transpositorPerm σ hσ (fun j => gammaPort Φ φ k₀ (.inr j))) ::ₘ
        ((Finset.univ.val.map fun p : Fin a =>
          s(ts[(p : ℕ)]'(hts ▸ p.2), gammaPort Φ φ k₀ (.inl p))) + Δ)) := by
  have hlen : (ts ++ [var ℓ]).length =
      (List.ofFn (fun i => gammaPort Φ φ k₀ (.inl i)) ++
        [transpositorPerm σ hσ (fun j => gammaPort Φ φ k₀ (.inr j))]).length := by
    simp [hts]
  refine (mux_muxStar _ _ Δ hlen).cast rfl ?_
  rw [List.zipWith_append (by simp [hts]), ← Multiset.coe_add, coe_zipWith_ofFn ts hts]
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, ← Multiset.cons_coe,
    Multiset.coe_nil]
  ms

/-- **The last rows of Fig. 7** (Lafont 1997, page 86). The multiplexor `M_{a+1}` with leaves `ts`
and `ℓ` against the package `Γ` of a side `φ`, and `M_{b+1}` with leaves `us` and the same `ℓ`
against the package `Γ` of a side `ψ` with the same involution `σ` of the `k` middle ports, reduce
up to wires to: the tree `ts[p]` against the tree of `[φ]` at its port `p`, the tree `us[q]`
against the tree of `[ψ]` at its port `q`, and the tree of `[φ]` at the middle port `l` against the
tree of `[ψ]` at the middle port `σ l`.

The two multiplexors annihilate with their duals (`mux_muxStar`), the loop `ℓ` joins the two
transpositors (`equiv_contract`), and these annihilate (`transpositorPerm_transpositorPerm`). No
hypothesis on `φ` and `ψ` is needed beyond linearity of the whole net. -/
theorem mux_gamma_mux_gamma (Φ : Translation S sig) {a b k : ℕ} (φ : Rule S a k)
    (ψ : Rule S b k) (σ : Equiv.Perm (Fin k)) (hσ : Function.Involutive σ) (k₀ k₁ : ℕ)
    (ts us : List (Term sig ℕ)) (hts : ts.length = a) (hus : us.length = b) (ℓ : ℕ) (Δ : CNet)
    (hlin : Net.Linear (s(mux (ts ++ [var ℓ]), gamma Φ φ σ hσ k₀) ::ₘ
      s(mux (us ++ [var ℓ]), gamma Φ ψ σ hσ k₁) ::ₘ Δ)) :
    ∃ M, StepsE system (s(mux (ts ++ [var ℓ]), gamma Φ φ σ hσ k₀) ::ₘ
        s(mux (us ++ [var ℓ]), gamma Φ ψ σ hσ k₁) ::ₘ Δ) M ∧
      Equiv M ((Finset.univ.val.map fun p : Fin a =>
          s(ts[(p : ℕ)]'(hts ▸ p.2), gammaPort Φ φ k₀ (.inl p))) +
        (Finset.univ.val.map fun q : Fin b =>
          s(us[(q : ℕ)]'(hus ▸ q.2), gammaPort Φ ψ k₁ (.inl q))) +
        (Finset.univ.val.map fun l : Fin k =>
          s(gammaPort Φ φ k₀ (.inr l), gammaPort Φ ψ k₁ (.inr (σ l)))) + Δ) := by
  set Tφ := transpositorPerm σ hσ (fun j => gammaPort Φ φ k₀ (.inr j)) with hTφ
  set Tψ := transpositorPerm σ hσ (fun j => gammaPort Φ ψ k₁ (.inr j)) with hTψ
  set Xφ : CNet := Finset.univ.val.map fun p : Fin a =>
    s(ts[(p : ℕ)]'(hts ▸ p.2), gammaPort Φ φ k₀ (.inl p)) with hXφ
  set Xψ : CNet := Finset.univ.val.map fun q : Fin b =>
    s(us[(q : ℕ)]'(hus ▸ q.2), gammaPort Φ ψ k₁ (.inl q)) with hXψ
  set Y : CNet := Finset.univ.val.map fun l : Fin k =>
    s(gammaPort Φ φ k₀ (.inr l), gammaPort Φ ψ k₁ (.inr (σ l))) with hY
  -- the first multiplexor meets its dual
  have h1 := mux_gamma_loop Φ φ σ hσ k₀ ts hts ℓ
    (s(mux (us ++ [var ℓ]), gamma Φ ψ σ hσ k₁) ::ₘ Δ)
  -- the second multiplexor meets its dual
  have h2 := mux_gamma_loop Φ ψ σ hσ k₁ us hus ℓ (s(var ℓ, Tφ) ::ₘ (Xφ + Δ))
  set R : CNet := Xφ + Xψ + Δ with hR
  have h12 : Red (s(mux (ts ++ [var ℓ]), gamma Φ φ σ hσ k₀) ::ₘ
      s(mux (us ++ [var ℓ]), gamma Φ ψ σ hσ k₁) ::ₘ Δ) (s(Tφ, var ℓ) ::ₘ s(var ℓ, Tψ) ::ₘ R) := by
    refine h1.trans (h2.cast (by rw [← hTφ, ← hXφ]; ms) ?_)
    rw [← hTψ, ← hXψ, hR, Sym2.eq_swap (a := Tφ)]
    ms
  have L2 : Net.Linear (s(Tφ, var ℓ) ::ₘ s(var ℓ, Tψ) ::ₘ R) :=
    h12.linear system_wellFormed.linear hlin
  -- the loop joins the two transpositors
  have E := equiv_contract Tφ Tψ ℓ R L2
  -- the transpositors annihilate
  have h3 := transpositorPerm_transpositorPerm σ hσ (fun j => gammaPort Φ φ k₀ (.inr j))
    (fun j => gammaPort Φ ψ k₁ (.inr j)) R
  obtain ⟨M, hS, hE⟩ := stepsE_of_equiv E h3.stepsE
  refine ⟨M, h12.stepsE.trans hS, hE.trans (Equiv.of_eq ?_)⟩
  rw [← hY, hR]
  ms

/-- **Fig. 7** (Lafont 1997, page 86), from the cells to the end. Two cells `[αᵢ]` and `[αⱼ]` of
Fig. 6 with menus `Gi`, `Gj` of packages, plugged by their roots in a context `Δ`, where the package
`Gj[i]` is `Γ` of a side `φ` of `a` ports and `Gi[j]` is `Γ` of a side `ψ` of `b` ports, both with
the involution `σ` of the `k` middle ports: the net reduces up to wires to the equations between
the trees `ts` and the trees of `[φ]` at its ports, between the trees `us` and the trees of `[ψ]` at
its ports, and between the middle port `l` of `[φ]` and the middle port `σ l` of `[ψ]`.

It composes `cellSkel_cellSkel` (first rows) with `mux_gamma_mux_gamma` (last rows). -/
theorem cellSkel_gamma_cellSkel_gamma (Φ : Translation S sig) {a b k : ℕ} (φ : Rule S a k)
    (ψ : Rule S b k) (σ : Equiv.Perm (Fin k)) (hσ : Function.Involutive σ) (k₀ k₁ : ℕ)
    (Gi Gj : List (Term sig ℕ)) (m i j : ℕ) (hGi : Gi.length = m) (hGj : Gj.length = m)
    (hi : i < m) (hj : j < m) (hpi : ∀ π ∈ Gi, π.IsPackage) (hpj : ∀ π ∈ Gj, π.IsPackage)
    (hGji : Gj[i]'(hGj ▸ hi) = gamma Φ φ σ hσ k₀) (hGij : Gi[j]'(hGi ▸ hj) = gamma Φ ψ σ hσ k₁)
    (ts us : List (Term sig ℕ)) (hts : ts.length = a) (hus : us.length = b) (ℓ ℓ' : ℕ)
    (Δ : CNet)
    (hlin : Net.Linear (s(cellSkel (menu Gi) m i ts ℓ, cellSkel (menu Gj) m j us ℓ') ::ₘ Δ)) :
    ∃ M, StepsE system (s(cellSkel (menu Gi) m i ts ℓ, cellSkel (menu Gj) m j us ℓ') ::ₘ Δ) M ∧
      Equiv M ((Finset.univ.val.map fun p : Fin a =>
          s(ts[(p : ℕ)]'(hts ▸ p.2), gammaPort Φ φ k₀ (.inl p))) +
        (Finset.univ.val.map fun q : Fin b =>
          s(us[(q : ℕ)]'(hus ▸ q.2), gammaPort Φ ψ k₁ (.inl q))) +
        (Finset.univ.val.map fun l : Fin k =>
          s(gammaPort Φ φ k₀ (.inr l), gammaPort Φ ψ k₁ (.inr (σ l)))) + Δ) := by
  obtain ⟨M1, hS1, hE1⟩ :=
    cellSkel_cellSkel Gi Gj m i j hGi hGj hi hj hpi hpj ts us ℓ ℓ' Δ hlin
  rw [hGji, hGij] at hE1
  have L1 := hE1.linear (hS1.linear system_wellFormed.linear hlin)
  obtain ⟨M2, hS2, hE2⟩ := mux_gamma_mux_gamma Φ φ ψ σ hσ k₀ k₁ ts us hts hus ℓ Δ L1
  obtain ⟨M3, hS3, hE3⟩ := stepsE_of_equiv hE1 hS2
  exact ⟨M3, hS1.trans hS3, hE3.trans hE2⟩

end INet.Comb
