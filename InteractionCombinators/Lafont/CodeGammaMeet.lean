import InteractionCombinators.Lafont.CodeCellsMeet
import InteractionCombinators.Lafont.CodeShift
import InteractionCombinators.Lafont.Fig7End

/-!
# The packages `Γ_{α,β}`, `Γ_{β,α}` of Fig. 10 against their multiplexors (pages 89–90)

Lafont 1997, Section 2.6, Fig. 10 (journal page 89, PDF page 21) and page 90, where the analogue
of Fig. 7 (page 86) is left to the reader. This file does the last rows of that analogue, as
`mux_gamma_mux_gamma` (`Fig7End.lean`) does them for Fig. 7. After the two cells `[α]`, `[β]` have
met (`codeCells_meet`), the multiplexor `M_{a+2}` of `[α]` faces the package `Γ_{α,β}` and the
multiplexor `M_{b+2}` of `[β]` faces `Γ_{β,α}`, the two multiplexors sharing the loop `ℓ`. Each
multiplexor annihilates with the dual multiplexor of its package (`mux_muxStar`): the code `!Γ` of
each cell meets the copier `C_p` of the package, the ports of each cell meet the trees of `⟨φ⟩` on
its side, and the loop joins the two transpositors `T_σ`, which annihilate
(`transpositorPerm_transpositorPerm`): the middle port `l` of `⟨φ⟩` meets the middle port `σ l` of
`⟨ψ⟩`.

* `codeGamma_loop` — `M_{a+2}` with leaves `c`, `ts`, `ℓ` against `Γ_{α,β}`.
* `codeGamma_meet` — the last rows of the analogue of Fig. 7, at the level of trees, in a context
  `Δ`.
* `codeCells_meet_end` — the two cells `[α]`, `[β]` of Fig. 10 plugged by their roots, when the
  sides of `α` against `β` and of `β` against `α` have the same middle ports and involution:
  `codeCells_meet` followed by `codeGamma_meet`.
-/

namespace INet.Comb

open Term Translation

variable {S : Signature}

/-- **`M_{a+2}` against `Γ_{α,β}`, with any trees on the ports** (Fig. 10, page 89; the analogue of
Fig. 7, row 3, page 86). The multiplexor with leaves `c`, the `a` trees `ts` and the loop `ℓ`
against the package `Γ_{α,β}` of a side `φ` reduces, in any context `Δ`, to `c` against the copier
`C_p`, the loop against the transpositor `T_σ` on the trees of `⟨φ⟩` at the middle ports, and each
`ts[p]` against the tree of `⟨φ⟩` at the port `p`. -/
theorem codeGamma_loop (m : ℕ) (idx : S.Sym → ℕ) {a k : ℕ} (φ : Rule S a k)
    (σ : Equiv.Perm (Fin k)) (hσ : Function.Involutive σ) (k₀ : ℕ) (c : Term sig ℕ)
    (ts : List (Term sig ℕ)) (hts : ts.length = a) (ℓ : ℕ) (Δ : CNet) :
    Red (s(mux (c :: ts ++ [var ℓ]), codeGamma m idx φ σ hσ k₀) ::ₘ Δ)
      (s(c, copier (codeGammaExtras m idx φ k₀)) ::ₘ
        s(var ℓ, transpositorPerm σ hσ (fun j => codePort m idx φ k₀ (.inr j))) ::ₘ
        ((Finset.univ.val.map fun p : Fin a =>
          s(ts[(p : ℕ)]'(hts ▸ p.2), codePort m idx φ k₀ (.inl p))) + Δ)) := by
  have hlen : (c :: ts ++ [var ℓ]).length =
      (copier (codeGammaExtras m idx φ k₀) ::
        (List.ofFn (fun i => codePort m idx φ k₀ (.inl i)) ++
          [transpositorPerm σ hσ (fun j => codePort m idx φ k₀ (.inr j))])).length := by
    simp [hts]
  refine (mux_muxStar _ _ Δ hlen).cast rfl ?_
  rw [List.cons_append, List.zipWith_cons_cons, List.zipWith_append (by simp [hts]),
    ← Multiset.cons_coe, ← Multiset.coe_add, coe_zipWith_ofFn ts hts]
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, ← Multiset.cons_coe,
    Multiset.coe_nil]
  ms

/-- **The last rows of the analogue of Fig. 7 for Fig. 10** (Lafont 1997, pages 89–90; Fig. 7,
page 86). The multiplexor `M_{a+2}` with leaves `c`, `ts` and `ℓ` against the package `Γ_{α,β}` of
a side `φ`, and `M_{b+2}` with leaves `c'`, `us` and the same `ℓ` against the package `Γ_{β,α}` of a
side `ψ` with the same involution `σ` of the `k` middle ports, reduce up to wires to: `c` against
the copier `C_p` of `Γ_{α,β}`, `c'` against the copier of `Γ_{β,α}`, the tree `ts[p]` against the
tree of `⟨φ⟩` at its port `p`, the tree `us[q]` against the tree of `⟨ψ⟩` at its port `q`, and the
tree of `⟨φ⟩` at the middle port `l` against the tree of `⟨ψ⟩` at the middle port `σ l`.

No hypothesis on `φ` and `ψ` is needed beyond linearity of the whole net. -/
theorem codeGamma_meet (m : ℕ) (idx : S.Sym → ℕ) {a b k : ℕ} (φ : Rule S a k)
    (ψ : Rule S b k) (σ : Equiv.Perm (Fin k)) (hσ : Function.Involutive σ) (k₀ k₁ : ℕ)
    (c c' : Term sig ℕ) (ts us : List (Term sig ℕ)) (hts : ts.length = a)
    (hus : us.length = b) (ℓ : ℕ) (Δ : CNet)
    (hlin : Net.Linear (s(mux (c :: ts ++ [var ℓ]), codeGamma m idx φ σ hσ k₀) ::ₘ
      s(mux (c' :: us ++ [var ℓ]), codeGamma m idx ψ σ hσ k₁) ::ₘ Δ)) :
    ∃ M, StepsE system (s(mux (c :: ts ++ [var ℓ]), codeGamma m idx φ σ hσ k₀) ::ₘ
        s(mux (c' :: us ++ [var ℓ]), codeGamma m idx ψ σ hσ k₁) ::ₘ Δ) M ∧
      Equiv M (s(c, copier (codeGammaExtras m idx φ k₀)) ::ₘ
        s(c', copier (codeGammaExtras m idx ψ k₁)) ::ₘ
        ((Finset.univ.val.map fun p : Fin a =>
            s(ts[(p : ℕ)]'(hts ▸ p.2), codePort m idx φ k₀ (.inl p))) +
          (Finset.univ.val.map fun q : Fin b =>
            s(us[(q : ℕ)]'(hus ▸ q.2), codePort m idx ψ k₁ (.inl q))) +
          (Finset.univ.val.map fun l : Fin k =>
            s(codePort m idx φ k₀ (.inr l), codePort m idx ψ k₁ (.inr (σ l)))) + Δ)) := by
  set Tφ := transpositorPerm σ hσ (fun j => codePort m idx φ k₀ (.inr j)) with hTφ
  set Tψ := transpositorPerm σ hσ (fun j => codePort m idx ψ k₁ (.inr j)) with hTψ
  set Cφ := copier (codeGammaExtras m idx φ k₀) with hCφ
  set Cψ := copier (codeGammaExtras m idx ψ k₁) with hCψ
  set Xφ : CNet := Finset.univ.val.map fun p : Fin a =>
    s(ts[(p : ℕ)]'(hts ▸ p.2), codePort m idx φ k₀ (.inl p)) with hXφ
  set Xψ : CNet := Finset.univ.val.map fun q : Fin b =>
    s(us[(q : ℕ)]'(hus ▸ q.2), codePort m idx ψ k₁ (.inl q)) with hXψ
  set Y : CNet := Finset.univ.val.map fun l : Fin k =>
    s(codePort m idx φ k₀ (.inr l), codePort m idx ψ k₁ (.inr (σ l))) with hY
  -- the first multiplexor meets its dual
  have h1 := codeGamma_loop m idx φ σ hσ k₀ c ts hts ℓ
    (s(mux (c' :: us ++ [var ℓ]), codeGamma m idx ψ σ hσ k₁) ::ₘ Δ)
  -- the second multiplexor meets its dual
  have h2 := codeGamma_loop m idx ψ σ hσ k₁ c' us hus ℓ
    (s(c, Cφ) ::ₘ s(var ℓ, Tφ) ::ₘ (Xφ + Δ))
  set R : CNet := s(c, Cφ) ::ₘ s(c', Cψ) ::ₘ (Xφ + Xψ + Δ) with hR
  have h12 : Red (s(mux (c :: ts ++ [var ℓ]), codeGamma m idx φ σ hσ k₀) ::ₘ
      s(mux (c' :: us ++ [var ℓ]), codeGamma m idx ψ σ hσ k₁) ::ₘ Δ)
      (s(Tφ, var ℓ) ::ₘ s(var ℓ, Tψ) ::ₘ R) := by
    refine h1.trans (h2.cast (by rw [← hTφ, ← hXφ, ← hCφ]; ms) ?_)
    rw [← hTψ, ← hXψ, ← hCψ, hR, Sym2.eq_swap (a := Tφ)]
    ms
  have L2 : Net.Linear (s(Tφ, var ℓ) ::ₘ s(var ℓ, Tψ) ::ₘ R) :=
    h12.linear system_wellFormed.linear hlin
  -- the loop joins the two transpositors
  have E := equiv_contract Tφ Tψ ℓ R L2
  -- the transpositors annihilate
  have h3 := transpositorPerm_transpositorPerm σ hσ (fun j => codePort m idx φ k₀ (.inr j))
    (fun j => codePort m idx ψ k₁ (.inr j)) R
  obtain ⟨M, hS, hE⟩ := stepsE_of_equiv E h3.stepsE
  refine ⟨M, h12.stepsE.trans hS, hE.trans (Equiv.of_eq ?_)⟩
  rw [← hY, hR]
  ms

/-! ## From the two cells to the end -/

/-- The package `Γ_{α,β}` met by `[α]` in `codeCells_meet`, renamed by `codeRen ys K'`, is the
package `Γ_{α,β}` numbered from `K' + B` (page 89), when the side of `α` against `β` exists. -/
theorem codeGammaOpt_bind_codeRen {a n k : ℕ} (o : Option (ExpSide S a)) (φ : Rule S a k)
    (σ : Equiv.Perm (Fin k)) (hl : φ.Linear) (he : φ.Expanded) (hσ : Function.Involutive σ)
    (ho : o = some ⟨k, φ, σ, hl, he, hσ⟩) (m : ℕ) (idx : S.Sym → ℕ) (ys : Fin n → ℕ)
    (K' B : ℕ) (hB : n ≤ B) :
    (codeGammaOpt m idx o B).bind (fun x => var (codeRen ys K' x)) =
      codeGamma m idx φ σ hσ (K' + B) := by
  subst ho
  refine codeGamma_shift m idx φ σ hσ _ B (K' + B) fun i => ?_
  simp only [codeRen, show ¬ B + i < n by omega, dite_false]
  omega

variable [Finite S.Sym] (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α)))

/-- **Two cells `[α]`, `[β]` of Fig. 10 plugged by their roots, to the end** (Lafont 1997, Fig. 10,
pages 89–90; the analogue of the whole of Fig. 7, page 86). Let the side of `α` against `β` be a
side `φ` and the side of `β` against `α` a side `ψ`, both with the same `k` middle ports and the
same involution `σ`. With the names `xs`, `ys` on the ports of `[α]`, `[β]`, any names of their
internal wires, in a context `Δ` with the whole net linear, the net reduces up to wires to:

* the code `!Γ` of `[α]` (renamed by `codeRen xs K`) against the copier `C_p` of `Γ_{α,β}`, and
  the code of `[β]` (renamed by `codeRen ys K'`) against the copier of `Γ_{β,α}`;
* each port `xs p` against the tree of `⟨φ⟩` at the port `p`, and each `ys q` against the tree of
  `⟨ψ⟩` at the port `q`;
* the tree of `⟨φ⟩` at the middle port `l` against the tree of `⟨ψ⟩` at the middle port `σ l`.

The package `Γ_{α,β}` is numbered from `K' + S.arity β + 1 + off (codeCellSizes side β) α`, its
place in the menu of `[β]` shifted by `K'`, and `Γ_{β,α}` likewise from `K + …`, the bounds `K`,
`K'` being those of `codeCells_meet`. It composes `codeCells_meet` with `codeGamma_meet`. -/
theorem codeCells_meet_end (α β : S.Sym) (xs : Fin (S.arity α) → ℕ) (ys : Fin (S.arity β) → ℕ)
    (f : Fin (codeNet side α).internal → ℕ) (g : Fin (codeNet side β).internal → ℕ) (Δ : CNet)
    {k : ℕ} (φ : Rule S (S.arity α) k) (ψ : Rule S (S.arity β) k) (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ) (hl : φ.Linear) (he : φ.Expanded) (hl' : ψ.Linear)
    (he' : ψ.Expanded) (hs : side α β = some ⟨k, φ, σ, hl, he, hσ⟩)
    (hs' : side β α = some ⟨k, ψ, σ, hl', he', hσ⟩)
    (hlin : Net.Linear (s((codeNet side α).inst (fun i => var (xs i)) f,
      (codeNet side β).inst (fun j => var (ys j)) g) ::ₘ Δ)) :
    ∃ (K K' : ℕ) (M : CNet),
      StepsE system (s((codeNet side α).inst (fun i => var (xs i)) f,
        (codeNet side β).inst (fun j => var (ys j)) g) ::ₘ Δ) M ∧
      Equiv M
        (s((code (codeKey side α) (menu (codeMenus side (codeMenuBase side α)))).bind
              (fun x => var (codeRen xs K x)),
            copier (codeGammaExtras (Nat.card S.Sym) (fun γ => symEnum S γ) φ
              (K' + (S.arity β + 1 + off (codeCellSizes side β) (symEnum S α))))) ::ₘ
          s((code (codeKey side β) (menu (codeMenus side (codeMenuBase side β)))).bind
              (fun x => var (codeRen ys K' x)),
            copier (codeGammaExtras (Nat.card S.Sym) (fun γ => symEnum S γ) ψ
              (K + (S.arity α + 1 + off (codeCellSizes side α) (symEnum S β))))) ::ₘ
          ((Finset.univ.val.map fun p : Fin (S.arity α) =>
              s(var (xs p), codePort (Nat.card S.Sym) (fun γ => symEnum S γ) φ
                (K' + (S.arity β + 1 + off (codeCellSizes side β) (symEnum S α))) (.inl p))) +
            (Finset.univ.val.map fun q : Fin (S.arity β) =>
              s(var (ys q), codePort (Nat.card S.Sym) (fun γ => symEnum S γ) ψ
                (K + (S.arity α + 1 + off (codeCellSizes side α) (symEnum S β))) (.inl q))) +
            (Finset.univ.val.map fun l : Fin k =>
              s(codePort (Nat.card S.Sym) (fun γ => symEnum S γ) φ
                  (K' + (S.arity β + 1 + off (codeCellSizes side β) (symEnum S α))) (.inr l),
                codePort (Nat.card S.Sym) (fun γ => symEnum S γ) ψ
                  (K + (S.arity α + 1 + off (codeCellSizes side α) (symEnum S β)))
                  (.inr (σ l)))) + Δ)) := by
  obtain ⟨K, K', M1, hS1, hE1⟩ := codeCells_meet side α β xs ys f g Δ hlin
  rw [codeGammaOpt_bind_codeRen _ φ σ hl he hσ hs _ _ ys K' _ (by omega),
    codeGammaOpt_bind_codeRen _ ψ σ hl' he' hσ hs' _ _ xs K _ (by omega)] at hE1
  have L1 := hE1.linear (hS1.linear system_wellFormed.linear hlin)
  obtain ⟨M2, hS2, hE2⟩ := codeGamma_meet (Nat.card S.Sym) (fun γ => symEnum S γ) φ ψ σ hσ _ _ _ _
    _ _ (List.length_ofFn) (List.length_ofFn) _ Δ L1
  obtain ⟨M3, hS3, hE3⟩ := stepsE_of_equiv hE1 hS2
  refine ⟨K, K', M3, hS1.trans hS3, hE3.trans (hE2.trans (Equiv.of_eq ?_))⟩
  simp only [List.getElem_ofFn]

end INet.Comb
