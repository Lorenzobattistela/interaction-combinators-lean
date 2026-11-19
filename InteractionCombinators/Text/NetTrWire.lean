import InteractionCombinators.Text.NetTrEquiv
import InteractionCombinators.Text.TranslationExists

/-!
# The translation of a net follows the equivalence of the source net

Lafont 1997, Section 1.7, pages 79–80: a translation of a net replaces every cell by an instance
of the principal net of its symbol, "up to the names of the new wires". The paper treats a net as
a graph, so two spellings of the same graph have the same translation, as a graph.

* `Translation.TermTr.count_le` — a translation keeps every leaf of the source tree.
* `Translation.NetTr.count_le`, `Translation.NetTr.linear_source` — the same for a net, and so
  the source of a translation is linear.
* `Translation.TermTr.subst` — translation commutes with plugging a tree into a name, when that
  name is not an internal wire of an instance.
* `Translation.NetTr.wire` — a wire substitution in the source is followed by a wire substitution
  in the translation.
* `Translation.NetTr.of_equiv` — equivalent source nets have equivalent translations.
-/

namespace INet

variable {S S' : Signature}

open Term

namespace Translation

variable {Φ : Translation S S'}

/-- A translation keeps every leaf of the source tree: each name occurs in the translation at
least as often as in the tree (Lafont 1997, Section 1.7, pages 79–80). -/
theorem TermTr.count_le {t : Term S ℕ} {t' : Term S' ℕ} (h : Φ.TermTr t t') (y : ℕ) :
    t.vars.count y ≤ t'.vars.count y := by
  induction h with
  | var x => exact le_rfl
  | app α ts ts' f _ ih =>
    rw [PNet.count_vars_inst, Term.vars_app, Multiset.count_sum']
    exact (Finset.sum_le_sum fun i _ => ih i).trans (Nat.le_add_right _ _)

/-- A translation of a net keeps every name of the source net: each name occurs in the
translation at least as often as in the source (Lafont 1997, Section 1.7, page 80). -/
theorem NetTr.count_le {N : Net S ℕ} {N' : Net S' ℕ} (h : Φ.NetTr N N') (y : ℕ) :
    N.vars.count y ≤ N'.vars.count y := by
  have hrel := h.rel
  clear h
  induction hrel with
  | zero => simp
  | @cons e e' N N' he _ ih =>
    obtain ⟨c, d, c', d', rfl, rfl, hc, hd⟩ := he
    simp only [Net.vars_cons, eqVars_mk, Multiset.count_add]
    have := hc.count_le y
    have := hd.count_le y
    omega

/-- The source of a translation is linear (Lafont 1997, Section 1.7, page 80): the translation
keeps every name, and the translation is linear. -/
theorem NetTr.linear_source {N : Net S ℕ} {N' : Net S' ℕ} (h : Φ.NetTr N N') : N.Linear :=
  fun y => (h.count_le y).trans (h.linear y)

/-- Plugging a tree into a name of an instance that is not one of its internal wires plugs it
into the arguments. -/
theorem _root_.INet.PNet.inst_subst {n : ℕ} (p : PNet S' n) (args : Fin n → Term S' ℕ)
    (f : Fin p.internal → ℕ) (x : ℕ) (u : Term S' ℕ) (hf : ∀ w, f w ≠ x) :
    (p.inst args f).subst x u = p.inst (fun i => (args i).subst x u) f := by
  simp only [PNet.inst, Term.subst, Term.bind_bind]
  congr 1
  funext q
  cases q with
  | inl i => rfl
  | inr w => simp [hf w]

/-- **Translation commutes with substitution** (Lafont 1997, Section 1.7, pages 79–80). If `t'`
translates `t` and `u'` translates `u`, and the name `x` occurs in `t'` as often as in `t` (so it
names no internal wire of an instance of `t'`), then `t'.subst x u'` translates `t.subst x u`. -/
theorem TermTr.subst {t u : Term S ℕ} {t' u' : Term S' ℕ} (ht : Φ.TermTr t t')
    (hu : Φ.TermTr u u') {x : ℕ} (hx : t'.vars.count x = t.vars.count x) :
    Φ.TermTr (t.subst x u) (t'.subst x u') := by
  induction ht with
  | var y =>
    by_cases hy : y = x
    · subst hy; simpa [Term.subst] using hu
    · simpa [Term.subst, hy] using TermTr.var (Φ := Φ) y
  | app α ts ts' f hts ih =>
    rw [PNet.count_vars_inst, Term.vars_app, Multiset.count_sum'] at hx
    have hle : ∀ i, (ts i).vars.count x ≤ (ts' i).vars.count x := fun i => (hts i).count_le x
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hle i
    have heq : ∀ i, (ts' i).vars.count x = (ts i).vars.count x := by
      intro i
      have := (Finset.sum_eq_sum_iff_of_le fun j (_ : j ∈ Finset.univ) => hle j).1 (by omega) i
        (Finset.mem_univ _)
      exact this.symm
    have hf : ∀ w, f w ≠ x := by
      intro w hw
      have h0 : (∑ w, if x = f w then 1 else 0) = 0 := by omega
      have := (Finset.sum_eq_zero_iff.1 h0) w (Finset.mem_univ _)
      simp [hw] at this
    rw [PNet.inst_subst _ _ _ _ _ hf]
    exact TermTr.app α _ _ f fun i => ih i (heq i)

/-- The translations of an equation `a = b` are the equations `a' = b'` with `a'` a translation
of `a` and `b'` one of `b`. -/
theorem EqTr.mk {a b : Term S ℕ} {e' : Sym2 (Term S' ℕ)} (h : Φ.EqTr s(a, b) e') :
    ∃ a' b', e' = s(a', b') ∧ Φ.TermTr a a' ∧ Φ.TermTr b b' := by
  obtain ⟨c, d, c', d', he, rfl, hc, hd⟩ := h
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨c', d', rfl, hc, hd⟩
  · exact ⟨d', c', Sym2.eq_swap, hd, hc⟩

/-- **A wire substitution in the source is followed by one in the translation** (Lafont 1997,
Section 1.7, pages 79–80). If `N'` translates `N` and `N` becomes `M` by a wire substitution, then
`N'` becomes a translation of `M` by a wire substitution. -/
theorem NetTr.wire {N M : Net S ℕ} {N' : Net S' ℕ} (hw : Wire N M) (h : Φ.NetTr N N') :
    ∃ M', Φ.NetTr M M' ∧ Wire N' M' := by
  obtain ⟨x, t, a, b, Δ, -, hx⟩ := hw
  obtain ⟨e₁, N₁, he₁, hN₁, rfl⟩ := Multiset.rel_cons_left.1 h.rel
  obtain ⟨e₂, Δ', he₂, hΔ, rfl⟩ := Multiset.rel_cons_left.1 hN₁
  obtain ⟨v, t', rfl, hv, ht⟩ := EqTr.mk he₁
  cases hv
  obtain ⟨a', b', rfl, ha, hb⟩ := EqTr.mk he₂
  have hlin := h.linear
  have hxl := hlin x
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hxl
  have hx1 : 1 ≤ (a.vars + b.vars).count x := Multiset.one_le_count_iff_mem.2 hx
  rw [Multiset.count_add] at hx1
  have hta := ha.count_le x
  have htb := hb.count_le x
  have hx' : x ∈ a'.vars + b'.vars :=
    Multiset.one_le_count_iff_mem.1 (by rw [Multiset.count_add]; omega)
  have hW := Wire.mk x t' a' b' Δ' hlin hx'
  refine ⟨_, ⟨Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl, ha.subst ht (by omega),
    hb.subst ht (by omega)⟩ hΔ, hW.linear_right⟩, hW⟩

/-- A wire substitution backwards: if `M` becomes `N` by a wire substitution and `N'` translates
`N`, some translation of `M` is equivalent to `N'`. -/
theorem NetTr.wire_symm {N M : Net S ℕ} {N' : Net S' ℕ} (hw : Wire M N) (h : Φ.NetTr N N') :
    ∃ M', Φ.NetTr M M' ∧ Equiv N' M' := by
  have hk : M.Below (M.vars.sup + 1) := fun _ hx => Nat.lt_succ_of_le (Multiset.le_sup hx)
  obtain ⟨M', -, hM', -⟩ := Φ.exists_netTr hw.linear_left hk
  obtain ⟨M'', hM'', hW⟩ := hM'.wire hw
  exact ⟨M', hM', (NetTr.equiv h hM'').trans hW.equiv.symm⟩

/-- **Equivalent source nets have equivalent translations** (Lafont 1997, Section 1.7, pages
79–80: the translation of a net is a graph, defined up to the names of the new wires). If `N` is
equivalent to `M` and `N'` translates `N`, then some translation `M'` of `M` is equivalent to
`N'`. No hypothesis on the translation `Φ` is needed. -/
theorem NetTr.of_equiv {N M : Net S ℕ} {N' : Net S' ℕ} (he : Equiv N M) (h : Φ.NetTr N N') :
    ∃ M', Φ.NetTr M M' ∧ Equiv N' M' := by
  let R : Net S ℕ → Net S ℕ → Prop := fun N M =>
    ∀ N', Φ.NetTr N N' → ∃ M', Φ.NetTr M M' ∧ Equiv N' M'
  suffices H : R N M ∧ R M N from H.1 N' h
  clear h N'
  induction he with
  | rel N M hw =>
    exact ⟨fun N' h => (h.wire hw).imp fun _ hM => ⟨hM.1, hM.2.equiv⟩,
      fun M' h => NetTr.wire_symm hw h⟩
  | refl N => exact ⟨fun N' h => ⟨N', h, Equiv.refl _⟩, fun N' h => ⟨N', h, Equiv.refl _⟩⟩
  | symm N M _ ih => exact ⟨ih.2, ih.1⟩
  | trans N M K _ _ ih ih' =>
    refine ⟨fun N' h => ?_, fun K' h => ?_⟩
    · obtain ⟨M', hM, e⟩ := ih.1 N' h
      obtain ⟨K', hK, e'⟩ := ih'.1 M' hM
      exact ⟨K', hK, e.trans e'⟩
    · obtain ⟨M', hM, e⟩ := ih'.2 K' h
      obtain ⟨N', hN, e'⟩ := ih.2 M' hM
      exact ⟨N', hN, e.trans e'⟩

end Translation

end INet
