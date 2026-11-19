import InteractionCombinators.Text.Instance
import InteractionCombinators.Text.RenameInj

/-!
# Translations exist, with fresh names, and commute with renaming

Lafont, "Interaction Combinators" (1997), Section 1.7, pages 79–80: the translation of a net
replaces every cell `α` by an instance of the principal net `Φ(α)`. The relation
`Translation.TermTr` lets the internal wires of each instance have any names; this file
chooses them.

* `Translation.size`, `Translation.trTerm` — the translation of a tree whose internal wires are
  numbered from `k` upwards, distinct across instances (as `dupNet` numbers its new wires). The
  next free name is `k + Φ.size t`.
* `termTr_trTerm`, `vars_trTerm` — it is a translation, and its names are those of the tree plus
  both ends of each name of `[k, k + Φ.size t)`.
* `exists_netTr` — every linear net has a translation, linear because its new names are fresh.
* `TermTr.bind_var`, `EqTr.bind_var`, `NetTr.bind_var` — translation commutes with renaming.
-/

namespace INet

variable {S S' : Signature}

namespace Translation

/-! ## Offsets of consecutive blocks -/

/-- The start of the `i`-th block, when blocks of sizes `s 0, s 1, …` are laid end to end. -/
def off {n : ℕ} (s : Fin n → ℕ) (i : Fin n) : ℕ := ∑ j : Fin i, s (Fin.castLE i.isLt.le j)

/-- Blocks laid end to end fill the interval of their total size. -/
theorem sum_Ico_off {n : ℕ} (s : Fin n → ℕ) (a : ℕ) :
    ∑ i, Multiset.Ico (a + off s i) (a + off s i + s i) = Multiset.Ico a (a + ∑ i, s i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have h1 : ∀ i : Fin n, off s (Fin.castSucc i) = off (fun j => s (Fin.castSucc j)) i :=
      fun _ => rfl
    have h2 : off s (Fin.last n) = ∑ j : Fin n, s (Fin.castSucc j) := rfl
    simp only [h1, h2]
    rw [ih (fun j => s (Fin.castSucc j)), ← add_assoc]
    exact Multiset.Ico_add_Ico_eq_Ico (by omega) (by omega)

theorem count_Ico (a b z : ℕ) : (Multiset.Ico a b).count z = if a ≤ z ∧ z < b then 1 else 0 := by
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem (Multiset.nodup_Ico) (Multiset.mem_Ico.2 h)
  · exact Multiset.count_eq_zero.2 (fun hm => h (Multiset.mem_Ico.1 hm))

theorem sum_ite_add (k m z : ℕ) :
    (∑ w : Fin m, if z = k + w then 1 else 0) = (Multiset.Ico k (k + m)).count z := by
  rw [count_Ico]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨z - k, by omega⟩]
    · simp; omega
    · intro w _ hw
      exact ite_eq_right_iff.2 fun hz => absurd (Fin.ext (by simp; omega)) hw
    · simp
  · refine Finset.sum_eq_zero fun w _ => ite_eq_right_iff.2 fun hz => ?_
    exact absurd ⟨by omega, by have := w.isLt; omega⟩ h

variable (Φ : Translation S S')

/-! ## The translation of a tree -/

/-- The number of internal wires of the translation of a tree: the sum, over its cells `α`, of
the internal wires of `Φ(α)` (Lafont 1997, Section 1.7, pages 79–80). -/
def size : Term S ℕ → ℕ
  | .var _ => 0
  | .app α ts => (Φ.net α).internal + ∑ i, size (ts i)

/-- The translation of a tree, its internal wires numbered from `k` upwards: the root instance
takes `[k, k + internal)`, then each subtree takes the next block of its size (Lafont 1997,
Section 1.7, pages 79–80). -/
def trTerm : ℕ → Term S ℕ → Term S' ℕ
  | _, .var x => .var x
  | k, .app α ts => (Φ.net α).inst
      (fun i => trTerm (k + (Φ.net α).internal + off (fun j => Φ.size (ts j)) i) (ts i))
      (fun w => k + w)

/-- `trTerm` is a translation of the tree (Lafont 1997, Section 1.7, pages 79–80). -/
theorem termTr_trTerm (k : ℕ) (t : Term S ℕ) : Φ.TermTr t (Φ.trTerm k t) := by
  induction t generalizing k with
  | var x => exact .var x
  | app α ts ih => exact TermTr.app α ts _ (fun w => k + w) fun i => ih i _

/-- The names of `trTerm k t`: those of `t`, with their multiplicity, and both ends of each of
the new names `k, …, k + Φ.size t - 1` (Lafont 1997, Section 1.7, pages 79–80). -/
theorem vars_trTerm (k : ℕ) (t : Term S ℕ) :
    (Φ.trTerm k t).vars = t.vars + 2 • Multiset.Ico k (k + Φ.size t) := by
  induction t generalizing k with
  | var x => simp [trTerm, size]
  | app α ts ih =>
    ext z
    set I := (Φ.net α).internal
    set s : Fin (S.arity α) → ℕ := fun j => Φ.size (ts j)
    have hsize : Φ.size (.app α ts) = I + ∑ i, s i := rfl
    have hblocks : Multiset.Ico k (k + I) + Multiset.Ico (k + I) (k + I + ∑ i, s i) =
        Multiset.Ico k (k + Φ.size (.app α ts)) := by
      rw [hsize, ← add_assoc]
      exact Multiset.Ico_add_Ico_eq_Ico (by omega) (by omega)
    have hsub := congrArg (Multiset.count z) (sum_Ico_off s (k + I))
    rw [Multiset.count_sum'] at hsub
    change (PNet.inst _ _ _).vars.count z = _
    rw [PNet.count_vars_inst, sum_ite_add]
    simp only [ih, Multiset.count_add, Multiset.count_nsmul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Term.vars_app, Multiset.count_sum']
    rw [← hblocks, Multiset.count_add, ← hsub]
    ring

/-! ## A translation of a linear net exists -/

/-- The translation of an equation, numbered from `k`. -/
theorem eqTr_trTerm (k : ℕ) (a b : Term S ℕ) :
    Φ.EqTr s(a, b) s(Φ.trTerm k a, Φ.trTerm (k + Φ.size a) b) :=
  ⟨a, b, _, _, rfl, rfl, Φ.termTr_trTerm k a, Φ.termTr_trTerm _ b⟩

/-- Every net has an equation-wise translation whose names are those of the net and both ends of
each name of an interval `[k, k')` (Lafont 1997, Section 1.7, pages 79–80). -/
theorem exists_rel (N : Net S ℕ) (k : ℕ) :
    ∃ (N' : Net S' ℕ) (k' : ℕ), k ≤ k' ∧ Multiset.Rel Φ.EqTr N N' ∧
      N'.vars = N.vars + 2 • Multiset.Ico k k' := by
  induction N using Multiset.induction_on generalizing k with
  | empty => exact ⟨0, k, le_rfl, Multiset.Rel.zero, by simp⟩
  | cons e N ih =>
    induction e using Sym2.ind with
    | _ a b =>
      let k₁ := k + Φ.size a
      let k₂ := k₁ + Φ.size b
      obtain ⟨N', k', hk', hrel, hv⟩ := ih k₂
      refine ⟨s(Φ.trTerm k a, Φ.trTerm k₁ b) ::ₘ N', k', by omega,
        Multiset.Rel.cons (Φ.eqTr_trTerm k a b) hrel, ?_⟩
      rw [Net.vars_cons, Net.vars_cons, hv, eqVars_mk, eqVars_mk, Φ.vars_trTerm,
        Φ.vars_trTerm, ← Multiset.Ico_add_Ico_eq_Ico (show k ≤ k₁ by omega)
          (show k₁ ≤ k' by omega), ← Multiset.Ico_add_Ico_eq_Ico (show k₁ ≤ k₂ by omega) hk']
      simp only [nsmul_add]
      abel

/-- **A translation of a linear net exists** (Lafont 1997, Section 1.7, pages 79–80): if `N` is
linear and its names are below `k`, then `N` has a translation `N'`, whose names are those of `N`
and both ends of each name of an interval `[k, k')`. Linearity of `N'` is proved, from the
freshness of the new names. -/
theorem exists_netTr {N : Net S ℕ} (hlin : N.Linear) {k : ℕ} (hk : N.Below k) :
    ∃ (N' : Net S' ℕ) (k' : ℕ), Φ.NetTr N N' ∧ k ≤ k' ∧ N'.Below k' ∧
      N'.vars = N.vars + 2 • Multiset.Ico k k' := by
  obtain ⟨N', k', hk', hrel, hv⟩ := Φ.exists_rel N k
  refine ⟨N', k', ⟨hrel, ?_⟩, hk', ?_, hv⟩
  · intro y
    have := hlin y
    rw [hv, Multiset.count_add, Multiset.count_nsmul, count_Ico]
    split_ifs with hy
    · rw [Multiset.count_eq_zero_of_notMem (hk.notMem hy.1)]
    · omega
  · intro x hx
    rw [hv, two_nsmul, Multiset.mem_add, Multiset.mem_add, or_self] at hx
    rcases hx with hx | hx
    · exact (hk x hx).trans_le hk'
    · exact (Multiset.mem_Ico.1 hx).2

/-! ## Translation commutes with renaming -/

/-- Renaming the names of a tree and of its translation by any `ι` gives a tree and its
translation: the internal wires of each instance, named by `f`, are named by `ι ∘ f` (Lafont
1997, Section 1.7, pages 79–80). -/
theorem TermTr.bind_var {Φ : Translation S S'} (ι : ℕ → ℕ) {t : Term S ℕ} {t' : Term S' ℕ}
    (h : Φ.TermTr t t') :
    Φ.TermTr (t.bind fun y => .var (ι y)) (t'.bind fun y => .var (ι y)) := by
  induction h with
  | var x => exact .var (ι x)
  | app α ts ts' f _ ih =>
    have e : ((Φ.net α).inst ts' f).bind (fun y => .var (ι y)) =
        (Φ.net α).inst (fun i => (ts' i).bind fun y => .var (ι y)) (fun w => ι (f w)) := by
      simp only [PNet.inst, Term.bind_bind]
      congr 1
      funext x
      cases x <;> rfl
    rw [e]
    exact TermTr.app α _ _ _ ih

/-- Renaming an equation and its translation by any `ι` gives an equation and its translation
(Lafont 1997, Section 1.7, pages 79–80). -/
theorem EqTr.bind_var {Φ : Translation S S'} (ι : ℕ → ℕ) {e : Sym2 (Term S ℕ)}
    {e' : Sym2 (Term S' ℕ)} (h : Φ.EqTr e e') :
    Φ.EqTr (e.map (Term.bind fun y => .var (ι y))) (e'.map (Term.bind fun y => .var (ι y))) := by
  obtain ⟨a, b, a', b', rfl, rfl, ha, hb⟩ := h
  exact ⟨_, _, _, _, rfl, rfl, ha.bind_var ι, hb.bind_var ι⟩

/-- Renaming a net and its translation by an injective `ι` gives a net and its translation; the
injectivity keeps the translation linear (Lafont 1997, Section 1.7, pages 79–80). -/
theorem NetTr.bind_var {Φ : Translation S S'} (ι : ℕ → ℕ) (hι : Function.Injective ι)
    {N : Net S ℕ} {N' : Net S' ℕ} (h : Φ.NetTr N N') :
    Φ.NetTr (N.bind fun y => .var (ι y)) (N'.bind fun y => .var (ι y)) :=
  ⟨Multiset.rel_map.2 (h.rel.mono fun _ _ _ _ he => he.bind_var ι), h.linear.bind_var ι hι⟩

end Translation

end INet
