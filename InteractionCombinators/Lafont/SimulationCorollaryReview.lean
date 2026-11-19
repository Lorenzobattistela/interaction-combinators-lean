import InteractionCombinators.Lafont.SimulationStrictCheck
import InteractionCombinators.Lafont.SimulationE
import InteractionCombinators.Lafont.DecompositionLemmas
import InteractionCombinators.Combinators

/-!
# Review of the corollaries of Proposition 4 (page 81)

Lafont 1997, page 81: "if `Φ` is strict, the left member is not reduced, and the reduction cannot
be of length 0 … `L > 0` if `Φ` is strict", and Proposition 4. This file checks the statements of
`SimulationStrict.lean` and `SimulationE.lean` against the page.

* The statements, restated with their types (`pos`, `stepsE`, `stepsEN`), and the extra hypothesis
  `hI'` (rules of the target linear) discharged for the combinators.
* `distinct_names_needed`: `Translation.not_equiv_pair_of_strict` is false without its hypotheses
  of distinct names. A system with two symbols `a`, `b` of arity `1` and the rule
  `a b ↦ {x = a(w), y = b(w)}` (linear, reduced), the identity translation, the names
  `xs 0 = ys 0 = 0`: the pair `a(0) = b(0)` is the same graph as the instance
  `{0 = a(1), 0 = b(1)}` of the right member. That instance has a cut: once two ports are
  identified, the right member of a reduced rule is no longer reduced.
* `swap_compatibleWithin`, `swap_pos`, `swap_stepsE`: a strict translation other than the identity
  (it exchanges `a` and `b`) to which `pos` and `stepsE` apply together.
-/

namespace INet.SimulationCorollaryReview

open Term

/-! ## The statements against page 81 -/

/-- `CompatibleWithin.pos` says "`L > 0` if `Φ` is strict" (Lafont 1997, page 81) in the form: a
strict translation compatible within `L, M` is compatible within `max L 1, M`. -/
example {S S' : Signature} {Φ : Translation S S'} {I : System S} {I' : System S'} {L M : ℕ}
    (hΦ : Φ.Strict) (hI : I.WellFormed) (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    (h : Φ.CompatibleWithin I I' L M) : Φ.CompatibleWithin I I' (max L 1) M :=
  h.pos hΦ hI hI'

/-- `CompatibleWithin.stepsEN` is Proposition 4 (Lafont 1997, page 81) with reduction of graphs on
both sides and `L n ≤ n' ≤ M n`. -/
example {S S' : Signature} {I : System S} {I' : System S'}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    {Φ : Translation S S'} {L M n : ℕ} (hΦ : Φ.CompatibleWithin I I' L M)
    {N M₀ : Net S ℕ} {N' : Net S' ℕ} (h : StepsEN I n N M₀) (hT : Φ.NetTr N N') :
    ∃ n' M₁ M', StepsEN I' n' N' M₁ ∧ L * n ≤ n' ∧ n' ≤ M * n ∧ Equiv M₁ M' ∧
      Φ.NetTr M₀ M' :=
  hΦ.stepsEN hI hI' h hT

/-- The hypothesis `hI'` of `pos` and of Proposition 4 holds for the target of Theorem 1: the rules
of the combinators are linear (Lafont 1997, page 72 and Fig. 2, page 81). -/
example : ∀ α β r, Comb.system.rule α β = some r → r.Linear := Comb.system_wellFormed.linear

/-! ## Distinct names are needed in `not_equiv_pair_of_strict` -/

/-- Two symbols, each with one auxiliary port. -/
inductive TSym : Type
  | a | b
  deriving DecidableEq

/-- The signature of `TSym`: both symbols have arity `1`. -/
def tsig : Signature where
  Sym := TSym
  arity _ := 1

instance : DecidableEq tsig.Sym := inferInstanceAs (DecidableEq TSym)

instance {ν : Type} [DecidableEq ν] : DecidableEq (Term tsig ν) :=
  Comb.DecompositionCheck.termDecEq

/-- An `a` cell with a tree on its auxiliary port. -/
def mkA {ν : Type} (t : Term tsig ν) : Term tsig ν := .app TSym.a fun _ => t

/-- A `b` cell with a tree on its auxiliary port. -/
def mkB {ν : Type} (t : Term tsig ν) : Term tsig ν := .app TSym.b fun _ => t

/-- The names of `a(t)` are those of `t`. -/
@[simp] theorem vars_mkA {ν : Type} (t : Term tsig ν) : (mkA t).vars = t.vars := by
  show (∑ _i : Fin 1, t.vars) = t.vars
  simp

/-- The names of `b(t)` are those of `t`. -/
@[simp] theorem vars_mkB {ν : Type} (t : Term tsig ν) : (mkB t).vars = t.vars := by
  show (∑ _i : Fin 1, t.vars) = t.vars
  simp

/-- A name of a rule: port of the first cell, port of the second, internal wire. -/
abbrev Nm : Type := Fin 1 ⊕ Fin 1 ⊕ Fin 1

/-- `a b ↦ {x = a(w), y = b(w)}`: the two cells are rebuilt, joined by a wire `w` of their
auxiliary ports, and their principal ports become the free ports `x`, `y`. -/
def ruleAB : Rule tsig 1 1 :=
  ⟨1, s(.var (.inl 0), mkA (.var (.inr (.inr 0)))) ::ₘ
    s(.var (.inr (.inl 0)), mkB (.var (.inr (.inr 0)))) ::ₘ 0⟩

/-- The system with the single rule `a`–`b`. -/
def tsys : System tsig where
  rule
    | .a, .b => some ruleAB
    | _, _ => none

/-- `ruleAB` is linear: `x`, `y` once, `w` twice (Lafont 1997, page 72). -/
theorem ruleAB_linear : ruleAB.Linear :=
  ⟨by decide, by decide, by decide⟩

/-- `ruleAB` is reduced: each equation has a free port on one side (page 72). -/
theorem ruleAB_reduced : ruleAB.Reduced := by
  intro e he
  have key : ∀ e ∈ (show Net tsig Nm from ruleAB.net),
      e ∈ [s(.var (.inl 0), mkA (.var (.inr (.inr 0)))),
        s(.var (.inr (.inl 0)), mkB (.var (.inr (.inr 0))))] := by
    decide
  have key := key e he
  rcases key with _ | ⟨_, _ | ⟨_, h⟩⟩
  · exact ⟨_, _, rfl, fun w h => by cases h⟩
  · exact ⟨_, _, rfl, fun w h => by cases h⟩
  · cases h

/-- `tsys` is an interaction system in the sense of Lafont (page 72). -/
theorem tsys_wellFormed : tsys.WellFormed where
  linear := by
    intro α β r h
    cases α <;> cases β <;> cases h
    exact ruleAB_linear
  reduced := by
    intro α β r h
    cases α <;> cases β <;> cases h
    exact ruleAB_reduced
  unique := by
    intro α β hne h
    cases α <;> cases β <;> simp_all [tsys]
  symm := by
    refine fun α r h => Rule.symm_of_equiv ?_
    revert α r h
    intro α r h
    cases α <;> cases h

/-- The instance of the right member with `xs 0 = ys 0 = 0` and the internal wire `1`. -/
theorem inst_ruleAB_shared :
    ruleAB.inst (fun _ => var 0) (fun _ => var 0) (fun _ => 1) =
      s(var 0, mkA (var 1)) ::ₘ s(var 0, mkB (var 1)) ::ₘ 0 := by
  decide

/-- `{0 = a(1), 0 = b(1)}` is linear. -/
theorem linear_shared : Net.Linear (s(var 0, mkA (var 1)) ::ₘ s(var 0, mkB (var 1)) ::ₘ 0 :
    Net tsig ℕ) := by
  intro y
  simp [Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- `{x = y, a(x) = b(y)}` is linear when `x ≠ y`. -/
theorem linear_link (x y : ℕ) (hxy : x ≠ y) :
    Net.Linear (s(var x, var y) ::ₘ s(mkA (var x), mkB (var y)) ::ₘ 0 : Net tsig ℕ) := by
  intro z
  simp [Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- The pair `a(0) = b(0)` is the same graph as the instance `{0 = a(1), 0 = b(1)}`. The wire `0`
is substituted, which gives `a(1) = b(1)`; that net and `a(0) = b(0)` are both obtained from
`{1 = 0, a(1) = b(0)}` by substituting one of the names of the link. -/
theorem equiv_pair_shared :
    Equiv (s(mkA (var 0), mkB (var 0)) ::ₘ 0 : Net tsig ℕ)
      (s(var 0, mkA (var 1)) ::ₘ s(var 0, mkB (var 1)) ::ₘ 0) := by
  have w1 := Wire.mk (S := tsig) 0 (mkA (var 1)) (var 0) (mkB (var 1)) 0 linear_shared
    (by simp)
  have w2 := Wire.mk (S := tsig) 1 (var 0) (mkA (var 1)) (mkB (var 0)) 0
    (by simpa using linear_link 1 0 (by decide)) (by simp)
  have e : (s(var 0, var 1) : Sym2 (Term tsig ℕ)) = s(var 1, var 0) := Sym2.eq_swap
  have w3 := Wire.mk (S := tsig) 0 (var 1) (mkA (var 1)) (mkB (var 0)) 0
    (by rw [e]; simpa using linear_link 1 0 (by decide)) (by simp)
  have e1 : (s((var 0 : Term tsig ℕ).subst 0 (mkA (var 1)), (mkB (var 1)).subst 0 (mkA (var 1)))
      ::ₘ 0 : Net tsig ℕ) = s(mkA (var 1), mkB (var 1)) ::ₘ 0 := by decide
  have e2 : (s((mkA (var 1) : Term tsig ℕ).subst 1 (var 0), (mkB (var 0)).subst 1 (var 0))
      ::ₘ 0 : Net tsig ℕ) = s(mkA (var 0), mkB (var 0)) ::ₘ 0 := by decide
  have e3 : (s((mkA (var 1) : Term tsig ℕ).subst 0 (var 1), (mkB (var 0)).subst 0 (var 1))
      ::ₘ 0 : Net tsig ℕ) = s(mkA (var 1), mkB (var 1)) ::ₘ 0 := by decide
  rw [e1] at w1
  rw [e2] at w2
  rw [e3, e] at w3
  exact w2.equiv.symm.trans (w3.equiv.trans w1.equiv.symm)

/-- The pair `a(0) = b(0)` is linear: the naming `xs 0 = ys 0 = 0` is one that
`Translation.Compatible` must handle (Lafont 1997, page 80). -/
theorem linear_pair_shared : Net.Linear (s(mkA (var 0), mkB (var 0)) ::ₘ 0 : Net tsig ℕ) := by
  intro y
  simp [Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> omega

/-- **Distinct names are needed in `Translation.not_equiv_pair_of_strict`** (Lafont 1997,
page 81). Without its hypotheses `Function.Injective xs`, `Function.Injective ys`,
`∀ i j, xs i ≠ ys j`, the statement is false: for the well-formed system `tsys`, the strict
identity translation, and `xs 0 = ys 0 = 0`, the pair `a(0) = b(0)` is the same graph as the
translation `{0 = a(1), 0 = b(1)}` of the right member. -/
theorem distinct_names_needed : ¬ ∀ (S S' : Signature) (Φ : Translation S S') (I : System S),
    Φ.Strict → I.WellFormed →
    ∀ (α β : S.Sym) (r : Rule S (S.arity α) (S.arity β)), I.rule α β = some r →
    ∀ (xs : Fin (S.arity α) → ℕ) (ys : Fin (S.arity β) → ℕ) (f : Fin (Φ.net α).internal → ℕ)
      (g : Fin (Φ.net β).internal → ℕ) (h : Fin r.internal → ℕ) (N' : Net S' ℕ),
      Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N' →
      ¬ Equiv ({s((Φ.net α).inst (fun i => .var (xs i)) f,
        (Φ.net β).inst (fun j => .var (ys j)) g)} : Net S' ℕ) N' := by
  intro H
  have hT : (Translation.id tsig).NetTr
      (ruleAB.inst (fun _ => var 0) (fun _ => var 0) (fun _ => 1))
      (s(var 0, mkA (var 1)) ::ₘ s(var 0, mkB (var 1)) ::ₘ 0) := by
    rw [inst_ruleAB_shared]
    exact ⟨Multiset.rel_refl_of_refl_on fun e _ => Translation.eqTr_id e, linear_shared⟩
  exact H tsig tsig (Translation.id tsig) tsys (fun _ _ h => by cases h) tsys_wellFormed
    TSym.a TSym.b ruleAB rfl (fun _ => 0) (fun _ => 0) Fin.elim0 Fin.elim0 (fun _ => 1) _ hT
    equiv_pair_shared

/-- The instance `{0 = a(1), 0 = b(1)}` of the right member of `ruleAB` has a cut: the cells
`a` and `b` are joined through the wire `0`. With shared names, an instance of a reduced rule
is not reduced, which is why `Rule.not_hasCut_inst` needs distinct names. -/
theorem hasCut_inst_shared :
    Net.HasCut (s(var 0, mkA (var 1)) ::ₘ s(var 0, mkB (var 1)) ::ₘ 0 : Net tsig ℕ) :=
  (Net.hasCut_of_mem (N := s(mkA (var 0), mkB (var 0)) ::ₘ 0)
    (Multiset.mem_cons_self _ _)).of_equiv equiv_pair_shared

/-! ## A strict translation other than the identity -/

/-- **The pair of a rule interacts** (Lafont 1997, page 72): if `I` has a rule `r` for `α`, `β`,
the net `α(xs) = β(ys)` reduces in one interaction to the instance of `r` whose internal wires
are numbered above the names of the net. -/
theorem step_pair {S : Signature} {I : System S} {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)} (hr : I.rule α β = some r)
    (xs : Fin (S.arity α) → ℕ) (ys : Fin (S.arity β) → ℕ) :
    Step I (s(.app α fun i => .var (xs i), .app β fun j => .var (ys j)) ::ₘ 0)
      (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) fun w =>
        (Net.vars (s(.app α fun i => .var (xs i), .app β fun j => .var (ys j)) ::ₘ 0 :
          Net S ℕ)).sup + 1 + w) := by
  have h := Step.mk (I := I) α β r hr (fun i => .var (xs i)) (fun j => .var (ys j)) 0
    (fun w => (Net.vars (s(.app α fun i => .var (xs i), .app β fun j => .var (ys j)) ::ₘ 0 :
      Net S ℕ)).sup + 1 + w)
    (fun a b hab => Fin.ext (by simpa using hab))
    (fun w hw => by
      have hle := Multiset.le_sup hw
      omega)
  rwa [add_zero] at h

/-- `b a ↦ {x = b(w), y = a(w)}`: the rule `ruleAB` with the two symbols exchanged. -/
def ruleBA : Rule tsig 1 1 :=
  ⟨1, s(.var (.inl 0), mkB (.var (.inr (.inr 0)))) ::ₘ
    s(.var (.inr (.inl 0)), mkA (.var (.inr (.inr 0)))) ::ₘ 0⟩

/-- The system with the single rule `b`–`a`. -/
def tsys' : System tsig where
  rule
    | .b, .a => some ruleBA
    | _, _ => none

/-- `ruleBA` is reduced (Lafont 1997, page 72). -/
theorem ruleBA_reduced : ruleBA.Reduced := by
  intro e he
  have key : ∀ e ∈ (show Net tsig Nm from ruleBA.net),
      e ∈ [s(.var (.inl 0), mkB (.var (.inr (.inr 0)))),
        s(.var (.inr (.inl 0)), mkA (.var (.inr (.inr 0))))] := by
    decide
  have key := key e he
  rcases key with _ | ⟨_, _ | ⟨_, h⟩⟩
  · exact ⟨_, _, rfl, fun w h => by cases h⟩
  · exact ⟨_, _, rfl, fun w h => by cases h⟩
  · cases h

/-- `tsys'` is an interaction system in the sense of Lafont (page 72). -/
theorem tsys'_wellFormed : tsys'.WellFormed where
  linear := by
    intro α β r h
    cases α <;> cases β <;> cases h
    exact ⟨by decide, by decide, by decide⟩
  reduced := by
    intro α β r h
    cases α <;> cases β <;> cases h
    exact ruleBA_reduced
  unique := by
    intro α β hne h
    cases α <;> cases β <;> simp_all [tsys']
  symm := by
    refine fun α r h => Rule.symm_of_equiv ?_
    revert α r h
    intro α r h
    cases α <;> cases h

/-- The principal nets of the exchange: `a` becomes a `b` cell and `b` an `a` cell. -/
def swapNet : (α : tsig.Sym) → PNet tsig (tsig.arity α)
  | .a => PNet.cell TSym.b
  | .b => PNet.cell TSym.a

/-- The translation that exchanges `a` and `b` (Lafont 1997, page 80: a renaming of the
symbols). -/
def swapT : Translation tsig tsig := ⟨swapNet⟩

/-- The exchange is strict: every symbol is translated to a cell (page 80). -/
theorem swapT_strict : swapT.Strict := by
  intro α
  cases α <;> intro x h <;> cases h

/-- The exchange is compatible within `1` and `1` from `tsys` to `tsys'` (Lafont 1997,
page 81): the translation `b(xs) = a(ys)` of the pair of `ruleAB` reduces in one interaction of
`ruleBA` to the translation of the right member. -/
theorem swap_compatibleWithin : swapT.CompatibleWithin tsys tsys' 1 1 := by
  intro α β r hr xs ys f g hlin
  cases α <;> cases β <;> cases hr
  have hs := step_pair (I := tsys') (α := TSym.b) (β := TSym.a) rfl xs ys
  refine ⟨_, _, fun w => (Net.vars (s(.app TSym.b fun i => .var (xs i),
      .app TSym.a fun j => .var (ys j)) ::ₘ 0 : Net tsig ℕ)).sup + 1 + w,
    ⟨1, le_rfl, le_rfl, StepsEN.single hs.stepE⟩, Equiv.refl _, ?_,
    hs.linear tsys'_wellFormed.linear hlin⟩
  refine Multiset.Rel.cons ?_ (Multiset.Rel.cons ?_ Multiset.Rel.zero)
  · exact ⟨_, _, _, _, rfl, rfl, Translation.TermTr.var _,
      Translation.TermTr.app (Φ := swapT) TSym.a _ _ Fin.elim0 fun _ => Translation.TermTr.var _⟩
  · exact ⟨_, _, _, _, rfl, rfl, Translation.TermTr.var _,
      Translation.TermTr.app (Φ := swapT) TSym.b _ _ Fin.elim0 fun _ => Translation.TermTr.var _⟩

/-- **`pos` applies to a strict translation other than the identity** (Lafont 1997, page 81):
from the bound `0`, `CompatibleWithin.pos` gives back `L = 1` for the exchange. -/
theorem swap_pos : swapT.CompatibleWithin tsys tsys' 1 1 :=
  (SimulationStrictCheck.compatibleWithin_mono (Nat.zero_le 1) swap_compatibleWithin).pos
    swapT_strict tsys_wellFormed tsys'_wellFormed.linear

/-- **Proposition 4 for reduction of graphs applies to the same translation** (Lafont 1997,
page 81): the exchange satisfies the hypotheses of `Compatible.stepsE` and
`CompatibleWithin.stepsEN` together with those of `pos`. -/
theorem swap_stepsEN {n : ℕ} {N M₀ : Net tsig ℕ} {N' : Net tsig ℕ} (h : StepsEN tsys n N M₀)
    (hT : swapT.NetTr N N') :
    ∃ n' M₁ M', StepsEN tsys' n' N' M₁ ∧ 1 * n ≤ n' ∧ n' ≤ 1 * n ∧ Equiv M₁ M' ∧
      swapT.NetTr M₀ M' :=
  swap_pos.stepsEN tsys_wellFormed.linear tsys'_wellFormed.linear h hT

/-- The hypotheses of `swap_stepsEN` hold: the pair `a(0) = b(1)` of `tsys` interacts, and
`b(0) = a(1)` is its translation by the exchange. -/
example : ∃ n' M₁ M', StepsEN tsys' n' (s(mkB (var 0), mkA (var 1)) ::ₘ 0) M₁ ∧
    n' = 1 ∧ Equiv M₁ M' ∧ swapT.NetTr
      (ruleAB.inst (fun _ => var 0) (fun _ => var 1) fun w =>
        (Net.vars (s(mkA (var 0), mkB (var 1)) ::ₘ 0 : Net tsig ℕ)).sup + 1 + w) M' := by
  have hs := step_pair (I := tsys) (α := TSym.a) (β := TSym.b) rfl (fun _ => 0) (fun _ => 1)
  have hT : swapT.NetTr (s(mkA (var 0), mkB (var 1)) ::ₘ 0) (s(mkB (var 0), mkA (var 1)) ::ₘ 0) :=
    ⟨Multiset.Rel.cons ⟨_, _, _, _, rfl, rfl,
      Translation.TermTr.app (Φ := swapT) TSym.a _ _ Fin.elim0 (fun _ => Translation.TermTr.var _),
      Translation.TermTr.app (Φ := swapT) TSym.b _ _ Fin.elim0 (fun _ => Translation.TermTr.var _)⟩
      Multiset.Rel.zero, by
        intro y
        simp [Multiset.count_cons, Multiset.count_singleton]
        split_ifs <;> omega⟩
  obtain ⟨n', M₁, M', h1, hL, hM, hE, hT'⟩ := swap_stepsEN (StepsEN.single hs.stepE) hT
  exact ⟨n', M₁, M', h1, by omega, hE, hT'⟩

end INet.SimulationCorollaryReview
