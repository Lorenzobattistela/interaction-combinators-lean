import InteractionCombinators.Core.System

/-!
# Principal nets and translations

Lafont, "Interaction Combinators" (1997), Section 1.7.

* `PNet S n` — a principal net of arity `n`: a tree whose leaves are its `n` auxiliary ports, each
  once, and the two ends of some internal wires. It behaves like a cell with `n` auxiliary ports.
* `Translation S S'` — a principal net over `S'` for each symbol of `S`.
* `Translation.NetTr` — a net over `S'` is a translation of a net over `S`: every cell is replaced
  by an instance of the principal net of its symbol, with new names for its internal wires.
* `Translation.Compatible` — a translation of interaction systems: it is compatible with
  reduction.
* `Universal` — every interaction system can be translated into the given one.
-/

namespace INet

variable {S S' : Signature}

/-- A principal net of arity `n`: a tree over the `n` auxiliary ports and some internal wires.
The root of the tree is the root of the net. -/
structure PNet (S : Signature) (n : ℕ) where
  /-- The number of internal wires. -/
  internal : ℕ
  /-- The tree: its leaves are auxiliary ports or ends of internal wires. -/
  tree : Term S (Fin n ⊕ Fin internal)
  /-- Every auxiliary port occurs exactly once. -/
  port_count : ∀ i, tree.vars.count (.inl i) = 1
  /-- Every internal wire has exactly two ends. -/
  internal_count : ∀ w, tree.vars.count (.inr w) = 2

namespace PNet

variable {n : ℕ}

/-- An instance of a principal net: trees plugged into the auxiliary ports, and the internal wires
named by `f`. -/
def inst (p : PNet S n) (args : Fin n → Term S ℕ) (f : Fin p.internal → ℕ) : Term S ℕ :=
  p.tree.bind (Sum.elim args fun w => Term.var (f w))

/-- A principal net is strict when it is not a single wire: its root is the principal port of a
cell. -/
def Strict (p : PNet S n) : Prop := ∀ x, p.tree ≠ Term.var x

/-- A single cell, as a principal net. -/
def cell (α : S.Sym) : PNet S (S.arity α) where
  internal := 0
  tree := .app α fun i => .var (.inl i)
  port_count i := by
    simp [Multiset.count_sum', Multiset.count_singleton]
  internal_count w := w.elim0

@[simp] theorem inst_cell (α : S.Sym) (args : Fin (S.arity α) → Term S ℕ)
    (f : Fin (cell α).internal → ℕ) : (cell α).inst args f = .app α args := rfl

end PNet

/-- A translation of the symbols of `S` into principal nets over `S'`. -/
structure Translation (S S' : Signature) where
  /-- The principal net that stands for a symbol. -/
  net : (α : S.Sym) → PNet S' (S.arity α)

namespace Translation

/-- A translation is strict when no symbol is translated to a single wire. -/
def Strict (Φ : Translation S S') : Prop := ∀ α, (Φ.net α).Strict

/-- `t'` is a translation of the tree `t`: names are kept, and every cell is replaced by an
instance of the principal net of its symbol. -/
inductive TermTr (Φ : Translation S S') : Term S ℕ → Term S' ℕ → Prop
  | var (x : ℕ) : TermTr Φ (.var x) (.var x)
  | app (α : S.Sym) (ts : Fin (S.arity α) → Term S ℕ) (ts' : Fin (S.arity α) → Term S' ℕ)
      (f : Fin (Φ.net α).internal → ℕ) (h : ∀ i, TermTr Φ (ts i) (ts' i)) :
      TermTr Φ (.app α ts) ((Φ.net α).inst ts' f)

/-- `e'` is a translation of the equation `e`. -/
def EqTr (Φ : Translation S S') (e : Sym2 (Term S ℕ)) (e' : Sym2 (Term S' ℕ)) : Prop :=
  ∃ a b a' b', e = s(a, b) ∧ e' = s(a', b') ∧ Φ.TermTr a a' ∧ Φ.TermTr b b'

/-- `N'` is a translation of the net `N`: equation by equation, and linear. Linearity forces the
internal wires of the instances to have names that are new and pairwise distinct. -/
structure NetTr (Φ : Translation S S') (N : Net S ℕ) (N' : Net S' ℕ) : Prop where
  /-- The equations of `N'` are translations of those of `N`. -/
  rel : Multiset.Rel Φ.EqTr N N'
  /-- The translated net is linear. -/
  linear : N'.Linear

/-- A translation of interaction systems (Lafont, Section 1.7): for every rule, the translations of
the two cells, plugged by their roots, reduce to a translation of the right-hand side. The
auxiliary ports of the two cells are the names `xs` and `ys`. Reduction is up to wires
(`StepsE`): cells whose principal ports are joined by a named wire may interact. -/
def Compatible (Φ : Translation S S') (I : System S) (I' : System S') : Prop :=
  ∀ (α β : S.Sym) (r : Rule S (S.arity α) (S.arity β)), I.rule α β = some r →
    ∀ (xs : Fin (S.arity α) → ℕ) (ys : Fin (S.arity β) → ℕ)
      (f : Fin (Φ.net α).internal → ℕ) (g : Fin (Φ.net β).internal → ℕ),
      Net.Linear ({s((Φ.net α).inst (fun i => .var (xs i)) f,
        (Φ.net β).inst (fun j => .var (ys j)) g)} : Net S' ℕ) →
      ∃ (M N' : Net S' ℕ) (h : Fin r.internal → ℕ),
        StepsE I' {s((Φ.net α).inst (fun i => .var (xs i)) f,
          (Φ.net β).inst (fun j => .var (ys j)) g)} M ∧
        Equiv M N' ∧
        Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N'

/-! ## The identity translation -/

/-- Every symbol is translated to itself. -/
protected def id (S : Signature) : Translation S S := ⟨PNet.cell⟩

theorem termTr_id (t : Term S ℕ) : (Translation.id S).TermTr t t := by
  induction t with
  | var x => exact .var x
  | app α ts ih => exact TermTr.app (Φ := Translation.id S) α ts ts Fin.elim0 ih

theorem eqTr_id (e : Sym2 (Term S ℕ)) : (Translation.id S).EqTr e e := by
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, b, a, b, rfl, rfl, termTr_id a, termTr_id b⟩

/-- A sanity check of the definitions: the identity translation of a well-formed system into
itself is a translation of interaction systems. -/
theorem id_compatible (I : System S) (hI : I.WellFormed) :
    (Translation.id S).Compatible I I := by
  intro α β r hr xs ys f g hlin
  let L : Sym2 (Term S ℕ) := s(.app α fun i => .var (xs i), .app β fun j => .var (ys j))
  let k : ℕ := (Net.vars ({L} : Net S ℕ)).sup + 1
  have hstep : Step I (L ::ₘ 0)
      (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) (fun w => k + w) + 0) :=
    Step.mk α β r hr _ _ 0 (fun w => k + w)
      (fun a b hab => Fin.ext (by simpa using hab))
      (fun w hw => by
        have hle : k + w ≤ (Net.vars ({L} : Net S ℕ)).sup :=
          Multiset.le_sup (show k + (w : ℕ) ∈ Net.vars ({L} : Net S ℕ) from hw)
        omega)
  have hstep' : Step I ({L} : Net S ℕ)
      (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) (fun w => k + w)) := by
    simpa using hstep
  refine ⟨_, _, fun w => k + w, (Steps.single hstep').stepsE, Equiv.refl _, ?_, ?_⟩
  · exact Multiset.rel_refl_of_refl_on fun e _ => eqTr_id e
  · exact hstep'.linear hI.linear hlin

end Translation

/-- A universal interaction system: every interaction system over a finite alphabet can be
translated into it. -/
def Universal (I' : System S') : Prop :=
  ∀ (S : Signature) [Finite S.Sym] (I : System S), I.WellFormed →
    ∃ Φ : Translation S S', Φ.Compatible I I'

/-- A strictly universal interaction system: every interaction system over a finite alphabet has a
strict translation into it. Strictness excludes translations that erase cells by turning them into
wires, so every interaction of the source costs at least one interaction of the target. -/
def StrictlyUniversal (I' : System S') : Prop :=
  ∀ (S : Signature) [Finite S.Sym] (I : System S), I.WellFormed →
    ∃ Φ : Translation S S', Φ.Strict ∧ Φ.Compatible I I'

theorem StrictlyUniversal.universal {I' : System S'} (h : StrictlyUniversal I') : Universal I' :=
  fun S _ I hI => (h S I hI).imp fun _ hΦ => hΦ.2

end INet
