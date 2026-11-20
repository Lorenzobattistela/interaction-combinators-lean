import Checks.Graphs.GraphStepCheck
import InteractionCombinators.Graphs.GraphContractUnique
import InteractionCombinators.Graphs.GraphIso

/-!
# Review of `Graph.Interact` (Lafont 1997, Section 1.2, page 73)

**Verdict: no defect.** `Graph.Interact` (`InteractionCombinators/Graphs/GraphStep.lean`) says what
page 73 says, in the port convention of `Step` on texts, and its docstrings are accurate. Part 2 of
Stage C.5 can be built on it. Its statement must be "up to `Iso`": `Interact` renumbers the cells of
the rule by an arbitrary `σ`.

The figure of page 73 draws `α_i` and `α_j` side by side, both with their auxiliary ports on top,
and `ν_{i,j}` with the `n_i` ports of `α_i` first, then the `n_j` ports of `α_j`, each in order.
`Interact` sends the `i`-th auxiliary port of the cell of `α` to the free port `.inl i` of the
rule and the `j`-th of the cell of `β` to `.inr (.inl j)`, as `Step` does with `as` and `bs`.

What was checked, bullet by bullet of issue #357:

* **Port order** (proved). `con`–`con` exchanges the auxiliary ports: `conCon_free`
  (in `GraphStepCheck`) gives `0–3, 1–2` from `con(0, 1) = con(2, 3)`, and
  `conCon_not_inOrder` proves that `0–2, 1–3` is *not* a result, for every choice of the cell of
  `α`, of the graph of the rule, of `σ`, `g` and of the order of contraction. `dup`–`dup` joins
  them in order: `dupDup_free` gives `0–2, 1–3` from `dup(0, 1) = dup(2, 3)`, and
  `dupDup_not_exchanged` proves that `0–3, 1–2` is not a result. The negative proofs invert
  `Interact` on the graph (`pairFree_inv`) and use a valuation of the names that every glued wire
  respects and contraction preserves (`contracts_good`).
* **Which cell is `α`** (proved). A graph does not record the order of the two cells:
  `pairFree_conDup_eq` writes `con(0, 1) = dup(2, 3)` with either cell first and gets one value.
  So nothing is needed for the rule `β, α`: `conDup_interact` and `dupCon_interact` give an
  interaction for the `con`–`dup` pair with the `con` cell numbered `0` or `1`, both through
  `ruleConDup`. `conDup_cell_of_alpha`: every interaction of `con(0, 1) = dup(2, 3)` takes the
  `con` cell for `α`, since `system` has no rule for `dup, con`; the two orders cannot give two
  different results. For a symbol with itself both orders apply; `conCon_free_other_cell` takes
  the other cell for `α` and reaches the same graph, by the symmetry of `ruleConCon`.
* **Degenerate cases** (proved). `c = d`: excluded by `WF` (`not_wf_sameCell`); on such a graph
  `Interact` still holds and gives a meaningless result, with two free ports from nowhere
  (`sameCell_interact`). This does not matter for part 2, where graphs of nets are `WF`
  (`Net.HasGraph.wf`). An auxiliary port wired to the other auxiliary port of the same cell:
  `conSelf_interact`, the result is the wire `0–1` as `con(x, x) = con(0, 1)` reduces to `0 = 1`;
  wired to the partner's auxiliary port: `dupDup_shared` and `conCon_closed` of `GraphStepCheck`,
  which create cyclic wires. `era`–`era`: the empty rule removes the pair and keeps the rest,
  free wire and cyclic wire included (`eraEra_interact`). Fresh names: every name of the graph
  occurs in `W`, because the wire between principal ports has no name, so `hgW` says exactly that
  the fresh names are not names of the graph; `hgW_excludes_free` shows it fails for a choice
  that clashes.
* **Determinism up to `Iso`** (proved on an example, argued in general).
  `conCon_free`, `conCon_free_other_cell` (other cell for `α`) and `conCon_free_other_names`
  (fresh names `10, …, 13`) reach the same graph. For fixed data, the result is unique:
  `contracts_unique` applies, because in the glued graph of a well-formed `G` and a linear rule
  every name ends at most two wires. In general I expect: two results of one well-formed `G` are
  `Iso`. The ingredients are (1) two graphs of a linear rule net are `Iso`
  (`Net.Linear.hasGraph_iso`) and contraction can be transported along `Iso` (`Iso.contracts`);
  (2) every fresh name ends exactly two wires of the glued graph and is contracted, so the result
  does not mention `g`, but this needs a lemma that contraction commutes with renaming the names,
  which the library does not have; (3) changing `σ` is an `Iso`. Not proved here.
* **Agreement with texts** (proved on one instance). `dupDupShared_agree`: the linear net
  `dup(x, 1) = dup(x, 2)` has the graph `dupDupShared`; one `Step` of `ruleDupDup` gives
  `x = x, 1 = 2`, whose graph is `dupDupSharedAfter`, and `Interact` takes `dupDupShared` to that
  same graph. The statement of part 2 is not vacuous.

Not checked: a rule whose net has cells, through a concrete result (only the existence of an
interaction for `ruleConDup` is proved, `conDup_interact`); `Interact` against Fig. 2 or other
figures; determinism in general.
-/

namespace INet.GraphStepReview

open Comb Graph GraphReview GraphStepCheck

/-! ## A valuation of the names that contraction respects -/

/-- The value of an end under a valuation `v` of the names: a port has the value `0`. -/
def endVal {ν : Type} (v : ν → ℕ) : End ν → ℕ
  | .port _ _ => 0
  | .name x => v x

/-- A wire is *good* for `v` when its two ends have the same value. -/
def Good {ν : Type} (v : ν → ℕ) (e : Sym2 (End ν)) : Prop :=
  ∀ p q, e = s(p, q) → endVal v p = endVal v q

theorem good_mk {ν : Type} {v : ν → ℕ} {p q : End ν} :
    Good v s(p, q) ↔ endVal v p = endVal v q := by
  constructor
  · intro h; exact h p q rfl
  · intro h p' q' e
    rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact h.symm

/-- **Contraction keeps every wire good** (Lafont 1997, page 71): joining two wires through a name
`x` gives a wire whose ends both have the value of `x`. -/
theorem contract_good {ν : Type} {v : ν → ℕ} {G H : Graph S ν} (h : Contract G H)
    (hG : ∀ e ∈ G.wires, Good v e) : ∀ e ∈ H.wires, Good v e := by
  cases h with
  | join x p q C W n =>
    intro e he
    rcases Multiset.mem_cons.1 he with rfl | he
    · have h1 := good_mk.1 (hG _ (Multiset.mem_cons_self _ _))
      have h2 := good_mk.1 (hG _ (Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)))
      exact good_mk.2 (h1.symm.trans h2)
    · exact hG e (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem he))
  | loop x C W n =>
    intro e he
    exact hG e (Multiset.mem_cons_of_mem he)

theorem contracts_good {ν : Type} {v : ν → ℕ} {G H : Graph S ν}
    (h : Relation.ReflTransGen Contract G H) (hG : ∀ e ∈ G.wires, Good v e) :
    ∀ e ∈ H.wires, Good v e := by
  induction h with
  | refl => exact hG
  | tail _ hs ih => exact contract_good hs ih

/-- A wire renamed by `End.map σ g` is good for `v` when it was good for `v ∘ g`. -/
theorem good_map {ν : Type} {v : ℕ → ℕ} {σ : ℕ → ℕ} {g : ν → ℕ} {e : Sym2 (End ν)}
    (h : Good (v ∘ g) e) : Good v (Sym2.map (End.map σ g) e) := by
  induction e using Sym2.ind with
  | _ p q =>
    rw [Sym2.map_mk, good_mk]
    have := good_mk.1 h
    cases p <;> cases q <;> simp only [End.map, endVal, Function.comp_apply] at this ⊢ <;>
      exact this

/-- The raw graph of a text made of equations between names of the same value has only good
wires. -/
theorem raw_good {ν : Type} (v : ν → ℕ) :
    ∀ (L : List (Term S ν × Term S ν)) (k : ℕ),
      (∀ p ∈ L, ∃ x y, p = (.var x, .var y) ∧ v x = v y) → ∀ e ∈ (raw k L).wires, Good v e
  | [], _, _ => by intro e he; simp [raw] at he
  | (a, b) :: L, k, hL => by
    obtain ⟨x, y, hxy, hv⟩ := hL _ (List.mem_cons_self ..)
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    intro e he
    simp only [raw, Term.rawWires, Term.rootEnd, Term.size, zero_add, add_zero,
      Multiset.mem_cons] at he
    rcases he with rfl | he
    · exact good_mk.2 hv
    · exact raw_good v L _ (fun p hp => hL p (List.mem_cons_of_mem _ hp)) e he

/-- The graph of a net made of equations between names of the same value has only good wires. -/
theorem hasGraph_good {ν : Type} [DecidableEq ν] (v : ν → ℕ) {N : Net S ν} {R : Graph S ν}
    (hR : N.HasGraph R)
    (hN : ∀ a b, s(a, b) ∈ N → ∃ x y, a = .var x ∧ b = .var y ∧ v x = v y) :
    ∀ e ∈ R.wires, Good v e := by
  obtain ⟨L, k, rfl, hc, -⟩ := hR
  refine contracts_good hc (raw_good v L k ?_)
  rintro ⟨a, b⟩ hp
  obtain ⟨x, y, rfl, rfl, h⟩ := hN a b (by
    show s(a, b) ∈ ((L.map fun e => s(e.1, e.2) : List _) : Multiset _)
    exact Multiset.mem_coe.2 (List.mem_map.2 ⟨_, hp, rfl⟩))
  exact ⟨x, y, rfl, h⟩

end INet.GraphStepReview

namespace INet.GraphStepReview

open Comb Graph GraphReview GraphStepCheck

/-- Two cells sharing one list of cells: who is who. -/
theorem cells_two {c d : ℕ} {α β a b : sig.Sym} {C : Multiset (ℕ × sig.Sym)}
    (hC : (c, α) ::ₘ (d, β) ::ₘ C = (0, a) ::ₘ (1, b) ::ₘ 0) :
    (c = 0 ∧ α = a ∧ d = 1 ∧ β = b ∨ c = 1 ∧ α = b ∧ d = 0 ∧ β = a) ∧ C = 0 := by
  rw [Multiset.cons_eq_cons] at hC
  rcases hC with ⟨h1, h2⟩ | ⟨-, cs, h2, h3⟩
  · rw [Multiset.cons_eq_cons] at h2
    rcases h2 with ⟨h3, h4⟩ | ⟨-, cs, -, h5⟩
    · simp only [Prod.mk.injEq] at h1 h3
      exact ⟨Or.inl ⟨h1.1, h1.2, h3.1, h3.2⟩, h4⟩
    · exact absurd h5.symm Multiset.cons_ne_zero
  · rw [Multiset.cons_eq_cons] at h3
    rcases h3 with ⟨h4, rfl⟩ | ⟨-, ds, h5, -⟩
    · rw [Multiset.cons_eq_cons] at h2
      rcases h2 with ⟨h6, h7⟩ | ⟨-, es, -, h8⟩
      · simp only [Prod.mk.injEq] at h4 h6
        exact ⟨Or.inr ⟨h4.1.symm, h4.2.symm, h6.1, h6.2⟩, h7⟩
      · exact absurd h8.symm Multiset.cons_ne_zero
    · exact absurd h5.symm Multiset.cons_ne_zero

end INet.GraphStepReview

namespace INet.GraphStepReview

open Comb Graph GraphReview GraphStepCheck

/-- Two cells `0 : a` and `1 : b` joined by their principal ports, the auxiliary ports of `0`
free under the names `0, 1`, those of `1` under `2, 3`: the graph of `a(0, 1) = b(2, 3)`. -/
def pairFree (a b : sig.Sym) : Graph sig ℕ :=
  ⟨(0, a) ::ₘ (1, b) ::ₘ 0, s(.port 0 0, .port 1 0) ::ₘ conConFreeW, 0⟩

/-- What an interaction of `pairFree` is made of, once the cell of `α` is `c` and that of `β` is
`d`: a rule, a graph of it, renamings, and contractions from the glued graph to `H`. -/
def After (c d : ℕ) (α β : sig.Sym) (H : Graph sig ℕ) : Prop :=
  ∃ r : Rule sig (sig.arity α) (sig.arity β), system.rule α β = some r ∧
    ∃ R : Graph sig (Fin (sig.arity α) ⊕ Fin (sig.arity β) ⊕ Fin r.internal), r.net.HasGraph R ∧
    ∃ (σ : ℕ → ℕ) (g : Fin (sig.arity α) ⊕ Fin (sig.arity β) ⊕ Fin r.internal → ℕ),
      Function.Injective g ∧ (∀ w, End.name (g w) ∉ conConFreeW.bind wireEnds) ∧
      Relation.ReflTransGen Contract
        ⟨0 + R.cells.map (Prod.map σ id),
          conConFreeW.map (Sym2.map (cutEnd c d (fun i => g (.inl i))
            (fun j => g (.inr (.inl j))))) + R.wires.map (Sym2.map (End.map σ g)),
          0 + R.loops⟩ H

/-- **Inversion of an interaction of `pairFree`.** Either the cell of `α` is `0` or it is `1`;
nothing else is chosen by the graph. -/
theorem pairFree_inv {a b : sig.Sym} {H : Graph sig ℕ} (h : Interact system (pairFree a b) H) :
    After 0 1 a b H ∨ After 1 0 b a H := by
  have key : ∀ G, Interact system G H → G = pairFree a b → After 0 1 a b H ∨ After 1 0 b a H := by
    rintro _ ⟨c, d, α, β, C, W, n, r, hr, R, hR, σ, -, -, g, hg, hgW, H, hH, -⟩ hG
    simp only [pairFree, Graph.mk.injEq] at hG
    obtain ⟨hC, hW, rfl⟩ := hG
    obtain ⟨hcd, rfl⟩ := cells_two hC
    rcases hcd with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · have hW' : W = conConFreeW := Multiset.cons_inj_right _ |>.1 hW
      subst hW'
      exact Or.inl ⟨r, hr, R, hR, σ, g, hg, hgW, hH⟩
    · have hW' : W = conConFreeW :=
        Multiset.cons_inj_right _ |>.1 (hW.trans (by rw [Sym2.eq_swap]))
      subst hW'
      exact Or.inr ⟨r, hr, R, hR, σ, g, hg, hgW, hH⟩
  exact key _ h rfl

end INet.GraphStepReview

namespace INet.GraphStepReview

open Comb Graph GraphReview GraphStepCheck

/-- The fresh names of an interaction of `pairFree` are not `0, 1, 2, 3`. -/
theorem fresh_ne {ν : Type} {g : ν → ℕ} (hgW : ∀ w, End.name (g w) ∉ conConFreeW.bind wireEnds)
    (w : ν) : g w ≠ 0 ∧ g w ≠ 1 ∧ g w ≠ 2 ∧ g w ≠ 3 := by
  have := hgW w
  simp only [conConFreeW, Multiset.insert_eq_cons, Multiset.cons_bind, Multiset.singleton_bind,
    wireEnds_mk, Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton, End.name.injEq,
    reduceCtorEq, false_or, not_or] at this
  omega

/-- `i0 s`, `i1 s`: the auxiliary ports `0`, `1` of a binary symbol `s`, at the type
`Fin (sig.arity s)`. -/
local macro "i0 " s:term:max : term => `((⟨0, by decide⟩ : Fin (sig.arity $s)))
/-- See `i0`. -/
local macro "i1 " s:term:max : term => `((⟨1, by decide⟩ : Fin (sig.arity $s)))

/-- The equations of `ruleConCon` are `l0 = r1` and `l1 = r0`. -/
theorem mem_ruleConCon {a b : Term sig (Fin (sig.arity Comb.con) ⊕ Fin (sig.arity Comb.con) ⊕
      Fin ruleConCon.internal)} (h : s(a, b) ∈ ruleConCon.net) :
    (a = .var (.inl (i0 Comb.con)) ∧ b = .var (.inr (.inl (i1 Comb.con))) ∨
      b = .var (.inl (i0 Comb.con)) ∧ a = .var (.inr (.inl (i1 Comb.con)))) ∨
    (a = .var (.inl (i1 Comb.con)) ∧ b = .var (.inr (.inl (i0 Comb.con))) ∨
      b = .var (.inl (i1 Comb.con)) ∧ a = .var (.inr (.inl (i0 Comb.con)))) := by
  change s(a, b) ∈ (s(.var (.inl (i0 Comb.con)), .var (.inr (.inl (i1 Comb.con)))) ::ₘ
    {s(.var (.inl (i1 Comb.con)), .var (.inr (.inl (i0 Comb.con))))} : Net sig _) at h
  simp only [Multiset.mem_cons, Multiset.mem_singleton, Sym2.eq_iff] at h
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact Or.inl (Or.inl ⟨h1, h2⟩)
  · exact Or.inl (Or.inr ⟨h2, h1⟩)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr ⟨h2, h1⟩)

@[simp] theorem cutEnd_name {c d a b x : ℕ} {u : Fin a → ℕ} {v : Fin b → ℕ} :
    cutEnd c d u v (.name x) = .name x := rfl

theorem cutEnd_c {c d a b k : ℕ} {u : Fin a → ℕ} {v : Fin b → ℕ} (hk : k < a) :
    cutEnd c d u v (.port c (k + 1)) = .name (u ⟨k, hk⟩) := by
  simp [cutEnd, hk]

theorem cutEnd_d {c d a b k : ℕ} {u : Fin a → ℕ} {v : Fin b → ℕ} (hcd : d ≠ c) (hk : k < b) :
    cutEnd c d u v (.port d (k + 1)) = .name (v ⟨k, hk⟩) := by
  simp [cutEnd, hk, hcd]

/-- The result of `con`–`con` on `con(0, 1) = con(2, 3)` if the auxiliary ports were joined in
order, as in `ruleDupDup`: the wires `0–2` and `1–3`. -/
def conConFreeInOrder : Graph sig ℕ := ⟨0, s(.name 0, .name 2) ::ₘ {s(.name 1, .name 3)}, 0⟩

/-- The result of `dup`–`dup` on `dup(0, 1) = dup(2, 3)` if the auxiliary ports were exchanged,
as in `ruleConCon`: the wires `0–3` and `1–2`. -/
def dupDupFreeExchanged : Graph sig ℕ := ⟨0, s(.name 0, .name 3) ::ₘ {s(.name 1, .name 2)}, 0⟩

/-- The equations of `ruleDupDup` are `l0 = r0` and `l1 = r1`. -/
theorem mem_ruleDupDup {a b : Term sig (Fin (sig.arity Comb.dup) ⊕ Fin (sig.arity Comb.dup) ⊕
      Fin ruleDupDup.internal)} (h : s(a, b) ∈ ruleDupDup.net) :
    (a = .var (.inl (i0 Comb.dup)) ∧ b = .var (.inr (.inl (i0 Comb.dup))) ∨
      b = .var (.inl (i0 Comb.dup)) ∧ a = .var (.inr (.inl (i0 Comb.dup)))) ∨
    (a = .var (.inl (i1 Comb.dup)) ∧ b = .var (.inr (.inl (i1 Comb.dup))) ∨
      b = .var (.inl (i1 Comb.dup)) ∧ a = .var (.inr (.inl (i1 Comb.dup)))) := by
  change s(a, b) ∈ (s(.var (.inl (i0 Comb.dup)), .var (.inr (.inl (i0 Comb.dup)))) ::ₘ
    {s(.var (.inl (i1 Comb.dup)), .var (.inr (.inl (i1 Comb.dup))))} : Net sig _) at h
  simp only [Multiset.mem_cons, Multiset.mem_singleton, Sym2.eq_iff] at h
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact Or.inl (Or.inl ⟨h1, h2⟩)
  · exact Or.inl (Or.inr ⟨h2, h1⟩)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr ⟨h2, h1⟩)

/-- **The valuation argument.** If, for every choice of the data of an interaction, some valuation
makes the cut wires and the wires of the rule good, then every wire of the result is good for it;
so a graph with a bad wire for every such valuation is not a result. -/
theorem after_good {c d : ℕ} {α β : sig.Sym} {H : Graph sig ℕ} (h : After c d α β H)
    (P : Graph sig ℕ → Prop)
    (hP : ∀ (r : Rule sig (sig.arity α) (sig.arity β)), system.rule α β = some r →
      ∀ R : Graph sig (Fin (sig.arity α) ⊕ Fin (sig.arity β) ⊕ Fin r.internal), r.net.HasGraph R →
      ∀ g : Fin (sig.arity α) ⊕ Fin (sig.arity β) ⊕ Fin r.internal → ℕ, Function.Injective g →
      (∀ w, End.name (g w) ∉ conConFreeW.bind wireEnds) →
      ∃ v : ℕ → ℕ, (∀ e ∈ conConFreeW, Good v (Sym2.map (cutEnd c d (fun i => g (.inl i))
            (fun j => g (.inr (.inl j)))) e)) ∧ (∀ e ∈ R.wires, Good (v ∘ g) e) ∧
        ∀ H : Graph sig ℕ, (∀ e ∈ H.wires, Good v e) → P H) : P H := by
  obtain ⟨r, hr, R, hR, σ, g, hg, hgW, hH⟩ := h
  obtain ⟨v, hcut, hRg, hPv⟩ := hP r hr R hR g hg hgW
  refine hPv H (contracts_good hH ?_)
  intro e he
  rcases Multiset.mem_add.1 he with he | he
  · obtain ⟨e', he', rfl⟩ := Multiset.mem_map.1 he
    exact hcut e' he'
  · obtain ⟨e', he', rfl⟩ := Multiset.mem_map.1 he
    exact good_map (hRg e' he')

/-- A graph whose wire `x–y` has ends of different values is not good. -/
theorem not_good_of_mem {v : ℕ → ℕ} {H : Graph sig ℕ} {x y : ℕ} (hm : s(.name x, .name y) ∈ H.wires)
    (hv : v x ≠ v y) : ¬ ∀ e ∈ H.wires, Good v e :=
  fun h => hv (good_mk.1 (h _ hm))

set_option linter.unusedSimpArgs false in
/-- **`con`–`con` exchanges the auxiliary ports** (Lafont 1997, page 73, with `ruleConCon`). On
`con(0, 1) = con(2, 3)`, the graph with the wires `0–2` and `1–3` (the ports joined in order) is
not a result of `Interact`, whatever the choice of the cell of `α`, of the graph of the rule, of
the renamings and of the order of contraction. The proof: the names `0, 3` and the fresh names
glued to them by the rule get the value `1`, the others `2`; every wire of the glued graph joins
two ends of the same value, contraction keeps this, and `0–2` does not. -/
theorem conCon_not_inOrder : ¬ Interact system conConFree conConFreeInOrder := by
  intro h
  have hbad : ∀ v : ℕ → ℕ, v 0 ≠ v 2 → ¬ ∀ e ∈ conConFreeInOrder.wires, Good v e :=
    fun v hv => not_good_of_mem (by decide) hv
  rcases pairFree_inv (a := Comb.con) (b := Comb.con) h with h | h <;>
  refine after_good h (fun H => ¬ H = conConFreeInOrder) ?_ rfl <;>
  intro r hr R hR g hg hgW <;>
  obtain rfl : ruleConCon = r := Option.some.inj hr <;>
  have h0 := fun w => (fresh_ne hgW w).1 <;>
  have h1 := fun w => (fresh_ne hgW w).2.1 <;>
  have h2 := fun w => (fresh_ne hgW w).2.2.1 <;>
  have h3 := fun w => (fresh_ne hgW w).2.2.2
  · refine ⟨fun x => if x = 0 ∨ x = 3 ∨ x = g (.inl ⟨0, by decide⟩) ∨
      x = g (.inr (.inl ⟨1, by decide⟩)) then 1 else 2, ?_, ?_, ?_⟩
    · intro e he
      simp only [conConFreeW, Multiset.mem_cons, Multiset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl <;>
        simp [Sym2.map_mk, good_mk, endVal, cutEnd_c (show 0 < sig.arity con by decide),
          cutEnd_c (show 1 < sig.arity con by decide),
          cutEnd_d (show 1 ≠ 0 by decide) (show 0 < sig.arity con by decide),
          cutEnd_d (show 1 ≠ 0 by decide) (show 1 < sig.arity con by decide),
          h0, h1, h2, h3, hg.eq_iff, fun w => (h0 w).symm, fun w => (h1 w).symm,
          fun w => (h2 w).symm, fun w => (h3 w).symm]
    · refine hasGraph_good _ hR fun a b hab => ?_
      rcases mem_ruleConCon hab with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        exact ⟨_, _, rfl, rfl, by simp [hg.eq_iff, h0, h1, h2, h3, fun w => (h0 w).symm,
          fun w => (h3 w).symm]⟩
    · intro H hH e
      subst e
      exact hbad _ (by simp [fun w => (h0 w).symm, fun w => (h2 w).symm]) hH
  · refine ⟨fun x => if x = 0 ∨ x = 3 ∨ x = g (.inl ⟨1, by decide⟩) ∨
      x = g (.inr (.inl ⟨0, by decide⟩)) then 1 else 2, ?_, ?_, ?_⟩
    · intro e he
      simp only [conConFreeW, Multiset.mem_cons, Multiset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl <;>
        simp [Sym2.map_mk, good_mk, endVal, cutEnd_c (show 0 < sig.arity con by decide),
          cutEnd_c (show 1 < sig.arity con by decide),
          cutEnd_d (show 0 ≠ 1 by decide) (show 0 < sig.arity con by decide),
          cutEnd_d (show 0 ≠ 1 by decide) (show 1 < sig.arity con by decide),
          h0, h1, h2, h3, hg.eq_iff, fun w => (h0 w).symm, fun w => (h1 w).symm,
          fun w => (h2 w).symm, fun w => (h3 w).symm]
    · refine hasGraph_good _ hR fun a b hab => ?_
      rcases mem_ruleConCon hab with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        exact ⟨_, _, rfl, rfl, by simp [hg.eq_iff, h0, h1, h2, h3, fun w => (h0 w).symm,
          fun w => (h3 w).symm]⟩
    · intro H hH e
      subst e
      exact hbad _ (by simp [fun w => (h0 w).symm, fun w => (h2 w).symm]) hH

/-- A joining of two wires, the graph after given by the rest of the wires. -/
theorem join' {G : Graph sig ℕ} (x : ℕ) (p q : End ℕ) (W : Multiset (Sym2 (End ℕ)))
    (hG : G.wires = s(.name x, p) ::ₘ s(.name x, q) ::ₘ W) :
    Contract G ⟨G.cells, s(p, q) ::ₘ W, G.loops⟩ :=
  join_eq x p q W hG rfl rfl rfl

/-- The graph of `dup(0, 1) = dup(2, 3)`. -/
abbrev dupDupFree : Graph sig ℕ := pairFree Comb.dup Comb.dup

/-- **`dup`–`dup` joins the auxiliary ports in order** (Lafont 1997, page 73, with `ruleDupDup`).
On `dup(0, 1) = dup(2, 3)` the result has the wires `0–2` and `1–3`. Fresh names `4, 5` and
`6, 7`; the contractions erase `4, 6, 5, 7`. -/
theorem dupDup_free : Interact system dupDupFree conConFreeInOrder := by
  refine Interact.mk (I := system) 0 1 Comb.dup Comb.dup 0 conConFreeW 0 ruleDupDup rfl
    (raw 0 dupDupText) dupDup_hasGraph id (Set.injOn_id _) (by decide) (fresh 4)
    (fresh_injective 4) (by decide) conConFreeInOrder ?_ (count_le_one_of_nodup (by decide))
  refine .head (join' 4 (.name 0) (.name 6) (s(.name 5, .name 1) ::ₘ s(.name 6, .name 2) ::ₘ
    s(.name 7, .name 3) ::ₘ {s(.name 5, .name 7)}) (by decide)) ?_
  refine .head (join' 6 (.name 0) (.name 2) (s(.name 5, .name 1) ::ₘ s(.name 7, .name 3) ::ₘ
    {s(.name 5, .name 7)}) (by decide)) ?_
  refine .head (join' 5 (.name 1) (.name 7) (s(.name 0, .name 2) ::ₘ {s(.name 7, .name 3)})
    (by decide)) ?_
  exact .single (join_eq 7 (.name 1) (.name 3) {s(.name 0, .name 2)} (by decide) rfl
    (by decide) rfl)

set_option linter.unusedSimpArgs false in
/-- **`dup`–`dup` does not exchange the auxiliary ports** (Lafont 1997, page 73, with
`ruleDupDup`). On `dup(0, 1) = dup(2, 3)`, the graph with the wires `0–3` and `1–2` is not a
result of `Interact`, whatever the choices. Same valuation argument as `conCon_not_inOrder`, with
`0, 2` and the fresh names glued to them in the class of value `1`. -/
theorem dupDup_not_exchanged : ¬ Interact system dupDupFree dupDupFreeExchanged := by
  intro h
  have hbad : ∀ v : ℕ → ℕ, v 0 ≠ v 3 → ¬ ∀ e ∈ dupDupFreeExchanged.wires, Good v e :=
    fun v hv => not_good_of_mem (by decide) hv
  rcases pairFree_inv (a := Comb.dup) (b := Comb.dup) h with h | h <;>
  refine after_good h (fun H => ¬ H = dupDupFreeExchanged) ?_ rfl <;>
  intro r hr R hR g hg hgW <;>
  obtain rfl : ruleDupDup = r := Option.some.inj hr <;>
  have h0 := fun w => (fresh_ne hgW w).1 <;>
  have h1 := fun w => (fresh_ne hgW w).2.1 <;>
  have h2 := fun w => (fresh_ne hgW w).2.2.1 <;>
  have h3 := fun w => (fresh_ne hgW w).2.2.2 <;>
  refine ⟨fun x => if x = 0 ∨ x = 2 ∨ x = g (.inl ⟨0, by decide⟩) ∨
      x = g (.inr (.inl ⟨0, by decide⟩)) then 1 else 2, ?_, ?_, ?_⟩
  · intro e he
    simp only [conConFreeW, Multiset.mem_cons, Multiset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Sym2.map_mk, good_mk, endVal, cutEnd_c (show 0 < sig.arity dup by decide),
        cutEnd_c (show 1 < sig.arity dup by decide),
        cutEnd_d (show 1 ≠ 0 by decide) (show 0 < sig.arity dup by decide),
        cutEnd_d (show 1 ≠ 0 by decide) (show 1 < sig.arity dup by decide),
        h0, h1, h2, h3, hg.eq_iff, fun w => (h0 w).symm, fun w => (h1 w).symm,
        fun w => (h2 w).symm, fun w => (h3 w).symm]
  · refine hasGraph_good _ hR fun a b hab => ?_
    rcases mem_ruleDupDup hab with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      exact ⟨_, _, rfl, rfl, by simp [hg.eq_iff, h0, h1, h2, h3, fun w => (h0 w).symm,
        fun w => (h2 w).symm]⟩
  · intro H hH e
    subst e
    exact hbad _ (by simp [fun w => (h0 w).symm, fun w => (h3 w).symm]) hH
  · intro e he
    simp only [conConFreeW, Multiset.mem_cons, Multiset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Sym2.map_mk, good_mk, endVal, cutEnd_c (show 0 < sig.arity dup by decide),
        cutEnd_c (show 1 < sig.arity dup by decide),
        cutEnd_d (show 0 ≠ 1 by decide) (show 0 < sig.arity dup by decide),
        cutEnd_d (show 0 ≠ 1 by decide) (show 1 < sig.arity dup by decide),
        h0, h1, h2, h3, hg.eq_iff, fun w => (h0 w).symm, fun w => (h1 w).symm,
        fun w => (h2 w).symm, fun w => (h3 w).symm]
  · refine hasGraph_good _ hR fun a b hab => ?_
    rcases mem_ruleDupDup hab with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      exact ⟨_, _, rfl, rfl, by simp [hg.eq_iff, h0, h1, h2, h3, fun w => (h0 w).symm,
        fun w => (h2 w).symm]⟩
  · intro H hH e
    subst e
    exact hbad _ (by simp [fun w => (h0 w).symm, fun w => (h3 w).symm]) hH

/-! ## Which cell is `α` -/

/-- **`con`–`con` read from the other cell gives the same result** (Lafont 1997, page 73: a rule
of a symbol with itself is the same read from either cell). The interaction of `conCon_free`,
with the cell of `α` taken to be `1` instead of `0`: the graph is the same value, because a
multiset of cells and an unordered wire do not record an order, and the result is again
`conConFreeAfter`. Fresh names `4, 5` (cell `1`) and `6, 7` (cell `0`); the contractions erase
`4, 7, 5, 6`. -/
theorem conCon_free_other_cell : Interact system conConFree conConFreeAfter := by
  have e : conConFree = ⟨(1, Comb.con) ::ₘ (0, Comb.con) ::ₘ 0,
      s(.port 1 0, .port 0 0) ::ₘ conConFreeW, 0⟩ :=
    graph_eq (Multiset.cons_swap (_ : ℕ × sig.Sym) _ 0) (by decide) rfl
  rw [e]
  refine Interact.mk (I := system) 1 0 Comb.con Comb.con 0 conConFreeW 0 ruleConCon rfl
    (raw 0 conConText) conCon_hasGraph id (Set.injOn_id _) (by decide) (fresh 4)
    (fresh_injective 4) (by decide) conConFreeAfter ?_ (count_le_one_of_nodup (by decide))
  refine .head (join' 4 (.name 2) (.name 7) (s(.name 6, .name 0) ::ₘ s(.name 7, .name 1) ::ₘ
    s(.name 5, .name 3) ::ₘ {s(.name 5, .name 6)}) (by decide)) ?_
  refine .head (join' 7 (.name 1) (.name 2) (s(.name 6, .name 0) ::ₘ s(.name 5, .name 3) ::ₘ
    {s(.name 5, .name 6)}) (by decide)) ?_
  refine .head (join' 5 (.name 3) (.name 6) (s(.name 1, .name 2) ::ₘ {s(.name 6, .name 0)})
    (by decide)) ?_
  exact .single (join_eq 6 (.name 3) (.name 0) {s(.name 1, .name 2)} (by decide) rfl
    (by decide) rfl)

/-- **The fresh names do not matter** (Lafont 1997, page 73). The interaction of `conCon_free`
with the fresh names `10, …, 13` instead of `4, …, 7` gives the same graph. -/
theorem conCon_free_other_names : Interact system conConFree conConFreeAfter := by
  refine Interact.mk (I := system) 0 1 Comb.con Comb.con 0 conConFreeW 0 ruleConCon rfl
    (raw 0 conConText) conCon_hasGraph id (Set.injOn_id _) (by decide) (fresh 10)
    (fresh_injective 10) (by decide) conConFreeAfter ?_ (count_le_one_of_nodup (by decide))
  refine .head (join' 10 (.name 0) (.name 13) (s(.name 11, .name 1) ::ₘ s(.name 12, .name 2) ::ₘ
    s(.name 13, .name 3) ::ₘ {s(.name 11, .name 12)}) (by decide)) ?_
  refine .head (join' 13 (.name 0) (.name 3) (s(.name 11, .name 1) ::ₘ s(.name 12, .name 2) ::ₘ
    {s(.name 11, .name 12)}) (by decide)) ?_
  refine .head (join' 11 (.name 1) (.name 12) (s(.name 0, .name 3) ::ₘ {s(.name 12, .name 2)})
    (by decide)) ?_
  exact .single (join_eq 12 (.name 1) (.name 2) {s(.name 0, .name 3)} (by decide) rfl
    (by decide) rfl)

/-- The graph of `con(0, 1) = dup(2, 3)`, and the same graph written with the `dup` cell first:
they are one value. Neither `Graph` nor `Interact` records which cell of an active pair comes
first. -/
theorem pairFree_conDup_eq : pairFree Comb.con Comb.dup =
    ⟨(1, Comb.dup) ::ₘ (0, Comb.con) ::ₘ 0, s(.port 1 0, .port 0 0) ::ₘ conConFreeW, 0⟩ :=
  graph_eq (Multiset.cons_swap (_ : ℕ × sig.Sym) _ 0) (by decide) rfl

/-- Fresh names for `ruleConDup`: `4, 5` and `6, 7` for the auxiliary ports, `8, …, 11` for its
four internal wires. -/
def freshCD : Fin 2 ⊕ Fin 2 ⊕ Fin 4 → ℕ :=
  Sum.elim (fun i => 4 + i) (Sum.elim (fun j => 6 + j) fun w => 8 + w)

theorem freshCD_injective : Function.Injective freshCD := by
  intro x y h
  rcases x with i | j | w <;> rcases y with i' | j' | w' <;>
    simp only [freshCD, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq] at h ⊢ <;> omega

/-- An interaction of a graph `pairFree a b` with a rule for `a, b`, its cells renumbered from
`2`. It exists for any graph of the rule. -/
theorem pairFree_interact_of_rule {a b : sig.Sym} (r : Rule sig (sig.arity a) (sig.arity b))
    (hr : system.rule a b = some r)
    (g : Fin (sig.arity a) ⊕ Fin (sig.arity b) ⊕ Fin r.internal → ℕ) (hg : Function.Injective g)
    (hgW : ∀ w, End.name (g w) ∉ conConFreeW.bind wireEnds) :
    ∃ H, Interact system (pairFree a b) H := by
  obtain ⟨R, hR, -⟩ := r.net.exists_graph
  obtain ⟨H, hH, hH1⟩ := exists_contracts (⟨0 + R.cells.map (Prod.map (· + 2) id),
      conConFreeW.map (Sym2.map (cutEnd 0 1 (fun i => g (.inl i))
        (fun j => g (.inr (.inl j))))) + R.wires.map (Sym2.map (End.map (· + 2) g)),
      0 + R.loops⟩ : Graph sig ℕ)
  refine ⟨H, Interact.mk (I := system) 0 1 a b 0 conConFreeW 0 r hr R hR (· + 2)
    (fun x _ y _ h => by simpa using h) ?_ g hg hgW H hH hH1⟩
  intro x _
  simp only [Multiset.map_cons, Multiset.map_zero, Multiset.mem_cons, Multiset.notMem_zero,
    or_false, not_or]
  omega

/-- **`con`–`dup` interacts, with the cell of `α` the `con` cell** (Lafont 1997, page 73). The
graph of `con(0, 1) = dup(2, 3)` has an interaction through `ruleConDup`. -/
theorem conDup_interact : ∃ H, Interact system (pairFree Comb.con Comb.dup) H :=
  pairFree_interact_of_rule ruleConDup rfl freshCD freshCD_injective (by decide)

/-- **`dup`–`con` interacts too, with no rule for `dup, con`** (Lafont 1997, page 73). The graph
of `dup(0, 1) = con(2, 3)` has an interaction, with the cell of `α` the cell `1`. -/
theorem dupCon_interact : ∃ H, Interact system (pairFree Comb.dup Comb.con) H := by
  have e : pairFree Comb.dup Comb.con =
      ⟨(1, Comb.con) ::ₘ (0, Comb.dup) ::ₘ 0, s(.port 1 0, .port 0 0) ::ₘ conConFreeW, 0⟩ :=
    graph_eq (Multiset.cons_swap (_ : ℕ × sig.Sym) _ 0) (by decide) rfl
  obtain ⟨R, hR, -⟩ := ruleConDup.net.exists_graph
  let g := freshCD
  obtain ⟨H, hH, hH1⟩ := exists_contracts (⟨0 + R.cells.map (Prod.map (· + 2) id),
      conConFreeW.map (Sym2.map (cutEnd 1 0 (fun i => g (.inl i))
        (fun j => g (.inr (.inl j))))) + R.wires.map (Sym2.map (End.map (· + 2) g)),
      0 + R.loops⟩ : Graph sig ℕ)
  refine ⟨H, e ▸ Interact.mk (I := system) 1 0 Comb.con Comb.dup 0 conConFreeW 0 ruleConDup rfl
    R hR (· + 2) (fun x _ y _ h => by simpa using h) ?_ g freshCD_injective (by decide) H hH hH1⟩
  intro x _
  simp only [Multiset.map_cons, Multiset.map_zero, Multiset.mem_cons, Multiset.notMem_zero,
    or_false, not_or]
  omega

/-- **Every interaction of `con(0, 1) = dup(2, 3)` takes the `con` cell for `α`** (Lafont 1997,
page 73). `system` has a rule for `con, dup` and none for `dup, con`, so of the two readings of
the active pair only one applies: the result is never computed from a second, different rule. -/
theorem conDup_cell_of_alpha {H : Graph sig ℕ}
    (h : Interact system (pairFree Comb.con Comb.dup) H) :
    After 0 1 Comb.con Comb.dup H := by
  rcases pairFree_inv h with h | ⟨r, hr, -⟩
  · exact h
  · exact absurd hr (by simp [system])

/-! ## Degenerate cases -/

/-- No name for the auxiliary ports of two erasers and no internal wire. -/
abbrev EN : Type := Fin (sig.arity Comb.era) ⊕ Fin (sig.arity Comb.era) ⊕ Fin ruleEraEra.internal

theorem en_empty (w : EN) : False := by
  rcases w with i | i | i <;> exact i.elim0

/-- The graph of `ruleEraEra`: empty. -/
theorem eraEra_hasGraph : ruleEraEra.net.HasGraph (⟨0, 0, 0⟩ : Graph sig EN) :=
  ⟨[], 0, rfl, .refl, by decide⟩

/-- Two erasers joined by their principal ports, next to a free wire `0–1` and a cyclic wire. -/
def eraEra : Graph sig ℕ :=
  ⟨(0, Comb.era) ::ₘ (1, Comb.era) ::ₘ 0, s(.port 0 0, .port 1 0) ::ₘ {s(.name 0, .name 1)}, 1⟩

/-- What is left: the free wire `0–1` and the cyclic wire. -/
def eraEraAfter : Graph sig ℕ := ⟨0, {s(.name 0, .name 1)}, 1⟩

/-- **`era`–`era`: the two cells and their wire disappear, the rest is kept** (Lafont 1997,
page 73, with `ruleEraEra`, a rule with no auxiliary port and an empty net). No fresh name and no
contraction. -/
theorem eraEra_interact : Interact system eraEra eraEraAfter :=
  Interact.mk (I := system) 0 1 Comb.era Comb.era 0
    ({s(End.name (0 : ℕ), End.name 1)} : Multiset (Sym2 (End ℕ))) 1
    ruleEraEra rfl
    ⟨0, 0, 0⟩ eraEra_hasGraph id (Set.injOn_id _) (by simp) (fun _ => 0)
    (fun w => (en_empty w).elim) (fun w => (en_empty w).elim) eraEraAfter .refl
    (count_le_one_of_nodup (by decide))

theorem eraEra_wf : eraEra.WF := (wf_iff _).2 (by decide)

/-- The graph of `con(x, x) = con(0, 1)`: the two auxiliary ports of the cell `0` are joined by
the wire `x`, those of `1` are free under `0, 1`. -/
def conSelf : Graph sig ℕ :=
  ⟨(0, Comb.con) ::ₘ (1, Comb.con) ::ₘ 0, s(.port 0 0, .port 1 0) ::ₘ s(.port 0 1, .port 0 2) ::ₘ
    s(.port 1 1, .name 0) ::ₘ {s(.port 1 2, .name 1)}, 0⟩

theorem conSelf_wf : conSelf.WF := (wf_iff _).2 (by decide)

/-- **A wire from one auxiliary port of `c` to the other** (Lafont 1997, page 73). On
`con(x, x) = con(0, 1)` the result is the single wire `0–1`: the rule joins `l0–r1` and `l1–r0`,
and `x` joins `l0–l1`. Fresh names `2, 3` and `4, 5`; the contractions erase `2, 3, 5, 4`. The
other degenerate wirings, an auxiliary port of `c` wired to one of `d`, are `dupDup_shared` and
`conCon_closed` of `Checks/Graphs/GraphStepCheck.lean`. -/
theorem conSelf_interact : Interact system conSelf freeWire := by
  refine Interact.mk (I := system) 0 1 Comb.con Comb.con 0 (s(.port 0 1, .port 0 2) ::ₘ
    s(.port 1 1, .name 0) ::ₘ {s(.port 1 2, .name 1)}) 0 ruleConCon rfl
    (raw 0 conConText) conCon_hasGraph id (Set.injOn_id _) (by decide) (fresh 2)
    (fresh_injective 2) (by decide) freeWire ?_ (count_le_one_of_nodup (by decide))
  refine .head (join' 2 (.name 3) (.name 5) (s(.name 4, .name 0) ::ₘ s(.name 5, .name 1) ::ₘ
    {s(.name 3, .name 4)}) (by decide)) ?_
  refine .head (join' 3 (.name 5) (.name 4) (s(.name 4, .name 0) ::ₘ {s(.name 5, .name 1)})
    (by decide)) ?_
  refine .head (join' 5 (.name 4) (.name 1) {s(.name 4, .name 0)} (by decide)) ?_
  exact .single (join_eq 4 (.name 1) (.name 0) 0 (by decide) rfl (by decide) rfl)

/-- Two `con` cells with the same number `0`, joined principal port to principal port, the
auxiliary ports free under `0, 1`. It is not well formed. -/
def sameCell : Graph sig ℕ :=
  ⟨(0, Comb.con) ::ₘ (0, Comb.con) ::ₘ 0, s(.port 0 0, .port 0 0) ::ₘ
    s(.port 0 1, .name 0) ::ₘ {s(.port 0 2, .name 1)}, 0⟩

theorem not_wf_sameCell : ¬ sameCell.WF := fun h => by
  have := (wf_iff _).1 h
  revert this
  decide

/-- **On a graph that is not well formed, `Interact` gives a meaningless result** (`c = d`).
With both cells numbered `0`, the cut sends the auxiliary ports of `0` to the names of the first
cell only; the names `4, 5` given to the auxiliary ports of the second cell then occur once each
and survive as free ports that the graph before did not have. This does not concern part 2 of
Stage C.5: the graph of a net is well formed (`Net.HasGraph.wf`), and `Interact.wf` assumes it. -/
theorem sameCell_interact :
    Interact system sameCell ⟨0, s(.name 0, .name 5) ::ₘ {s(.name 1, .name 4)}, 0⟩ := by
  refine Interact.mk (I := system) 0 0 Comb.con Comb.con 0 (s(.port 0 1, .name 0) ::ₘ
    {s(.port 0 2, .name 1)}) 0 ruleConCon rfl
    (raw 0 conConText) conCon_hasGraph id (Set.injOn_id _) (by decide) (fresh 2)
    (fresh_injective 2) (by decide) ⟨0, s(.name 0, .name 5) ::ₘ {s(.name 1, .name 4)}, 0⟩ ?_
    (count_le_one_of_nodup (by decide))
  refine .head (join' 2 (.name 0) (.name 5) (s(.name 3, .name 1) ::ₘ {s(.name 3, .name 4)})
    (by decide)) ?_
  exact .single (join_eq 3 (.name 1) (.name 4) {s(.name 0, .name 5)} (by decide) rfl
    (by decide) rfl)

/-- **`hgW` is what keeps the fresh names away from the free ports.** With the fresh names
`0, …, 3`, which are the free ports of `con(0, 1) = con(2, 3)`, the condition fails. Every name
of a graph `⟨…, s(port c 0, port d 0) ::ₘ W, n⟩` occurs in `W`, since the wire between the
principal ports has none; so `hgW` says exactly that the fresh names are not names of the graph. -/
theorem hgW_excludes_free : ¬ ∀ w, End.name (fresh 0 w) ∉ conConFreeW.bind wireEnds := by
  decide

/-! ## Agreement with interaction on texts -/

/-- The text `x = x, 1 = 2`, with `x = 0`. -/
def dupDupSharedAfterText : List (Term sig ℕ × Term sig ℕ) :=
  [(.var 0, .var 0), (.var 1, .var 2)]

/-- **One instance of part 2 of Stage C.5** (Lafont 1997, pages 71 and 73). The linear net
`dup(x, 1) = dup(x, 2)` has the graph `dupDupShared`; one `Step` of `ruleDupDup` rewrites it into
`x = x, 1 = 2`, whose graph is `dupDupSharedAfter` (a cyclic wire and the wire `1–2`); and
`Interact` takes `dupDupShared` to that same graph. -/
theorem dupDupShared_agree :
    (Net.ofList dupDupText2).Linear ∧ (Net.ofList dupDupText2).HasGraph dupDupShared ∧
    Step system (Net.ofList dupDupText2) (Net.ofList dupDupSharedAfterText) ∧
    (Net.ofList dupDupSharedAfterText).HasGraph dupDupSharedAfter ∧
    Interact system dupDupShared dupDupSharedAfter ∧ Iso dupDupSharedAfter dupDupSharedAfter := by
  refine ⟨?_, dupDupShared_hasGraph, ?_, ?_, dupDup_shared, Iso.refl _⟩
  · intro x
    by_cases h : x = 0 <;> by_cases h' : x = 1 <;> by_cases h'' : x = 2 <;>
      simp_all [Net.ofList, dupDupText2, Net.vars]
  · exact Step.mk (I := system) Comb.dup Comb.dup ruleDupDup rfl
      (![Term.var 0, Term.var 1] : Fin 2 → Term sig ℕ)
      (![Term.var 0, Term.var 2] : Fin 2 → Term sig ℕ)
      0 Fin.elim0 (fun i => i.elim0) (fun i => i.elim0)
  · exact ⟨dupDupSharedAfterText, 0, rfl,
      .single (loop_eq 0 {s(.name 1, .name 2)} (by decide) rfl rfl rfl),
      count_le_one_of_nodup (by decide)⟩

end INet.GraphStepReview
