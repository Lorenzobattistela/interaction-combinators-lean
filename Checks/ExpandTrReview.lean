import InteractionCombinators.Lafont.ExpandedRoot
import Checks.ExpandCheck
import Checks.TranslationExistsCheck

/-!
# Review of the tools for Fig. 6: `Rule.Expanded`, `Rule.exists_expanded`, `Translation.trTerm`

Lafont 1997, page 86 (Fig. 6) and Section 1.7, pages 79–80. Issue #87.

## Expanded form

The paper has no expanded form; it is the normal form chosen for the symmetric decomposition of
page 86. The checks below argue that it is harmless.

* The rules of the combinators. `ruleConDup`, `ruleEraBin` and `ruleEraEra` are already expanded
  (`ruleConDup_expanded`, `ruleEraBin_expanded`, `ruleEraEra_expanded`). `ruleConCon` and
  `ruleDupDup` are not (each equation joins two ports); the construction of `Rule.exists_expanded`
  (`Expand.stepRule`, applied twice) is computed on them and gives the expected expanded rules
  (`conCon_two_steps`, `dupDup_two_steps`). The rules of `systemNoConDup` are among these.
* One tree per port: `Rule.Expanded.existsUnique_root` (`Lafont/ExpandedRoot.lean`). On
  `ruleConDup`, the root tree of each port is computed (`ruleConDup_root`).
* Attempts to refute `Rule.exists_expanded`:
  - a cycle of port-to-port equations `a₀ = b₀, b₀ = a₀` is not linear (`cycle_not_linear`), and in
    a linear reduced rule every equation has its own root port, so no cycle can occur;
  - a port deep inside the tree of another port, `a₀ = con(dup(b₀, ε), b₁)`: two steps pull `b₀`
    and `b₁` out, and the result is expanded (`deep_two_steps`, `deepExp_expanded`);
  - the empty rule: a linear reduced rule with no port has no equation and no internal wire
    (`eq_empty_of_no_port`), and it is expanded.

## `trTerm`

* `Φswap` translates `con` into `con` with its auxiliary ports exchanged: `trTerm` exchanges the
  subtrees of every `con` cell, at every depth (`swap_depth2`). So the `i`-th subtree goes to the
  `i`-th auxiliary port of `Φ(α)`, wherever that port sits in the tree of `Φ(α)`.
* `Φrev` translates `con` into a tree of two cells joined by one internal wire, its ports in the
  reverse order: `con(con(p₁, w), con(w, p₀))`. On a tree of depth 2 the names of the three
  instances are `10`, `11`, `12`: the root takes `10`, its first subtree `11` and its second
  subtree `12` (`rev_depth2`); when the first subtree has no internal wire, the second starts at
  `11` (`rev_mixed`). The names are both ends of each block, and the blocks are disjoint
  (`rev_depth2_vars`, by `decide`, agreeing with `vars_trTerm`).
-/

namespace INet.Comb.ExpandTrReview

open Term Rule DecompositionReview DecompositionCheck ExpandedIsoCheck

/-! ## The rules of the combinators -/

/-- `con`–`dup` is already expanded: each port is the root of a tree whose leaves are internal
wires (page 86). -/
theorem ruleConDup_expanded : ruleConDup.Expanded := by
  change (⟨4, (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 4) from ruleConDup.net)⟩ : Rule sig 2 2).Expanded
  intro e he
  have key : ∀ e ∈ (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 4) from ruleConDup.net),
      e ∈ [s(pl 0, mkDup (pw 0) (pw 1)), s(pl 1, mkDup (pw 2) (pw 3)),
        s(pr 0, mkCon (pw 0) (pw 2)), s(pr 1, mkCon (pw 1) (pw 3))] := by decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl, fun w h => (by cases h), by decide⟩

/-- `era`–`con` (and `era`–`dup`) is already expanded: each port of the binary cell is the root of
an eraser (page 86). -/
theorem ruleEraBin_expanded : ruleEraBin.Expanded := by
  intro e he
  have key : ∀ e ∈ (show Net sig (Fin 0 ⊕ Fin 2 ⊕ Fin 0) from ruleEraBin.net),
      e ∈ [s(pr 0, mkEra), s(pr 1, mkEra)] := by decide
  rcases List.mem_pair.1 (key e he) with rfl | rfl <;>
    exact ⟨_, _, rfl, fun w h => (by cases h), by decide⟩

/-- `era`–`era` is expanded: it has no equation. -/
theorem ruleEraEra_expanded : ruleEraEra.Expanded := fun _ he => absurd he (Multiset.notMem_zero _)

/-- `con`–`dup` has `a + b = 4` equations, one per port. -/
example : Multiset.card ruleConDup.net = 4 := ruleConDup_expanded.card_eq ruleConDup_linear

/-- The root tree of each port of `con`–`dup`, as given by `Rule.Expanded.existsUnique_root`:
`a₀ = dup(w₀, w₁)`, `a₁ = dup(w₂, w₃)`, `b₀ = con(w₀, w₂)`, `b₁ = con(w₁, w₃)`. -/
theorem ruleConDup_root (t : Term sig (Fin 2 ⊕ Fin 2 ⊕ Fin 4)) :
    (s(pl 0, t) ∈ ruleConDup.net → t = mkDup (pw 0) (pw 1)) ∧
      (s(pl 1, t) ∈ ruleConDup.net → t = mkDup (pw 2) (pw 3)) ∧
      (s(pr 0, t) ∈ ruleConDup.net → t = mkCon (pw 0) (pw 2)) ∧
      (s(pr 1, t) ∈ ruleConDup.net → t = mkCon (pw 1) (pw 3)) := by
  have u := ruleConDup_expanded.existsUnique_root ruleConDup_linear
  refine ⟨fun h => (u (.inl 0)).unique h (by decide), fun h => (u (.inl 1)).unique h (by decide),
    fun h => (u (.inr 0)).unique h (by decide), fun h => (u (.inr 1)).unique h (by decide)⟩

/-- Two steps of the expansion on `con`–`con` (`a₀ = b₁, a₁ = b₀`): pulling out `b₁`, then `b₀`,
gives exactly the expanded rule `a₀ = x₀, b₁ = x₀, a₁ = x₁, b₀ = x₁` (`conConExp`). -/
theorem conCon_two_steps :
    (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2) from
      (Expand.stepRule (Expand.stepRule ruleConCon (.inr 1)) (.inr 0)).net) = conConExp := by
  decide

/-- The expanded `dup`–`dup` rule: `a₀ = x₀, b₀ = x₀, a₁ = x₁, b₁ = x₁`. -/
def dupDupExp : Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2) :=
  s(pl 0, pw 0) ::ₘ s(pr 0, pw 0) ::ₘ s(pl 1, pw 1) ::ₘ {s(pr 1, pw 1)}

/-- `dup`–`dup` (`a₀ = b₀, a₁ = b₁`) is not expanded. -/
theorem ruleDupDup_not_expanded : ¬ ruleDupDup.Expanded := by
  intro h
  have hmem : (s(pl 0, pr 0) : Sym2 (Term sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0))) ∈
      (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0) from ruleDupDup.net) := by decide
  obtain ⟨p, t, he, -, ht⟩ := h _ hmem
  rcases Sym2.eq_iff.1 he with ⟨-, rfl⟩ | ⟨rfl, -⟩
  · exact (ht _ (Multiset.mem_singleton_self _)).choose.elim0
  · exact (ht _ (Multiset.mem_singleton_self _)).choose.elim0

/-- Two steps of the expansion on `dup`–`dup`, pulling out `b₀`, then `b₁`, give `dupDupExp`. -/
theorem dupDup_two_steps :
    (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2) from
      (Expand.stepRule (Expand.stepRule ruleDupDup (.inr 0)) (.inr 1)).net) = dupDupExp := by
  decide

theorem dupDupExp_linear : (⟨2, dupDupExp⟩ : Rule sig 2 2).Linear :=
  ⟨by decide, by decide, by decide⟩

theorem dupDupExp_expanded : (⟨2, dupDupExp⟩ : Rule sig 2 2).Expanded := by
  intro e he
  have key : ∀ e ∈ dupDupExp,
      e ∈ [s(pl 0, pw 0), s(pr 0, pw 0), s(pl 1, pw 1), s(pr 1, pw 1)] := by decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl, fun w h => (by cases h), by decide⟩

/-! ## Attempts to refute `Rule.exists_expanded` -/

/-- A cycle of two port-to-port equations, `a₀ = b₀`, `b₀ = a₀`, is not linear: `a₀` occurs twice.
So `Rule.exists_expanded` never meets it. -/
theorem cycle_not_linear :
    ¬ (⟨0, s(pl 0, pr 0) ::ₘ {s(pr 0, pl 0)}⟩ : Rule sig 1 1).Linear :=
  fun h => absurd (h.left 0) (by decide)

/-- The empty case: a linear reduced rule with no port has no equation (each equation needs a root
port) and no internal wire (each would occur twice in the empty net). It is then expanded. -/
theorem eq_empty_of_no_port {S : Signature} (r : Rule S 0 0) (hl : r.Linear) (hr : r.Reduced) :
    r.net = 0 ∧ r.internal = 0 ∧ r.Expanded := by
  have h0 : r.net = 0 := Multiset.eq_zero_of_forall_notMem fun e he => by
    obtain ⟨p, t, -, hp⟩ := hr e he
    rcases p with i | j | w
    · exact i.elim0
    · exact j.elim0
    · exact hp w rfl
  refine ⟨h0, ?_, fun e he => absurd (h0 ▸ he) (Multiset.notMem_zero _)⟩
  by_contra hne
  have h2 := hl.internal ⟨0, Nat.pos_of_ne_zero hne⟩
  rw [h0] at h2
  simp [Net.vars] at h2

/-- A rule with a port deep inside the tree of another port: `a₀ = con(dup(b₀, ε), b₁)`. -/
def deepRule : Rule sig 1 2 := ⟨0, {s(pl 0, mkCon (mkDup (pr 0) mkEra) (pr 1))}⟩

theorem deepRule_linear : deepRule.Linear := ⟨by decide, by decide, by decide⟩

theorem deepRule_reduced : deepRule.Reduced := by
  intro e he
  rw [Multiset.mem_singleton.1 he]
  exact ⟨_, _, rfl, fun w => w.elim0⟩

/-- The expected expanded form of `deepRule`: `a₀ = con(dup(x₀, ε), x₁)`, `b₀ = x₀`, `b₁ = x₁`. -/
def deepExp : Net sig (Fin 1 ⊕ Fin 2 ⊕ Fin 2) :=
  s(pl 0, mkCon (mkDup (pw 0) mkEra) (pw 1)) ::ₘ s(pr 0, pw 0) ::ₘ {s(pr 1, pw 1)}

/-- Two steps of the expansion, pulling out `b₀`, then `b₁`, give `deepExp`. -/
theorem deep_two_steps :
    (show Net sig (Fin 1 ⊕ Fin 2 ⊕ Fin 2) from
      (Expand.stepRule (Expand.stepRule deepRule (.inr 0)) (.inr 1)).net) = deepExp := by
  decide

theorem deepExp_linear : (⟨2, deepExp⟩ : Rule sig 1 2).Linear := ⟨by decide, by decide, by decide⟩

theorem deepExp_expanded : (⟨2, deepExp⟩ : Rule sig 1 2).Expanded := by
  intro e he
  have key : ∀ e ∈ deepExp,
      e ∈ [s(pl 0, mkCon (mkDup (pw 0) mkEra) (pw 1)), s(pr 0, pw 0), s(pr 1, pw 1)] := by decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> exact ⟨_, _, rfl, fun w h => (by cases h), by decide⟩

/-- `Rule.exists_expanded` applies to `deepRule`. -/
example : ∃ (r' : Rule sig 1 2) (ι : Fin deepRule.internal → Fin r'.internal),
    Function.Injective ι ∧ r'.Linear ∧ r'.Expanded ∧
      Equiv r'.net (deepRule.net.bind fun x => Term.var (Sum.map id (Sum.map id ι) x)) :=
  deepRule.exists_expanded deepRule_linear deepRule_reduced

/-! ## `trTerm` keeps the order of the auxiliary ports -/

/-- `con` with its two auxiliary ports exchanged. -/
def conSwap : PNet sig 2 where
  internal := 0
  tree := mkCon (.var (.inl 1)) (.var (.inl 0))
  port_count i := by fin_cases i <;> decide
  internal_count w := w.elim0

/-- `con` is translated into `con` with its ports exchanged; `dup` and `era` are kept. -/
def Φswap : Translation sig sig := ⟨fun α => match α with
  | .con => conSwap
  | .dup => PNet.cell (S := sig) Comb.dup
  | .era => PNet.cell (S := sig) Comb.era⟩

/-- `Φswap` exchanges the subtrees of every `con` cell, at both depths, and keeps `dup`. -/
theorem swap_depth2 :
    Φswap.trTerm 7 (mkCon (mkCon (var 0) (var 1)) (mkDup (var 2) (var 3))) =
      mkCon (mkDup (var 2) (var 3)) (mkCon (var 1) (var 0)) := by
  decide

/-- `con` as two cells joined by one wire, its ports in the reverse order:
`con(con(p₁, w), con(w, p₀))`. -/
def conRev : PNet sig 2 where
  internal := 1
  tree := mkCon (mkCon (.var (.inl 1)) (.var (.inr 0))) (mkCon (.var (.inr 0)) (.var (.inl 0)))
  port_count i := by fin_cases i <;> decide
  internal_count w := by fin_cases w; decide

/-- `con` is translated by `conRev`; `dup` and `era` are kept. -/
def Φrev : Translation sig sig := ⟨fun α => match α with
  | .con => conRev
  | .dup => PNet.cell (S := sig) Comb.dup
  | .era => PNet.cell (S := sig) Comb.era⟩

/-- A tree of depth 2 with three `con` cells. -/
def t₂ : Term sig ℕ := mkCon (mkCon (var 0) (var 1)) (mkCon (var 2) (var 3))

/-- On `t₂`, from `10`: the root instance takes `10`, the first subtree `11`, the second `12`; each
subtree sits on the port of `conRev` that has its index. -/
theorem rev_depth2 :
    Φrev.trTerm 10 t₂ =
      mkCon (mkCon (mkCon (mkCon (var 3) (var 12)) (mkCon (var 12) (var 2))) (var 10))
        (mkCon (var 10) (mkCon (mkCon (var 1) (var 11)) (mkCon (var 11) (var 0)))) := by
  decide

theorem rev_size : Φrev.size t₂ = 3 := by decide

/-- The names of `Φrev.trTerm 10 t₂`: the leaves of `t₂` once, and `10`, `11`, `12` twice each:
three disjoint blocks of one name. Computed directly. -/
theorem rev_depth2_vars :
    (Φrev.trTerm 10 t₂).vars = {0, 1, 2, 3} + 2 • Multiset.Ico 10 13 := by
  decide

/-- The same equation, as an instance of `vars_trTerm`. -/
example : (Φrev.trTerm 10 t₂).vars = t₂.vars + 2 • Multiset.Ico 10 (10 + Φrev.size t₂) :=
  Φrev.vars_trTerm 10 t₂

/-- When the first subtree has no internal wire (a `dup` cell), the block of the second subtree
starts right after the root instance, at `11`. -/
theorem rev_mixed :
    Φrev.trTerm 10 (mkCon (mkDup (var 0) (var 1)) (mkCon (var 2) (var 3))) =
      mkCon (mkCon (mkCon (mkCon (var 3) (var 11)) (mkCon (var 11) (var 2))) (var 10))
        (mkCon (var 10) (mkDup (var 0) (var 1))) := by
  decide

end INet.Comb.ExpandTrReview
