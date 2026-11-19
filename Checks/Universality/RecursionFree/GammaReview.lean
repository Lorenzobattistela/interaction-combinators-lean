import Checks.Universality.RecursionFree.GammaCheck

/-!
# Review of the package `Γ_{i,j}` (`gamma`) against Fig. 6, page 86

Lafont 1997, Section 2.4, Fig. 6 and Fig. 7, journal page 86 (PDF page 18). Review of
`Lafont/Gamma.lean` (issue #96).

## Against the figure

* `Γ_{i,j}` is the dual multiplexor `M*_{n_i+1}`, root up (free port of the package), whose first
  `n_i` leaves go to the top ports of `[φ_{i,j}]` and whose last (rightmost) leaf goes down to the
  root of `T_{σ_{i,j}}`. `gamma` is `muxStar (ofFn (gammaPort (.inl ·)) ++ [T_σ])`: same thing.
  What matters is that the leaf `l` of `M*` meets the leaf `l` of `M_{n_i+1}` of `[α_i]` (Fig. 7),
  and `mux_gamma` below checks this: the auxiliary port `i` of `α_i` meets the tree of `[φ]` at its
  port `i`, and the loop meets `T_σ`.
* `T_σ` receives the tree of `[φ]` at middle port `l` on its port `l`
  (`transpositorPerm σ hσ (fun j => gammaPort … (.inr j))`).
* The direction of `σ`. Two transpositors `T_σ(ts)`, `T_σ(us)` give `ts l = us (σ l)`
  (`transpositorPerm_transpositorPerm`). With `ts` the middle trees of `[φ_{i,j}]` and `us` those of
  `[φ_{j,i}] = [ψ_{i,j}]`, this joins the middle port `l` of `φ` to the middle port `σ l` of `ψ`,
  which is what `Rule.plug` does (`plugR_middle`, true for any `σ`). In the other order
  (`ts` from `ψ`) one gets `σ⁻¹`, which is `σ` because `σ` is involutive (`symm_eq_of_involutive`).
  So the question does not arise; `mux_gamma` shows the pairing `vs l = [φ](σ l)` explicitly.
* The menu `Γ_j = Γ_{1,j} & … & Γ_{m,j}` of `[α_j]` contains `Γ_{i,j}`, built from `φ_{i,j}`, the
  side on the ports of `α_i` of the rule `α_i ⋈ α_j`: `gamma` takes `φ : Rule S a k` with `a` the
  arity of the cell whose `M` it meets (`α_i`). `RecursionFreeData.rank_φ` bounds the symbols of
  `(dec α β r h).φ` by `β = α_j`, the cell whose menu holds `Γ_{i,j}`: the translation of `α_j` uses
  only translations of smaller symbols, as the recursion of page 86 needs.

## Refutation attempts

* A port as a leaf: for a linear expanded side no tree contains a port (`mem_vars_gammaTree`).
  Without `Expanded` it can happen and then `vars_gamma` is false (`wire_not_vars_gamma`), so the
  hypothesis is needed, not decorative.
* Collisions of names: an instance with four non-trivial translated trees, two of them of size 2,
  from `k₀ = 3` (`gamma_col`), whose names are checked by computation to be `3, …, 13` each twice
  (`gamma_col_vars`), independently of `vars_gamma`.
* `a = 0` (`gamma_a0`, `gamma_a0_id`), `k = 0` (`gamma_k0`), `a = k = 0` (`gamma_empty`), and
  `σ = swap 0 2` on `k = 3` (`gamma_k3`).
-/

namespace INet.Comb.GammaReview

open Term Rule Translation DecompositionReview ExpandedIso ExpandTrReview GammaCheck

variable {S : Signature} {a k : ℕ}

/-! ## General facts -/

/-- An involutive permutation is its own inverse: the direction of `σ_{i,j}` (page 86) does not
matter. -/
theorem symm_eq_of_involutive {σ : Equiv.Perm (Fin k)} (hσ : Function.Involutive σ) :
    σ.symm = σ :=
  Equiv.ext fun x => by rw [Equiv.symm_apply_eq, hσ]

/-- In `Rule.plug` (page 85), the middle wire `σ l` of `ψ` is the middle wire `l` of `φ`, for any
permutation `σ`. -/
theorem plugR_middle {b m n : ℕ} (σ : Equiv.Perm (Fin k)) (l : Fin k) :
    Rule.plugR (a := a) (b := b) (m := m) (n := n) σ (.inr (.inl (σ l))) =
      Rule.plugL (.inr (.inl l)) := by
  simp [Rule.plugR, Rule.plugL]

/-- For a linear side in expanded form, the trees of `Γ_{i,j}` before translation have only
names in `[k₀, k₀ + φ.internal)` (Fig. 6, page 86): no port of `φ` is a leaf, so the value `k₀`
that `gammaName` gives to ports is never used. -/
theorem mem_vars_gammaTree {φ : Rule S a k} (he : φ.Expanded) (hl : φ.Linear) (k₀ : ℕ)
    (p : Fin a ⊕ Fin k) {x : ℕ} (hx : x ∈ (gammaTree φ k₀ p).vars) :
    k₀ ≤ x ∧ x < k₀ + φ.internal := by
  rw [gammaTree_eq_portTree he hl, Term.vars_bind, Multiset.mem_bind] at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨w, rfl⟩ := (he.net_eq_portTree hl).2 p y hy
  simp only [vars_var, Multiset.mem_singleton, gammaName, Sum.elim_inr] at hx
  subst hx
  exact ⟨Nat.le_add_right _ _, by have := w.isLt; omega⟩

/-- **`Γ_{i,j}` against `M_{a+1}` of `[α_i]`** (Fig. 7, page 86): `M_{a+1}(ts, T_σ(vs))` against
`Γ_{i,j}` reduces to the equations `ts i = [φ]` at port `i`, and `vs l = [φ]` at middle port `σ l`.
So the leaves of `M*` are in the order of the leaves of `M`, the loop meets `T_σ`, and the
transpositor joins middle ports through `σ`. -/
theorem mux_gamma (Φ : Translation S sig) (φ : Rule S a k) (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ) (k₀ : ℕ) (ts : Fin a → Term sig ℕ) (vs : Fin k → Term sig ℕ)
    (Δ : CNet) :
    Red (s(mux (List.ofFn ts ++ [transpositorPerm σ hσ vs]), gamma Φ φ σ hσ k₀) ::ₘ Δ)
      ((Finset.univ.val.map fun l => s(vs l, gammaPort Φ φ k₀ (.inr (σ l)))) +
        ((Finset.univ.val.map fun i => s(ts i, gammaPort Φ φ k₀ (.inl i))) + Δ)) := by
  set g : Fin a → Term sig ℕ := fun i => gammaPort Φ φ k₀ (.inl i)
  set g' : Fin k → Term sig ℕ := fun j => gammaPort Φ φ k₀ (.inr j)
  have h1 := mux_muxStar (List.ofFn ts ++ [transpositorPerm σ hσ vs])
    (List.ofFn g ++ [transpositorPerm σ hσ g']) Δ (by simp)
  have h2 := transpositorPerm_transpositorPerm σ hσ vs g'
    ((Finset.univ.val.map fun i => s(ts i, g i)) + Δ)
  refine h1.trans (h2.cast ?_ rfl)
  rw [List.zipWith_append (by simp)]
  have hz : List.zipWith (fun t u => s(t, u)) (List.ofFn ts) (List.ofFn g) =
      List.ofFn fun i => s(ts i, g i) := by
    apply List.ext_getElem <;> simp
  rw [hz, Fin.univ_val_map, ← Multiset.coe_add, List.zipWith_cons_cons, List.zipWith_nil_left]
  simp only [← Multiset.cons_coe, Multiset.coe_nil]
  rw [Multiset.add_cons, Multiset.add_zero, Multiset.cons_add]


/-! ## A side that is not expanded: a port as a leaf -/

/-- A tree of a side is determined by the equation rooted at its port when that equation is
unique; no expansion needed. -/
theorem portTree_of_unique {φ : Rule S a k} {p : Fin a ⊕ Fin k}
    {t : Term S (Fin a ⊕ Fin k ⊕ Fin φ.internal)} (ht : s(Term.var (port p), t) ∈ φ.net)
    (hu : ∀ t', s(Term.var (port p), t') ∈ φ.net → t' = t) : φ.portTree p = t := by
  have h : ∃ t, s(Term.var (port p), t) ∈ φ.net := ⟨t, ht⟩
  unfold Rule.portTree
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact hu _ h.choose_spec

/-- The side `a₀ = b₀`: one wire between the two groups of ports, linear, not expanded. -/
abbrev ruleWire : Rule sig 1 1 := ⟨0, {s(pl 0, pr 0)}⟩

theorem ruleWire_linear : ruleWire.Linear := ⟨by decide, by decide, by decide⟩

theorem ruleWire_not_expanded : ¬ ruleWire.Expanded := by
  intro h
  obtain ⟨p, t, he, -, ht⟩ := h _ (Multiset.mem_singleton_self _)
  rcases Sym2.eq_iff.1 he with ⟨-, rfl⟩ | ⟨rfl, -⟩
  · exact (ht _ (Multiset.mem_singleton_self _)).choose.elim0
  · exact (ht _ (Multiset.mem_singleton_self _)).choose.elim0

/-- The identity permutation of `Fin n` is an involution. -/
theorem hid (n : ℕ) : Function.Involutive (1 : Equiv.Perm (Fin n)) := fun _ => rfl

/-- On `ruleWire`, both ports are leaves of the other's tree, and `gammaName` sends both to
`k₀`: `Γ = con(k₀, k₀)`. -/
theorem gamma_wire (k₀ : ℕ) :
    gamma (Translation.id sig) ruleWire 1 (hid 1) k₀ = mkCon (var k₀) (var k₀) := by
  have h0 : ruleWire.portTree (.inl 0) = pr 0 :=
    portTree_of_unique (Multiset.mem_singleton_self _) fun t' h => by
      rcases Sym2.eq_iff.1 (Multiset.mem_singleton.1 h) with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · cases h
  have h1 : ruleWire.portTree (.inr 0) = pl 0 :=
    portTree_of_unique (by
      show s(pr 0, _) ∈ ({s(pl 0, pr 0)} : Multiset _)
      rw [Sym2.eq_swap]; exact Multiset.mem_singleton_self _) fun t' h => by
      rcases Sym2.eq_iff.1 (Multiset.mem_singleton.1 h) with ⟨h, -⟩ | ⟨-, h⟩
      · cases h
      · exact h
  have hl : portList (1 : Equiv.Perm (Fin 1)) = [0] := by decide
  have hp : pairFst (1 : Equiv.Perm (Fin 1)) = [] := by decide
  simp only [gamma, gammaPort, trTerm_id, transpositorPerm, hl, hp, List.ofFn_succ,
    List.ofFn_zero, gammaTree, h0, h1, List.map_cons, List.map_nil]
  rfl

/-- **The hypothesis `Expanded` of `vars_gamma` is needed** (Fig. 6, page 86): on the linear
non-expanded side `ruleWire`, `gammaSize = 0` but `Γ` has the name `k₀`. -/
theorem wire_not_vars_gamma (k₀ : ℕ) :
    (gamma (Translation.id sig) ruleWire 1 (hid 1) k₀).vars ≠
      2 • Multiset.Ico k₀ (k₀ + gammaSize (Translation.id sig) ruleWire k₀) := by
  have hs : gammaSize (Translation.id sig) ruleWire k₀ = 0 := by
    simp [gammaSize, gammaSizes, size_id, ruleWire]
  rw [gamma_wire, hs]
  simp

/-! ## Names: four translated trees, two of size 2 -/

/-- A side with a `con` tree on every port, two of depth 2:
`a₀ = con(con(w₀, w₁), w₂)`, `a₁ = con(w₃, w₄)`, `b₀ = con(w₀, w₃)`, `b₁ = con(con(w₁, w₄), w₂)`. -/
abbrev ruleCol : Rule sig 2 2 :=
  ⟨5, s(pl 0, mkCon (mkCon (pw 0) (pw 1)) (pw 2)) ::ₘ s(pl 1, mkCon (pw 3) (pw 4)) ::ₘ
    s(pr 0, mkCon (pw 0) (pw 3)) ::ₘ {s(pr 1, mkCon (mkCon (pw 1) (pw 4)) (pw 2))}⟩

theorem ruleCol_linear : ruleCol.Linear := ⟨by decide, by decide, by decide⟩

theorem ruleCol_expanded : ruleCol.Expanded := by
  intro e he
  have key : ∀ e ∈ (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 5) from ruleCol.net),
      e ∈ [s(pl 0, mkCon (mkCon (pw 0) (pw 1)) (pw 2)), s(pl 1, mkCon (pw 3) (pw 4)),
        s(pr 0, mkCon (pw 0) (pw 3)), s(pr 1, mkCon (mkCon (pw 1) (pw 4)) (pw 2))] := by decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl, fun w h => (by cases h), by decide⟩

theorem portTree_col :
    ruleCol.portTree (.inl 0) = (mkCon (mkCon (pw 0) (pw 1)) (pw 2) : V 5) ∧
      ruleCol.portTree (.inl 1) = (mkCon (pw 3) (pw 4) : V 5) ∧
      ruleCol.portTree (.inr 0) = (mkCon (pw 0) (pw 3) : V 5) ∧
      ruleCol.portTree (.inr 1) = (mkCon (mkCon (pw 1) (pw 4)) (pw 2) : V 5) :=
  ⟨portTree_eq ruleCol_expanded ruleCol_linear (by decide),
    portTree_eq ruleCol_expanded ruleCol_linear (by decide),
    portTree_eq ruleCol_expanded ruleCol_linear (by decide),
    portTree_eq ruleCol_expanded ruleCol_linear (by decide)⟩

/-- The same for the computable twin `Rule.portTreeC`, which `gammaTree` uses (Fig. 6, page 86). -/
theorem portTreeC_col :
    ruleCol.portTreeC (.inl 0) = (mkCon (mkCon (pw 0) (pw 1)) (pw 2) : V 5) ∧
      ruleCol.portTreeC (.inl 1) = (mkCon (pw 3) (pw 4) : V 5) ∧
      ruleCol.portTreeC (.inr 0) = (mkCon (pw 0) (pw 3) : V 5) ∧
      ruleCol.portTreeC (.inr 1) = (mkCon (mkCon (pw 1) (pw 4)) (pw 2) : V 5) := by
  rw [portTreeC_eq_portTree ruleCol_expanded ruleCol_linear]
  exact portTree_col

/-- The tree computed by hand: from `k₀ = 3`, the internal wires of the side are `3, …, 7`, the
blocks of the translations are `8, 9` (`a₀`), `10` (`a₁`), `11` (`b₀`), `12, 13` (`b₁`). -/
def colTree : Term sig ℕ :=
  mkCon (mkCon (mkCon (mkCon (mkCon (var 6) (var 11)) (mkCon (var 11) (var 3)))
    (mkCon (mkCon (var 5) (var 12)) (mkCon (var 12) (mkCon (mkCon (var 7) (var 13))
      (mkCon (var 13) (var 4))))))
    (mkCon (mkCon (var 7) (var 10)) (mkCon (var 10) (var 6))))
    (mkCon (mkCon (var 5) (var 8)) (mkCon (var 8) (mkCon (mkCon (var 4) (var 9))
      (mkCon (var 9) (var 3)))))

/-- **`Γ` on `ruleCol` under `Φrev`, from `3`** (Fig. 6, page 86). -/
theorem gamma_col : gamma Φrev ruleCol (Equiv.swap 0 1) hs 3 = colTree := by
  obtain ⟨h0, h1, h2, h3⟩ := portTreeC_col
  have hl : portList (Equiv.swap (0 : Fin 2) 1) = [0, 1] := by decide
  have hp : pairFst (Equiv.swap (0 : Fin 2) 1) = [0] := by decide
  have hsz : gammaSizes Φrev ruleCol 3 = ![2, 1, 1, 2] := by
    funext q
    have e0 : (finSumFinEquiv.symm (⟨0, by omega⟩ : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = .inl 0 := rfl
    have e1 : (finSumFinEquiv.symm (⟨1, by omega⟩ : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = .inl 1 := rfl
    have e2 : (finSumFinEquiv.symm (⟨2, by omega⟩ : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = .inr 0 := rfl
    have e3 : (finSumFinEquiv.symm (⟨3, by omega⟩ : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = .inr 1 := rfl
    fin_cases q
    · simp only [gammaSizes, gammaTree]; rw [e0, h0]; rfl
    · simp only [gammaSizes, gammaTree]; rw [e1, h1]; rfl
    · simp only [gammaSizes, gammaTree]; rw [e2, h2]; rfl
    · simp only [gammaSizes, gammaTree]; rw [e3, h3]; rfl
  simp only [gamma, gammaPort, hsz, transpositorPerm, hl, hp, List.ofFn_succ,
    List.ofFn_zero, gammaTree, h0, h1, h2, h3, List.map_cons, List.map_nil, Fin.succ_zero_eq_one]
  decide

/-- **No collision** (Fig. 6, page 86): the names of `colTree`, computed directly, are `3, …, 13`,
each twice: the internal wires of the side and the five new wires of the translations are
disjoint. -/
theorem gamma_col_vars : (gamma Φrev ruleCol (Equiv.swap 0 1) hs 3).vars =
    2 • Multiset.Ico 3 14 := by
  rw [gamma_col]
  decide

/-- The same interval, from `vars_gamma`: `gammaSize = 5 + 6 = 11`. -/
example : (gamma Φrev ruleCol (Equiv.swap 0 1) hs 3).vars =
    2 • Multiset.Ico 3 (3 + gammaSize Φrev ruleCol 3) :=
  vars_gamma _ ruleCol_expanded ruleCol_linear _ _ _

/-! ## Edge cases -/

/-- `a = 0`, `k = 2`: the side `b₀ = w₀`, `b₁ = w₀`. -/
abbrev ruleA0 : Rule sig 0 2 := ⟨1, s(pr 0, pw 0) ::ₘ {s(pr 1, pw 0)}⟩

theorem ruleA0_linear : ruleA0.Linear := ⟨by decide, by decide, by decide⟩

theorem ruleA0_expanded : ruleA0.Expanded := by
  intro e he
  have key : ∀ e ∈ (show Net sig (Fin 0 ⊕ Fin 2 ⊕ Fin 1) from ruleA0.net),
      e ∈ [s(pr 0, pw 0), s(pr 1, pw 0)] := by decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> exact ⟨_, _, rfl, fun w h => (by cases h), by decide⟩

theorem portTree_a0 :
    ruleA0.portTree (.inr 0) = (pw 0 : Term sig (Fin 0 ⊕ Fin 2 ⊕ Fin 1)) ∧
      ruleA0.portTree (.inr 1) = (pw 0 : Term sig (Fin 0 ⊕ Fin 2 ⊕ Fin 1)) :=
  ⟨portTree_eq ruleA0_expanded ruleA0_linear (by decide),
    portTree_eq ruleA0_expanded ruleA0_linear (by decide)⟩

/-- `a = 0`, `σ = swap 0 1`: `M*_1` is a wire, `Γ = T_σ(w₀, w₀) = con(5, 5)`. -/
theorem gamma_a0 : gamma (Translation.id sig) ruleA0 (Equiv.swap 0 1) hs 5 =
    mkCon (var 5) (var 5) := by
  obtain ⟨h0, h1⟩ := portTree_a0
  have hl : portList (Equiv.swap (0 : Fin 2) 1) = [0, 1] := by decide
  have hp : pairFst (Equiv.swap (0 : Fin 2) 1) = [0] := by decide
  simp only [gamma, gammaPort, trTerm_id, transpositorPerm, hl, hp, List.ofFn_zero,
    gammaTree, h0, h1, List.map_cons, List.map_nil, List.nil_append]
  rfl

/-- `a = 0`, `σ = 1`: `T_1 = T_{0,2}` is the autodual multiplexor, `Γ = dup(5, 5)`. -/
theorem gamma_a0_id : gamma (Translation.id sig) ruleA0 1 (hid 2) 5 =
    mkDup (var 5) (var 5) := by
  obtain ⟨h0, h1⟩ := portTree_a0
  have hl : portList (1 : Equiv.Perm (Fin 2)) = [0, 1] := by decide
  have hp : pairFst (1 : Equiv.Perm (Fin 2)) = [] := by decide
  simp only [gamma, gammaPort, trTerm_id, transpositorPerm, hl, hp, List.ofFn_zero,
    gammaTree, h0, h1, List.map_cons, List.map_nil, List.nil_append]
  rfl

/-- `k = 0`: the side `a₀ = w₀`, `a₁ = w₀`. -/
abbrev ruleK0 : Rule sig 2 0 := ⟨1, s(pl 0, pw 0) ::ₘ {s(pl 1, pw 0)}⟩

theorem ruleK0_linear : ruleK0.Linear := ⟨by decide, by decide, by decide⟩

theorem ruleK0_expanded : ruleK0.Expanded := by
  intro e he
  have key : ∀ e ∈ (show Net sig (Fin 2 ⊕ Fin 0 ⊕ Fin 1) from ruleK0.net),
      e ∈ [s(pl 0, pw 0), s(pl 1, pw 0)] := by decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> exact ⟨_, _, rfl, fun w h => (by cases h), by decide⟩

/-- `k = 0`: `T_σ` has no port and is `ε`; `Γ = M*_3(5, 5, ε) = con(con(ε, 5), 5)`, a package. -/
theorem gamma_k0 : gamma (Translation.id sig) ruleK0 1 (hid 0) 5 =
    mkCon (mkCon mkEra (var 5)) (var 5) := by
  have h0 : ruleK0.portTree (.inl 0) = (pw 0 : Term sig (Fin 2 ⊕ Fin 0 ⊕ Fin 1)) :=
    portTree_eq ruleK0_expanded ruleK0_linear (by decide)
  have h1 : ruleK0.portTree (.inl 1) = (pw 0 : Term sig (Fin 2 ⊕ Fin 0 ⊕ Fin 1)) :=
    portTree_eq ruleK0_expanded ruleK0_linear (by decide)
  have hl : portList (1 : Equiv.Perm (Fin 0)) = [] := by decide
  have hp : pairFst (1 : Equiv.Perm (Fin 0)) = [] := by decide
  simp only [gamma, gammaPort, trTerm_id, transpositorPerm, hl, hp, List.ofFn_succ,
    List.ofFn_zero, gammaTree, h0, h1, List.map_nil, Fin.succ_zero_eq_one]
  rfl

example : (gamma (Translation.id sig) ruleK0 1 (hid 0) 5).IsPackage :=
  gamma_isPackage _ ruleK0_expanded ruleK0_linear _ _ _

/-- `a = k = 0`, the empty side: `Γ = M*_1(T_σ) = ε`. -/
theorem gamma_empty (k₀ : ℕ) :
    gamma (Translation.id sig) (⟨0, 0⟩ : Rule sig 0 0) 1 (hid 0) k₀ = mkEra := by
  have hl : portList (1 : Equiv.Perm (Fin 0)) = [] := by decide
  have hp : pairFst (1 : Equiv.Perm (Fin 0)) = [] := by decide
  simp only [gamma, transpositorPerm, hl, hp, List.ofFn_zero, List.map_nil]
  rfl

/-! ## A non-identity involution on three middle ports -/

/-- `a = 1`, `k = 3`: `a₀ = dup(w₀, w₁)`, `b₀ = w₀`, `b₁ = con(w₂, w₂)`, `b₂ = w₁`. -/
abbrev ruleK3 : Rule sig 1 3 :=
  ⟨3, s(pl 0, mkDup (pw 0) (pw 1)) ::ₘ s(pr 0, pw 0) ::ₘ s(pr 1, mkCon (pw 2) (pw 2)) ::ₘ
    {s(pr 2, pw 1)}⟩

theorem ruleK3_linear : ruleK3.Linear := ⟨by decide, by decide, by decide⟩

theorem ruleK3_expanded : ruleK3.Expanded := by
  intro e he
  have key : ∀ e ∈ (show Net sig (Fin 1 ⊕ Fin 3 ⊕ Fin 3) from ruleK3.net),
      e ∈ [s(pl 0, mkDup (pw 0) (pw 1)), s(pr 0, pw 0), s(pr 1, mkCon (pw 2) (pw 2)),
        s(pr 2, pw 1)] := by decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl, fun w h => (by cases h), by decide⟩

/-- **`σ = swap 0 2` on `k = 3`** (Fig. 6, page 86): `T_σ` puts the trees of middle ports `0` and
`2` under its `con` and the tree of port `1` on the free port of its `dup`:
`Γ = M*_2(dup(0, 1), dup(con(0, 1), con(2, 2)))`. -/
theorem gamma_k3 :
    gamma (Translation.id sig) ruleK3 (Equiv.swap 0 2) (Equiv.swap_apply_self 0 2) 0 =
      mkCon (mkDup (mkCon (var 0) (var 1)) (mkCon (var 2) (var 2))) (mkDup (var 0) (var 1)) := by
  have h0 : ruleK3.portTree (.inl 0) = (mkDup (pw 0) (pw 1) : Term sig (Fin 1 ⊕ Fin 3 ⊕ Fin 3)) :=
    portTree_eq ruleK3_expanded ruleK3_linear (by decide)
  have h1 : ruleK3.portTree (.inr 0) = (pw 0 : Term sig (Fin 1 ⊕ Fin 3 ⊕ Fin 3)) :=
    portTree_eq ruleK3_expanded ruleK3_linear (by decide)
  have h2 : ruleK3.portTree (.inr 1) =
      (mkCon (pw 2) (pw 2) : Term sig (Fin 1 ⊕ Fin 3 ⊕ Fin 3)) :=
    portTree_eq ruleK3_expanded ruleK3_linear (by decide)
  have h3 : ruleK3.portTree (.inr 2) = (pw 1 : Term sig (Fin 1 ⊕ Fin 3 ⊕ Fin 3)) :=
    portTree_eq ruleK3_expanded ruleK3_linear (by decide)
  unfold gamma; rw [transpositorPerm_swap02]
  simp only [gammaPort, trTerm_id, List.ofFn_succ, List.ofFn_zero, gammaTree, h0, h1, h2, h3]
  decide

example : (gamma (Translation.id sig) ruleK3 (Equiv.swap 0 2)
    (Equiv.swap_apply_self 0 2) 0).IsPackage :=
  gamma_isPackage _ ruleK3_expanded ruleK3_linear _ _ _

end INet.Comb.GammaReview
