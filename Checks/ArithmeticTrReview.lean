import Demo.ArithmeticTr

/-!
# Review of the hand-written sides of unary addition (pages 85–86, Fig. 10 pages 89–90)

Issue #363 reviews `Demo/ArithmeticTr.lean` (PR #361): the numbering `arithEnum`, the expanded
sides `arithSide` of the rules `add`–`zero` and `add`–`succ`, and the evaluation of `[0]`, `[S]`,
`[add]`.

* **Where `arithSide` is defined.** It is `some` on the four orientations of the two rules and
  `none` on the five other pairs (`arithSide_some`, `arithSide_none`).
* **The sides are not the canonical decomposition of page 85.** The canonical decomposition puts
  each tree of the right member with the cell whose port is at its root. In `add`–`succ` the tree
  `x = add(y, w)` is rooted at the port `x` of `succ`, so the canonical decomposition has the cell
  `add` on the side of `succ`, `succ` on the side of `add`, and two middle wires (for `y` and `w`).
  `Rule.decompose` computes it: `decompose_addSucc_k`, `decompose_addSucc_cells`. The hand-written
  side keeps `add` on the side of `add`, with one middle wire. Page 85 says a decomposition is not
  unique, and Fig. 10 needs only one that plugs back (`System.SidesPlug`); the normalisation of
  page 86 (`φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}`, `σ` involutive) holds, with `σ = 1`, the
  only permutation of `Fin 1`.
* **The canonical sides also plug back.** `canonSide` takes the canonical sides for `add`–`succ`
  (`k = 2`, `σ = 1`) and satisfies `SidesPlug` (`canon_sidesPlug`); its translation is compatible
  (`canonTr_compatible`). So the placement of `add` is a choice, not forced by the construction; it
  changes the sizes of `[S]` and `[add]` (evaluated below).
* **Exchanging the ports `y`, `r` of `add` breaks the sides.** With `y = S(w)`, `r = v` in place of
  `y = v`, `r = S(w)`, plugging gives `y = S(w)`, `x = add(r, w)`, which is not the rule:
  `swap_not_plugs` (for every `σ`) and `swap_not_sidesPlug`. The proof uses the invariant
  `Equiv.sol_iff`: the rule has a solution with `y` a variable, the plugged net has none.
* **Sizes.** The cell count of `[α]` is the sum of the parts of Fig. 10: `T_{1,1}` (2 cells), the
  menu `Γ_α`, the selector `S^α_3` (4 cells), the multiplexor `M_{n+2}` (`n + 1` cells), and the
  code `!Γ` (77 cells for every `α`). The internal wires are the names `n, …, codeKeyE − 1` and the
  cut names of the code. Checked by `#guard`.
* **The printed `[0]`.** It is `dup(con(Γ_0, con(con(era, era), con(!Γ, 0))), 0)`: the `dup` of
  `T_{1,1}`, whose `con` carries the menu `Γ_0` and the selector `S^0_3 = M_3*` with two erasers,
  on the multiplexor `M_2 = con(!Γ, ℓ)`, with the loop `ℓ = 0`. Checked by `#guard`.
-/

namespace INet.Demo.Arith.ArithmeticTrReview

open Term

/-! ## Where the sides are defined -/

/-- `arithSide` is defined on both orientations of the two rules `add`–`zero` and `add`–`succ`
(page 86). -/
theorem arithSide_some :
    (arithSide (Sym.add : sig.Sym) (Sym.zero : sig.Sym)).isSome ∧
    (arithSide (Sym.zero : sig.Sym) (Sym.add : sig.Sym)).isSome ∧
    (arithSide (Sym.add : sig.Sym) (Sym.succ : sig.Sym)).isSome ∧
    (arithSide (Sym.succ : sig.Sym) (Sym.add : sig.Sym)).isSome :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `arithSide` is `none` on the five pairs without a rule in either orientation (page 86). -/
theorem arithSide_none :
    arithSide (Sym.zero : sig.Sym) (Sym.zero : sig.Sym) = none ∧
    arithSide (Sym.zero : sig.Sym) (Sym.succ : sig.Sym) = none ∧
    arithSide (Sym.succ : sig.Sym) (Sym.zero : sig.Sym) = none ∧
    arithSide (Sym.succ : sig.Sym) (Sym.succ : sig.Sym) = none ∧
    arithSide (Sym.add : sig.Sym) (Sym.add : sig.Sym) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The pairs without a side are exactly the pairs without a rule in either orientation. -/
theorem arithSide_isSome_iff (α β : sig.Sym) :
    (arithSide α β).isSome ↔ (system.rule α β).isSome ∨ (system.rule β α).isSome := by
  cases α <;> cases β <;> decide

/-! ## The canonical decomposition of page 85 -/

/-- The canonical decomposition of `add`–`succ` (page 85) has two middle wires: the port `y` of
`add`, which occurs in the tree rooted at `x`, and the wire `w`, which joins the two trees. -/
theorem decompose_addSucc_k : (Rule.decompose ruleAddSucc).k = 2 := by decide

/-- The canonical decomposition of `add`–`zero` (page 85) has no middle wire. -/
theorem decompose_addZero_k : (Rule.decompose ruleAddZero).k = 0 := by decide

/-- In the canonical decomposition of `add`–`succ` (page 85), the side of `add` holds the cell
`succ` and the side of `succ` holds the cell `add`: the opposite of `sideAddSucc`, whose side of
`add` holds both cells. -/
theorem decompose_addSucc_cells :
    (Rule.decompose ruleAddSucc).φ.net.cells = {(Sym.succ : sig.Sym)} ∧
    (Rule.decompose ruleAddSucc).ψ.net.cells = {(Sym.add : sig.Sym)} := by
  constructor <;> decide

/-! ## The canonical sides plug back too -/

section Canon

/-- The canonical side of `add` against `succ` (page 85), expanded: `y = m₀`, `r = S(m₁)`. -/
def canonAddSucc : Rule sig 2 2 :=
  ⟨2, s(ap 0, iw 0) ::ₘ s(mp 0, iw 0) ::ₘ s(ap 1, mkSucc (iw 1)) ::ₘ s(mp 1, iw 1) ::ₘ 0⟩

/-- The canonical side of `succ` against `add` (page 85), expanded: `x = add(m₀, m₁)`. -/
def canonSuccAdd : Rule sig 1 2 :=
  ⟨2, s(ap 0, mkAdd (iw 0) (iw 1)) ::ₘ s(mp 0, iw 0) ::ₘ s(mp 1, iw 1) ::ₘ 0⟩

theorem canonAddSucc_linear : canonAddSucc.Linear := ⟨by decide, by decide, by decide⟩
theorem canonSuccAdd_linear : canonSuccAdd.Linear := ⟨by decide, by decide, by decide⟩

theorem canonAddSucc_expanded : canonAddSucc.Expanded := by
  change ∀ e ∈ (s(ap 0, iw 0) ::ₘ s(mp 0, iw 0) ::ₘ s(ap 1, mkSucc (iw 1)) ::ₘ s(mp 1, iw 1) ::ₘ 0 :
      Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2)), ∃ p t, e = s(var p, t) ∧
    (∀ w : Fin 2, p ≠ .inr (.inr w)) ∧ ∀ x ∈ t.vars, ∃ w : Fin 2, x = .inr (.inr w)
  intro e he
  obtain rfl | rfl | rfl | rfl : e = _ ∨ e = _ ∨ e = _ ∨ e = _ := by
    rcases Multiset.mem_cons.1 he with h | he; · exact .inl h
    rcases Multiset.mem_cons.1 he with h | he; · exact .inr (.inl h)
    rcases Multiset.mem_cons.1 he with h | he; · exact .inr (.inr (.inl h))
    rcases Multiset.mem_cons.1 he with h | he; · exact .inr (.inr (.inr h))
    exact absurd he (Multiset.notMem_zero _)
  · exact ⟨_, _, rfl, fun w => by simp, fun x hx => by
      rw [vars_var, Multiset.mem_singleton] at hx; exact ⟨_, hx⟩⟩
  · exact ⟨_, _, rfl, fun w => by simp, fun x hx => by
      rw [vars_var, Multiset.mem_singleton] at hx; exact ⟨_, hx⟩⟩
  · exact ⟨_, _, rfl, fun w => by simp, fun x hx => by
      rw [vars_mkSucc, vars_var, Multiset.mem_singleton] at hx; exact ⟨_, hx⟩⟩
  · exact ⟨_, _, rfl, fun w => by simp, fun x hx => by
      rw [vars_var, Multiset.mem_singleton] at hx; exact ⟨_, hx⟩⟩

theorem canonSuccAdd_expanded : canonSuccAdd.Expanded := by
  change ∀ e ∈ (s(ap 0, mkAdd (iw 0) (iw 1)) ::ₘ s(mp 0, iw 0) ::ₘ s(mp 1, iw 1) ::ₘ 0 :
      Net sig (Fin 1 ⊕ Fin 2 ⊕ Fin 2)), ∃ p t, e = s(var p, t) ∧
    (∀ w : Fin 2, p ≠ .inr (.inr w)) ∧ ∀ x ∈ t.vars, ∃ w : Fin 2, x = .inr (.inr w)
  intro e he
  obtain rfl | rfl | rfl : e = _ ∨ e = _ ∨ e = _ := by
    rcases Multiset.mem_cons.1 he with h | he; · exact .inl h
    rcases Multiset.mem_cons.1 he with h | he; · exact .inr (.inl h)
    rcases Multiset.mem_cons.1 he with h | he; · exact .inr (.inr h)
    exact absurd he (Multiset.notMem_zero _)
  · refine ⟨_, _, rfl, fun w => by simp, fun x hx => ?_⟩
    rw [vars_mkAdd, vars_var, vars_var, Multiset.mem_add, Multiset.mem_singleton,
      Multiset.mem_singleton] at hx
    rcases hx with hx | hx <;> exact ⟨_, hx⟩
  all_goals
    exact ⟨_, _, rfl, fun w => by simp, fun x hx => by
      rw [vars_var, Multiset.mem_singleton] at hx; exact ⟨_, hx⟩⟩

/-- The sides of unary addition with the canonical decomposition of `add`–`succ` (page 85) in
place of the hand-written one; `add`–`zero` is unchanged (its canonical decomposition has no
middle wire either). -/
def canonSide : ∀ α : sig.Sym, sig.Sym → Option (ExpSide sig (sig.arity α))
  | .add, .zero => some ⟨0, sideAddZero, 1, sideAddZero_linear, sideAddZero_expanded,
      fun _ => rfl⟩
  | .zero, .add => some ⟨0, sideZeroAdd, 1, sideZeroAdd_linear, sideZeroAdd_expanded,
      fun _ => rfl⟩
  | .add, .succ => some ⟨2, canonAddSucc, 1, canonAddSucc_linear, canonAddSucc_expanded,
      fun _ => rfl⟩
  | .succ, .add => some ⟨2, canonSuccAdd, 1, canonSuccAdd_linear, canonSuccAdd_expanded,
      fun _ => rfl⟩
  | _, _ => none

/-- The plugged canonical net of `add`–`succ` after the wire `m₀` of `φ` is substituted. -/
private abbrev canonMid₁ : Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 6) :=
  s(iw 0, ap 0) ::ₘ s(ap 1, mkSucc (iw 3)) ::ₘ s(iw 1, iw 3) ::ₘ
    s(mp 0, mkAdd (iw 4) (iw 5)) ::ₘ s(iw 0, iw 4) ::ₘ s(iw 1, iw 5) ::ₘ 0

/-- After the joined wire `0` is substituted. -/
private abbrev canonMid₂ : Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 6) :=
  s(ap 0, iw 4) ::ₘ s(ap 1, mkSucc (iw 3)) ::ₘ s(iw 1, iw 3) ::ₘ
    s(mp 0, mkAdd (iw 4) (iw 5)) ::ₘ s(iw 1, iw 5) ::ₘ 0

/-- After the wire `m₀` of `ψ` is substituted. -/
private abbrev canonMid₃ : Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 6) :=
  s(mp 0, mkAdd (ap 0) (iw 5)) ::ₘ s(ap 1, mkSucc (iw 3)) ::ₘ s(iw 1, iw 3) ::ₘ
    s(iw 1, iw 5) ::ₘ 0

/-- After the joined wire `1` is substituted. -/
private abbrev canonMid₄ : Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 6) :=
  s(iw 3, iw 5) ::ₘ s(mp 0, mkAdd (ap 0) (iw 5)) ::ₘ s(ap 1, mkSucc (iw 3)) ::ₘ 0

/-- Plugging the canonical sides of `add`–`succ` through `σ = 1` gives back the rule
`r = S(w), x = add(y, w)` (page 85), up to five wires. -/
theorem canonAddSucc_plugs :
    (⟨2, canonAddSucc, canonSuccAdd, 1⟩ : Decomposition sig 2 1).Plugs ruleAddSucc := by
  refine ⟨fun _ => ⟨3, by decide⟩, fun i j _ => Subsingleton.elim (α := Fin 1) i j, ?_⟩
  have h₁ := equiv_wire (ν := Fin 2 ⊕ Fin 1 ⊕ Fin 6)
    (N := (show Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 6) from
      (Rule.plug canonAddSucc canonSuccAdd 1).net))
    (M := canonMid₁)
    (.inr (.inr 2)) (ap 0) (iw 0) (iw 2)
    (s(ap 1, mkSucc (iw 3)) ::ₘ s(iw 1, iw 3) ::ₘ s(mp 0, mkAdd (iw 4) (iw 5)) ::ₘ
      s(iw 0, iw 4) ::ₘ s(iw 1, iw 5) ::ₘ 0)
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have h₂ := equiv_wire (ν := Fin 2 ⊕ Fin 1 ⊕ Fin 6) (N := canonMid₁) (M := canonMid₂)
    (.inr (.inr 0)) (ap 0) (iw 0) (iw 4)
    (s(ap 1, mkSucc (iw 3)) ::ₘ s(iw 1, iw 3) ::ₘ s(mp 0, mkAdd (iw 4) (iw 5)) ::ₘ
      s(iw 1, iw 5) ::ₘ 0)
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have h₃ := equiv_wire (ν := Fin 2 ⊕ Fin 1 ⊕ Fin 6) (N := canonMid₂) (M := canonMid₃)
    (.inr (.inr 4)) (ap 0) (mp 0) (mkAdd (iw 4) (iw 5))
    (s(ap 1, mkSucc (iw 3)) ::ₘ s(iw 1, iw 3) ::ₘ s(iw 1, iw 5) ::ₘ 0)
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have h₄ := equiv_wire (ν := Fin 2 ⊕ Fin 1 ⊕ Fin 6) (N := canonMid₃) (M := canonMid₄)
    (.inr (.inr 1)) (iw 3) (iw 1) (iw 5)
    (s(mp 0, mkAdd (ap 0) (iw 5)) ::ₘ s(ap 1, mkSucc (iw 3)) ::ₘ 0)
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have h₅ := equiv_wire (ν := Fin 2 ⊕ Fin 1 ⊕ Fin 6) (N := canonMid₄)
    (M := (show Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 6) from ruleAddSucc.net.bind
      fun x => var (Sum.map id (Sum.map id (fun _ : Fin 1 => (3 : Fin 6))) x)))
    (.inr (.inr 5)) (iw 3) (mp 0) (mkAdd (ap 0) (iw 5))
    (s(ap 1, mkSucc (iw 3)) ::ₘ 0)
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- **The canonical sides of page 85 also plug back into the rules of unary addition**
(pages 85–86, Fig. 10 pages 89–90): `SidesPlug` does not force the cell `add` of the right member
of `add`–`succ` onto the side of `add`, as `arithSide` puts it. -/
theorem canon_sidesPlug : system.SidesPlug canonSide := by
  intro α β r h
  cases α <;> cases β <;> cases h
  · exact ⟨0, sideAddZero, sideZeroAdd, 1, fun _ => rfl, sideAddZero_linear,
      sideAddZero_expanded, sideZeroAdd_linear, sideZeroAdd_expanded, rfl, rfl, addZero_plugs⟩
  · exact ⟨2, canonAddSucc, canonSuccAdd, 1, fun _ => rfl, canonAddSucc_linear,
      canonAddSucc_expanded, canonSuccAdd_linear, canonSuccAdd_expanded, rfl, rfl,
      canonAddSucc_plugs⟩

/-- **The translation built from the canonical sides is compatible** (Section 2.7, Fig. 10,
pages 89–90). -/
theorem canonTr_compatible :
    (Comb.codeTranslationE arithEnum canonSide).Compatible system Comb.system :=
  Comb.codeTranslationE_compatible_of_sides arithEnum canon_sidesPlug

-- With the canonical sides, `[0]`, `[S]`, `[add]` have 95, 112, 115 cells, against 93, 128, 95
-- with `arithSide`: the translated `add` moves from the package `Γ_{add,S}` (in the menu `Γ_S`)
-- to `Γ_{S,add}` (in the menu `Γ_add`), and the code `!Γ`, which holds every package, changes too.
#guard [(Comb.codeNetE arithEnum canonSide (Sym.zero : sig.Sym)).tree.size,
  (Comb.codeNetE arithEnum canonSide (Sym.succ : sig.Sym)).tree.size,
  (Comb.codeNetE arithEnum canonSide (Sym.add : sig.Sym)).tree.size] == [95, 112, 115]

-- Their numbers of internal wires.
#guard [(Comb.codeNetE arithEnum canonSide (Sym.zero : sig.Sym)).internal,
  (Comb.codeNetE arithEnum canonSide (Sym.succ : sig.Sym)).internal,
  (Comb.codeNetE arithEnum canonSide (Sym.add : sig.Sym)).internal] == [25, 31, 31]

end Canon

/-! ## Exchanging the ports `y` and `r` of `add` -/

section Swap

/-- The side of `add` against `succ` with its two auxiliary ports exchanged:
`y = S(w), r = v, m = add(v, w)`. -/
def swapAddSucc : Rule sig 2 1 :=
  ⟨2, s(ap 0, mkSucc (iw 1)) ::ₘ s(ap 1, iw 0) ::ₘ s(mp 0, mkAdd (iw 0) (iw 1)) ::ₘ 0⟩

theorem swapAddSucc_linear : swapAddSucc.Linear := ⟨by decide, by decide, by decide⟩

theorem swapAddSucc_expanded : swapAddSucc.Expanded := by
  change ∀ e ∈ (s(ap 0, mkSucc (iw 1)) ::ₘ s(ap 1, iw 0) ::ₘ s(mp 0, mkAdd (iw 0) (iw 1)) ::ₘ 0 :
      Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 2)), ∃ p t, e = s(var p, t) ∧
    (∀ w : Fin 2, p ≠ .inr (.inr w)) ∧ ∀ x ∈ t.vars, ∃ w : Fin 2, x = .inr (.inr w)
  intro e he
  obtain rfl | rfl | rfl : e = _ ∨ e = _ ∨ e = _ := by
    rcases Multiset.mem_cons.1 he with h | he; · exact .inl h
    rcases Multiset.mem_cons.1 he with h | he; · exact .inr (.inl h)
    rcases Multiset.mem_cons.1 he with h | he; · exact .inr (.inr h)
    exact absurd he (Multiset.notMem_zero _)
  · exact ⟨_, _, rfl, fun w => by simp, fun x hx => by
      rw [vars_mkSucc, vars_var, Multiset.mem_singleton] at hx; exact ⟨_, hx⟩⟩
  · exact ⟨_, _, rfl, fun w => by simp, fun x hx => by
      rw [vars_var, Multiset.mem_singleton] at hx; exact ⟨_, hx⟩⟩
  · refine ⟨_, _, rfl, fun w => by simp, fun x hx => ?_⟩
    rw [vars_mkAdd, vars_var, vars_var, Multiset.mem_add, Multiset.mem_singleton,
      Multiset.mem_singleton] at hx
    rcases hx with hx | hx <;> exact ⟨_, hx⟩

/-- `arithSide` with the side of `add` against `succ` replaced by `swapAddSucc`. -/
def swapSide : ∀ α : sig.Sym, sig.Sym → Option (ExpSide sig (sig.arity α))
  | .add, .zero => some ⟨0, sideAddZero, 1, sideAddZero_linear, sideAddZero_expanded,
      fun _ => rfl⟩
  | .zero, .add => some ⟨0, sideZeroAdd, 1, sideZeroAdd_linear, sideZeroAdd_expanded,
      fun _ => rfl⟩
  | .add, .succ => some ⟨1, swapAddSucc, 1, swapAddSucc_linear, swapAddSucc_expanded,
      fun _ => rfl⟩
  | .succ, .add => some ⟨1, sideSuccAdd, 1, sideSuccAdd_linear, sideSuccAdd_expanded,
      fun _ => rfl⟩
  | _, _ => none

/-- The values on the free ports of `add`–`succ` used to separate the two nets: `y` is the
variable `0`, `r` is `S(1)`, `x` is `add(0, 1)`, and every internal wire is `1`. -/
def sepSol {m : ℕ} : Fin 2 ⊕ Fin 1 ⊕ Fin m → Term sig ℕ
  | .inl 0 => var 0
  | .inl 1 => mkSucc (var 1)
  | .inr (.inl _) => mkAdd (var 0) (var 1)
  | .inr (.inr _) => var 1

/-- **Exchanging the ports `y`, `r` of `add` breaks the decomposition** (page 85): for every `σ`,
plugging `swapAddSucc` and `sideSuccAdd` does not give back the rule `add`–`succ`. The rule has a
solution in which the port `y` is a variable (`sepSol`); in the plugged net `y` meets the
principal port of `succ`, so no solution makes it a variable (`Equiv.sol_iff`). -/
theorem swap_not_plugs (σ : Equiv.Perm (Fin 1)) :
    ¬ (⟨1, swapAddSucc, sideSuccAdd, σ⟩ : Decomposition sig 2 1).Plugs ruleAddSucc := by
  rintro ⟨ι, -, hE⟩
  obtain rfl : σ = 1 := Subsingleton.elim _ _
  have hsol :
      Net.Sol (ruleAddSucc.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) sepSol := by
    refine ⟨sepSol, ?_, fun _ _ => rfl⟩
    let w₀ : Fin ruleAddSucc.internal := ⟨0, Nat.one_pos⟩
    change ∀ e ∈ Net.bind _ (s(var (.inl 1), mkSucc (var (.inr (.inr w₀)))) ::ₘ
      s(var (.inr (.inl 0)), mkAdd (var (.inl 0)) (var (.inr (.inr w₀)))) ::ₘ 0 :
        Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin ruleAddSucc.internal)), _
    intro e he
    simp only [Net.bind, Multiset.map_cons, Multiset.map_zero, Multiset.mem_cons,
      Multiset.notMem_zero, or_false] at he
    rcases he with rfl | rfl <;>
    · simp only [Sym2.map_mk, Sym2.lift_mk, bind_var, bind_mkSucc, bind_mkAdd]
      rfl
  obtain ⟨s', hs', hp⟩ : ∃ s' : Fin 2 ⊕ Fin 1 ⊕ Fin 4 → Term sig ℕ,
      Net.Solves s' (show Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 4) from
        (Rule.plug swapAddSucc sideSuccAdd 1).net) ∧
      ∀ p, Multiset.count p (Net.vars (show Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 4) from
        (Rule.plug swapAddSucc sideSuccAdd 1).net)) = 1 → s' p = sepSol p :=
    (hE.sol_iff sepSol).2 hsol
  have hmem : (s(ap 0, mkSucc (iw 2)) : Sym2 (Term sig (Fin 2 ⊕ Fin 1 ⊕ Fin 4))) ∈
      (show Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 4) from
        (Rule.plug swapAddSucc sideSuccAdd 1).net) := by decide
  have hcount : Multiset.count (.inl 0) (Net.vars (show Net sig (Fin 2 ⊕ Fin 1 ⊕ Fin 4) from
      (Rule.plug swapAddSucc sideSuccAdd 1).net)) = 1 := by decide
  have h1 : (ap 0 : Term sig (Fin 2 ⊕ Fin 1 ⊕ Fin 4)).bind s' = (mkSucc (iw 2)).bind s' :=
    hs' _ hmem
  have h3 : sepSol (.inl 0) = mkSucc ((iw 2 : Term sig (Fin 2 ⊕ Fin 1 ⊕ Fin 4)).bind s') :=
    (hp _ hcount).symm.trans (h1.trans (bind_mkSucc _ _))
  cases h3

/-- **With the ports of `add` exchanged, the sides no longer plug back** (page 86): `swapSide`
does not satisfy `SidesPlug`. -/
theorem swap_not_sidesPlug : ¬ system.SidesPlug swapSide := by
  intro h
  obtain ⟨k, φ, ψ, σ, hσ, hl, he, hl', he', hs, hs', hP⟩ :=
    h (α := (Sym.add : sig.Sym)) (β := (Sym.succ : sig.Sym)) (r := ruleAddSucc) rfl
  simp only [swapSide, Option.some.injEq] at hs hs'
  cases hs
  cases hs'
  exact swap_not_plugs _ hP

end Swap

/-! ## Non-vacuity of the `2 + 2` theorem -/

/-- The hypothesis of `two_plus_two_in_combinators_computed` is met, and so is that of its
conclusion: both `2 + 2` and `4` have translations. -/
example : (∃ N' : Net Comb.sig ℕ, arithTr.NetTr twoPlusTwo N') ∧
    ∃ M' : Net Comb.sig ℕ, arithTr.NetTr four M' :=
  ⟨twoPlusTwo_has_translation _, by
    have hlin : four.Linear := by
      intro z
      simp only [four, Net.vars_singleton, eqVars_mk, vars_var, vars_num,
        Multiset.count_add, Multiset.count_singleton, Multiset.count_zero]
      split_ifs <;> omega
    have hk : four.Below 1 := by
      intro z hz
      simp [four, Net.vars] at hz
      omega
    obtain ⟨M', _, h, _⟩ := arithTr.exists_netTr hlin hk
    exact ⟨M', h⟩⟩

/-! ## The sizes, part by part (Fig. 10, page 89) -/

/-- The menu `Γ_α` of `[α]`. -/
abbrev menuOf (α : sig.Sym) : Term Comb.sig ℕ :=
  Comb.menu (Comb.codeCellMenuE arithEnum arithSide α (sig.arity α + 1))

/-- The code `!Γ` in `[α]`. -/
abbrev codeOf (α : sig.Sym) : Term Comb.sig ℕ :=
  Comb.code (Comb.codeKeyE arithEnum arithSide α)
    (Comb.menu (Comb.codeMenusE arithEnum arithSide (Comb.codeMenuBaseE arithEnum arithSide α)))

-- `T_{1,1}` has 2 cells and `S^i_3` with a wire in place of `M_{n+2}` has 4 (2 `con`, 2 `era`).
#guard (Comb.transpositor 1 [var 0, var 1, var 2] : Term Comb.sig ℕ).size == 2
#guard (Comb.cellSel 3 0 (var 0) : Term Comb.sig ℕ).size == 4

-- The code `!Γ` has 77 cells in each `[α]`: it differs only by the names.
#guard [(Sym.zero : sig.Sym), Sym.succ, Sym.add].map (fun α => (codeOf α).size) == [77, 77, 77]

-- The menus `Γ_0`, `Γ_S`, `Γ_add` have 9, 43, 9 cells.
#guard [(Sym.zero : sig.Sym), Sym.succ, Sym.add].map (fun α => (menuOf α).size) == [9, 43, 9]

-- Cells of `[α]` = `T_{1,1}` + `Γ_α` + `S^α_3` + `M_{n+2}` + `!Γ`, where `M_{n+2}` has `n + 1`.
#guard [(Sym.zero : sig.Sym), Sym.succ, Sym.add].all fun α =>
  (Comb.codeNetE arithEnum arithSide α).tree.size ==
    2 + (menuOf α).size + 4 + (sig.arity α + 1) + (codeOf α).size

-- Internal wires of `[α]` = the names `[n, codeKeyE)` + the cut names of `!Γ`.
#guard [(Sym.zero : sig.Sym), Sym.succ, Sym.add].all fun α =>
  (Comb.codeNetE arithEnum arithSide α).internal ==
    Comb.codeKeyE arithEnum arithSide α - sig.arity α +
      (Comb.decomp (Comb.codeKeyE arithEnum arithSide α)
        (Comb.menu (Comb.codeMenusE arithEnum arithSide
          (Comb.codeMenuBaseE arithEnum arithSide α)))).ports.card

/-! ## The printed `[0]` (Fig. 10, page 89) -/

-- The tree of `[0]` is `T_{1,1}` = `dup(con(Γ_0, S^0_3), ℓ)`, with `S^0_3 = M_3*[M_2, era, era]`,
-- `M_2 = con(!Γ, ℓ)` and the loop `ℓ = 0`. (The printed `[0]` of `Demo/ArithmeticTr.lean` is
-- this tree with the cut names `40, 55, 68, 71, 84, 87, 100` of `!Γ` renumbered `16, …, 22`.)
#guard Comb.Term.toStr (Comb.codeTreeE arithEnum arithSide (Sym.zero : sig.Sym)) ==
  "dup(con(" ++ Comb.Term.toStr (menuOf (Sym.zero : sig.Sym)) ++ ", con(con(era, era), con(" ++
    Comb.Term.toStr (codeOf (Sym.zero : sig.Sym)) ++ ", 0))), 0)"

-- The menu `Γ_0 = Γ_{0,0} & Γ_{S,0} & Γ_{add,0}`: only `add` has a rule with `0`, so the first
-- two packages are erasers.
#guard Comb.Term.toStr (menuOf (Sym.zero : sig.Sym)) ==
  "con(era, con(era, con(con(con(era, 1), 1), era)))"

end INet.Demo.Arith.ArithmeticTrReview
