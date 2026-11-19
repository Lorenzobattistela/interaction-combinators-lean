import InteractionCombinators.Lafont.DecompositionCheck
import InteractionCombinators.RenameMany
import InteractionCombinators.Instance

/-!
# Review of the canonical decomposition (page 85)

Review of `Lafont/Decomposition.lean` against Lafont 1997, page 85 (PDF page 17). The figure
draws `ν_{i,j}` as `φ_{i,j}` (on the `n_i` auxiliary ports of `α_i`, on the left) and `ψ_{i,j}`
(on the `n_j` ports of `α_j`, on the right) above a box `σ_{i,j}` that joins their lower wires.

## An invariant of `Equiv`

To show that two nets are *not* `Equiv`, this file uses solutions of equations. A map
`s : ν → Term S μ` solves a net if both sides of every equation become the same tree under `s`.
A wire substitution is a step of unification, so the restrictions of the solutions to the free
ports do not change (`Equiv.sol_iff`). For a net without cells, this says that the pairs of free
ports joined by a path are the same. `Net.Sol`, `Equiv.sol_iff`, the port names `pl`, `pr`, `pw`
and `equiv_wire_of_eq` are in `DecompositionLemmas.lean`, because library files use them.

## The checks

* `cyc`: a rule without cells whose canonical `σ` is the 3-cycle `[1, 2, 0]`. Plugging through `σ`
  gives back the rule (`cyc_plug`); plugging through `σ⁻¹` does not (`cyc_plug_symm_not`). So the
  convention of `Rule.plug` (wire `l` of `φ` joined to wire `σ l` of `ψ`) is the one that
  `decompose` produces, and it can be told apart from the inverse.
* `mix`: a rule with internal wires inside each side, a wire crossing between the sides, a port of
  the second cell in a tree of the first, and a port of the first cell in a tree of the second.
  Its decomposition is computed by `decide` and agrees with a hand computation; `plug_decompose`
  applies to it.
* The symmetric normalisation of page 85 (`ψ_{j,i} = φ_{i,j}`, `σ_{j,i} = σ_{i,j}⁻¹`) holds
  literally on `mix`, `cyc` and `ruleConDup` (`mix_swap`, `cyc_swap`, `conDup_swap`). For `i ≠ j`
  it is not needed anyway: only one of the rules `α_i`–`α_j`, `α_j`–`α_i` exists (`System.unique`),
  and `φ_{j,i}` can be defined as `ψ_{i,j}`.
* For `i = j` it fails. Page 86 assumes "in all cases `φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}`,
  and `σ_{i,j}` is involutive", and derives it for `i = j` from the symmetry of the rule and the
  uniqueness of the canonical decomposition. `selfRule` is a linear, reduced rule `α`–`α` that
  satisfies `System.symm` (`selfRule_symm`), yet its canonical `σ` is the 3-cycle `[2, 0, 1, 3]`
  (`selfRule_σ`) and its `φ` and `ψ` differ (`selfRule_φ_ne_ψ`). The cause is that `Half.key`
  numbers the middle wires by the names of the rule, so `Rule.decompose` depends on the text of the
  rule, not only on its graph: `selfRule.swap` and `selfRule` are `Equiv` but not equal.
* A remark on `System.symm`: `Equiv` works at the type of the rule's names, which has no spare
  name when every internal wire is used (as `Rule.Linear` demands). A net with no equation of the
  form `x = w` for an internal wire `w` then admits no wire substitution in either direction, and
  is `Equiv` only to itself (argued here, not proved in Lean). `selfRule` has the equations
  `a₂ = w₃`, `b₂ = w₃`, which free the name `w₃` and make the renaming possible.
-/

namespace INet

open Term

/-- Two nets that differ by the renaming of the wire `x` into an unused name `y` are `Equiv`: both
are obtained from the net with an extra equation `y = x` by one wire substitution. -/
theorem Net.equiv_two_wires {S : Signature} {ν : Type} [DecidableEq ν] {N M : Net S ν} (x y : ν)
    (a b c d : Term S ν) (Δ : Net S ν)
    (hlin : Net.Linear (s(var y, var x) ::ₘ s(a, b) ::ₘ s(c, d) ::ₘ Δ))
    (hy : y ∈ a.vars + b.vars) (hx : x ∈ c.vars + d.vars)
    (hN : N = s(a.subst y (var x), b.subst y (var x)) ::ₘ s(c, d) ::ₘ Δ)
    (hM : M = s(c.subst x (var y), d.subst x (var y)) ::ₘ s(a, b) ::ₘ Δ) : Equiv N M := by
  have e : (s(var y, var x) ::ₘ s(a, b) ::ₘ s(c, d) ::ₘ Δ : Net S ν) =
      s(var x, var y) ::ₘ s(c, d) ::ₘ s(a, b) ::ₘ Δ := by
    rw [Sym2.eq_swap, Multiset.cons_swap (s(a, b))]
  have h1 := (Wire.mk y (var x) a b _ hlin hy).equiv
  have h2 := (Wire.mk x (var y) c d (s(a, b) ::ₘ Δ) (e ▸ hlin) hx).equiv
  rw [← e] at h2
  rw [hN, hM]
  exact h1.symm.trans h2

end INet

namespace INet.Comb.DecompositionReview

open Term Rule

/-! ### The direction of `σ`: a rule whose `σ` is a 3-cycle -/

/-- A rule without cells that joins the port `i` of the first cell to the port `i + 1` of the
second. -/
def cyc : Rule sig 3 3 := ⟨0, s(pl 0, pr 1) ::ₘ s(pl 1, pr 2) ::ₘ {s(pl 2, pr 0)}⟩

/-- `cyc` is linear. -/
theorem cyc_linear : cyc.Linear := ⟨by decide, by decide, by decide⟩

/-- `cyc` has three middle wires, one per equation. -/
theorem cyc_k : cyc.decompose.k = 3 := by decide

/-- `φ` of `cyc`: the port `i` on the middle wire `i` (numbered by the port at the root). -/
theorem cyc_φ : (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 0) from cyc.decompose.φ.net) =
    s(pl 0, pr 0) ::ₘ s(pl 1, pr 1) ::ₘ {s(pl 2, pr 2)} := by decide

/-- `ψ` of `cyc`: the port `j` on the middle wire `j`. -/
theorem cyc_ψ : (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 0) from cyc.decompose.ψ.net) =
    s(pl 0, pr 0) ::ₘ s(pl 1, pr 1) ::ₘ {s(pl 2, pr 2)} := by decide

/-- `σ` of `cyc` is the 3-cycle `l ↦ l + 1`: not an involution. -/
theorem cyc_σ : (List.finRange cyc.decompose.k).map (fun l => (cyc.decompose.σ l).val) =
    [1, 2, 0] := by decide

/-- Plugging the sides of `cyc` through `σ` gives back `cyc` (`plug_decompose`). -/
theorem cyc_plug : ∃ ι : Fin cyc.internal →
    Fin (Rule.plug cyc.decompose.φ cyc.decompose.ψ cyc.decompose.σ).internal,
    Function.Injective ι ∧
      Equiv (Rule.plug cyc.decompose.φ cyc.decompose.ψ cyc.decompose.σ).net
        (cyc.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) :=
  cyc.plug_decompose cyc_linear

/-- Plugging the sides of `cyc` through `σ⁻¹` does not give back `cyc`, for any renaming: the
port `0` of the first cell ends up joined to the port `2` of the second, not to the port `1`. So
the direction of `σ` in `Rule.plug` matters, and `decompose` produces the one `plug` expects. -/
theorem cyc_plug_symm_not : ¬ ∃ ι : Fin cyc.internal →
    Fin (Rule.plug cyc.decompose.φ cyc.decompose.ψ cyc.decompose.σ.symm).internal,
    Function.Injective ι ∧
      Equiv (Rule.plug cyc.decompose.φ cyc.decompose.ψ cyc.decompose.σ.symm).net
        (cyc.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) := by
  rintro ⟨ι, -, hE⟩
  let s : Fin 3 ⊕ Fin 3 ⊕ Fin (Rule.plug cyc.decompose.φ cyc.decompose.ψ
      cyc.decompose.σ.symm).internal → Term sig (Fin 3) :=
    Sum.elim (fun i => var i) (Sum.elim (fun j => var (j + 2)) fun _ => var 0)
  have hN : Net.Sol (cyc.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) s := by
    refine ⟨s, ?_, fun _ _ => rfl⟩
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.1 he
    have key : ∀ e ∈ cyc.net, e = s(pl 0, pr 1) ∨ e = s(pl 1, pr 2) ∨ e = s(pl 2, pr 0) := by
      decide
    rcases key e₀ he₀ with rfl | rfl | rfl <;> rfl
  obtain ⟨s', hs, hp⟩ := (hE.sol_iff s).2 hN
  have h1 := hs s(var (.inl 0), var (.inr (.inr ⟨0, by decide⟩))) (by decide)
  have h2 := hs s(var (.inr (.inl 2)), var (.inr (.inr ⟨0, by decide⟩))) (by decide)
  have p1 := hp (.inl 0) (by decide)
  have p2 := hp (.inr (.inl 2)) (by decide)
  simp only [Sym2.lift_mk, Term.bind_var] at h1 h2
  rw [p1] at h1
  rw [p2, ← h1] at h2
  exact absurd h2 (by decide)

end INet.Comb.DecompositionReview

namespace INet.Comb.DecompositionReview

open Term Rule

/-! ### A rule with every kind of middle wire -/

/-- A rule with three wires: `w₁` stays on the side of the first cell, `w₂` on the side of the
second, `w₀` crosses; the port `0` of the second cell sits in a tree of the first, and the port `2`
of the first cell in a tree of the second:
`a₀ = con(w₀, w₁)`, `a₁ = dup(w₁, b₀)`, `b₁ = con(w₀, w₂)`, `b₂ = dup(w₂, a₂)`. -/
def mix : Rule sig 3 3 :=
  ⟨3, s(pl 0, mkCon (pw 0) (pw 1)) ::ₘ s(pl 1, mkDup (pw 1) (pr 0)) ::ₘ
    s(pr 1, mkCon (pw 0) (pw 2)) ::ₘ {s(pr 2, mkDup (pw 2) (pl 2))}⟩

/-- `mix` is linear. -/
theorem mix_linear : mix.Linear := ⟨by decide, by decide, by decide⟩

/-- `mix` is reduced: every equation is rooted at a port. -/
theorem mix_reduced : mix.Reduced := by
  show ∀ e ∈ (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 3) from mix.net),
    ∃ (p : Fin 3 ⊕ Fin 3 ⊕ Fin 3) (t : Term sig (Fin 3 ⊕ Fin 3 ⊕ Fin 3)),
      e = s(Term.var p, t) ∧ ∀ w : Fin 3, p ≠ .inr (.inr w)
  intro e he
  have key : ∀ e ∈ (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 3) from mix.net),
      e ∈ [s(pl 0, mkCon (pw 0) (pw 1)), s(pl 1, mkDup (pw 1) (pr 0)),
        s(pr 1, mkCon (pw 0) (pw 2)), s(pr 2, mkDup (pw 2) (pl 2))] := by
    decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl, fun w h => by cases h⟩

/-- The middle wires of `mix` are `w₀`, `b₀` and `a₂`: exactly the three wires that cross between
the two parts. -/
theorem mix_k : mix.decompose.k = 3 := by decide

/-- Each side of `mix` keeps one internal wire: `w₁` in `φ`, `w₂` in `ψ`. -/
theorem mix_internal : mix.decompose.φ.internal = 1 ∧ mix.decompose.ψ.internal = 1 := by decide

/-- `φ` of `mix`: the middle wires are numbered `w₀ ↦ 0` (root `a₀`), `b₀ ↦ 1` (root `a₁`),
`a₂ ↦ 2` (root `a₂`), and the port `a₂`, which occurs in a tree of the second cell, gets the
equation `a₂ = 2`. -/
theorem mix_φ : (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 1) from mix.decompose.φ.net) =
    s(pl 0, mkCon (pr 0) (pw 0)) ::ₘ s(pl 1, mkDup (pw 0) (pr 1)) ::ₘ {s(pl 2, pr 2)} := by
  decide

/-- `ψ` of `mix`: the middle wires are numbered `b₀ ↦ 0`, `w₀ ↦ 1` (root `b₁`), `a₂ ↦ 2` (root
`b₂`), and the port `b₀`, which occurs in a tree of the first cell, gets the equation `b₀ = 0`. -/
theorem mix_ψ : (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 1) from mix.decompose.ψ.net) =
    s(pl 1, mkCon (pr 1) (pw 0)) ::ₘ s(pl 2, mkDup (pw 0) (pr 2)) ::ₘ {s(pl 0, pr 0)} := by
  decide

/-- `σ` of `mix`: `w₀` is `0` in `φ` and `1` in `ψ`, `b₀` is `1` and `0`, `a₂` is `2` and `2`. -/
theorem mix_σ : (List.finRange mix.decompose.k).map (fun l => (mix.decompose.σ l).val) =
    [1, 0, 2] := by decide

/-- The sides of `mix` are linear and reduced (`decompose_linear`, `decompose_reduced`). -/
theorem mix_sides : (mix.decompose.φ.Linear ∧ mix.decompose.ψ.Linear) ∧
    (mix.decompose.φ.Reduced ∧ mix.decompose.ψ.Reduced) :=
  ⟨mix.decompose_linear mix_linear, mix.decompose_reduced mix_reduced⟩

/-- Plugging the sides of `mix` gives back `mix` (`plug_decompose`), with internal wires renamed
injectively. -/
theorem mix_plug : ∃ ι : Fin mix.internal →
    Fin (Rule.plug mix.decompose.φ mix.decompose.ψ mix.decompose.σ).internal,
    Function.Injective ι ∧
      Equiv (Rule.plug mix.decompose.φ mix.decompose.ψ mix.decompose.σ).net
        (mix.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) :=
  mix.plug_decompose mix_linear

/-- The plugged net of `mix`, literally: the middle wires are the wires `0, 1, 2`, the internal
wire of `φ` is `3` and that of `ψ` is `4`. Up to these names, this is `mix`. -/
theorem mix_plug_net :
    (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 5) from
      (Rule.plug mix.decompose.φ mix.decompose.ψ mix.decompose.σ).net) =
    s(pl 0, mkCon (pw 0) (pw 3)) ::ₘ s(pl 1, mkDup (pw 3) (pw 1)) ::ₘ s(pl 2, pw 2) ::ₘ
      s(pr 1, mkCon (pw 0) (pw 4)) ::ₘ s(pr 2, mkDup (pw 4) (pw 2)) ::ₘ {s(pr 0, pw 1)} := by
  decide

/-! ### The symmetric normalisation of page 85 -/

/-- On `mix`, the decomposition of the rule read from the other cell exchanges the two sides:
`ψ_{j,i} = φ_{i,j}` and `φ_{j,i} = ψ_{i,j}`, literally (page 85). -/
theorem mix_swap :
    (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 1) from mix.swap.decompose.φ.net) =
      (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 1) from mix.decompose.ψ.net) ∧
    (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 1) from mix.swap.decompose.ψ.net) =
      (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 1) from mix.decompose.φ.net) := by
  decide +kernel

/-- On `cyc`, the decomposition of the rule read from the other cell has `σ⁻¹`: `σ` is
`[1, 2, 0]`, and `σ` of `cyc.swap` is `[2, 0, 1]` (page 85: `σ_{j,i} = σ_{i,j}⁻¹`). -/
theorem cyc_swap :
    (List.finRange cyc.swap.decompose.k).map (fun l => (cyc.swap.decompose.σ l).val) =
      [2, 0, 1] := by decide

/-- On `con`–`dup`, the decomposition of `dup`–`con` exchanges the sides and keeps `σ`, which is
an involution. -/
theorem conDup_swap :
    (show Net sig (Fin 2 ⊕ Fin 4 ⊕ Fin 0) from ruleConDup.swap.decompose.φ.net) =
      (show Net sig (Fin 2 ⊕ Fin 4 ⊕ Fin 0) from ruleConDup.decompose.ψ.net) ∧
    (show Net sig (Fin 2 ⊕ Fin 4 ⊕ Fin 0) from ruleConDup.swap.decompose.ψ.net) =
      (show Net sig (Fin 2 ⊕ Fin 4 ⊕ Fin 0) from ruleConDup.decompose.φ.net) ∧
    (List.finRange ruleConDup.swap.decompose.k).map
      (fun l => (ruleConDup.swap.decompose.σ l).val) = [0, 2, 1, 3] := by
  decide +kernel

/-! ### A symmetric rule whose canonical `σ` is not an involution -/

/-- A rule of a symbol with three auxiliary ports with itself:
`a₀ = con(w₀, w₁)`, `a₁ = con(w₂, ε)`, `a₂ = w₃`, `b₀ = con(w₂, w₁)`, `b₁ = con(w₀, ε)`,
`b₂ = w₃`. Read from the other cell it is the same graph, with `w₀` and `w₂` exchanged. -/
def selfRule : Rule sig 3 3 :=
  ⟨4, s(pl 0, mkCon (pw 0) (pw 1)) ::ₘ s(pl 1, mkCon (pw 2) mkEra) ::ₘ s(pl 2, pw 3) ::ₘ
    s(pr 0, mkCon (pw 2) (pw 1)) ::ₘ s(pr 1, mkCon (pw 0) mkEra) ::ₘ {s(pr 2, pw 3)}⟩

/-- `selfRule` is linear: every internal wire, `w₃` included, occurs twice. -/
theorem selfRule_linear : selfRule.Linear := ⟨by decide, by decide, by decide⟩

/-- `selfRule` is reduced: every equation is rooted at a port. -/
theorem selfRule_reduced : selfRule.Reduced := by
  show ∀ e ∈ (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4) from selfRule.net),
    ∃ (p : Fin 3 ⊕ Fin 3 ⊕ Fin 4) (t : Term sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4)),
      e = s(Term.var p, t) ∧ ∀ w : Fin 4, p ≠ .inr (.inr w)
  intro e he
  have key : ∀ e ∈ (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4) from selfRule.net),
      e ∈ [s(pl 0, mkCon (pw 0) (pw 1)), s(pl 1, mkCon (pw 2) mkEra), s(pl 2, pw 3),
        s(pr 0, mkCon (pw 2) (pw 1)), s(pr 1, mkCon (pw 0) mkEra), s(pr 2, pw 3)] := by
    decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl, fun w h => by cases h⟩

/-- `selfRule` is symmetric as `System.symm` asks: read from the other cell, it is `Equiv` to
itself. The wire `w₃` is first absorbed (`a₂ = b₂`), which frees its name; then `w₀ ↦ w₃`,
`w₂ ↦ w₀`, `w₃ ↦ w₂`; then `w₃` is put back. -/
theorem selfRule_symm : Equiv selfRule.swap.net selfRule.net := by
  -- `a₂ = b₂`, the rest as in `selfRule.swap`
  have h₀ := equiv_wire_of_eq (ν := Fin 3 ⊕ Fin 3 ⊕ Fin 4)
    (N := (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4) from selfRule.swap.net))
    (.inr (.inr 3)) (pr 2) (pl 2) (pw 3)
    (s(pr 0, mkCon (pw 0) (pw 1)) ::ₘ s(pr 1, mkCon (pw 2) mkEra) ::ₘ
      s(pl 0, mkCon (pw 2) (pw 1)) ::ₘ {s(pl 1, mkCon (pw 0) mkEra)})
    (by unfold Net.Linear; decide) (by decide) (by decide) rfl
  -- `w₀ ↦ w₃`
  have h₁ := Net.equiv_two_wires (ν := Fin 3 ⊕ Fin 3 ⊕ Fin 4) (.inr (.inr 0)) (.inr (.inr 3))
    (pr 0) (mkCon (pw 3) (pw 1)) (pl 1) (mkCon (pw 0) mkEra)
    (s(pr 1, mkCon (pw 2) mkEra) ::ₘ s(pl 0, mkCon (pw 2) (pw 1)) ::ₘ {s(pl 2, pr 2)})
    (by unfold Net.Linear; decide) (by decide) (by decide) rfl rfl
  -- `w₂ ↦ w₀`
  have h₂ := Net.equiv_two_wires (ν := Fin 3 ⊕ Fin 3 ⊕ Fin 4) (.inr (.inr 2)) (.inr (.inr 0))
    (pr 1) (mkCon (pw 0) mkEra) (pl 0) (mkCon (pw 2) (pw 1))
    (s(pl 1, mkCon (pw 3) mkEra) ::ₘ s(pr 0, mkCon (pw 3) (pw 1)) ::ₘ {s(pl 2, pr 2)})
    (by unfold Net.Linear; decide) (by decide) (by decide) rfl rfl
  -- `w₃ ↦ w₂`
  have h₃ := Net.equiv_two_wires (ν := Fin 3 ⊕ Fin 3 ⊕ Fin 4) (.inr (.inr 3)) (.inr (.inr 2))
    (pl 1) (mkCon (pw 2) mkEra) (pr 0) (mkCon (pw 3) (pw 1))
    (s(pl 0, mkCon (pw 0) (pw 1)) ::ₘ s(pr 1, mkCon (pw 0) mkEra) ::ₘ {s(pl 2, pr 2)})
    (by unfold Net.Linear; decide) (by decide) (by decide) rfl rfl
  -- `w₃` back
  have h₄ := equiv_wire_of_eq (ν := Fin 3 ⊕ Fin 3 ⊕ Fin 4)
    (M := s(pl 2, pr 2) ::ₘ s(pr 0, mkCon (pw 2) (pw 1)) ::ₘ
      s(pl 1, mkCon (pw 2) mkEra) ::ₘ s(pl 0, mkCon (pw 0) (pw 1)) ::ₘ
      {s(pr 1, mkCon (pw 0) mkEra)})
    (N := (show Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4) from selfRule.net))
    (.inr (.inr 3)) (pr 2) (pl 2) (pw 3)
    (s(pr 0, mkCon (pw 2) (pw 1)) ::ₘ s(pl 1, mkCon (pw 2) mkEra) ::ₘ
      s(pl 0, mkCon (pw 0) (pw 1)) ::ₘ {s(pr 1, mkCon (pw 0) mkEra)})
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have e₁ : (s((pl 2).subst (.inr (.inr 3)) (pr 2), (pw 3).subst (.inr (.inr 3)) (pr 2)) ::ₘ
      s(pr 0, mkCon (pw 0) (pw 1)) ::ₘ s(pr 1, mkCon (pw 2) mkEra) ::ₘ
      s(pl 0, mkCon (pw 2) (pw 1)) ::ₘ {s(pl 1, mkCon (pw 0) mkEra)} :
        Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4)) =
      s((pr 0).subst (.inr (.inr 3)) (var (.inr (.inr 0))),
        (mkCon (pw 3) (pw 1)).subst (.inr (.inr 3)) (var (.inr (.inr 0)))) ::ₘ
      s(pl 1, mkCon (pw 0) mkEra) ::ₘ
      (s(pr 1, mkCon (pw 2) mkEra) ::ₘ s(pl 0, mkCon (pw 2) (pw 1)) ::ₘ {s(pl 2, pr 2)}) := by
    decide
  have e₂ : (s((pl 1).subst (.inr (.inr 0)) (var (.inr (.inr 3))),
        (mkCon (pw 0) mkEra).subst (.inr (.inr 0)) (var (.inr (.inr 3)))) ::ₘ
      s(pr 0, mkCon (pw 3) (pw 1)) ::ₘ
      (s(pr 1, mkCon (pw 2) mkEra) ::ₘ s(pl 0, mkCon (pw 2) (pw 1)) ::ₘ {s(pl 2, pr 2)}) :
        Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4)) =
      s((pr 1).subst (.inr (.inr 0)) (var (.inr (.inr 2))),
        (mkCon (pw 0) mkEra).subst (.inr (.inr 0)) (var (.inr (.inr 2)))) ::ₘ
      s(pl 0, mkCon (pw 2) (pw 1)) ::ₘ
      (s(pl 1, mkCon (pw 3) mkEra) ::ₘ s(pr 0, mkCon (pw 3) (pw 1)) ::ₘ {s(pl 2, pr 2)}) := by
    decide
  have e₃ : (s((pl 0).subst (.inr (.inr 2)) (var (.inr (.inr 0))),
        (mkCon (pw 2) (pw 1)).subst (.inr (.inr 2)) (var (.inr (.inr 0)))) ::ₘ
      s(pr 1, mkCon (pw 0) mkEra) ::ₘ
      (s(pl 1, mkCon (pw 3) mkEra) ::ₘ s(pr 0, mkCon (pw 3) (pw 1)) ::ₘ {s(pl 2, pr 2)}) :
        Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4)) =
      s((pl 1).subst (.inr (.inr 2)) (var (.inr (.inr 3))),
        (mkCon (pw 2) mkEra).subst (.inr (.inr 2)) (var (.inr (.inr 3)))) ::ₘ
      s(pr 0, mkCon (pw 3) (pw 1)) ::ₘ
      (s(pl 0, mkCon (pw 0) (pw 1)) ::ₘ s(pr 1, mkCon (pw 0) mkEra) ::ₘ {s(pl 2, pr 2)}) := by
    decide
  have e₄ : (s((pr 0).subst (.inr (.inr 3)) (var (.inr (.inr 2))),
        (mkCon (pw 3) (pw 1)).subst (.inr (.inr 3)) (var (.inr (.inr 2)))) ::ₘ
      s(pl 1, mkCon (pw 2) mkEra) ::ₘ
      (s(pl 0, mkCon (pw 0) (pw 1)) ::ₘ s(pr 1, mkCon (pw 0) mkEra) ::ₘ {s(pl 2, pr 2)}) :
        Net sig (Fin 3 ⊕ Fin 3 ⊕ Fin 4)) =
      s(pl 2, pr 2) ::ₘ s(pr 0, mkCon (pw 2) (pw 1)) ::ₘ
      s(pl 1, mkCon (pw 2) mkEra) ::ₘ s(pl 0, mkCon (pw 0) (pw 1)) ::ₘ
      {s(pr 1, mkCon (pw 0) mkEra)} := by
    decide
  rw [e₁] at h₀
  rw [e₂] at h₁
  rw [e₃] at h₂
  rw [e₄] at h₃
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄.symm)))

/-- The canonical `σ` of the symmetric rule `selfRule` is `[2, 0, 1, 3]`, which is not an
involution. Page 85 derives from the symmetry of a rule `α_i`–`α_i` and the uniqueness of the
canonical decomposition that `σ_{i,i}` is involutive; for `Rule.decompose`, which numbers the
middle wires by the names of the rule (`Half.key`), this fails. -/
theorem selfRule_σ :
    (List.finRange selfRule.decompose.k).map (fun l => (selfRule.decompose.σ l).val) =
      [2, 0, 1, 3] := by decide +kernel

/-- For `selfRule`, `φ` and `ψ` are different nets, although the rule is symmetric: page 85
derives `φ_{i,i} = ψ_{i,i}` for the canonical decomposition. -/
theorem selfRule_φ_ne_ψ :
    (show Net sig (Fin 3 ⊕ Fin 4 ⊕ Fin 0) from selfRule.decompose.φ.net) ≠
      (show Net sig (Fin 3 ⊕ Fin 4 ⊕ Fin 0) from selfRule.decompose.ψ.net) := by
  decide +kernel

end INet.Comb.DecompositionReview
