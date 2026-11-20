import InteractionCombinators.Universality.Codes.Decode
import InteractionCombinators.Universality.General.CodeGamma

/-!
# Review of the code `!π`, the decoder `D`, `decodeNet` and `codeExtra` after PR #298

Lafont 1997, Fig. 8 (page 88, PDF page 20), Fig. 9 and Fig. 10 (page 89, PDF page 21). Issue #318.
The figures were rendered alone at 600 dpi and read wire by wire.

## The convention

Page 71: the ports of a cell are "implicitly numbered in clockwise order", so a cell pointing up is
a cell pointing down turned by 180°. Page 82 (PDF page 14) numbers them: the upper `γ` (pointing
down) has its auxiliary ports `1 2` from left to right, the lower `γ` (pointing up) has `2 1` from
left to right. **A cell drawn pointing up has its port 1 (Lean port 0) on the right.** In the same
picture `γγ` joins, by straight wires, the upper `1` to the lower `2` and the upper `2` to the lower
`1`; `δδ` crosses the wires, joining `1` to `1` and `2` to `2`. `ruleConCon` joins `l 0` to `r 1`
and `l 1` to `r 0`, `ruleDupDup` joins `l 0` to `r 0` and `l 1` to `r 1`
(`InteractionCombinators/Core/Combinators.lean`): both agree with this reading (`conCon_page82`,
`dupDup_page82`). (The issue points to pages 70 and 72 for the pictures of the combinators; the
cell pictures are on page 71, the rules in Fig. 2, page 81, and the numbered picture on page 82.)

`mux` (pointing down) and `muxStar` (pointing up) list their ports from left to right as drawn:
for `mux` the head of the list is on port 0 of the root `con` (drawn left for a cell pointing down),
for `muxStar` the head is on port 0 of the last `con` and the rest on port 1 (drawn left for a cell
pointing up), so in both the head is leftmost (`mux_order`, `muxStar_order`).

## Wire by wire

* **The decomposition above Fig. 8.** Each `δ` points up. Its drawn left port (Lean port 1) goes
  down to the left group of free ports of `π'`; its drawn right port (Lean port 0) crosses over to
  the right group.
* **The code (Fig. 8, left).** `M_4` points down; its ports from left to right go to: `M_n` (whose
  auxiliary ports go round the top to the cut names, the principal ports of the `δ`); a wire up
  and over to the **right** `M_n*` (sitting on the right group, the trees on port 0); a wire up and
  over to the **left** `M_n*` (on the left group, the trees on port 1); the root of `π'`. This is
  `Decomp.code = M_4 [M_n (x_i), M_n* (l_i), M_n* (r_i), τ]` (`code_π_eq`, on a package whose two
  cells have different trees on their two ports).
* **The decoder (Fig. 8, right).** `M_4*` points up. Its first port (leftmost) carries a `δ`
  pointing up. The small inner loop joins the drawn right port of the `δ` (Lean port 0) to the
  second port of `M_4*`; the big outer loop joins its drawn left port (Lean port 1) to the third;
  the fourth port (rightmost) is free. This is `decoder w k = M_4* [dup(k, k + 1), k, k + 1, w]`,
  with `w` last (`decoder_leaves`, `decoder_dup_ports`).
* **Fig. 9, first stage.** `M_n` meets the `δ`; the `δ`'s drawn left port goes to the left `M_n*`
  (trees `r_i`), its drawn right port to the right `M_n*` (trees `l_i`). This is `decodeNet`, with
  `a` (port 0) on `M_n*` of the `l_i` (`decodeNet_π`, the net that `code_decoder` reaches).
* **Fig. 10, bottom left, `⟨α_k⟩`.** The decoder inside is the decoder above: `codeExtra` contains
  `M_4* [dup(k₀, k₀ + 1), k₀, k₀ + 1, S^i_m(y)]` (`codeExtra_inst`, and `codeExtra_eq` on a concrete
  instance). One observation, not a defect: in the figure `D` hangs on the drawn **left** auxiliary
  port of `C_2`, which points up, and `codeExtra` puts it on port 0 of the `dup` cell `C_2(D, u)`.
  If `C_2` is read as a `δ` cell turned up, its drawn left port is port 1, and the Lean is mirrored;
  if the ports of a named principal net are read from left to right as drawn (as for `M_n*`), the
  Lean agrees. The paper never numbers the ports of `C_n`, and both ports receive a copy of the same
  closed package `!Γ` (`copier_package`), so the choice changes no property. The owner's comparison
  with the figures records the same point as "not comparable".

## Reduction

`decode_π` applies `code_decoder_package` with satisfied hypotheses to `π = con(dup(con(0, 1), 0),
dup(1, ε))`, whose two `dup` cells have different trees on their two ports. The decoded net is
`Equiv` to `π` on the free port, and `π` on the free port is **not** `Equiv` to the package `πx`
with the auxiliary ports of both `dup` cells exchanged (`not_equiv_π_πx`). The invariant used is
the set of values on the free ports that extend to a solution where `con` is `and`, `dup` keeps its
port 0 and `era` is `false` (`Equiv.sol_iff`): `π` reaches `true`, `πx` does not.

This test cannot see an exchange made on both `code` and `decoder`: before #298 the two middle
ports were exchanged in both, and Theorem 1 held. Only the comparison with the figure above can see
that.

## Refutation attempt

`oldDecoder` is the decoder before #298, `M_4* [dup(k, k + 1), k + 1, k, w]`. The current code
against it decodes `π` into the exchanged package `πx` (`decode_old`), which is not `Equiv` to `π`.
So the order of the middle ports matters, and the current pair `code`/`decoder` is the one that
decodes `π` itself.

## What was not checked

The wiring of the rest of `⟨α_k⟩` and of `Γ_{i,j}` (Fig. 10) beyond the decoder, and the order of
the extra ports in `C_{p_{i,j}}`, are outside this issue.
-/

namespace INet.Comb.CodeFig8Review

open Term Decomp

/-! ## The convention of page 82 -/

/-- **`γγ` on page 82.** The upper `con` (pointing down) has `a` on port 1 (left) and `b` on port
2; the lower one (pointing up) has `c` on port 1 (drawn right) and `d` on port 2 (drawn left).
The straight wires join `a` to `d` and `b` to `c`. -/
theorem conCon_page82 (a b c d : Term sig ℕ) (Δ : CNet) :
    Step system (s(mkCon a b, mkCon c d) ::ₘ Δ) (s(a, d) ::ₘ s(b, c) ::ₘ Δ) :=
  step_con_con a b c d Δ

/-- **`δδ` on page 82.** The crossing wires join port 1 to port 1 and port 2 to port 2. -/
theorem dupDup_page82 (a b c d : Term sig ℕ) (Δ : CNet) :
    Step system (s(mkDup a b, mkDup c d) ::ₘ Δ) (s(a, c) ::ₘ s(b, d) ::ₘ Δ) :=
  step_dup_dup a b c d Δ

/-- `M_3` (pointing down, page 82): the head of the list on port 0 of the root `con`, drawn left. -/
theorem mux_order (t₁ t₂ t₃ : Term sig ℕ) : mux [t₁, t₂, t₃] = mkCon t₁ (mkCon t₂ t₃) := rfl

/-- `M_3*` (pointing up, page 82): the head on port 0 of the lowest `con`, which is drawn left of
the rest on port 1 of the root, itself drawn left of the last leaf on port 0. -/
theorem muxStar_order (u₁ u₂ u₃ : Term sig ℕ) :
    muxStar [u₁, u₂, u₃] = mkCon (mkCon u₃ u₂) u₁ := rfl

/-! ## The decoder, wire by wire (Fig. 8, page 88) -/

/-- The four leaves of `M_4*` in the decoder (Fig. 8, page 88), from left to right: the `dup` cell,
the wire `k` (inner loop), the wire `k + 1` (outer loop), the free port `w`. -/
theorem decoder_leaves (w k : ℕ) :
    (decoder w k : Term sig ℕ) = muxStar [mkDup (var k) (var (k + 1)), var k, var (k + 1), var w] :=
  rfl

/-- The `dup` cell of the decoder (Fig. 8): its port 0 (drawn right, the inner loop) is the second
leaf of `M_4*`, its port 1 (drawn left, the outer loop) the third. -/
theorem decoder_dup_ports (w k : ℕ) :
    ∃ a b, (decoder w k : Term sig ℕ) = muxStar [mkDup (var a) (var b), var a, var b, var w] :=
  ⟨k, k + 1, rfl⟩

/-! ## The package `π` and its exchanged form -/

/-- `π = con(dup(con(0, 1), 0), dup(1, ε))`: two `dup` cells, each with different trees on its
port 0 and its port 1. -/
def π : Term sig ℕ := mkCon (mkDup (mkCon (var 0) (var 1)) (var 0)) (mkDup (var 1) mkEra)

/-- `π` with the auxiliary ports of both `dup` cells exchanged. -/
def πx : Term sig ℕ := mkCon (mkDup (var 0) (mkCon (var 0) (var 1))) (mkDup mkEra (var 1))

theorem π_isPackage : π.IsPackage := by unfold Term.IsPackage; decide

theorem πx_isPackage : πx.IsPackage := by unfold Term.IsPackage; decide

/-- The decomposition of `π` with new names from `3` (page 88): cells cut at `5` and `10`, with
`l = con(0, 1)`, `r = 0` and `l = 1`, `r = ε`; `τ = con(5, 10)`; next name `13`. -/
theorem decomp_π : decomp 3 π =
    ⟨mkCon (var 5) (var 10), [(5, mkCon (var 0) (var 1), var 0), (10, var 1, mkEra)], 13⟩ := rfl

/-- The decomposition of `πx`: the same cut names and the same `τ`, the trees exchanged. -/
theorem decomp_πx : decomp 3 πx =
    ⟨mkCon (var 5) (var 10), [(5, var 0, mkCon (var 0) (var 1)), (10, mkEra, var 1)], 13⟩ := rfl

/-- **The code of `π` (Fig. 8, page 88).** `M_4 [M_2 (5, 10), M_2* (con(0, 1), 1),
M_2* (0, ε), con(5, 10)]`: the trees on port 0 of the cells on the second leaf, those on port 1 on
the third. -/
theorem code_π_eq : code 3 π =
    mux [mux [var 5, var 10], muxStar [mkCon (var 0) (var 1), var 1], muxStar [var 0, mkEra],
      mkCon (var 5) (var 10)] := rfl

/-- **The first stage of Fig. 9 (page 89) on `π`** reaches `decodeNet` of the cells of `π`: `M_2` on
the `dup` cell with ports `13` (port 0) and `14`, `M_2*` of the trees on port 0 on `13`, `M_2*` of
the trees on port 1 on `14`, and `τ` on the free port `2`. -/
theorem decodeNet_π : Red {s(code 3 π, decoder 2 13)}
    (decodeNet (decomp 3 π).cells 13 14 {s((decomp 3 π).τ, var 2)}) :=
  code_decoder 3 π 2 13 0

/-- `decodeNet` of the cells of `π`, written out. -/
theorem decodeNet_π_eq : decodeNet (decomp 3 π).cells 13 14 {s((decomp 3 π).τ, var 2)} =
    s(mux [var 5, var 10], mkDup (var 13) (var 14)) ::ₘ
      s(muxStar [mkCon (var 0) (var 1), var 1], var 13) ::ₘ
      s(muxStar [var 0, mkEra], var 14) ::ₘ {s(mkCon (var 5) (var 10), var 2)} := rfl

/-! ## `codeExtra` on a concrete instance (Fig. 10, page 89) -/

/-- `codeExtra 3 1 7 8 9` (Fig. 10, page 89): the copier `C_2` whose port 0 carries the decoder
with loop `9, 10` and the selector `S^1_3(7)` on its free port, and whose port 1 is `u = 8`. -/
theorem codeExtra_inst : codeExtra 3 1 7 8 9 =
    copier [muxStar [mkDup (var 9) (var 10), var 9, var 10, selector 3 1 7], var 8] := rfl

/-- `codeExtra_eq` on the same instance, with the free port `w = 20` of the decoder. -/
theorem codeExtra_inst_eq : codeExtra 3 1 7 8 9 =
    copier [(decoder 20 9).subst 20 (selector 3 1 7), var 8] :=
  codeExtra_eq 3 1 7 8 9 20 (by decide) (by decide)

/-! ## An invariant of `Equiv`: solutions with interpreted cells -/

section Sol

variable {S : Signature}

/-- The value of a tree when the names have the values `ρ` and each cell `α` computes `I α`. -/
def eval (I : (α : S.Sym) → (Fin (S.arity α) → Bool) → Bool) (ρ : ℕ → Bool) : Term S ℕ → Bool
  | .var x => ρ x
  | .app α ts => I α fun i => eval I ρ (ts i)

variable (I : (α : S.Sym) → (Fin (S.arity α) → Bool) → Bool)

theorem eval_subst (ρ : ℕ → Bool) (a : Term S ℕ) (x : ℕ) (t : Term S ℕ) :
    eval I ρ (a.subst x t) = eval I (Function.update ρ x (eval I ρ t)) a := by
  induction a with
  | var y =>
    by_cases h : y = x
    · subst h
      simp [Term.subst, eval]
    · simp [Term.subst, eval, h]
  | app α ts ih =>
    change I α (fun i => eval I ρ ((ts i).subst x t)) = _
    simp only [ih]
    rfl

theorem eval_congr {ρ ρ' : ℕ → Bool} {a : Term S ℕ} (h : ∀ y ∈ a.vars, ρ y = ρ' y) :
    eval I ρ a = eval I ρ' a := by
  induction a with
  | var y => exact h y (by simp)
  | app α ts ih =>
    change I α (fun i => eval I ρ (ts i)) = I α (fun i => eval I ρ' (ts i))
    congr 1
    funext i
    exact ih i fun y hy => h y (Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, hy⟩)

/-- `ρ` solves `N`: the two sides of each equation have the same value. -/
def Solves (ρ : ℕ → Bool) (N : Net S ℕ) : Prop := ∀ a b, s(a, b) ∈ N → eval I ρ a = eval I ρ b

/-- The values on the free names of `N` that extend to a solution of `N`. -/
def Sol (N : Net S ℕ) (s : ℕ → Bool) : Prop :=
  ∃ ρ, Solves I ρ N ∧ ∀ p, N.vars.count p = 1 → ρ p = s p

theorem solves_cons {ρ : ℕ → Bool} {c d : Term S ℕ} {N : Net S ℕ} :
    Solves I ρ (s(c, d) ::ₘ N) ↔ eval I ρ c = eval I ρ d ∧ Solves I ρ N := by
  constructor
  · intro h
    exact ⟨h c d (Multiset.mem_cons_self _ _), fun a b hab => h a b (Multiset.mem_cons_of_mem hab)⟩
  · rintro ⟨h1, h2⟩ a b hab
    rcases Multiset.mem_cons.1 hab with e | hm
    · rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h1
      · exact h1.symm
    · exact h2 a b hm

/-- A wire substitution does not change the values on the free names that extend to a solution
(the proof of `PairStepE.Wire.blindSol_iff`, with interpreted cells). -/
theorem Wire.sol_iff {N M : Net S ℕ} (h : Wire N M) (s : ℕ → Bool) : Sol I N s ↔ Sol I M s := by
  have hfree := h.free_iff
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hc := hlin x
  have hx1 := Multiset.one_le_count_iff_mem.2 hx
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hc hx1
  have ht : x ∉ t.vars := fun h => by
    have := Multiset.one_le_count_iff_mem.2 h; omega
  have hΔ : x ∉ Δ.vars := fun h => by
    have := Multiset.one_le_count_iff_mem.2 h; omega
  constructor
  · rintro ⟨ρ, hs, hp⟩
    rw [solves_cons, solves_cons] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    have hu : Function.update ρ x (eval I ρ t) = ρ := by
      rw [Function.update_eq_self_iff]; exact h1.symm
    refine ⟨ρ, (solves_cons I).2 ⟨?_, h3⟩, fun p hp1 => hp p ((hfree p).2 hp1)⟩
    rw [eval_subst, eval_subst, hu]
    exact h2
  · rintro ⟨ρ, hs, hp⟩
    rw [solves_cons] at hs
    obtain ⟨h2, h3⟩ := hs
    set ρ' := Function.update ρ x (eval I ρ t) with hρ'
    have hts : eval I ρ' t = eval I ρ t :=
      eval_congr I fun y hy => Function.update_of_ne (fun e => ht (by rw [← e]; exact hy)) _ _
    refine ⟨ρ', ?_, fun p hp1 => ?_⟩
    · rw [solves_cons, solves_cons]
      refine ⟨by simp [ρ', hts, eval], by rwa [eval_subst, eval_subst] at h2, ?_⟩
      intro c d hcd
      have hv : ∀ y ∈ c.vars + d.vars, y ≠ x := fun y hy e => hΔ (e ▸ Multiset.mem_bind.2
        ⟨s(c, d), hcd, by simpa using hy⟩)
      rw [eval_congr I (ρ' := ρ) fun y hy => Function.update_of_ne
          (hv y (Multiset.mem_add.2 (Or.inl hy))) _ _,
        eval_congr I (a := d) (ρ' := ρ) fun y hy => Function.update_of_ne
          (hv y (Multiset.mem_add.2 (Or.inr hy))) _ _]
      exact h3 c d hcd
    · have hpx : p ≠ x := by
        rintro rfl
        simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
          Multiset.count_singleton_self] at hp1
        omega
      rw [show ρ' p = ρ p from Function.update_of_ne hpx _ _]
      exact hp p ((hfree p).1 hp1)

/-- **Nets that are the same graph have the same solutions** (page 71), for every interpretation
of the cells. -/
theorem Equiv.sol_iff {N M : Net S ℕ} (h : Equiv N M) (s : ℕ → Bool) : Sol I N s ↔ Sol I M s := by
  induction h with
  | rel _ _ h => exact Wire.sol_iff I h s
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Sol

/-- The interpretation that separates `π` from `πx`: `con` is `and`, `dup` keeps its port 0, `era`
is `false`. -/
def andI : (α : sig.Sym) → (Fin (sig.arity α) → Bool) → Bool
  | .con => fun (v : Fin 2 → Bool) => v 0 && v 1
  | .dup => fun (v : Fin 2 → Bool) => v 0
  | .era => fun _ => false

/-- **`π` and the exchanged package are not the same graph** (page 71). On the free port `2`,
`π` reaches the value `true` (all names `true`), while `πx` always has the value `ρ 0 && false`. -/
theorem not_equiv_π_πx : ¬ Equiv ({s(var 2, π)} : CNet) {s(var 2, πx)} := by
  intro h
  have h1 : Sol andI ({s(var 2, π)} : CNet) fun _ => true := by
    refine ⟨fun _ => true, fun a b hab => ?_, fun _ _ => rfl⟩
    rcases Sym2.eq_iff.1 (Multiset.mem_singleton.1 hab) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  obtain ⟨ρ, hs, hp⟩ := (Equiv.sol_iff andI h _).1 h1
  have e : ρ 2 = (ρ 0 && false) := hs _ _ (Multiset.mem_singleton_self _)
  have h2 : ρ 2 = true := hp 2 (by decide)
  simp [h2] at e

/-! ## Fig. 9 on `π` -/

/-- **Fig. 9 (page 89) on `π`**: `code_decoder_package` with satisfied hypotheses. The code of `π`
(new names from `3`) against the decoder with free port `2` and loop `13, 14` reduces to a net
`Equiv` to `π` on `2`. -/
theorem decode_π : ∃ M, StepsE system {s(code 3 π, decoder 2 13)} M ∧ Equiv M {s(var 2, π)} :=
  code_decoder_package π π_isPackage 3 2 13 0
    (Net.linear_of_forall_mem (by decide)) (by unfold Net.Below; decide) (by decide)

/-- **The decoded net is `π`, not `πx`**: no net reached by `decode_π` is `Equiv` to `πx` on `2`. -/
theorem decode_π_not_πx :
    ∀ M, Equiv M {s(var 2, π)} → ¬ Equiv M {s(var 2, πx)} :=
  fun _ h h' => not_equiv_π_πx (h.symm.trans h')

/-! ## Refutation: the decoder before #298 -/

/-- The decoder before #298: the middle ports of `M_4*` exchanged, `M_4* [dup(k, k + 1), k + 1, k,
w]`. -/
def oldDecoder (w k : ℕ) : Term sig ℕ :=
  muxStar [mkDup (var k) (var (k + 1)), var (k + 1), var k, var w]

/-- The first stage of Fig. 9 with the old decoder: `M_4` against `M_4*` reaches `decodeNet` of the
cells of `πx`, that is the trees on port 1 of the cells of `π` on port 0 of the `dup` cell. -/
theorem old_first_stage : Red {s(code 3 π, oldDecoder 2 13)}
    (decodeNet (decomp 3 πx).cells 13 14 {s((decomp 3 πx).τ, var 2)}) := by
  have h := mux_muxStar [mux [var 5, var 10], muxStar [mkCon (var 0) (var 1), var 1],
    muxStar [var 0, mkEra], mkCon (var 5) (var 10)]
    [mkDup (var 13) (var 14), var 14, var 13, var 2] 0 rfl
  refine h.cast rfl ?_
  simp only [List.zipWith_cons_cons, List.zipWith_nil_left, ← Multiset.cons_coe,
    Multiset.coe_nil, add_zero, decodeNet, decomp_πx, List.map_cons, List.map_nil, mux, muxStar]
  ms

/-- **The current code against the old decoder decodes `π` into `πx`** (page 89): it reduces to a
net `Equiv` to the exchanged package on the free port, which is not `Equiv` to `π` there
(`not_equiv_π_πx`). -/
theorem decode_old : ∃ M, StepsE system {s(code 3 π, oldDecoder 2 13)} M ∧
    Equiv M {s(var 2, πx)} ∧ ¬ Equiv M {s(var 2, π)} := by
  have hlin : Net.Linear (decodeNet (decomp 3 πx).cells 13 14 {s((decomp 3 πx).τ, var 2)}) :=
    Net.linear_of_forall_mem (by decide)
  have hb : Net.Below 15 (decodeNet (decomp 3 πx).cells 13 14 {s((decomp 3 πx).τ, var 2)}) := by
    unfold Net.Below; decide
  obtain ⟨M, hS, hE⟩ := decode_cells _ 13 14 15 _ hlin hb
  have E := decomp_equiv πx 3 (var 2) 0 (Net.linear_of_forall_mem (by decide))
    (by unfold Net.Below; decide)
  have hM : Equiv M {s(var 2, πx)} := by
    refine hE.trans ((Equiv.of_eq ?_).trans E.symm)
    rw [decomp_πx]
    simp only [Decomp.net, List.map_cons, List.map_nil, ← Multiset.cons_coe, Multiset.coe_nil,
      add_zero]
    rw [Sym2.eq_swap (a := mkCon (var 5) (var 10))]
    ms
  exact ⟨M, old_first_stage.stepsE.trans hS, hM,
    fun h => not_equiv_π_πx (h.symm.trans hM)⟩

end INet.Comb.CodeFig8Review
