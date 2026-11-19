import InteractionCombinators.Universality.Codes.PackageDecomp
import InteractionCombinators.Universality.Codes.Copier

/-!
# Lafont, "Interaction Combinators" (1997): the code `!π` and the decoder `D`

Page 88, Section 2.6, Fig. 8. A package `π` with `n` `dup` cells is decomposed (`decomp`,
`PackageDecomp.lean`) into a `dup`-free net `π'` and the `n` cells. The code `!π` keeps `π'` and
replaces the cells by multiplexors: an `M_4` at the root, whose four auxiliary ports carry, from
left to right as drawn in Fig. 8,

1. an `M_n` whose auxiliary ports are the principal ports `x_i` of the cut cells;
2. an `M_n*` whose auxiliary ports are the trees `l_i` on auxiliary port 0 of the cells;
3. an `M_n*` whose auxiliary ports are the trees `r_i` on auxiliary port 1 of the cells;
4. the root tree `τ` of `π'`.

How this is read from the figure. The ports of a cell are numbered clockwise (page 71), so a cell
drawn pointing up has its first auxiliary port (Lean port 0, Lafont's port 1) on the right, as in
the numbered picture of page 82; `M_4` points down, so its ports are listed from left to right, and
an `M_n*` pointing up lists its ports from left to right too (`muxStar`). In the decomposition above
Fig. 8 the `dup` cells point up, and the wires cross so that the left group of ports of `π'`
receives the drawn left ports of the cells (Lean port 1, `r_i`) and the right group their drawn
right ports (Lean port 0, `l_i`). In Fig. 8 the left `M_n*` sits on the left group and the right one
on the right group; the second wire of `M_4` runs to the right `M_n*` (the trees `l_i`) and the
third to the left one (the trees `r_i`). The decoder `D` is an `M_4*` whose first auxiliary port
carries a `dup` cell pointing up; the inner loop joins its drawn right port (port 0) to the second
port of `M_4*`, the outer loop its drawn left port (port 1) to the third; the fourth is the free
port. In Fig. 9, `M_4` meets `M_4*`, so `M_n` meets the `dup` cell, the `M_n*` of the `l_i` its
port 0, the `M_n*` of the `r_i` its port 1, and `τ` comes out on the free port: `code_decoder`
checks this first stage of Fig. 9.

* `code` — `!π`, from `decomp k π`.
* `decoder` — `D`, with free port `w` and internal wires `k`, `k + 1`.
* `code_dupFree`, `code_isPackage`, `vars_decoder`, `decoder_free` — the structural properties.
-/

namespace INet.Comb

open Term

/-! ## Multiplexors without `dup` -/

/-- `M_n` is built from `con` and `era` only. -/
theorem dupFree_mux : ∀ ts : List (Term sig ℕ), (∀ t ∈ ts, DupFree t) → DupFree (mux ts)
  | [], _ => trivial
  | [t], h => h t (by simp)
  | t :: t' :: ts, h => by
    rw [mux, dupFree_mkCon]
    exact ⟨h t (by simp), dupFree_mux (t' :: ts) fun s hs => h s (List.mem_cons_of_mem _ hs)⟩

/-- `M_n*` is built from `con` and `era` only. -/
theorem dupFree_muxStar : ∀ us : List (Term sig ℕ), (∀ u ∈ us, DupFree u) → DupFree (muxStar us)
  | [], _ => trivial
  | [u], h => h u (by simp)
  | u :: u' :: us, h => by
    rw [muxStar, dupFree_mkCon]
    exact ⟨dupFree_muxStar (u' :: us) fun s hs => h s (List.mem_cons_of_mem _ hs), h u (by simp)⟩

/-! ## The code -/

/-- The code built from a decomposition (Fig. 8, page 88): `M_4` of `M_n` on the cut names,
`M_n*` on the trees on auxiliary port 0 of the cells, `M_n*` on the trees on auxiliary port 1, and
the root tree `τ`. -/
def Decomp.code (D : Decomp) : Term sig ℕ :=
  mux [mux (D.cells.map fun c => var c.1), muxStar (D.cells.map fun c => c.2.1),
    muxStar (D.cells.map fun c => c.2.2), D.τ]

/-- The code `!π` of a package `π` (Lafont, page 88, Fig. 8), with the new names of the
decomposition numbered from `k`. Its root is the principal port of an `M_4` whose four auxiliary
ports carry, in this order: an `M_n` on the principal ports `x_i` of the `n` `dup` cells of `π`; an
`M_n*` on the trees `l_i` on their auxiliary port 0; an `M_n*` on the trees `r_i` on their auxiliary
port 1; and the root tree `τ` of `π'`. The `i`-th auxiliary port of each multiplexor belongs to the `i`-th cell of
`(decomp k π).cells`. -/
def code (k : ℕ) (π : Term sig ℕ) : Term sig ℕ := (decomp k π).code

/-- The decoder `D` (Lafont, page 88, Fig. 8), a principal net of arity 1: an `M_4*` whose four
auxiliary ports carry, in this order, a `dup` cell with auxiliary port 0 on `k` and auxiliary port 1
on `k + 1`, the wire `k`, the wire `k + 1`, and the free port `w`. The `dup` cell points up in
Fig. 8, so its port 0 is drawn on the right: the inner loop joins it to the second port of `M_4*`,
the outer loop joins port 1 to the third. -/
def decoder (w k : ℕ) : Term sig ℕ :=
  muxStar [mkDup (var k) (var (k + 1)), var k, var (k + 1), var w]

/-- The names of the code are the cut names (on `M_n`) and the names of `π'`. -/
theorem Decomp.vars_code (D : Decomp) : D.code.vars = D.ports + D.τ.vars + D.auxVars := by
  have h1 : ((D.cells.map fun c => (var c.1 : Term sig ℕ)).map Term.vars).sum = D.ports := by
    simp only [Decomp.ports, List.map_map]
    induction D.cells with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Function.comp, vars_var]
      rfl
  have h2 : ((D.cells.map fun c => c.2.1).map Term.vars).sum +
      ((D.cells.map fun c => c.2.2).map Term.vars).sum = D.auxVars := by
    simp only [Decomp.auxVars, List.map_map]
    induction D.cells with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp] at ih ⊢
      rw [← ih]
      abel
  simp only [Decomp.code, mux, vars_mkCon, vars_mux, vars_muxStar, h1]
  rw [← h2]
  abel

/-- "Clearly, `!π` contains no `δ`" (page 88): the code is built without `dup`. -/
theorem code_dupFree (k : ℕ) (π : Term sig ℕ) : DupFree (code k π) := by
  obtain ⟨hτ, hc⟩ := decomp_dupFree π k
  refine dupFree_mux _ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro t (rfl | rfl | rfl | rfl)
  · exact dupFree_mux _ fun t ht => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 ht
      trivial
  · exact dupFree_muxStar _ fun t ht => by
      obtain ⟨c, hc', rfl⟩ := List.mem_map.1 ht
      exact (hc c hc').1
  · exact dupFree_muxStar _ fun t ht => by
      obtain ⟨c, hc', rfl⟩ := List.mem_map.1 ht
      exact (hc c hc').2
  · exact hτ

/-- The names of `!π` are the names of `π` and the `n` cut names, each cut name twice: once on `M_n`
and once in `π'` (page 88). -/
theorem vars_code (k : ℕ) (π : Term sig ℕ) :
    (code k π).vars = π.vars + (decomp k π).ports + (decomp k π).ports := by
  have h := decomp_vars π k
  simp only [Decomp.vars'] at h
  rw [code, Decomp.vars_code, add_assoc _ (decomp k π).τ.vars, h]
  abel

/-- The code of a package is a package (page 88: "another package `!π`"). The new names must be
above the names of `π`. -/
theorem code_isPackage (k : ℕ) (π : Term sig ℕ) (hπ : π.IsPackage) (hb : π.Below k) :
    (code k π).IsPackage := by
  obtain ⟨hnd, hr, -⟩ := decomp_ports π k
  intro y hy
  rw [vars_code] at hy ⊢
  rw [Multiset.count_add, Multiset.count_add]
  rcases Multiset.mem_add.1 hy with hy | hy
  · rcases Multiset.mem_add.1 hy with hy | hy
    · have hn : y ∉ (decomp k π).ports := fun h => by
        have := (hr y h).1; have := hb y hy; omega
      rw [hπ y hy, Multiset.count_eq_zero.2 hn]
    · have hn : y ∉ π.vars := fun h => by
        have := (hr y hy).1; have := hb y h; omega
      rw [Multiset.count_eq_zero.2 hn, Multiset.count_eq_one_of_mem hnd hy]
  · have hn : y ∉ π.vars := fun h => by
      have := (hr y hy).1; have := hb y h; omega
    rw [Multiset.count_eq_zero.2 hn, Multiset.count_eq_one_of_mem hnd hy]

/-- The code of a package, copied by `C_n` (page 88): `n` copies of `!π`, each renamed injectively
on its names. This is `copier_package`, since `!π` is a package without `dup`. -/
theorem copier_code (k : ℕ) (π : Term sig ℕ) (hπ : π.IsPackage) (hb : π.Below k)
    (us : List (Term sig ℕ)) (Δ : CNet) (hlin : Net.Linear (s(copier us, code k π) ::ₘ Δ)) :
    ∃ (fs : List (ℕ → ℕ)) (N : CNet), fs.length = us.length ∧
      (∀ f ∈ fs, Set.InjOn f {x | x ∈ (code k π).vars}) ∧
      StepsE system (s(copier us, code k π) ::ₘ Δ) N ∧
      Equiv N ((List.zipWith (fun u f => s(u, (code k π).bind (fun x => var (f x)))) us fs : CNet)
        + Δ) :=
  copier_package _ (code_isPackage k π hπ hb) (code_dupFree k π) us Δ hlin

/-! ## The decoder -/

/-- The names of the decoder (page 88, Fig. 8): the free port `w` once, and the two wires of the
loop, `k` and `k + 1`, twice each. -/
theorem vars_decoder (w k : ℕ) :
    (decoder w k : Term sig ℕ).vars = {w, k, k, k + 1, k + 1} := by
  simp only [decoder, muxStar, vars_mkCon, vars_mkDup, vars_var]
  simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
  abel

/-- The decoder is a principal net of arity 1 (page 88): if its free port `w` is not one of the
names `k`, `k + 1` of the loop, then `w` occurs once and every other name of the decoder twice. -/
theorem decoder_free (w k : ℕ) (hw : w ≠ k) (hw' : w ≠ k + 1) :
    (decoder w k : Term sig ℕ).vars.count w = 1 ∧
      ∀ y ∈ (decoder w k : Term sig ℕ).vars, y ≠ w → (decoder w k : Term sig ℕ).vars.count y = 2 := by
  rw [vars_decoder]
  refine ⟨?_, fun y hy hyw => ?_⟩
  · simp only [Multiset.insert_eq_cons]
    rw [Multiset.count_cons_self, Multiset.count_cons_of_ne hw, Multiset.count_cons_of_ne hw,
      Multiset.count_cons_of_ne hw', Multiset.count_singleton]
    simp [hw']
  · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hy
    simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hyw
    all_goals simp [hyw]

/-- The first stage of Fig. 9 (page 89): the code against the decoder, `M_4` against `M_4*`,
reduces to four wires. `M_n` meets the `dup` cell of the decoder, the `M_n*` of the trees `l_i`
meets its auxiliary port 0, on `k`, the `M_n*` of the trees `r_i` its auxiliary port 1, on `k + 1`,
and the root tree `τ` of `π'` comes out on the free port `w`. -/
theorem code_decoder (k' : ℕ) (π : Term sig ℕ) (w k : ℕ) (Δ : CNet) :
    Red (s(code k' π, decoder w k) ::ₘ Δ)
      (s(mux ((decomp k' π).cells.map fun c => var c.1), mkDup (var k) (var (k + 1))) ::ₘ
        s(muxStar ((decomp k' π).cells.map fun c => c.2.1), var k) ::ₘ
        s(muxStar ((decomp k' π).cells.map fun c => c.2.2), var (k + 1)) ::ₘ
        s((decomp k' π).τ, var w) ::ₘ Δ) := by
  have h := mux_muxStar [mux ((decomp k' π).cells.map fun c => var c.1),
    muxStar ((decomp k' π).cells.map fun c => c.2.1),
    muxStar ((decomp k' π).cells.map fun c => c.2.2), (decomp k' π).τ]
    [mkDup (var k) (var (k + 1)), var k, var (k + 1), var w] Δ rfl
  simp only [List.zipWith_cons_cons, List.zipWith_nil_left, ← Multiset.cons_coe,
    Multiset.coe_nil, Multiset.cons_add, zero_add] at h
  exact h

/-! ## Checks -/

/-- A package without `dup` (`n = 0`): `M_0 = ε`, so the code is `M_4` of `ε, ε, ε, π`. -/
example : code 1 (mkCon (var 0) (var 0) : Term sig ℕ) =
    mux [mkEra, mkEra, mkEra, mkCon (var 0) (var 0)] := rfl

/-- The code of a package without `dup` is `M_4` of `ε, ε, ε, π`, for every such package. -/
theorem code_of_dupFree (k : ℕ) (π : Term sig ℕ) (hd : DupFree π) :
    code k π = mux [mkEra, mkEra, mkEra, π] := by
  obtain ⟨h1, h2⟩ := decomp_of_dupFree π hd k
  simp [code, Decomp.code, h1, h2, mux, muxStar]

/-- A package with one `dup`, `dup(con(0, 1), con(0, 1))`, new names from `2`: the cell is cut at
`2`, `τ = 2`, `l₀ = r₀ = con(0, 1)`, and `M_1` is a wire, so the code is `M_4` of
`2, con(0, 1), con(0, 1), 2`. -/
example : code 2 (mkDup (mkCon (var 0) (var 1)) (mkCon (var 0) (var 1)) : Term sig ℕ) =
    mux [var 2, mkCon (var 0) (var 1), mkCon (var 0) (var 1), var 2] := rfl

/-- The same package, with distinct auxiliary trees `dup(con(0, 1), con(1, 0))`: the tree
`con(0, 1)` on port 0 sits on the second port of `M_4`, the tree `con(1, 0)` on port 1 on the
third. -/
example : code 2 (mkDup (mkCon (var 0) (var 1)) (mkCon (var 1) (var 0)) : Term sig ℕ) =
    mux [var 2, mkCon (var 0) (var 1), mkCon (var 1) (var 0), var 2] := rfl

/-- Two nested `dup` cells, `dup(dup(0, 1), con(0, 1))`, new names from `3`: cells cut at `3` and
`6` (see `PackageDecomp.lean`), so `M_2` on `3, 6`, `M_2*` on the trees on port 0, `6, 0`, `M_2*`
on the trees on port 1, `con(0, 1), 1`, and `τ = 3`. -/
example : code 3 (mkDup (mkDup (var 0) (var 1)) (mkCon (var 0) (var 1)) : Term sig ℕ) =
    mux [mux [var 3, var 6], muxStar [var 6, var 0], muxStar [mkCon (var 0) (var 1), var 1],
      var 3] := rfl

/-- The decoder with free port `0` and loop `1`, `2`, written out. -/
example : (decoder 0 1 : Term sig ℕ) =
    mkCon (mkCon (mkCon (var 0) (var 2)) (var 1)) (mkDup (var 1) (var 2)) := rfl

end INet.Comb
