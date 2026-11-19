import InteractionCombinators.NetLemmas
import InteractionCombinators.Lafont.PlugsExpand
import InteractionCombinators.Lafont.PlugsNetTr

/-!
# Review of `PlugsExpand.lean` and `PlugsNetTr.lean` (pages 80, 85–86)

Lafont 1997, page 85: the right member of a rule is `φ_{i,j}` and `ψ_{i,j}`, two reduced nets,
whose `k` lower wires are joined by the permutation `σ_{i,j}`; page 80: the translation of a net.

## The linearity of the sides

In the figure of page 85 the box `φ_{i,j}` has its `n_i` ports above and `k` distinct wires below,
each going into `σ_{i,j}`. Each lower wire is a free port of the net `φ_{i,j}`, so it occurs exactly
once in it, as each internal wire occurs twice: this is `Rule.Linear` of the side, with the middle
wires `.inr (.inl l)` as free ports. `Rule.plug_rename` assumes this of `φ` and `ψ`, which is
the paper's reading, not a weakening. `badSide` (a middle wire that occurs twice) is not a net in
the sense of page 85 as a side: `badSide_not_linear` checks that it is `Net.Linear` and not
`Rule.Linear`. In `plugs_expand` the hypotheses come from `RecursionFreeData.linear`, so that
statement needs nothing but `D` and the rule.

## The checks

* `twistSide`, `twistSide'`: a side with one internal wire `w` (`a₀ = con(m₀, w)`,
  `a₁ = con(w, m₁)`), and the same side written with the internal wires `w₀`, `w₁` and the extra
  equation `w₀ = w₁`. `twistSide'` is `twistSide` up to one wire substitution and the
  renaming `ι₁ = fun _ => 1`, which is neither the identity nor onto.
* `twist_plugIota`: `plugIota ι₁ id` fixes the middle wires `0`, `1` and sends the wire `2` of
  `φ` to `3`, the last wire of the `φ'` block.
* `twist_plug'_net`: the plug of `twistSide'` and `idSide` through `σ = swap 0 1`, computed: `ψ`
  joins `b₀` to the middle wire `σ⁻¹ 0 = 1`, and `b₁` to `0`.
* `twistDec_plugs`: `⟨2, twistSide, idSide, swap 0 1⟩` plugs `twistRule`
  (`a₀ = con(b₁, w)`, `a₁ = con(w, b₀)`), by two wire substitutions.
* `twist_of_expand`: `Plugs.of_expand` applies with `σ = swap 0 1`, the non-trivial `ι₁` and the
  non-trivial `Equiv`, and gives that `⟨2, twistSide', idSide, swap 0 1⟩` plugs `twistRule`.
* `twist_inst_of_equiv_rename`: `NetTr.inst_of_equiv_rename` for the identity translation, with
  `P = twistSide'`, `r = twistSide` and `ι = fun _ => 1`: the instance of `r` it gives uses the
  name `h 1 = 21` of `P` for the wire of `r`, and the name `20` disappears.
-/

namespace INet.Comb.PlugsReview

open Term Rule DecompositionReview

/-! ### The linearity of the sides -/

/-- `badSide` (`w = m`, `w = m`) is a linear net but not a linear side: its middle wire occurs
twice, which a net with `m` as a free port cannot do (page 85). -/
theorem badSide_not_linear : Net.Linear badSide.net ∧ ¬ badSide.Linear := by
  refine ⟨by unfold Net.Linear; decide, fun h => ?_⟩
  have := h.right 0
  revert this
  decide

/-! ### A side with a non-trivial renaming, and `σ = swap 0 1` -/

/-- `a₀ = con(m₀, w)`, `a₁ = con(w, m₁)`. -/
def twistSide : Rule sig 2 2 :=
  ⟨1, s(pl 0, mkCon (pr 0) (pw 0)) ::ₘ {s(pl 1, mkCon (pw 0) (pr 1))}⟩

/-- `a₀ = con(m₀, w₀)`, `w₀ = w₁`, `a₁ = con(w₁, m₁)`. -/
def twistSide' : Rule sig 2 2 :=
  ⟨2, s(pw 0, pw 1) ::ₘ s(pl 0, mkCon (pr 0) (pw 0)) ::ₘ {s(pl 1, mkCon (pw 1) (pr 1))}⟩

/-- The rule plugged by `twistSide`, `idSide`, `swap 0 1`: `a₀ = con(b₁, w)`, `a₁ = con(w, b₀)`. -/
def twistRule : Rule sig 2 2 :=
  ⟨1, s(pl 0, mkCon (pr 1) (pw 0)) ::ₘ {s(pl 1, mkCon (pw 0) (pr 0))}⟩

/-- The renaming of the internal wire of `twistSide` into `twistSide'`: `w ↦ w₁`. -/
def ι₁ : Fin 1 → Fin 2 := fun _ => 1

theorem ι₁_injective : Function.Injective ι₁ := fun x y _ => Subsingleton.elim (α := Fin 1) x y

theorem twistSide_linear : twistSide.Linear := ⟨by decide, by decide, by decide⟩

theorem twistSide'_linear : twistSide'.Linear := ⟨by decide, by decide, by decide⟩

theorem twistRule_linear : twistRule.Linear := ⟨by decide, by decide, by decide⟩

/-- `twistSide'` is `twistSide` renamed by `ι₁`, up to the wire substitution of `w₀`. -/
theorem twist_equiv : Equiv twistSide'.net
    (twistSide.net.bind fun x => var (Sum.map id (Sum.map id ι₁) x)) := by
  have h := equiv_wire_of_eq (ν := Fin 2 ⊕ Fin 2 ⊕ Fin 2)
    (N := (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2) from twistSide'.net))
    (M := s(pl 0, mkCon (pr 0) (pw 1)) ::ₘ {s(pl 1, mkCon (pw 1) (pr 1))})
    (.inr (.inr 0)) (pw 1) (pl 0) (mkCon (pr 0) (pw 0)) {s(pl 1, mkCon (pw 1) (pr 1))}
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  refine h.trans (Equiv.of_eq ?_)
  show (s(pl 0, mkCon (pr 0) (pw 1)) ::ₘ {s(pl 1, mkCon (pw 1) (pr 1))} :
    Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2)) =
    (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 1) from twistSide.net).bind
      fun x => var (Sum.map id (Sum.map id ι₁) x)
  decide

/-- `plugIota ι₁ id` fixes the two middle wires and sends the wire `2` (the wire of `twistSide`) to
`3` (the wire `w₁` of `twistSide'`). -/
theorem twist_plugIota :
    (List.finRange 3).map (fun x => (plugIota (k := 2) ι₁ (id : Fin 0 → Fin 0) x).val) =
      [0, 1, 3] := by decide +kernel

/-- The plug of `twistSide'` and `idSide` through `swap 0 1`: the middle wires are `0`, `1`, the
wires of `twistSide'` are `2`, `3`; `b₀` meets the middle wire `σ⁻¹ 0 = 1`, `b₁` meets `0`. -/
theorem twist_plug'_net :
    (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 4) from (Rule.plug twistSide' idSide (Equiv.swap 0 1)).net) =
      s(pw 2, pw 3) ::ₘ s(pl 0, mkCon (pw 0) (pw 2)) ::ₘ s(pl 1, mkCon (pw 3) (pw 1)) ::ₘ
        s(pr 0, pw 1) ::ₘ {s(pr 1, pw 0)} := by decide

/-- `⟨2, twistSide, idSide, swap 0 1⟩` plugs `twistRule` (page 85), by two wire substitutions. -/
theorem twistDec_plugs : Decomposition.Plugs ⟨2, twistSide, idSide, Equiv.swap 0 1⟩ twistRule := by
  refine ⟨(fun _ => (2 : Fin 3) : Fin 1 → Fin 3),
    fun x y _ => Subsingleton.elim (α := Fin 1) x y, ?_⟩
  have h₁ := equiv_wire_of_eq (ν := Fin 2 ⊕ Fin 2 ⊕ Fin 3)
    (N := (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 3) from
      (Rule.plug twistSide idSide (Equiv.swap 0 1)).net))
    (M := s(pl 1, mkCon (pw 2) (pr 0)) ::ₘ s(pl 0, mkCon (pw 0) (pw 2)) ::ₘ {s(pr 1, pw 0)})
    (.inr (.inr 1)) (pr 0) (pl 1) (mkCon (pw 2) (pw 1))
    (s(pl 0, mkCon (pw 0) (pw 2)) ::ₘ {s(pr 1, pw 0)})
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have h₂ := equiv_wire_of_eq (ν := Fin 2 ⊕ Fin 2 ⊕ Fin 3)
    (N := s(pl 1, mkCon (pw 2) (pr 0)) ::ₘ s(pl 0, mkCon (pw 0) (pw 2)) ::ₘ {s(pr 1, pw 0)})
    (M := s(pl 0, mkCon (pr 1) (pw 2)) ::ₘ {s(pl 1, mkCon (pw 2) (pr 0))})
    (.inr (.inr 0)) (pr 1) (pl 0) (mkCon (pw 0) (pw 2)) {s(pl 1, mkCon (pw 2) (pr 0))}
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  refine h₁.trans (h₂.trans (Equiv.of_eq ?_))
  show (s(pl 0, mkCon (pr 1) (pw 2)) ::ₘ {s(pl 1, mkCon (pw 2) (pr 0))} :
    Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 3)) =
    (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 1) from twistRule.net).bind
      fun x => var (Sum.map id (Sum.map id (fun _ => (2 : Fin 3) : Fin 1 → Fin 3)) x)
  decide

/-- **`Plugs.of_expand` with `σ = swap 0 1` and a non-trivial renaming** (pages 85–86): replacing
`twistSide` by `twistSide'` (one more internal wire, renaming `ι₁ = fun _ => 1`, one wire
substitution) keeps a decomposition of `twistRule`. -/
theorem twist_of_expand :
    Decomposition.Plugs ⟨2, twistSide', idSide, Equiv.swap 0 1⟩ twistRule :=
  Decomposition.Plugs.of_expand (D := ⟨2, twistSide, idSide, Equiv.swap 0 1⟩) twistDec_plugs
    twistSide_linear idSide_linear ι₁_injective (ι₂ := id) Function.injective_id twist_equiv
    (Equiv.of_eq (Net.bind_sumMap_id _).symm)

/-- `Plugs.netTr_inst_of_sides` applies to the decomposition of `twist_of_expand`: its hypotheses
are those of `RecursionFreeData` (`Plugs`, linear sides). -/
theorem twist_netTr_inst_of_sides (xs ys : Fin 2 → ℕ)
    (h : Fin (Rule.plug twistSide' idSide (Equiv.swap 0 1)).internal → ℕ) {N' : Net sig ℕ}
    (hN : (Translation.id sig).NetTr ((Rule.plug twistSide' idSide (Equiv.swap 0 1)).inst
      (fun i => .var (xs i)) (fun j => .var (ys j)) h) N') :
    ∃ (h' : Fin twistRule.internal → ℕ) (N'' : Net sig ℕ),
      (Translation.id sig).NetTr (twistRule.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h')
        N'' ∧ Equiv N' N'' :=
  Decomposition.Plugs.netTr_inst_of_sides (D := ⟨2, twistSide', idSide, Equiv.swap 0 1⟩)
    twist_of_expand twistSide'_linear idSide_linear xs ys h hN

/-! ### `NetTr.inst_of_equiv_rename` with a non-trivial `ι` -/

/-- The instance of `twistSide'` with ports `10, 11`, `12, 13` and internal wires `20, 21`. -/
theorem twist'_inst :
    twistSide'.inst (fun i => .var (![10, 11] i)) (fun j => .var (![12, 13] j)) ![20, 21] =
      s(var 20, var 21) ::ₘ s(var 10, mkCon (var 12) (var 20)) ::ₘ
        {s(var 11, mkCon (var 21) (var 13))} := by
  decide

/-- **`NetTr.inst_of_equiv_rename` with `ι = fun _ => 1`** (pages 80 and 85): for the identity
translation, the instance of `twistSide'` above is its own translation, and the theorem gives a
translation of an instance of `twistSide`. That instance is the one with the wire named
`h (ι 0) = 21`: `10 = con(12, 21)`, `11 = con(21, 13)`, and the translation `N'` of
`twistSide'` is equivalent to it. -/
theorem twist_inst_of_equiv_rename :
    ∃ (h' : Fin twistSide.internal → ℕ) (N'' : Net sig ℕ),
      (Translation.id sig).NetTr
        (twistSide.inst (fun i => .var (![10, 11] i)) (fun j => .var (![12, 13] j)) h') N'' ∧
      Equiv (twistSide'.inst (fun i => .var (![10, 11] i)) (fun j => .var (![12, 13] j))
        ![20, 21]) N'' := by
  have hlin : Net.Linear (twistSide'.inst (fun i => .var (![10, 11] i))
      (fun j => .var (![12, 13] j)) ![20, 21]) := by
    rw [twist'_inst]
    apply Net.linear_of_forall_mem
    decide
  exact Translation.NetTr.inst_of_equiv_rename twistSide' twistSide twistSide'_linear ι₁
    twist_equiv _ _ _ ⟨Multiset.rel_refl_of_refl_on fun e _ => Translation.eqTr_id e, hlin⟩

/-- The instance of `twistSide` that `NetTr.inst_of_equiv_rename` uses, `h ∘ ι₁`, names the wire
of `twistSide` `21`, the name of `w₁` in the instance of `twistSide'`. -/
theorem twist_inst_comp :
    twistSide.inst (fun i => .var (![10, 11] i)) (fun j => .var (![12, 13] j))
        ((![20, 21] : Fin 2 → ℕ) ∘ ι₁) =
      s(var 10, mkCon (var 12) (var 21)) ::ₘ {s(var 11, mkCon (var 21) (var 13))} := by
  decide

end INet.Comb.PlugsReview
