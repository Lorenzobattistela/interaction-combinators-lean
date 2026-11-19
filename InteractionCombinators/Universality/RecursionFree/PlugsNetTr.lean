import InteractionCombinators.Universality.RecursionFree.RecursionFree
import InteractionCombinators.Reduction.RuleInstances
import InteractionCombinators.Text.NetTrWire

/-!
# A translation of an instance of `Rule.plug φ ψ σ` is a translation of an instance of `r`

Lafont 1997, page 85: the right-hand side of the rule `r` for `α_i`, `α_j` is the net `φ_{i,j}`
plugged to `ψ_{i,j}` through `σ_{i,j}`; page 80: a translation of interaction systems asks that
the translations of the two cells reduce to a translation of the right-hand side.

`mux_gamma_mux_gamma_netTr` (`PlugTr.lean`) ends Fig. 7 with a translation of an instance of
`Rule.plug φ ψ σ`, while `Translation.Compatible` asks for a translation of an instance of `r`.
`Decomposition.Plugs` links the two: an injective renaming `ι` of the internal wires of `r` and an
`Equiv` of the two right-hand sides. This file moves the translation along that link.

* `Rule.equiv_inst_of_equiv_rename` — equivalent right-hand sides give equivalent instances.
* `Translation.NetTr.inst_of_equiv_rename` — the `NetTr` moves along the `Equiv`.
* `Decomposition.Plugs.netTr_inst` — the same, for a decomposition that plugs into `r`.
-/

namespace INet

variable {S S' : Signature}

open Term

namespace Rule

variable {a b : ℕ}

/-- **Equivalent right-hand sides give equivalent instances** (Lafont 1997, pages 80 and 85: a
right-hand side is a graph, plugged into the net by its ports). If the net of `P` is equivalent to
the net of `r` with its internal wires renamed by `ι`, then the instance of `P` with names `xs`,
`ys` on the ports and `h` on the internal wires is equivalent to the instance of `r` with the same
ports and `h ∘ ι` on the internal wires, provided the instance of `P` is linear. -/
theorem equiv_inst_of_equiv_rename (P r : Rule S a b) (hP : P.Linear)
    (ι : Fin r.internal → Fin P.internal)
    (hE : Equiv P.net (r.net.bind fun x => var (Sum.map id (Sum.map id ι) x)))
    (xs : Fin a → ℕ) (ys : Fin b → ℕ) (h : Fin P.internal → ℕ)
    (hlin : (P.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h).Linear) :
    Equiv (P.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h)
      (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) (h ∘ ι)) := by
  have hL : ∀ y, ∑ i, (Term.var (S := S) (xs i)).vars.count y +
      ∑ j, (Term.var (S := S) (ys j)).vars.count y +
      2 * (∑ w, if y = h w then 1 else 0) + (0 : Net S ℕ).vars.count y ≤ 2 := by
    intro y
    have := hlin y
    rw [count_vars_inst P hP] at this
    simpa using this
  have E := equiv_bind_args hE (portShape_net P hP) (fun i => .var (xs i))
    (fun j => .var (ys j)) h 0 hL
  simp only [add_zero] at E
  refine E.trans (Equiv.of_eq ?_)
  rw [Net.bind_bind]
  show r.net.bind _ = r.net.bind _
  congr 1
  funext x
  rcases x with i | j | w <;> rfl

end Rule

namespace Translation

variable {Φ : Translation S S'}

/-- **A translation moves along equivalent right-hand sides** (Lafont 1997, pages 80 and 85). If
the net of `P` is equivalent to the net of `r` with its internal wires renamed by an injective `ι`,
then a translation `N'` of an instance of `P` is equivalent to a translation of an instance of `r`
with the same names on the ports. -/
theorem NetTr.inst_of_equiv_rename {a b : ℕ} (P r : Rule S a b) (hP : P.Linear)
    (ι : Fin r.internal → Fin P.internal)
    (hE : Equiv P.net (r.net.bind fun x => var (Sum.map id (Sum.map id ι) x)))
    (xs : Fin a → ℕ) (ys : Fin b → ℕ) (h : Fin P.internal → ℕ) {N' : Net S' ℕ}
    (hN : Φ.NetTr (P.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N') :
    ∃ (h' : Fin r.internal → ℕ) (N'' : Net S' ℕ),
      Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h') N'' ∧ Equiv N' N'' := by
  have E := Rule.equiv_inst_of_equiv_rename P r hP ι hE xs ys h hN.linear_source
  obtain ⟨N'', hN'', e⟩ := hN.of_equiv E
  exact ⟨h ∘ ι, N'', hN'', e⟩

end Translation

namespace Decomposition

variable {a b : ℕ}

/-- **A translation of an instance of the plugged sides is a translation of an instance of the
rule** (Lafont 1997, page 85: the right-hand side of `r` is `φ` plugged to `ψ` through `σ`; page
80: the translation of interaction systems). If `D` plugs into `r` and the plugged rule is linear,
a translation `N'` of an instance of `Rule.plug D.φ D.ψ D.σ` is equivalent to a translation of an
instance of `r` with the same names on the ports. -/
theorem Plugs.netTr_inst {D : Decomposition S a b} {r : Rule S a b} (hD : D.Plugs r)
    (hP : (Rule.plug D.φ D.ψ D.σ).Linear) {Φ : Translation S S'} (xs : Fin a → ℕ)
    (ys : Fin b → ℕ) (h : Fin (Rule.plug D.φ D.ψ D.σ).internal → ℕ) {N' : Net S' ℕ}
    (hN : Φ.NetTr ((Rule.plug D.φ D.ψ D.σ).inst (fun i => .var (xs i)) (fun j => .var (ys j)) h)
      N') :
    ∃ (h' : Fin r.internal → ℕ) (N'' : Net S' ℕ),
      Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h') N'' ∧ Equiv N' N'' := by
  obtain ⟨ι, -, hE⟩ := hD
  exact Translation.NetTr.inst_of_equiv_rename _ r hP ι hE xs ys h hN

/-- `Plugs.netTr_inst` with the linearity of the plugged rule obtained from that of the two sides
(`Rule.plug_linear`), as `System.RecursionFreeData.linear` supplies it (Lafont 1997, pages 85 and
80). -/
theorem Plugs.netTr_inst_of_sides {D : Decomposition S a b} {r : Rule S a b} (hD : D.Plugs r)
    (hφ : D.φ.Linear) (hψ : D.ψ.Linear) {Φ : Translation S S'} (xs : Fin a → ℕ)
    (ys : Fin b → ℕ) (h : Fin (Rule.plug D.φ D.ψ D.σ).internal → ℕ) {N' : Net S' ℕ}
    (hN : Φ.NetTr ((Rule.plug D.φ D.ψ D.σ).inst (fun i => .var (xs i)) (fun j => .var (ys j)) h)
      N') :
    ∃ (h' : Fin r.internal → ℕ) (N'' : Net S' ℕ),
      Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h') N'' ∧ Equiv N' N'' :=
  hD.netTr_inst (Rule.plug_linear D.σ hφ hψ) xs ys h hN

end Decomposition

end INet
