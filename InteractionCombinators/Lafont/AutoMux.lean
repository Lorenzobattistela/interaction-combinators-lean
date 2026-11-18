import InteractionCombinators.Lafont.Basic

/-!
# Lafont, "Interaction Combinators" (1997): the autodual multiplexor

* `autoMux` — the autodual multiplexor `T_n` of Fig. 5 (page 83), built with `dup`.
* `autoMux_autoMux` — its property (page 83): two copies of `T_n` plugged by their roots reduce
  to `n` wires, joining port `i` of one to port `i` of the other.
* `vars_mux`, `vars_muxStar`, `vars_autoMux` — the names of the three multiplexors are the names
  of the trees plugged into their auxiliary ports.
-/

namespace INet.Comb

open Term

/-- The autodual multiplexor `T_n` (Lafont, Fig. 5, page 83), applied to the trees plugged into
its `n` auxiliary ports. `T_0` is `era`, `T_1` is a wire, and `T_{n+2}` is a `dup` whose right
auxiliary port carries `T_{n+1}`, as `M_n` is nested in Fig. 4. -/
def autoMux : List (Term sig ℕ) → Term sig ℕ
  | [] => mkEra
  | [t] => t
  | t :: t' :: ts => mkDup t (autoMux (t' :: ts))

/-- The property of the autodual multiplexor (Lafont, page 83, picture above Fig. 5): two copies
of `T_n` plugged by their roots reduce to `n` wires, here the equations between the trees plugged
into matching auxiliary ports. Only the rules `δδ` and `εε` are used. -/
theorem autoMux_autoMux : ∀ (ts us : List (Term sig ℕ)) (Δ : CNet), ts.length = us.length →
    Red (s(autoMux ts, autoMux us) ::ₘ Δ)
      ((List.zipWith (fun t u => s(t, u)) ts us : CNet) + Δ)
  | [], [], Δ, _ => by simpa [autoMux] using Steps.single (step_era_era Δ)
  | [t], [u], Δ, _ => by simpa [autoMux] using Relation.ReflTransGen.refl
  | t :: t' :: ts, u :: u' :: us, Δ, h => by
    have hlen : (t' :: ts).length = (u' :: us).length := by simpa using h
    refine Relation.ReflTransGen.head
      (step_dup_dup t (autoMux (t' :: ts)) u (autoMux (u' :: us)) Δ) ?_
    have ih := autoMux_autoMux (t' :: ts) (u' :: us) (s(t, u) ::ₘ Δ) hlen
    refine ih.cast (Multiset.cons_swap _ _ _) ?_
    simp only [List.zipWith_cons_cons, ← Multiset.cons_coe]
    ms
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | [_], _ :: _ :: _, _, h => by simp at h
  | _ :: _ :: _, [_], _, h => by simp at h

/-- The names of the multiplexor `M_n` (Lafont, Fig. 4, page 83) are those of the trees plugged
into its auxiliary ports: the cells of `M_n` carry no name. -/
theorem vars_mux : ∀ (ts : List (Term sig ℕ)), (mux ts).vars = (ts.map Term.vars).sum
  | [] => by simp [mux]
  | [t] => by simp [mux]
  | t :: t' :: ts => by
    rw [mux, vars_mkCon, vars_mux (t' :: ts)]
    simp

/-- The names of the dual multiplexor `M_n*` (Lafont, Fig. 4, page 83) are those of the trees
plugged into its auxiliary ports. -/
theorem vars_muxStar : ∀ (ts : List (Term sig ℕ)), (muxStar ts).vars = (ts.map Term.vars).sum
  | [] => by simp [muxStar]
  | [t] => by simp [muxStar]
  | t :: t' :: ts => by
    rw [muxStar, vars_mkCon, vars_muxStar (t' :: ts)]
    simp [add_comm]

/-- The names of the autodual multiplexor `T_n` (Lafont, Fig. 5, page 83) are those of the trees
plugged into its auxiliary ports. -/
theorem vars_autoMux : ∀ (ts : List (Term sig ℕ)), (autoMux ts).vars = (ts.map Term.vars).sum
  | [] => by simp [autoMux]
  | [t] => by simp [autoMux]
  | t :: t' :: ts => by
    rw [autoMux, vars_mkDup, vars_autoMux (t' :: ts)]
    simp

end INet.Comb
