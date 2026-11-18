import InteractionCombinators.Combinators

/-!
# Lafont, "Interaction Combinators" (1997): erasing and multiplexors

* `erase_tree` — Lemma 2 (i): an eraser plugged into the root of a tree leaves an eraser on each
  leaf.
* `mux_muxStar` — Section 2.2: the multiplexor `M_n` against its dual `M_n*` reduces to `n` wires.
-/

namespace INet.Comb

open Term

/-- Lafont's Lemma 2 (i). -/
theorem erase_tree (τ : Term sig ℕ) (Δ : CNet) :
    Red (s(mkEra, τ) ::ₘ Δ) (τ.vars.map (fun x => s(mkEra, var x)) + Δ) := by
  induction τ using Comb.induction generalizing Δ with
  | var x => simpa using Relation.ReflTransGen.refl
  | era => simpa using Steps.single (step_era_era Δ)
  | con a b iha ihb =>
    refine Relation.ReflTransGen.head (step_era_con a b Δ) ?_
    have h1 : Red _ _ := iha (s(mkEra, b) ::ₘ Δ)
    have h2 : Red _ _ := ihb (a.vars.map (fun x => s(mkEra, var x)) + Δ)
    refine h1.trans (Steps.cast h2 ?_ ?_)
    · ms
    · simp only [vars_mkCon, Multiset.map_add]
      ms
  | dup a b iha ihb =>
    refine Relation.ReflTransGen.head (step_era_dup a b Δ) ?_
    have h1 : Red _ _ := iha (s(mkEra, b) ::ₘ Δ)
    have h2 : Red _ _ := ihb (a.vars.map (fun x => s(mkEra, var x)) + Δ)
    refine h1.trans (Steps.cast h2 ?_ ?_)
    · ms
    · simp only [vars_mkDup, Multiset.map_add]
      ms

/-- The multiplexor `M_n`, applied to the trees plugged into its `n` auxiliary ports. -/
def mux : List (Term sig ℕ) → Term sig ℕ
  | [] => mkEra
  | [t] => t
  | t :: t' :: ts => mkCon t (mux (t' :: ts))

/-- The dual multiplexor `M_n*`. -/
def muxStar : List (Term sig ℕ) → Term sig ℕ
  | [] => mkEra
  | [u] => u
  | u :: u' :: us => mkCon (muxStar (u' :: us)) u

/-- Lafont's multiplexor property: `M_n` against `M_n*` reduces to `n` wires, here the equations
between the trees plugged into matching auxiliary ports. -/
theorem mux_muxStar : ∀ (ts us : List (Term sig ℕ)) (Δ : CNet), ts.length = us.length →
    Red (s(mux ts, muxStar us) ::ₘ Δ)
      ((List.zipWith (fun t u => s(t, u)) ts us : CNet) + Δ)
  | [], [], Δ, _ => by simpa [mux, muxStar] using Steps.single (step_era_era Δ)
  | [t], [u], Δ, _ => by simpa [mux, muxStar] using Relation.ReflTransGen.refl
  | t :: t' :: ts, u :: u' :: us, Δ, h => by
    have hlen : (t' :: ts).length = (u' :: us).length := by simpa using h
    refine Relation.ReflTransGen.head
      (step_con_con t (mux (t' :: ts)) (muxStar (u' :: us)) u Δ) ?_
    have ih := mux_muxStar (t' :: ts) (u' :: us) (s(t, u) ::ₘ Δ) hlen
    refine ih.cast (Multiset.cons_swap _ _ _) ?_
    simp only [List.zipWith_cons_cons, ← Multiset.cons_coe]
    ms
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | [_], _ :: _ :: _, _, h => by simp at h
  | _ :: _ :: _, [_], _, h => by simp at h

end INet.Comb
