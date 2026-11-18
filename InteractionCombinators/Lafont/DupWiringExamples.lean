import InteractionCombinators.Lafont.DupWiring

/-!
# Lemma 3 (ii) on concrete wirings

These examples check `dup_wiring` (Lafont 1997, page 87) on small wirings: two wires, names of
the auxiliary ports shared between wires or with the rest of the net, and a wire whose two
duplicators are joined through their auxiliary ports. They also check that a wiring cannot use
the same wire name twice.

In the figure of Lemma 3 (ii) the left auxiliary ports of all the duplicators carry the first copy
of `ω`, and the right ones the second copy. For a wire `x` with `dup (a x) (b x)` at one end and
`dup (c x) (d x)` at the other, the first copy joins `a x` to `c x`, the second `b x` to `d x`.
-/

namespace INet.Comb

open Term

/-- A net is linear as soon as every name that occurs in it occurs at most twice. This turns
linearity of a concrete net into a finite check. -/
private theorem linear_of_forall_mem {N : CNet} (h : ∀ y ∈ N.vars, N.vars.count y ≤ 2) :
    N.Linear := fun y => by
  by_cases hy : y ∈ N.vars
  · exact h y hy
  · rw [Multiset.count_eq_zero.2 hy]; omega

/-- Two wires `0` and `1`, all eight auxiliary ports free (`10` to `17`). The first copy of the
wiring joins the left auxiliary ports `10—12` and `14—16`, the second the right ones `11—13` and
`15—17` (Lemma 3 (ii), page 87). -/
example : StepsE system
    ({s(mkDup (var 10) (var 11), var 0), s(mkDup (var 14) (var 15), var 1),
      s(mkDup (var 12) (var 13), var 0), s(mkDup (var 16) (var 17), var 1)} : CNet)
    {s(var 10, var 12), s(var 14, var 16), s(var 11, var 13), s(var 15, var 17)} := by
  have h := dup_wiring {0, 1} (fun x => var (10 + 4 * x)) (fun x => var (11 + 4 * x))
    (fun x => var (12 + 4 * x)) (fun x => var (13 + 4 * x)) 0
    (linear_of_forall_mem (by decide))
  simpa only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.cons_add, Multiset.singleton_add, add_zero] using h

/-- Names shared across wires: the left auxiliary port of the first end of wire `0` and the left
auxiliary port of the second end of wire `1` are joined by the wire `5`. Both lie in the first
copy, so the first copy goes `23—5—20`, a path through the two wires, and the second copy has
the two wires `21—24` and `22—25` (Lemma 3 (ii), page 87). -/
example : StepsE system
    ({s(mkDup (var 5) (var 21), var 0), s(mkDup (var 20) (var 22), var 1),
      s(mkDup (var 23) (var 24), var 0), s(mkDup (var 5) (var 25), var 1)} : CNet)
    {s(var 5, var 23), s(var 20, var 5), s(var 21, var 24), s(var 22, var 25)} := by
  have h := dup_wiring {0, 1} (fun x => if x = 0 then var 5 else var 20)
    (fun x => if x = 0 then var 21 else var 22) (fun x => if x = 0 then var 23 else var 5)
    (fun x => if x = 0 then var 24 else var 25) 0 (linear_of_forall_mem (by decide))
  simpa only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.cons_add, Multiset.singleton_add, add_zero, one_ne_zero,
    reduceIte] using h

/-- The two duplicators of a wire share a name on their left auxiliary ports, so these ports are
joined to each other rather than free. The first copy of the wire is then a cyclic wire, kept
as the equation `5 = 5`; the second copy joins `1` to `2` (Lemma 3 (ii), page 87). -/
example : StepsE system
    ({s(mkDup (var 5) (var 1), var 0), s(mkDup (var 5) (var 2), var 0)} : CNet)
    {s(var 5, var 5), s(var 1, var 2)} := by
  have h := dup_wiring {0} (fun _ => var 5) (fun _ => var 1) (fun _ => var 5) (fun _ => var 2) 0
    (linear_of_forall_mem (by decide))
  simpa only [Multiset.insert_eq_cons, Multiset.map_singleton, Multiset.singleton_add,
    add_zero] using h

/-- An auxiliary port need not be a name: here it is the tree `con 5 era`, and `5` also occurs in
the rest of the net `Δ`, on an eraser. Wire `0` carries the tree into the first copy, and `Δ` is
untouched (Lemma 3 (ii), page 87). -/
example : StepsE system
    ({s(mkDup (mkCon (var 5) mkEra) (var 1), var 0), s(mkDup (var 3) (var 4), var 0),
      s(mkEra, var 5)} : CNet)
    {s(mkCon (var 5) mkEra, var 3), s(var 1, var 4), s(mkEra, var 5)} := by
  have h := dup_wiring {0} (fun _ => mkCon (var 5) mkEra) (fun _ => var 1) (fun _ => var 3)
    (fun _ => var 4) {s(mkEra, var 5)} (linear_of_forall_mem (by decide))
  simpa only [Multiset.insert_eq_cons, Multiset.map_singleton, Multiset.singleton_add,
    Multiset.cons_add] using h

/-- A wiring cannot use the same wire name twice: with `D = {0, 0}` the name `0` occurs four
times, so the hypothesis `hlin` of `dup_wiring` fails. Each name of `D` is one wire of `ω`, with
two ends (Lemma 3 (ii), page 87). -/
example : ¬ Net.Linear
    (({0, 0} : Multiset ℕ).map (fun x => s(mkDup (var 1) (var 2), var x)) +
      ({0, 0} : Multiset ℕ).map (fun x => s(mkDup (var 3) (var 4), var x)) : CNet) :=
  fun h => absurd (h 0) (by decide)

/-- The empty wiring: nothing reduces and the rest of the net is unchanged (Lemma 3 (ii),
page 87). -/
example (a b c d : ℕ → Term sig ℕ) (Δ : CNet) (hlin : Net.Linear Δ) : StepsE system
    ((0 : Multiset ℕ).map (fun x => s(mkDup (a x) (b x), var x)) +
      (0 : Multiset ℕ).map (fun x => s(mkDup (c x) (d x), var x)) + Δ) Δ := by
  simpa using dup_wiring 0 a b c d Δ (by simpa using hlin)

end INet.Comb
