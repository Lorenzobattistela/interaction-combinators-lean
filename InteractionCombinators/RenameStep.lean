import InteractionCombinators.Instance
import InteractionCombinators.NetLemmas

/-!
# Reduction is invariant under injective renaming

Reduction is defined on graphs (Lafont 1997, Section 1.3, page 72), so it does not depend on the
names of the wires. In the text presentation: when every name of a net is renamed by an injective
function `f`, an interaction stays an interaction (`Step.bind_var`), and so does a reduction
(`Steps.bind_var`). The wires created by a rule are renamed by `f` too (`Rule.inst_bind_var`).

The renamed net is written `N.bind fun x => Term.var (f x)`.
-/

namespace INet

variable {S : Signature}

/-- Plugging trees into the names of a net distributes over the sum of nets. -/
theorem Net.bind_add {ν μ : Type} (f : ν → Term S μ) (N M : Net S ν) :
    Net.bind f (N + M) = N.bind f + M.bind f := Multiset.map_add _ _ _

/-- Plugging trees into the names of a net, one equation at a time. -/
theorem Net.bind_cons {ν μ : Type} (f : ν → Term S μ) (a b : Term S ν) (N : Net S ν) :
    Net.bind f (s(a, b) ::ₘ N) = s(a.bind f, b.bind f) ::ₘ N.bind f := by
  simp [Net.bind]

/-- **An instance of a rule, renamed.** Renaming every name of an instance of a rule gives the
instance of the same rule on the renamed trees, with the renamed new wires. Reduction is defined
on graphs (Lafont 1997, Section 1.3, page 72): the right-hand side of a rule does not depend on
the names. -/
theorem Rule.inst_bind_var {a b : ℕ} (r : Rule S a b) (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ) (g : Fin r.internal → ℕ) (f : ℕ → ℕ) :
    (r.inst as bs g).bind (fun y => Term.var (f y)) =
      r.inst (fun i => (as i).bind fun y => Term.var (f y))
        (fun j => (bs j).bind fun y => Term.var (f y)) (fun w => f (g w)) := by
  rw [Rule.inst, Rule.inst, Net.bind_bind]
  congr 1
  funext p
  rcases p with i | j | w <;> rfl

/-- **One interaction, renamed.** An interaction stays an interaction when every name of the net
is renamed by an injective function: reduction is defined on graphs (Lafont 1997, Section 1.3,
page 72), so it does not depend on names. The wires created by the rule are renamed too; they
stay distinct and unused because the renaming is injective. -/
theorem Step.bind_var {I : System S} (f : ℕ → ℕ) (hf : Function.Injective f) {N M : Net S ℕ}
    (h : Step I N M) :
    Step I (N.bind fun y => Term.var (f y)) (M.bind fun y => Term.var (f y)) := by
  obtain ⟨α, β, r, hr, as, bs, Δ, g, hg, hfresh⟩ := h
  rw [Net.bind_add, Rule.inst_bind_var, Net.bind_cons]
  refine Step.mk α β r hr _ _ _ _ (hf.comp hg) fun w hw => hfresh w ?_
  rw [← Term.bind_app, ← Term.bind_app, ← Net.bind_cons, Net.vars_bind_var,
    Multiset.mem_map] at hw
  obtain ⟨x, hx, hxw⟩ := hw
  exact hf hxw ▸ hx

/-- **A reduction, renamed.** A reduction in any number of interactions stays a reduction when
every name is renamed by an injective function (Lafont 1997, Section 1.3, page 72: reduction is
defined on graphs). -/
theorem Steps.bind_var {I : System S} (f : ℕ → ℕ) (hf : Function.Injective f) {N M : Net S ℕ}
    (h : Steps I N M) :
    Steps I (N.bind fun y => Term.var (f y)) (M.bind fun y => Term.var (f y)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (hstep.bind_var f hf)

end INet
