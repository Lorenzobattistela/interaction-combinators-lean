inductive Wire : Net S ν → Net S ν → Prop
  | mk
      (x : ν)
      (t : Term S ν)
      (a b : Term S ν)
      (Δ : Net S ν)
      (hlin : Net.Linear (s(var x, t) ::ₘ s(a, b) ::ₘ Δ))
      (hx : x ∈ a.vars + b.vars) :
      Wire (s(var x, t) ::ₘ s(a, b) ::ₘ Δ) (s(a.subst x t, b.subst x t) ::ₘ Δ)

def Equiv : Net S ν → Net S ν → Prop :=
  Relation.EqvGen Wire
