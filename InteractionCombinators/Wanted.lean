import InteractionCombinators.Instance

/-!
# Closure properties: all proved

This file used to state three closure properties with `proof_wanted`. All three are now proved,
each with the statement that was wanted:

* `Equiv.add_right`, in `InteractionCombinators/EquivAdd.lean`: equivalent nets stay equivalent
  inside a larger net.
* `Translation.NetTr.equiv`, in `InteractionCombinators/NetTrEquiv.lean`: two translations of a
  net are equivalent.
* `StepsE.add_right`, in `InteractionCombinators/StepsEAdd.lean`: reduction up to wires can be
  done inside a larger net. `StepE.add_right` is the version for one interaction.

They are needed to use a translation inside a larger net (Lafont's Proposition 4) and for strong
confluence (Proposition 1). The only statements left unproved are the two forms of Theorem 1 in
`InteractionCombinators/Lafont/Universality.lean`.
-/
