# From the paper to the code

A reading map for the Lean 4 formalization of Yves Lafont, *Interaction Combinators*
(Information and Computation 137, 1997, journal pages 69-101; `.papers/lafont-1997.pdf`, journal
page `p` is PDF page `p - 68`). For each definition, lemma, proposition, figure and theorem of the
paper it gives the Lean declaration that formalizes it, and it says which statements deserve to be
read by eye. It does not judge proofs: Lean checks those.

## Legend

| In the code | In the paper | Meaning |
|---|---|---|
| `con` (`mkCon a b`) | γ | constructor, arity 2 |
| `dup` (`mkDup a b`) | δ | duplicator, arity 2 |
| `era` (`mkEra`) | ε | eraser, arity 0 |
| `Net S ν` | a net | a multiset of unordered equations `s(t, u)` between trees; a name is a wire (twice = internal, once = free port) |
| `Equiv` | equality of nets | same graph, up to wire substitution; performs no interaction |
| `Step`, `Steps` (`Red` for the combinators) | | literal reduction: the active pair is one equation `α(..) = β(..)` |
| `StepE`, `StepsE` | reduction | reduction of graphs: an `Equiv` is allowed before each interaction |
| `StepsN n`, `StepsEN n` | "in `n` steps" | the same, with the number of interactions |
| `Φ.NetTr N N'` | `Φ(N)` | `N'` is a translation of `N` (a relation: internal wires are named freely) |

How to read the tables:

- Paths are relative to the repository root. In the column "Lean declaration", `name` :123 means
  the declaration starts at line 123 of the file in the next column. One file per row.
- "Check file" is the file of examples, non-vacuity tests or adversarial review, under `Checks/`.
- "read" in the notes means the statement was read for this map (not only its docstring).
  "docstring" means the row was taken from the docstring or the module header only.
- Constructions of Section 2 are functions on trees: `mux ts` is `M_n` with the trees `ts` plugged
  into its `n` auxiliary ports, not a `PNet`. Their properties carry the rest of the net as `Δ`.

## The statements to read first

In this order. Items 1-13 are the definitions that `universal_strict` unfolds to; they are in the
protected files, which the owner reviewed.

1. `Signature`, `Term` — `InteractionCombinators/Core/Term.lean:57`, `:65`. A tree is a name or a cell
   `app α ts` whose root is the principal port and whose `i`-th auxiliary port carries `ts i`.
2. `Net`, `Net.Linear` — `InteractionCombinators/Core/Net.lean:20`, `:65`. A net is a multiset of
   unordered pairs of trees; linear means every name occurs at most twice.
3. `Wire`, `Equiv` — `InteractionCombinators/Core/Net.lean:127`, `:133`. One wire substitution
   `x = t, a = b  ~>  a[t/x] = b[t/x]` in a linear net; `Equiv` is the equivalence it generates.
4. `Rule`, `Rule.inst`, `Rule.Linear`, `Rule.Reduced`, `Rule.swap` —
   `InteractionCombinators/Core/System.lean:19`, `:27`, `:37`, `:45`, `:49`. A right member is a net
   over `Fin a ⊕ Fin b ⊕ Fin internal` (ports of the first cell, of the second, new wires).
   `Reduced` is a syntactic form: every equation has an auxiliary port on one side.
5. `System`, `Step` — `InteractionCombinators/Core/System.lean:79`, `:85`. A partial matrix of rules;
   one interaction replaces `α(as) = β(bs)` by an instance of the rule with fresh, distinct names
   for the new wires. Equations are unordered, so a rule stored for `α, β` also fires `β, α`.
6. `System.WellFormed` — `InteractionCombinators/Core/System.lean:119`. Lafont's conditions on a
   system (pages 72-73, 79). Verbatim (field docstrings removed):

   ```lean
   structure System.WellFormed (I : System S) : Prop where
     linear : ∀ α β r, I.rule α β = some r → r.Linear
     reduced : ∀ α β r, I.rule α β = some r → r.Reduced
     unique : ∀ α β, α ≠ β → (I.rule α β).isSome → I.rule β α = none
     symm : ∀ α r, I.rule α α = some r → ∃ π : _root_.Equiv.Perm (Fin r.internal),
       Equiv r.swap.net (r.net.bind fun x => Term.var (Sum.map id (Sum.map id π) x))
   ```

7. `Steps`, `StepE`, `StepsE` — `InteractionCombinators/Core/System.lean:183`, `:204`, `:207`.
   `StepE I N M := ∃ N', Equiv N N' ∧ Step I N' M`; the starred forms are reflexive-transitive
   closures.
8. `PNet`, `PNet.inst`, `PNet.Strict` — `InteractionCombinators/Core/Translation.lean:24`, `:40`,
   `:45`. A principal net of arity `n` is a tree over `Fin n ⊕ Fin internal` in which every port
   occurs once and every internal wire twice; strict means the tree is not a single name.
9. `Translation`, `Translation.Strict` — `InteractionCombinators/Core/Translation.lean:61`, `:68`. One
   principal net of the right arity per symbol; strict when each is strict.
10. `TermTr`, `EqTr`, `NetTr` — `InteractionCombinators/Core/Translation.lean:72`, `:79`, `:84`. `N'`
    translates `N` when its equations translate those of `N` one for one (each cell replaced by
    an instance of its principal net, internal wires named arbitrarily) and `N'` is linear.
11. `Translation.Compatible` — `InteractionCombinators/Core/Translation.lean:94`. The property of
    page 81. Verbatim:

    ```lean
    def Compatible (Φ : Translation S S') (I : System S) (I' : System S') : Prop :=
      ∀ (α β : S.Sym) (r : Rule S (S.arity α) (S.arity β)), I.rule α β = some r →
        ∀ (xs : Fin (S.arity α) → ℕ) (ys : Fin (S.arity β) → ℕ)
          (f : Fin (Φ.net α).internal → ℕ) (g : Fin (Φ.net β).internal → ℕ),
          Net.Linear ({s((Φ.net α).inst (fun i => .var (xs i)) f,
            (Φ.net β).inst (fun j => .var (ys j)) g)} : Net S' ℕ) →
          ∃ (M N' : Net S' ℕ) (h : Fin r.internal → ℕ),
            StepsE I' {s((Φ.net α).inst (fun i => .var (xs i)) f,
              (Φ.net β).inst (fun j => .var (ys j)) g)} M ∧
            Equiv M N' ∧
            Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N'
    ```

12. `Universal`, `StrictlyUniversal` — `InteractionCombinators/Core/Translation.lean:146`, `:153`.
    Verbatim:

    ```lean
    def StrictlyUniversal (I' : System S') : Prop :=
      ∀ (S : Signature) [Finite S.Sym] (I : System S), I.WellFormed →
        ∃ Φ : Translation S S', Φ.Strict ∧ Φ.Compatible I I'
    ```

    `Universal` is the same without `Φ.Strict`.
13. `Comb`, `Comb.sig`, the rules `ruleConCon`, `ruleDupDup`, `ruleEraEra`, `ruleEraBin`,
    `ruleConDup`, and `Comb.system` — `InteractionCombinators/Core/Combinators.lean:17`, `:24`,
    `:101`-`:109`, `:116`. Fig. 2. Compare port by port with the figure: `con`-`con` exchanges
    the ports, `dup`-`dup` does not.
14. `INet.Comb.universal_strict : StrictlyUniversal system` and
    `INet.Comb.universal : Universal system` —
    `InteractionCombinators/Universality/Theorem1.lean:21`, `:15`. Theorem 1. Proved in
    `InteractionCombinators/Universality/General/CodeCompatible.lean:55` (`universal_strict'`), `:63`.

Then, if time allows, the three statements that carry the proof:
`System.DecData.codeTranslation_compatible` (`InteractionCombinators/Universality/General/CodeCompatible.lean:32`),
`System.exists_decData` (`InteractionCombinators/Universality/General/CodeData.lean:151`) and
`codeTranslation_strict` (`InteractionCombinators/Universality/General/CodeTr.lean:283`); and the definition of
the translated cell, `codeTree` (`InteractionCombinators/Universality/General/CodeTr.lean:189`), against
Fig. 10.

## Section 1.1, Nets (pages 71-72)

| Paper item | Lean declaration | File | Check file | Notes |
|---|---|---|---|---|
| Symbol with arity, cell, ports (p. 71) | `Signature` :57, `Term` :65 | `InteractionCombinators/Core/Term.lean` | | read. A cell exists only as the root of a tree. |
| Net: cells, free ports, wires, cyclic wires (p. 71-72) | `Net` :20, `Net.vars` :43, `Net.cells` :37, `Net.Linear` :65 | `InteractionCombinators/Core/Net.lean` | | read. Textual, not a graph. A cyclic wire is the equation `x = x`. |
| Same net (graph equality) | `Wire` :127, `Equiv` :133, `Equiv.cells_eq` :249, `Equiv.free_iff` :241, `Equiv.linear_iff` :231 | `InteractionCombinators/Core/Net.lean` | | read (definitions). No completeness theorem "same graph iff `Equiv`". |
| Renaming of internal wires gives the same net | `Net.equiv_rename` :363 | `InteractionCombinators/Text/Rename.lean` | | docstring |
| The same, several names at once | `Net.equiv_bind_var` :156 | `InteractionCombinators/Text/RenameMany.lean` | | docstring |
| Equality of nets is closed under context | `Equiv.add_right` :50 | `InteractionCombinators/Text/EquivAdd.lean` | `Checks/Misc/WantedCheck.lean` | docstring |
| Tree, root (p. 72) | `Term` :65, `Term.bind` :79, `Term.subst` :123 | `InteractionCombinators/Core/Term.lean` | | read |
| Wiring; wiring of a permutation σ (p. 72) | no type. A wiring appears as a multiset of names (`erase_wiring`, `dup_wiring`) or as equations `ts i = us (σ i)` | | | not a declaration |

## Section 1.2, Interaction (page 73)

| Paper item | Lean declaration | File | Check file | Notes |
|---|---|---|---|---|
| Interaction rule, right member `ν_{i,j}` | `Rule` :19, `Rule.inst` :27, `Rule.Linear` :37 | `InteractionCombinators/Core/System.lean` | | read |
| `ν̄_{i,j}`: exchange the two groups of ports | `Rule.swap` :49 | `InteractionCombinators/Core/System.lean` | `Checks/Universality/RecursionFree/SymmPermReview.lean` | read |
| Interaction system; "no other rule for `α_i, α_j` or `α_j, α_i`" | `System` :79, `System.WellFormed.unique` (field of :119) | `InteractionCombinators/Core/System.lean` | | read. One orientation is stored; `Step` fires both because equations are unordered. |
| "if `α_i` interacts with itself then `ν_{i,i} = ν̄_{i,i}`" | `System.WellFormed.symm` (field of :119) | `InteractionCombinators/Core/System.lean` | `Checks/Universality/RecursionFree/SymmPermCheck.lean`, `Checks/Universality/RecursionFree/SymmPermReview.lean` | read. Up to `Equiv` and a permutation of the internal wires. |
| The same condition, named | `Rule.SymmPerm` :35, `Rule.SymmPerm.of_equiv` :41 | `InteractionCombinators/Universality/RecursionFree/SymmPerm.lean` | `Checks/Universality/RecursionFree/SymmPermCheck.lean` | read. Same formula as the field `symm`. |
| One step of reduction | `Step` :85, `Steps` :183, `StepE` :204, `StepsE` :207 | `InteractionCombinators/Core/System.lean` | `Checks/Translations/SimulationECheck.lean` | read |
| Reduction keeps nets well formed | `Step.linear` :134, `StepsE.linear` :222 | `InteractionCombinators/Core/System.lean` | | docstring |
| Reduction is local (context) | `Step.add_right` :160 | `InteractionCombinators/Core/System.lean` | | docstring |
| Reduction of graphs is local | `StepE.add_right` :91, `StepsE.add_right` :156 | `InteractionCombinators/Text/StepsEAdd.lean` | `Checks/Text/StepsEAddCheck.lean` | docstring. The result is reached up to a renaming of new wires. |
| Reduction does not depend on names | `Step.bind_var` :46, `Steps.bind_var` :60 | `InteractionCombinators/Text/RenameStep.lean` | | docstring |
| Proposition 1, two different active pairs | `Step.commute` :165 | `InteractionCombinators/Reduction/Commute.lean` | | read |
| Proposition 1, the same pair `α`-`α` read both ways | `equiv_inst_swap` :28 | `InteractionCombinators/Reduction/StrongConfluence.lean` | | read |
| **Proposition 1** (strong confluence) | `Step.strong_confluence` :46 | `InteractionCombinators/Reduction/StrongConfluence.lean` | | read. `N.Linear`, `I.WellFormed`; conclusion `Equiv M₁ M₂ ∨ ∃ P₁ P₂, Step .. ∧ Step .. ∧ Equiv P₁ P₂`. Literal `Step` only: see caveats. |
| **Proposition 1** for reduction of graphs | `StepE.strong_confluence` :502 | `InteractionCombinators/Reduction/StrongConfluenceE.lean` | `Checks/Reduction/StrongConfluenceECheck.lean` | read. Two `StepE` from a linear net: the results are `Equiv`, or each takes one more `StepE` to `Equiv` nets. Second phase. |
| Consequence: all reductions to an irreducible net have the same length (p. 73-74) | not found | | | |

## Sections 1.3 to 1.5, Examples (pages 74-78)

Turing machines, cellular automata, unary arithmetic, Fig. 1: not formalized (see below).

## Section 1.6, Reduced nets (pages 78-80)

| Paper item | Lean declaration | File | Check file | Notes |
|---|---|---|---|---|
| Cut (p. 78) | `Net.HasCut` :32, `HasCut.of_equiv` :43 | `InteractionCombinators/Reduced/Cut.lean` | `Checks/Reduced/CutCheck.lean` | read. "Some `Equiv` net has an equation between two cells." |
| Cut, without the quantifier over `Equiv` nets | `ChainCut` :140, `hasCut_iff_chainCut` :416 | `InteractionCombinators/Reduced/CutChain.lean` | `Checks/Reduced/CutCheck.lean` | docstring |
| Principal path (p. 78-79) | `Path` :108 | `InteractionCombinators/Reduced/Vicious.lean` | `Checks/Reduced/ViciousCheck.lean` | docstring. Auxiliary; used only inside the proofs about circles. |
| Vicious circle, cyclic wire (p. 79) | `Net.HasVicious` :50, `ChainVicious` :217, `hasVicious_iff_chainVicious` :444 | `InteractionCombinators/Reduced/Vicious.lean` | `Checks/Reduced/ViciousCheck.lean`, `Checks/Reduced/ViciousReview.lean` | read (`HasVicious`): some `Equiv` net has `x = t` with `x` a leaf of `t`. |
| Reduced net (p. 79) | `Net.IsReduced` :70 | `InteractionCombinators/Reduced/Vicious.lean` | `Checks/Reduced/ViciousReview.lean` | read |
| "Trees are typical examples of reduced nets" | `isReduced_tree` :451 | `InteractionCombinators/Reduced/Vicious.lean` | | read |
| "All right members of rules are reduced nets" (p. 79) | `Rule.Reduced` :45, field `reduced` of `System.WellFormed` :119 | `InteractionCombinators/Core/System.lean` | `Checks/Translations/SimulationInvertibleReview.lean` | read. Syntactic form, not `IsReduced`: see caveats. |
| An instance of a reduced right member has no cut | `Rule.not_hasCut_inst` :80 | `InteractionCombinators/Translations/SimulationStrict.lean` | `Checks/Translations/SimulationStrictCheck.lean` | docstring. For distinct names on the ports. |
| Proposition 2 (decomposition into trees and a wiring) | not found | | | The form it gives is taken as the definition of `Rule.Reduced`, `PNet` and `IsPackage`. |
| Principal net of arity `n`, root, degenerate case (p. 79-80) | `PNet` :24, `PNet.inst` :40, `PNet.Strict` :45, `PNet.cell` :48 | `InteractionCombinators/Core/Translation.lean` | | read |
| Lemma 1 (principal paths of a principal net) | not found | | | Not needed: a `PNet` is a tree, the path is a branch (`InteractionCombinators/Reduced/Vicious.lean:490`). |
| Package (p. 80) | `Term.IsPackage` :20 | `InteractionCombinators/Universality/Menus/Package.lean` | `Checks/Universality/Menus/PackageCheck.lean` | read. A tree in which every name occurs exactly twice. |

## Section 1.7, Translations (pages 80-81)

| Paper item | Lean declaration | File | Check file | Notes |
|---|---|---|---|---|
| Translation, strict translation | `Translation` :61, `Translation.Strict` :68 | `InteractionCombinators/Core/Translation.lean` | | read |
| "A translation extends to nets" | `TermTr` :72, `EqTr` :79, `NetTr` :84 | `InteractionCombinators/Core/Translation.lean` | | read. A relation, because of the names of the new wires. |
| Every linear net has a translation | `Translation.exists_netTr` :144, `Translation.trTerm` :76 | `InteractionCombinators/Text/TranslationExists.lean` | `Checks/Text/TranslationExistsCheck.lean` | read |
| Two translations of a net are the same net | `Translation.NetTr.equiv` :209 | `InteractionCombinators/Text/NetTrEquiv.lean` | `Checks/Text/NetTrEquivCheck.lean`, `Checks/Misc/WantedCheck.lean` | read |
| Equal nets have equal translations | `Translation.NetTr.of_equiv` :148 | `InteractionCombinators/Text/NetTrWire.lean` | `Checks/Text/NetTrWireCheck.lean` | read |
| Prop. 3, "if `Φ(ν)` contains a cut, so does `ν`" | `Translation.NetTr.hasCut_reflect` :509 | `InteractionCombinators/Reduced/CutChain.lean` | `Checks/Reduced/CutCheck.lean` | docstring |
| Prop. 3, "if `Φ` is strict and `ν` contains a cut, so does `Φ(ν)`" | `Translation.NetTr.hasCut_of_strict` :82 | `InteractionCombinators/Reduced/Cut.lean` | `Checks/Reduced/CutCheck.lean` | docstring |
| Prop. 3, "if `ν` contains a vicious circle, so does `Φ(ν)`" | `Translation.NetTr.hasVicious` :493 | `InteractionCombinators/Reduced/Vicious.lean` | `Checks/Reduced/ViciousCheck.lean` | read |
| Prop. 3, "if `Φ(ν)` contains a vicious circle, `ν` contains a vicious circle or a cut" | `Translation.NetTr.hasVicious_reflect` :278 | `InteractionCombinators/Reduced/ViciousReflect.lean` | `Checks/Reduced/ViciousReflectCheck.lean` | docstring |
| **Proposition 3** and its converse for strict `Φ` | `Translation.NetTr.isReduced` :292, `Translation.NetTr.isReduced_of_strict` :299 | `InteractionCombinators/Reduced/ViciousReflect.lean` | `Checks/Reduced/ViciousReflectCheck.lean`, `Checks/Reduced/ViciousReview.lean` | read. No extra hypothesis. |
| Composition of translations | `Translation.trPNet` :256, `Translation.comp` :263, `comp_id` :295, `id_comp` :307 | `InteractionCombinators/Translations/TranslationComp.lean` | `Checks/Translations/TranslationCompCheck.lean`, `Checks/Translations/TranslationCompReview.lean` | read (`comp` statement); definition goes through `trTerm`. |
| Translating by `Ψ ∘ Φ` is translating twice | `Translation.NetTr.comp` :272 | `InteractionCombinators/Translations/TranslationCompTr.lean` | `Checks/Translations/TranslationCompTrCheck.lean`, `Checks/Translations/TranslationCompTrReview.lean` | read |
| Composition is associative, respects equality | `comp_iso_right` :199, `comp_iso_left` :220, `comp_assoc` :229 | `InteractionCombinators/Translations/TranslationCompAssoc.lean` | `Checks/Translations/TranslationCompAssocCheck.lean` | read (`comp_assoc`). Up to `PNet.Iso`. |
| Equality of principal nets; invertible translation | `PNet.Iso` :116, `Translation.Invertible` :269, `invertible_id` :318 | `InteractionCombinators/Translations/TranslationComp.lean` | `Checks/Translations/TranslationCompCheck.lean` | docstring |
| Composite of invertibles is invertible | `Invertible.comp` :237 | `InteractionCombinators/Translations/TranslationCompAssoc.lean` | `Checks/Translations/TranslationCompAssocCheck.lean` | docstring |
| Invertible ⇒ a renaming of symbols and a permutation of ports (p. 81, top) | `Invertible.net_eq` :155, `Invertible.symEquiv` :220, `Invertible.exists_symEquiv` :235 | `InteractionCombinators/Translations/TranslationInvertible.lean` | `Checks/Translations/TranslationInvertibleCheck.lean`, `Checks/Translations/TranslationInvertibleReview.lean` | read. The converse is only in the review file (`renPermTr_invertible`). |
| Conversely, a renaming of symbols with a permutation of ports is invertible; the characterization (p. 81) | `permCell` :44, `renPermTr` :75, `renPermTr_invertible` :112, `invertible_iff_renPermTr` :154 | `InteractionCombinators/Translations/TranslationRenPerm.lean` | `Checks/Translations/TranslationInvertibleReview.lean` | docstring; moved to the library in the second phase |
| Translation of interaction systems (the diagram of p. 81) | `Translation.Compatible` :94, `Translation.id_compatible` :122 | `InteractionCombinators/Core/Translation.lean` | `Checks/Universality/General/CodeCompatibleReview.lean` | read. Quantifies over every linear naming: more than the paper asks. |
| The same with any relation in place of `→*` | `Translation.CompatibleBy` :382, `compatible_iff_compatibleBy` :397, `CompatibleByDistinct` :404 | `InteractionCombinators/Translations/Simulation.lean` | `Checks/Translations/SimulationCheck.lean` | read (`CompatibleBy`) |
| Composite of two translations of systems | `Translation.Compatible.comp` :94 | `InteractionCombinators/Translations/TranslationCompCompatible.lean` | `Checks/Translations/TranslationCompCompatibleCheck.lean` | read. Rules of the middle and target systems linear. |
| `L`, `M`: least and greatest length | `StepsN` :32, `StepsEN` :38, `Translation.CompatibleWithin` :148 | `InteractionCombinators/Translations/SimulationCount.lean` | `Checks/Translations/SimulationCountCheck.lean` | read. `L ≤ k ≤ M` for every rule and naming; `L`, `M` are bounds, not shown attained. |
| `L`, `M` exist (finite alphabet) | `Compatible.exists_length` :182, `Compatible.len` :226, `Compatible.compatibleWithin_len` :239, `Compatible.exists_compatibleWithin` :258 | `InteractionCombinators/Translations/SimulationUniform.lean` | `Checks/Translations/SimulationUniformCheck.lean`, `Checks/Translations/SimulationUniformReview.lean` | read (:258). `[Finite S.Sym]`, `I.WellFormed`, rules of `I'` linear. |
| "`L > 0` if `Φ` is strict" | `CompatibleWithin.distinct_pos` :146, `CompatibleWithin.pos` :166 | `InteractionCombinators/Translations/SimulationStrict.lean` | `Checks/Translations/SimulationStrictCheck.lean`, `Checks/Translations/SimulationCorollaryReview.lean` | read (:166). Conclusion is `CompatibleWithin (max L 1) M`. |
| "`L = M = 1` if `Φ` is invertible" | `Invertible.compatibleWithin_one_of_wellFormed` :617 | `InteractionCombinators/Translations/PairStepE.lean` | `Checks/Translations/SimulationInvertibleCheck.lean`, `Checks/Translations/SimulationInvertibleReview.lean` | read. Asks `I'.WellFormed`, more than it uses. |
| The same from linear and reduced rules only | `Invertible.compatibleWithin_one_of_linear_reduced` :94, `Invertible.compatibleWithin_one_of_reduced` :131 | `InteractionCombinators/Translations/PairStepEReduced.lean` | (examples in the same file, from :171) | read (:94) |
| Proposition 4, one step | `Translation.Compatible.step` :600 | `InteractionCombinators/Translations/Simulation.lean` | `Checks/Translations/SimulationCheck.lean` | read |
| Proposition 4, without counts, literal source | `Translation.Compatible.steps` :613 | `InteractionCombinators/Translations/Simulation.lean` | `Checks/Translations/SimulationCheck.lean` | read |
| Proposition 4, without counts, source up to wires | `Compatible.stepsE` :48 | `InteractionCombinators/Translations/SimulationE.lean` | `Checks/Translations/SimulationECheck.lean` | read |
| **Proposition 4** with `L n ≤ n' ≤ M n`, literal source | `CompatibleWithin.steps` :206 | `InteractionCombinators/Translations/SimulationCount.lean` | `Checks/Translations/SimulationCountCheck.lean` | read. Rules of `I` and `I'` linear; `Φ(ν)` reached up to `Equiv`. |
| **Proposition 4** with counts, source up to wires | `CompatibleWithin.stepsEN` :81 | `InteractionCombinators/Translations/SimulationE.lean` | `Checks/Translations/SimulationECheck.lean` | read. The form closest to the paper. |

## Section 2.1, The system (pages 81-82)

| Paper item | Lean declaration | File | Check file | Notes |
|---|---|---|---|---|
| The three combinators | `Comb` :17, `sig` :24, `mkCon` :34, `mkDup` :36, `mkEra` :38 | `InteractionCombinators/Core/Combinators.lean` | | read |
| Fig. 2, the six rules | `ruleConCon` :101, `ruleDupDup` :103, `ruleEraEra` :105, `ruleEraBin` :107, `ruleConDup` :109, `system` :116 | `InteractionCombinators/Core/Combinators.lean` | `Checks/Universality/General/CodeCompatibleReview.lean` | read. `era`-`con` and `era`-`dup` share `ruleEraBin`. Stored orientations: `era`-`con`, `era`-`dup`, `con`-`dup`. |
| "The symmetry condition is satisfied" | `system_wellFormed` :217 | `InteractionCombinators/Core/Combinators.lean` | | read |
| The rules as steps in a context | `step_con_con` :264, `step_dup_dup` :271, `step_era_era` :278, `step_era_con` :284, `step_era_dup` :293, `step_con_dup` :302 | `InteractionCombinators/Core/Combinators.lean` | | docstring |
| "γγ, not δδ, exchanges the ports" | `ruleConCon` :101 vs `ruleDupDup` :103 | `InteractionCombinators/Core/Combinators.lean` | | read |
| Fig. 3, a net that reduces to itself in four steps | not found | | | |
| **Theorem 1** (stated p. 82) | `universal` :15, `universal_strict` :21 | `InteractionCombinators/Universality/Theorem1.lean` | `Checks/Universality/General/CodeCompatibleReview.lean` | read. See Section 2.7 below. |

## Section 2.2, Multiplexors and transpositors (pages 82-84)

| Paper item | Lean declaration | File | Check file | Notes |
|---|---|---|---|---|
| Fig. 4, `M_n` and `M_n*` | `mux` :39, `muxStar` :45 | `InteractionCombinators/Universality/Multiplexors/Multiplexor.lean` | `Checks/Universality/Multiplexors/BasicCheck.lean` | read. `M_0 = era`, `M_1` a wire, nested to the right; `M_n*` mirrors it. No `dup`. |
| Property of the multiplexors | `mux_muxStar` :52 | `InteractionCombinators/Universality/Multiplexors/Multiplexor.lean` | `Checks/Universality/Multiplexors/BasicCheck.lean` | read. Literal `Red`; result is `ts[i] = us[i]`. |
| "Our implementation does not use δ" | `dupFree_mux` :36, `dupFree_muxStar` :44 | `InteractionCombinators/Universality/Codes/Code.lean` | | docstring |
| Fig. 5, autodual `T_n` | `autoMux` :20 | `InteractionCombinators/Universality/Multiplexors/AutoMux.lean` | `Checks/Universality/Multiplexors/AutoMuxCheck.lean` | read. Same shape as `mux`, with `dup`. |
| Property of `T_n` | `autoMux_autoMux` :28 | `InteractionCombinators/Universality/Multiplexors/AutoMux.lean` | `Checks/Universality/Multiplexors/AutoMuxCheck.lean` | read. Literal `Red`. |
| Transpositor `T_{p,q}` (p. 83) | `pairCon` :30, `transpositor` :40 | `InteractionCombinators/Universality/Multiplexors/Transpositor.lean` | `Checks/Universality/Multiplexors/TranspositorCheck.lean` | read. `T_{p+q}` with a `con` on each of its first `p` ports. |
| `ι_{p,q}` | `swapPairs` :44 | `InteractionCombinators/Universality/Multiplexors/Transpositor.lean` | `Checks/Universality/Multiplexors/TranspositorCheck.lean` | read. As a function on lists. |
| Property of `T_{p,q}` | `transpositor_transpositor` :89 | `InteractionCombinators/Universality/Multiplexors/Transpositor.lean` | `Checks/Universality/Multiplexors/TranspositorCheck.lean` | read. Literal `Red`. No hypothesis `2p ≤ length`. |
| `ι_{p,q}` as a permutation | `swapPerm` :74 | `InteractionCombinators/Universality/Multiplexors/TranspositorPerm.lean` | `Checks/Universality/Multiplexors/TranspositorPermCheck.lean` | docstring |
| "`σ = ρ⁻¹ ∘ ι_{p,q} ∘ ρ`" (p. 84) | `involutive_decomp` :188 | `InteractionCombinators/Universality/Multiplexors/TranspositorPerm.lean` | `Checks/Universality/Multiplexors/TranspositorPermCheck.lean` | read |
| `T_σ` for an involution σ | `portList` :93, `transpositorPerm` :217 | `InteractionCombinators/Universality/Multiplexors/TranspositorPerm.lean` | `Checks/Universality/Multiplexors/TranspositorPermCheck.lean` | read (statement); the involutivity argument is not used by the definition. |
| Property of `T_σ` | `transpositorPerm_transpositorPerm` :247 | `InteractionCombinators/Universality/Multiplexors/TranspositorPerm.lean` | `Checks/Universality/Multiplexors/TranspositorPermCheck.lean` | read. Result is `ts i = us (σ i)`. |
| "Conversely, if such a `T_σ` exists, σ is involutive" | not found | | | |

## Section 2.3, Menus and selectors (pages 84-85)

| Paper item | Lean declaration | File | Check file | Notes |
|---|---|---|---|---|
| Menu `π₁ & ... & πₙ` | `menu` :22 | `InteractionCombinators/Universality/Menus/Menu.lean` | `Checks/Universality/Menus/MenuCheck.lean` | read. `menu πs = mux πs`. |
| Selector `Sⁱₙ` | `selector` :26 | `InteractionCombinators/Universality/Menus/Menu.lean` | `Checks/Universality/Menus/MenuCheck.lean` | docstring. `i` is counted from 0. |
| A menu of packages is a package | `IsPackage.menu` :116 | `InteractionCombinators/Universality/Menus/Menu.lean` | | docstring |
| Property of menus and selectors | `menu_selector` :82 | `InteractionCombinators/Universality/Menus/Menu.lean` | `Checks/Universality/Menus/MenuCheck.lean` | read. `StepsE`; every `π` a package, net linear. Result literally `πs[i] = x`. |
| **Lemma 2 (i)**, erasing a tree | `erase_tree` :16 | `InteractionCombinators/Universality/Multiplexors/Multiplexor.lean` | `Checks/Universality/Multiplexors/BasicCheck.lean` | read. Literal `Red`; no hypothesis. |
| **Lemma 2 (ii)**, erasing a wiring | `erase_wiring` :105 | `InteractionCombinators/Universality/Menus/Package.lean` | `Checks/Universality/Menus/PackageCheck.lean` | read. `StepsE`; the wiring is the multiset `D` of its wire names. |
| Corollary: a package is erased | `erase_package` :125 | `InteractionCombinators/Universality/Menus/Package.lean` | `Checks/Universality/Menus/PackageCheck.lean` | read. `StepsE`; `π.IsPackage`, net linear. |
| The same for a list of packages | `erase_packages` :62 | `InteractionCombinators/Universality/Menus/Menu.lean` | | docstring |
| "(i) holds for principal nets, (ii) for reduced nets" | not found | | | Only trees, wirings and packages. |

## Section 2.4, Translation, restricted case (pages 85-87)

| Paper item | Lean declaration | File | Check file | Notes |
|---|---|---|---|---|
| Decomposition of a right member into `φ`, `ψ`, `σ` (figure of p. 85) | `Decomposition` :65, `Rule.plug` :95, `Rule.plug_linear` :122 | `InteractionCombinators/Universality/RecursionFree/Decomposition.lean` | `Checks/Universality/RecursionFree/DecompositionCheck.lean`, `Checks/Universality/RecursionFree/DecompositionReview.lean` | read (`Decomposition`); `plug` by docstring: middle wire `l` of `φ` joined to `σ l` of `ψ`. A side is a `Rule S a k`. |
| "plugging the sides gives the right member" | `Decomposition.Plugs` :68 | `InteractionCombinators/Universality/RecursionFree/RecursionFree.lean` | | read. Up to `Equiv` and an injective renaming of the internal wires of the rule. |
| One side of the canonical decomposition | `Half.half` :183 | `InteractionCombinators/Universality/RecursionFree/DecompositionHalf.lean` | | docstring |
| "there is a canonical one" | `Rule.decompose` :310, `decompose_linear` :328, `decompose_reduced` :346, `decompose_cells` :367, `plug_decompose` :540 | `InteractionCombinators/Universality/RecursionFree/Decomposition.lean` | `Checks/Universality/RecursionFree/DecompositionCheck.lean`, `Checks/Universality/RecursionFree/DecompositionReview.lean` | read (:540). Uniqueness of the canonical decomposition is not stated. |
| Example: canonical decomposition of a rule (p. 85) | `conDup_k`, `conDup_φ`, `conDup_ψ`, `conDup_σ`, `conCon_σ` (in the check file) | `Checks/Universality/RecursionFree/DecompositionCheck.lean` | | The paper's example is the rule `s`-`×` of Section 1.5; the checks use the combinators. |
| Expanded form of a rule (not in the paper; one tree per port) | `Rule.Expanded` :34, `Rule.exists_perm_of_equiv` :303 | `InteractionCombinators/Universality/RecursionFree/ExpandedIso.lean` | `Checks/Universality/RecursionFree/ExpandedIsoCheck.lean` | read (:303) |
| Every linear reduced rule has an expanded form | `Rule.exists_expanded` :264 | `InteractionCombinators/Universality/RecursionFree/Expand.lean` | `Checks/Universality/RecursionFree/ExpandCheck.lean`, `Checks/Universality/RecursionFree/ExpandTrReview.lean` | read |
| "`φ_{i,i} = ψ_{i,i}`, `σ_{i,i}` involutive" (p. 85-86), from symmetry up to wires | `Rule.exists_symm_decomposition` :94 | `InteractionCombinators/Universality/RecursionFree/DecompositionSymm.lean` | `Checks/Universality/RecursionFree/DecompositionSymmCheck.lean`, `Checks/Universality/RecursionFree/DecompositionSymmReview.lean` | read. Hypothesis `Equiv r.swap.net r.net`: stronger than page 73. Superseded by the next row. |
| The same from the symmetry of page 73 | `Rule.exists_symm_decomposition_of_symmPerm` :154 | `InteractionCombinators/Universality/RecursionFree/SymmPerm.lean` | `Checks/Universality/RecursionFree/SymmPermCheck.lean`, `Checks/Universality/RecursionFree/SymmPermReview.lean` | read. This is the one `symmDec` uses. The decomposition is not the canonical one. |
| "If `i ≠ j`, include the permutation into `φ_{i,j}`, so that `σ_{i,j}` is an identity" | `Decomposition.absorb` :46, `System.WellFormed.symmDec` :158 | `InteractionCombinators/Universality/RecursionFree/DecompositionAbsorb.lean` | `Checks/Universality/RecursionFree/RecursionFreeCheck.lean` | read (`symmDec`, `symmDec_spec`); `absorb` by docstring. |
| "one can assume in all cases ..." (p. 86), as data | `System.DecData` :39, `System.exists_decData` :151, `DecData.side` :182 | `InteractionCombinators/Universality/General/CodeData.lean` | `Checks/Universality/General/CodeDataCheck.lean`, `Checks/Universality/General/CodeDataReview.lean` | read (structure and :151). |
| "`φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}`": the two sides of a rule | `DecData.sides_expand` :72 | `InteractionCombinators/Universality/General/CodeDataSides.lean` | `Checks/Universality/General/CodeDataSidesCheck.lean` | read. Needs `I.WellFormed` (shown necessary in `Checks/Universality/General/CodeDataReview.lean`). |
| Recursion-free system (order on the alphabet, p. 86) | `System.RecursionFreeData` :76, `System.RecursionFree` :103 | `InteractionCombinators/Universality/RecursionFree/RecursionFree.lean` | `Checks/Universality/RecursionFree/RecursionFreeCheck.lean` | read. Order given by `rank : S.Sym → ℕ`; the decomposition is part of the data. |
| "Reduction always terminates in such a system" | not found | | | |
| Example of p. 87: the combinators without `con`-`dup` | `systemNoConDup` :112, `systemNoConDup_wellFormed` :132, `recursionFreeDataNoConDup` :305, `systemNoConDup_recursionFree` :347 | `InteractionCombinators/Universality/RecursionFree/RecursionFree.lean` | `Checks/Universality/RecursionFree/RecursionFreeCheck.lean` | read (:347) |
| The side of `α` against `β`, in expanded form | `RawSide` :35, `ExpSide` :48, `RawSide.expand` :65, `RecursionFreeData.side` :120 | `InteractionCombinators/Universality/RecursionFree/RecursionFreeSide.lean` | | docstring |
| Fig. 6 left, the cell `[α_i]`, as a tree | `cellSel` :34, `cellSkel` :45 | `InteractionCombinators/Universality/RecursionFree/CellSkeleton.lean` | `Checks/Universality/RecursionFree/CellSkeletonCheck.lean`, `Checks/Universality/RecursionFree/CellSkeletonReview.lean` | docstring. `T_{1,1}(Γ, S(M_{n+1}(ts, ℓ)), ℓ)`. |
| Fig. 6 right, the package `Γ_{i,j}`; `[φ_{i,j}]` | `Rule.portTree` :40, `gammaTree` :110, `gammaPort` :126, `gamma` :133, `gamma_isPackage` :191 | `InteractionCombinators/Universality/RecursionFree/Gamma.lean` | `Checks/Universality/RecursionFree/GammaCheck.lean`, `Checks/Universality/RecursionFree/GammaReview.lean` | docstring |
| Fig. 6, `[α]` as a principal net; the translation by induction on the order | `cellPNet` :192, `symEnum` :232, `cellNet` :259, `RecursionFreeData.translation` :304, `translation_net` :310 | `InteractionCombinators/Universality/RecursionFree/RecursionFreeTr.lean` | `Checks/Universality/RecursionFree/RecursionFreeTrReview.lean` | read (:304, :310). Noncomputable. |
| The translation of Fig. 6 is strict | `RecursionFreeData.translation_strict` :56 | `InteractionCombinators/Universality/RecursionFree/RecursionFreeStrict.lean` | | read |
| Fig. 7, rows 1-2 (trees) | `cellSkel_cellSkel` :145 | `InteractionCombinators/Universality/RecursionFree/CellSkeleton.lean` | `Checks/Universality/RecursionFree/CellSkeletonCheck.lean` | read |
| Fig. 7, last rows; the whole figure (trees) | `mux_gamma_mux_gamma` :71, `cellSkel_gamma_cellSkel_gamma` :123 | `InteractionCombinators/Universality/RecursionFree/Fig7End.lean` | `Checks/Universality/RecursionFree/Fig7EndCheck.lean`, `Checks/Universality/RecursionFree/Fig7EndReview.lean` | read |
| The net at the end of Fig. 7 is a translation of `plug φ ψ σ` | `plugTarget` :33, `netTr_plug_gamma` :112, `mux_gamma_mux_gamma_netTr` :229 | `InteractionCombinators/Universality/RecursionFree/PlugTr.lean` | `Checks/Universality/RecursionFree/PlugTrCheck.lean`, `Checks/Universality/RecursionFree/PlugTrReview.lean` | docstring |
| The same for any translated trees | `plugTermTarget` :31, `netTr_plug_termTr` :53 | `InteractionCombinators/Universality/RecursionFree/PlugTermTr.lean` | `Checks/Universality/RecursionFree/PlugTermTrCheck.lean`, `Checks/Universality/RecursionFree/PlugTermTrReview.lean` | read |
| ... hence a translation of the rule itself | `Decomposition.Plugs.netTr_inst` :93, `Plugs.netTr_inst_of_sides` :106 | `InteractionCombinators/Universality/RecursionFree/PlugsNetTr.lean` | `Checks/Universality/RecursionFree/PlugsNetTrCheck.lean`, `Checks/Misc/PlugsReview.lean` | read (:106) |
| Expanded sides still plug the rule | `Decomposition.Plugs.of_expand` :289, `RecursionFreeData.plugs_expand` :312 | `InteractionCombinators/Universality/RecursionFree/PlugsExpand.lean` | `Checks/Misc/PlugsReview.lean` | docstring |
| Fig. 7 for the translation itself | `translation_cells_meet` :355, `translation_cells_netTr_plug` :461 | `InteractionCombinators/Universality/RecursionFree/RecursionFreeFig7.lean` | `Checks/Universality/RecursionFree/RecursionFreeFig7Check.lean` | read |
| **"In that way, one gets a translation of interaction systems (Fig. 7)"** | `RecursionFreeData.translation_compatible` :37, `recursionFree_strict` :54, `recursionFree_strict_noConDup` :62 | `InteractionCombinators/Universality/RecursionFree/RecursionFreeCompatible.lean` | `Checks/Universality/RecursionFree/RecursionFreeCompatibleReview.lean` | read. `I.WellFormed`, `[Finite S.Sym]` (from the section variables). |

## Section 2.5, Duplication (page 87)

| Paper item | Lean declaration | File | Check file | Notes |
|---|---|---|---|---|
| "without δ" | `DupFree` :19 | `InteractionCombinators/Universality/Duplication/Duplication.lean` | | read |
| **Lemma 3 (i)**, text form | `dupNet` :31, `dup_tree` :55 | `InteractionCombinators/Universality/Duplication/Duplication.lean` | `Checks/Universality/Duplication/DuplicationExamples.lean` | read. Literal `Red`; the result is a net computed by `dupNet`. |
| **Lemma 3 (i)**, as drawn (two copies, a `dup` on each leaf) | `Copy` :118, `nested` :130, `dup_tree_nested` :246 | `InteractionCombinators/Universality/Duplication/Duplication.lean` | `Checks/Universality/Duplication/DuplicationExamples.lean` | read. Up to `Equiv`. |
| **Lemma 3 (ii)**, duplicating a wiring | `dup_wiring` :43 | `InteractionCombinators/Universality/Duplication/DupWiring.lean` | `Checks/Universality/Duplication/DupWiringExamples.lean` | read. `StepsE`. |
| Corollary: a package without `dup` is duplicated | `dup_package` :216 | `InteractionCombinators/Universality/Duplication/DupPackage.lean` | `Checks/Universality/Duplication/DupPackageCheck.lean` | read. The copies are `π` renamed by maps injective on its names. |
| "δ cannot duplicate δ" (necessity of `DupFree`) | not found | | | The check file says why it was not proved. |
| "(i) holds for principal nets, (ii) for reduced nets without δ" | not found | | | |

## Section 2.6, Codes, copiers and decoder (pages 88-89)

| Paper item | Lean declaration | File | Check file | Notes |
|---|---|---|---|---|
| Copier `C_n` | `copier` :28 | `InteractionCombinators/Universality/Codes/Copier.lean` | `Checks/Universality/Codes/CopierCheck.lean` | read. `copier = autoMux`, as in the paper. |
| Property of `C_n` on a package without `dup` | `copier_package` :71 | `InteractionCombinators/Universality/Codes/Copier.lean` | `Checks/Universality/Codes/CopierCheck.lean` | read. `n` renamed copies, up to `Equiv`. |
| "`π` can be decomposed ... `π'` with `3n + 1` free ports, no δ" | `Decomp` :28, `decomp` :39, `dupCount` :182, `package_decomp` :463, `package_decomp_exists` :482 | `InteractionCombinators/Universality/Codes/PackageDecomp.lean` | `Checks/Universality/Codes/PackageDecompCheck.lean` | read (:463). The `3n + 1` count is implicit: `n` cut names plus the trees. |
| Fig. 8, the code `!π` | `Decomp.code` :55, `code` :65 | `InteractionCombinators/Universality/Codes/Code.lean` | `Checks/Universality/Codes/CodeCheck.lean` | docstring. `M_4(M_n(cut names), M_n*(right trees), M_n*(left trees), τ)`. Compare with the figure. |
| Fig. 8, the decoder `D` | `decoder` :72 | `InteractionCombinators/Universality/Codes/Code.lean` | `Checks/Universality/Codes/CodeCheck.lean`, `Checks/Universality/Codes/DecodeReview.lean` | docstring |
| "`!π` contains no δ"; "another package `!π`" | `code_dupFree` :98, `code_isPackage` :125 | `InteractionCombinators/Universality/Codes/Code.lean` | `Checks/Universality/Codes/CodeCheck.lean` | read |
| Property of `C_n` on `!π` | `copier_code` :145 | `InteractionCombinators/Universality/Codes/Code.lean` | `Checks/Universality/Codes/CodeCheck.lean` | read |
| Fig. 9, first stage (`M_4` against `M_4*`) | `code_decoder` :185 | `InteractionCombinators/Universality/Codes/Code.lean` | `Checks/Universality/Codes/CodeCheck.lean` | read. Literal `Red`. |
| **Fig. 9**: the decoder extracts `π` from `!π` | `code_decoder_tree` :174, `code_decoder_package` :239 | `InteractionCombinators/Universality/Codes/Decode.lean` | `Checks/Universality/Codes/DecodeCheck.lean`, `Checks/Universality/Codes/DecodeReview.lean` | read (:239). The package hypothesis is unused (`_hπ`): true for any tree. |
| Fig. 9 on a copy made by the copier | `code_decoder_copy` :189 | `InteractionCombinators/Universality/Codes/DecodeCopy.lean` | `Checks/Universality/Codes/DecodeCopyCheck.lean`, `Checks/Universality/Codes/DecodeCopyReview.lean` | read |

## Section 2.7, Translation, general case (pages 88-90)

The paper ends with "the reader is invited to complete the proof of Theorem 1 by working out the
analogue of Fig. 7 for this translation". Everything below `codeCells_meet` is that analogue.

| Paper item | Lean declaration | File | Check file | Notes |
|---|---|---|---|---|
| Fig. 10 bottom left, `⟨α_k⟩` | `codeCell` :46 | `InteractionCombinators/Universality/General/CodeCell.lean` | `Checks/Universality/General/CodeCellCheck.lean`, `Checks/Universality/General/CodeCellReview.lean` | docstring. A net of three equations, not one tree. |
| `C_2` and `D` against a copy of `!Γ` | `copier_decoder_copy` :43 | `InteractionCombinators/Universality/Codes/DecodeCopyChain.lean` | `Checks/Universality/Codes/DecodeCopyReview.lean` | read |
| The picture of p. 90: `!Γ` on the extra port of `⟨α_k⟩` gives `[α_k]` | `codeCell_code` :88 | `InteractionCombinators/Universality/General/CodeCell.lean` | `Checks/Universality/General/CodeCellCheck.lean`, `Checks/Universality/General/CodeCellReview.lean` | read |
| `⟨φ_{i,j}⟩`: cells replaced by `⟨α_k⟩` | `codeExtra` :48, `codeTerm` :130, `codeExtras` :139 | `InteractionCombinators/Universality/General/CodeGamma.lean` | `Checks/Universality/General/CodeGammaCheck.lean`, `Checks/Universality/General/CodeGammaReview.lean` | docstring. Each cell takes five new names. |
| Fig. 10 bottom right, `Γ_{i,j}` with the copier `C_{p_{i,j}}` | `codeGamma` :231, `codeGamma_isPackage` :295 | `InteractionCombinators/Universality/General/CodeGamma.lean` | `Checks/Universality/General/CodeGammaCheck.lean`, `Checks/Universality/General/CodeGammaReview.lean` | docstring |
| The menus `Γ_i` and `Γ = Γ_1 & ... & Γ_m` | `codeCellMenu` :330, `codeMenus` :350, `codeCell_code_codeMenus` :395 | `InteractionCombinators/Universality/General/CodeGamma.lean` | `Checks/Universality/General/CodeGammaCheck.lean` | docstring |
| **Fig. 10 top left, `[α_i]`** | `codeTree` :189, `treePNet` :88, `codeNet` :249, `codeTranslation` :254 | `InteractionCombinators/Universality/General/CodeTr.lean` | `Checks/Universality/General/CodeTrCheck.lean`, `Checks/Universality/General/CodeTrReview.lean` | read (`codeTree`): `cellSkel` with `!Γ` as first leaf of `M_{n+2}`. Parameter `side`: any choice of expanded sides. Noncomputable. |
| The translation is strict | `codeTranslation_strict` :283 | `InteractionCombinators/Universality/General/CodeTr.lean` | `Checks/Universality/General/CodeTrCheck.lean` | read |
| Renaming of the pieces; the extracted cell is an instance of `[β]` | `codeNet_inst_eq` :150 | `InteractionCombinators/Universality/General/CodeShift.lean` | | docstring |
| "and we get the translation of `φ_{i,j}`", for one tree | `codeCopies` :37, `codeTerm_extract` :304 | `InteractionCombinators/Universality/General/CodeTermExtract.lean` | `Checks/Universality/General/CodeTermExtractCheck.lean` | read (:304) |
| The same for a whole side: `C_p` against `!Γ` | `codeGamma_extract` :113 | `InteractionCombinators/Universality/General/CodeGammaExtract.lean` | `Checks/Universality/General/CodeGammaExtractCheck.lean` | docstring |
| Analogue of Fig. 7, rows 1-2 | `codeCells_meet` :177 | `InteractionCombinators/Universality/General/CodeCellsMeet.lean` | `Checks/Universality/General/CodeCellsMeetCheck.lean`, `Checks/Universality/Codes/CodeMeetReview.lean` | docstring. `codeCells_meet_gamma` :279 in the same file has no library user. |
| Analogue of Fig. 7, last rows | `codeGamma_meet` :67, `codeCells_meet_end` :150 | `InteractionCombinators/Universality/General/CodeGammaMeet.lean` | `Checks/Universality/General/CodeGammaMeetCheck.lean`, `Checks/Universality/Codes/CodeMeetReview.lean` | docstring |
| Analogue of Fig. 7, the whole figure | `middle_reindex` :70, `codeCells_plug` :90 | `InteractionCombinators/Universality/General/CodeCellsPlug.lean` | `Checks/Universality/General/CodeCellsPlugCheck.lean`, `Checks/Universality/General/CodeCellsPlugReview.lean` | read (:90) |
| **The translation of Fig. 10 is a translation of interaction systems** | `System.DecData.codeTranslation_compatible` :32 | `InteractionCombinators/Universality/General/CodeCompatible.lean` | `Checks/Universality/General/CodeCompatibleReview.lean` | read. `[Finite S.Sym]`, `I.WellFormed`, any `D : I.DecData`. |
| **Theorem 1** | `universal_strict'` :55, `universal'` :63 | `InteractionCombinators/Universality/General/CodeCompatible.lean` | `Checks/Universality/General/CodeCompatibleReview.lean` | read |
| **Theorem 1**, the target names | `universal` :15, `universal_strict` :21 | `InteractionCombinators/Universality/Theorem1.lean` | `Checks/Universality/General/CodeCompatibleReview.lean` | read. Docstring says "page 90"; the theorem is stated on page 82. |
| Theorem 1 with step counts (`0 < L`) | `codeTranslation_compatibleWithin` :283 | `InteractionCombinators/Translations/SimulationUniform.lean` | `Checks/Translations/SimulationUniformReview.lean` | read. `L`, `M` exist; their values are not computed. |

## What is not formalized

Checked by grep over `InteractionCombinators/` and `Checks/` (words searched: the proposition and
lemma numbers, the figure numbers, "Turing", "terminat", "minimal", "Section 3", "necessarily
involutive").

| Paper item | Page | Status |
|---|---|---|
| The consequence of Proposition 1: uniqueness of the normal form and of the length of reductions | 73-74 | proved in the second phase: `StepE.Normal`, `StepsEN.normal_of_stepsEN`, `StepsEN.normal_unique` in `InteractionCombinators/Reduction/NormalFormE.lean`; check `Checks/Reduction/NormalFormECheck.lean` |
| Section 1.3, Turing machines; Section 1.4, cellular automata; Fig. 1 | 74-77 | not found |
| Section 1.5, unary arithmetic | 77-78 | addition only, as a demo: `Demo/Arithmetic.lean` (`system_wellFormed`, `two_plus_two`, `two_plus_two_in_combinators`); multiplication, which needs duplication and erasing, is not there |
| Proposition 2 (unique decomposition of a reduced net into trees and a wiring) | 79 | not found; its conclusion is built into `Rule.Reduced`, `PNet`, `Term.IsPackage` |
| Lemma 1 (principal paths of a principal net) | 80 | not found; avoided because a `PNet` is a tree |
| "A reduced net with no free port is empty" | 80 | not found |
| Fig. 3, a nonterminating net | 82 | not found |
| "If such a `T_σ` exists, σ is necessarily involutive" | 84 | not found |
| Lemma 2 and Lemma 3 "more generally for principal nets / reduced nets" | 85, 87 | not found |
| Uniqueness of the canonical decomposition | 85 | not found; the symmetric decomposition is obtained another way (expanded forms) |
| Termination of recursion-free systems | 86 | not found |
| "δ cannot duplicate δ" | 87 | proved in the second phase as a refutation of `dup_package` and `copier_package` without `DupFree`: `Checks/Misc/DupDupCheck.lean` |
| Section 2.8, minimality of the system | 90 | not found |
| Section 3, semantics: execution (Prop. 5, Fig. 11-13), equivalence (Prop. 6, Fig. 14), algebraic formulation (Fig. 15), directed combinators and 2-translations (Prop. 7, Fig. 16-19) | 90-99 | not found |
| Section 4, discussion | 99-100 | nothing to formalize |

The symmetric combinators (both annihilations alike) are not in the paper's Theorem 1 and not in
the code.

## Known gaps and caveats

From `history/progress/20261119T092037Z_summary.md`, `history/progress/20261119T073500Z_summary.md`,
the later progress files, and from reading the statements.

1. **Nets are text, not graphs.** A net is a multiset of equations, and graph equality is `Equiv`.
   There is no graph model and no theorem that `Equiv` is exactly graph isomorphism. The review of
   `Rule.SymmPerm` (`history/progress/20261119T102046Z_022dcc38.md`) says the completeness direction
   is "an argument, not a theorem".
2. **`Rule.Reduced` is a syntactic form** (`InteractionCombinators/Core/System.lean:45`): every equation
   has an auxiliary port on one side. By Proposition 2 every reduced net can be written so, but
   Proposition 2 is not formalized, and `Rule.Reduced` is not related to `Net.IsReduced` beyond
   `Rule.not_hasCut_inst` (`InteractionCombinators/Translations/SimulationStrict.lean:80`, no cut, for
   distinct port names). A rule whose text has an equation between an internal wire and a tree is
   rejected even if its graph is reduced; the user must write the substituted form.
3. **Proposition 1** exists in both forms: `Step.strong_confluence` for literal steps
   (`InteractionCombinators/Reduction/StrongConfluence.lean:46`) and `StepE.strong_confluence` for
   reduction of graphs (`InteractionCombinators/Reduction/StrongConfluenceE.lean:502`). Its
   consequences (uniqueness of the normal form and of the length of reductions,
   `InteractionCombinators/Reduction/NormalFormE.lean`) and the necessity of `DupFree`
   (`Checks/Misc/DupDupCheck.lean`) are proved too.
4. **Which results use which reduction.** Literal `Red`: `erase_tree`, `mux_muxStar`,
   `autoMux_autoMux`, `transpositor_transpositor`, `transpositorPerm_transpositorPerm`, `dup_tree`,
   `code_decoder`. Up to wires (`StepsE`, then `Equiv` to the stated net): `erase_wiring`,
   `erase_package`, `menu_selector`, `dup_wiring`, `dup_package`, `copier_package`, Fig. 7, Fig. 9,
   Fig. 10 and Theorem 1. A literal reduction is a reduction up to wires (`Steps.stepsE`,
   `InteractionCombinators/Core/System.lean:212`), so the literal results are the stronger ones.
5. **`Translation.Compatible` asks more than the paper**: every naming of the ports for which the
   pair is linear, including two ports of one cell joined by a wire, and every naming of the
   internal wires. The internal wires of the result are existential. This makes Theorem 1
   stronger, and it is what lets Proposition 4 apply inside any net.
6. **`System.WellFormed.symm`** is now symmetry up to a permutation of the internal wires (the
   owner's change after issue #136). The older lemma `Rule.exists_symm_decomposition`
   (`InteractionCombinators/Universality/RecursionFree/DecompositionSymm.lean:94`) and `Rule.equiv_inst_comm`
   (`InteractionCombinators/Reduction/RuleInstances.lean:259`) still take the stronger hypothesis
   `Equiv r.swap.net r.net`; the `_of_symmPerm` versions in
   `InteractionCombinators/Universality/RecursionFree/SymmPerm.lean` are the ones that match page 73.
7. **Hypotheses stronger than needed.** `Invertible.compatibleWithin_one_of_wellFormed`
   (`InteractionCombinators/Translations/PairStepE.lean:617`) asks `I'.WellFormed`; linear and reduced
   rules suffice (`InteractionCombinators/Translations/PairStepEReduced.lean:94`).
   `code_decoder_package` (`InteractionCombinators/Universality/Codes/Decode.lean:239`) has an unused package
   hypothesis. Proposition 4 asks only linear rules on both sides, which is less than
   `WellFormed`.
8. **Hypotheses whose necessity was shown only in checks, or not at all.** Shown in `Checks/`:
   linearity in `Equiv.add_right`, `IsPackage` in `dup_package`, well-formedness in
   `sides_expand`, distinct names in `not_equiv_pair_of_strict`, linear sides in `plug_rename`.
   `DupFree` in `dup_package` and `copier_package` (`Checks/Misc/DupDupCheck.lean`).
9. **The translations are not computable** (`Classical.choose` in `RawSide.expand`, `symmDec`,
   `decData`; `Finite.equivFin` in `symEnum`). No translated net is evaluated; the checks are
   proofs. The bounds `L`, `M` of Theorem 1 are shown to exist with `0 < L`, not computed.
10. **`[Finite S.Sym]`** is assumed by `Universal`, `StrictlyUniversal` and the uniform bounds.
    The paper fixes a finite alphabet, so this is the paper's hypothesis.
11. **The decomposition used is not the paper's canonical one for `α`-`α` rules.** The paper gets
    `φ_{i,i} = ψ_{i,i}` from uniqueness of the canonical decomposition. The code expands the rule
    (one tree per port, `Rule.exists_expanded`) and decomposes the expanded rule. The resulting
    `Decomposition.Plugs` is up to `Equiv` and an injective renaming of internal wires.
12. **Stale documentation.** `history/PLAN.md` is the roadmap as the agents used it, kept as a
    record: its State section predates the proof of Theorem 1. Several docstrings cite
    "Section 1.3, page 72" for nets and reduction as graphs; in the paper that is Sections 1.1
    and 1.2 (Section 1.3 is the Turing machine example).
13. **Leftovers.** `codeCells_meet_gamma` (`InteractionCombinators/Universality/General/CodeCellsMeet.lean:279`)
    and `Cut.rel_count_le` (`InteractionCombinators/Reduced/CutChain.lean:487`) have no library
    user, according to the last summary.
