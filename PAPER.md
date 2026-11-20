# From the paper to the code

A reading map for the Lean 4 formalization of Yves Lafont, *Interaction Combinators*
(Information and Computation 137, 1997, journal pages 69-101; journal page `p` is page `p - 68`
of the article's PDF). For each definition, lemma, proposition, figure and theorem of the
paper it gives the Lean declaration that formalizes it, where it is, and what is known about how
closely its statement was looked at. It does not judge proofs: Lean checks those.

No line numbers are given: a declaration is named with its file.

## Legend

| In the code | In the paper | Meaning |
|---|---|---|
| `con` (`mkCon a b`) | γ | constructor, arity 2 |
| `dup` (`mkDup a b`) | δ | duplicator, arity 2 |
| `era` (`mkEra`) | ε | eraser, arity 0 |
| `Net S ν` | a net | a multiset of unordered equations `s(t, u)` between trees; a name is a wire (twice = internal, once = free port) |
| `Equiv` | equality of nets | same graph, up to wire substitution; performs no interaction. For linear nets it is isomorphism of graphs (`Net.Linear.equiv_iff_hasGraph_iso`) |
| `Step`, `Steps` (`Red` for the combinators) | | literal reduction: the active pair is one equation `α(..) = β(..)` |
| `StepE`, `StepsE` | reduction | reduction of graphs: an `Equiv` is allowed before each interaction |
| `StepsN`, `StepsEN` | "in n steps" | the same, with the number of interactions |
| `Φ.NetTr N N'` | Φ(N) | `N'` is a translation of `N` (a relation: internal wires are named freely) |

The folders. `InteractionCombinators/Core/` holds the definitions; `InteractionCombinators/Text/`
the general lemmas on texts (renaming, context, translation of a net);
`InteractionCombinators/Reduction/` Proposition 1 and normal forms;
`InteractionCombinators/Reduced/` Section 1.6; `InteractionCombinators/Translations/` Section 1.7;
`InteractionCombinators/Graphs/` the correspondence between texts and graphs;
`InteractionCombinators/Universality/` Section 2, one folder per construction, and
`InteractionCombinators/Universality/Theorem1.lean` the target. `Checks/` mirrors these folders
(examples, non-vacuity tests, adversarial reviews) plus `Checks/Misc/`; the library does not
import it. `Demo/` has unary arithmetic.

How to read the tables:

- Paths are relative to the repository root. One file per row: every name of the second column
  is declared in the file of the third.
- "Check file" is the file of examples, non-vacuity tests or adversarial review, under `Checks/`.
- **Read** says whether somebody read the *statement* (or the definition), not only its docstring:
  - **map**: read by the earlier pass that wrote the first version of this map (19 November 2026).
    The declaration has since been reformatted (one binder per line), under a gate that
    compared a fingerprint of every declaration (`docs/paper/experiment-data.md`); it was not
    re-read.
  - **fig**: read by the wire-by-wire comparison with the figures (next column).
  - **now**: read in the pass that rewrote this map (20 November 2026): the whole of
    `InteractionCombinators/Results.lean`, the definitions of `InteractionCombinators/Core/`, and
    the definitions that the statements of `Results.lean` use, and a few statements next to them.
    A library theorem marked **now** was
    read through its restatement in `Results.lean`, which Lean checks to follow from it in one
    line.
  - **no**: the row was taken from the docstring or the module header only.
  None of these marks means that a person compared the statement with the paper.
- **Figure** gives the verdict of the wire-by-wire comparison of the definition or statement with
  the picture of the paper, **equal**, **different** or **n.c.** (not comparable: the figure does not
  determine it), with the report and the item: "equal 1.6" is item 6 of
  the first of three comparison reports, 2.x is in the second and 3.x in the third (the reports
  quote figures of the paper and are not part of this repository). Empty: not compared. The
  comparison was made on 19 November 2026. The files of Sections 2.1 to 2.5 have only been
  reformatted since. Those of Section 2.6 were changed by the correction of Fig. 8, and those of
  Section 2.7 by the computable twins; the rows say so.
- Constructions of Section 2 are functions on trees: `mux ts` is M_n with the trees `ts` plugged
  into its `n` auxiliary ports, not a `PNet`. Their properties carry the rest of the net as a
  variable `Δ`.

## The statements to read first

In this order.

1. **`InteractionCombinators/Results.lean`**, the front page: 38 theorems that restate the main
   results in the order and with the numbering of the paper, each proved in one line from the
   library theorem its docstring names, and three abbreviations (`LinearRules`, `Wires`,
   `CopyOf`). Its statements are written one binder per line, in commented groups. The tables
   below give, for each of them, the library theorem behind it. Its eight sections:
   reduction (`proposition_1`, `normal_form_unique`, `normal_form_reached`); reduced nets
   (`proposition_2_exists`, `proposition_2_unique`, `reduced_iff_trees_on_wiring`,
   `reduced_closed_empty`); translations (`proposition_3`, `proposition_3_converse`,
   `invertible_iff_renaming`, `proposition_4`, `proposition_4_bounds`, `bounds_exist`,
   `bounds_pos_of_strict`, `bounds_one_of_invertible`); nets as graphs (`graph_exists`,
   `graph_unique`, `equiv_iff_graph_iso`, `graph_of_net`, `step_is_interaction`,
   `interaction_is_step`); the combinators (`combinators_wellFormed`, `multiplexor_property`,
   `autodual_multiplexor_property`, `transpositor_property`, `transpositor_involutive`,
   `lemma_2_erase_package`, `menu_selector_property`); recursion-free systems
   (`recursion_free_compatible`, `recursion_free_strict`, `recursion_free_terminates`);
   duplication and codes (`lemma_3_dup_package`, `copier_property`, `decoder_property`);
   Theorem 1 (`theorem_1`, `theorem_1_strict`, `theorem_1_explicit`, `theorem_1_bounds`).

Then the definitions these statements unfold to, in the order in which the files of
`InteractionCombinators/Core/` depend on each other.

2. `Signature`, `Term`, with `Term.vars`, `Term.bind`, `Term.cells`, `Term.subst` —
   `InteractionCombinators/Core/Term.lean`. A tree is a name or a cell `app α ts` whose root is
   the principal port and whose `i`-th auxiliary port carries `ts i`.
3. `Net`, `Net.vars`, `Net.Linear`, `Net.Below` — `InteractionCombinators/Core/Net.lean`. A net is
   a multiset of unordered pairs of trees; linear means every name occurs at most twice.
4. `Wire`, `Equiv` — `InteractionCombinators/Core/Net.lean`. One wire substitution
   `x = t, a = b  ~>  a[t/x] = b[t/x]` in a linear net; `Equiv` is the equivalence it generates.
5. `Rule`, `Rule.inst`, `Rule.Linear`, `Rule.Reduced`, `Rule.swap` —
   `InteractionCombinators/Core/System.lean`. A right member is a net over
   `Fin a ⊕ Fin b ⊕ Fin internal` (ports of the first cell, of the second, new wires).
   `Rule.Reduced` is a syntactic form: every equation has an auxiliary port on one side.
6. `System`, `Step` — `InteractionCombinators/Core/System.lean`. A partial matrix of rules; one
   interaction replaces `α(as) = β(bs)` by an instance of the rule with fresh, distinct names for
   the new wires. Equations are unordered, so a rule stored for `α, β` also fires `β, α`.
7. `System.WellFormed` — `InteractionCombinators/Core/System.lean`. Lafont's conditions on a
   system (pages 72-73, 79). Verbatim:

    ```lean
    /-- An interaction system in the sense of Lafont: rules are linear and reduced, and can be applied
    without ambiguity. -/
    structure System.WellFormed (I : System S) : Prop where
      /-- Every rule is linear. -/
      linear : ∀ α β r, I.rule α β = some r → r.Linear
      /-- Every right-hand side is a reduced net. -/
      reduced : ∀ α β r, I.rule α β = some r → r.Reduced
      /-- A rule given for `α`, `β` excludes another rule for `β`, `α`. -/
      unique : ∀ α β, α ≠ β → (I.rule α β).isSome → I.rule β α = none
      /-- A rule of a symbol with itself is symmetric: read from the other cell it is the same graph
      (Lafont 1997, page 73), that is, the same net up to wires and up to a permutation of its
      internal wires. The permutation is needed because the internal wires of a rule are named by
      `Fin r.internal`, which leaves no spare name through which `Equiv` could exchange two of them. -/
      symm :
        -- for every rule `r` of a symbol `α` with itself,
        ∀ α r, I.rule α α = some r →
          -- there is a permutation `π` of the wires created by the rule such that
          ∃ π : _root_.Equiv.Perm (Fin r.internal),
            -- the rule read from the other cell is, up to wires, the rule with its wires permuted
            Equiv r.swap.net (r.net.bind fun x => Term.var (Sum.map id (Sum.map id π) x))
    ```

8. `Steps`, `StepE`, `StepsE` — `InteractionCombinators/Core/System.lean`. `StepE I N M` says
   that some `N'` is `Equiv` to `N` and `Step I N' M`; the starred forms are reflexive-transitive
   closures.
9. `PNet`, `PNet.inst`, `PNet.Strict`, `PNet.cell` — `InteractionCombinators/Core/Translation.lean`.
   A principal net of arity `n` is a tree over `Fin n ⊕ Fin internal` in which every port occurs
   once and every internal wire twice; strict means the tree is not a single name.
10. `Translation`, `Translation.Strict`, then `Translation.TermTr`, `Translation.EqTr`,
    `Translation.NetTr` — `InteractionCombinators/Core/Translation.lean`. One principal net of the
    right arity per symbol. `N'` translates `N` when its equations translate those of `N` one for
    one (each cell replaced by an instance of its principal net, internal wires named
    arbitrarily) and `N'` is linear.
11. `Translation.Compatible` — `InteractionCombinators/Core/Translation.lean`. The property of
    page 81. Verbatim:

    ```lean
    /-- A translation of interaction systems (Lafont, Section 1.7): for every rule, the translations of
    the two cells, plugged by their roots, reduce to a translation of the right-hand side. The
    auxiliary ports of the two cells are the names `xs` and `ys`. Reduction is up to wires
    (`StepsE`): cells whose principal ports are joined by a named wire may interact. -/
    def Compatible
        -- the translation: a principal net over `S'` for each symbol of `S`
        (Φ : Translation S S')
        -- the system that is translated, over `S`
        (I : System S)
        -- the system it is translated into, over `S'`
        (I' : System S') :
        Prop :=
      -- for all symbols `α`, `β` of `S` and every net `r` such that
      ∀ (α β : S.Sym) (r : Rule S (S.arity α) (S.arity β)),
        -- `r` is the right-hand side of the rule of `I` for an `α` cell against a `β` cell,
        I.rule α β = some r →
        ∀
          -- for all names `xs` of the auxiliary ports of the `α` cell,
          (xs : Fin (S.arity α) → ℕ)
          -- all names `ys` of the auxiliary ports of the `β` cell,
          (ys : Fin (S.arity β) → ℕ)
          -- all names `f` of the internal wires of the translation of `α`,
          (f : Fin (Φ.net α).internal → ℕ)
          -- and all names `g` of the internal wires of the translation of `β`,
          (g : Fin (Φ.net β).internal → ℕ),
          -- if the translation of `α` plugged by its root into the root of the translation of `β`
          -- is a linear net, that is, if no name among `xs`, `ys`, `f`, `g` occurs more than twice,
          Net.Linear ({s((Φ.net α).inst (fun i => .var (xs i)) f,
            (Φ.net β).inst (fun j => .var (ys j)) g)} : Net S' ℕ) →
          -- then there are two nets `M`, `N'` over `S'`, and names `h` for the wires created by the
          -- rule, such that
          ∃ (M N' : Net S' ℕ) (h : Fin r.internal → ℕ),
            -- in `I'`, the two translations plugged by their roots reduce, up to wires, to `M`,
            StepsE I' {s((Φ.net α).inst (fun i => .var (xs i)) f,
              (Φ.net β).inst (fun j => .var (ys j)) g)} M ∧
            -- `M` is the same graph as `N'`,
            Equiv M N' ∧
            -- and `N'` is a translation of the right-hand side of the rule, taken with the same
            -- names `xs` and `ys` on the auxiliary ports of the two cells and with `h` on its wires
            Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N'
    ```

12. `Universal`, `StrictlyUniversal` — `InteractionCombinators/Core/Translation.lean`. Verbatim,
    the strict one; `Universal` is the same without `Φ.Strict`:

    ```lean
    /-- A strictly universal interaction system: every interaction system over a finite alphabet has a
    strict translation into it. Strictness excludes translations that erase cells by turning them into
    wires, so every interaction of the source costs at least one interaction of the target. -/
    def StrictlyUniversal
        -- the system, over the signature `S'`
        (I' : System S') :
        Prop :=
      ∀
        -- for every signature `S`
        (S : Signature)
        -- with finitely many symbols,
        [Finite S.Sym]
        -- and every system `I` over `S`
        (I : System S),
        -- that is an interaction system in the sense of Lafont,
        I.WellFormed →
        -- there is a translation `Φ` of the symbols of `S` into principal nets over `S'`
        ∃ Φ : Translation S S',
          -- that translates no symbol to a single wire,
          Φ.Strict ∧
          -- and that is a translation of the interaction system `I` into `I'`
          Φ.Compatible I I'
    ```

13. `Comb`, `sig`, `mkCon`, `mkDup`, `mkEra`, the rules `ruleConCon`, `ruleDupDup`, `ruleEraEra`,
    `ruleEraBin`, `ruleConDup`, the system `system`, and `CNet`, `Red` —
    `InteractionCombinators/Core/Combinators.lean`. Fig. 2. Compare port by port with the figure:
    `con`-`con` exchanges the ports, `dup`-`dup` does not.
14. `End`, `Graph`, `Graph.WF`, `Graph.Iso`, `Graph.raw`, `Graph.Contract`, `Net.HasGraph` —
    `InteractionCombinators/Core/Graph.lean`. The graph of a net: read the raw graph off a text,
    then erase every name that ends two wires. Needed only for Section 4 of `Results.lean`.
15. `universal` and `universal_strict` — `InteractionCombinators/Universality/Theorem1.lean`.
    Theorem 1, as `Universal system` and `StrictlyUniversal system`. Proved in
    `InteractionCombinators/Universality/General/CodeCompatible.lean` (`universal'`,
    `universal_strict'`).

The definitions outside `InteractionCombinators/Core/` that the statements of `Results.lean` use:
`StepE.Normal` (`InteractionCombinators/Reduction/NormalFormE.lean`); `StepsEN`,
`Translation.CompatibleWithin` (`InteractionCombinators/Translations/SimulationCount.lean`);
`Net.HasCut` (`InteractionCombinators/Reduced/Cut.lean`); `Net.HasVicious`, `Net.IsReduced`
(`InteractionCombinators/Reduced/Vicious.lean`); `Net.IsTreesOnWiring`
(`InteractionCombinators/Reduced/ReducedDecomp.lean`); `Net.IsTreesOnWiringN`
(`InteractionCombinators/Reduced/ReducedDecompUnique.lean`); `PNet.Iso`, `Translation.comp`,
`Translation.Invertible` (`InteractionCombinators/Translations/TranslationComp.lean`);
`Translation.renPermTr` (`InteractionCombinators/Translations/TranslationRenPerm.lean`);
`Graph.Interact` (`InteractionCombinators/Graphs/GraphStep.lean`); `Term.IsPackage`
(`InteractionCombinators/Universality/Menus/Package.lean`); `DupFree`
(`InteractionCombinators/Universality/Duplication/Duplication.lean`); `System.RecursionFreeData`,
`System.RecursionFree`, `Decomposition.Plugs`
(`InteractionCombinators/Universality/RecursionFree/RecursionFree.lean`); `ExpSide`
(`InteractionCombinators/Universality/RecursionFree/RecursionFreeSide.lean`); `System.SidesPlug`
(`InteractionCombinators/Universality/General/CodeCompatibleSides.lean`); `System.DecData`
(`InteractionCombinators/Universality/General/CodeData.lean`); and the constructions `mux`,
`muxStar`, `autoMux`, `transpositorPerm`, `menu`, `selector`, `copier`, `code`, `decoder`,
`codeTranslation`, `codeTranslationE`, which are in the tables of Section 2 below.

## Section 1.1, Nets (pages 71-72)

| Paper item | Lean declaration | File | Check file | Read | Figure | Notes |
|---|---|---|---|---|---|---|
| Symbol with arity, cell, ports (p. 71) | `Signature`, `Term` | `InteractionCombinators/Core/Term.lean` | | map, now | | A cell exists only as the root of a tree. |
| Tree, root (p. 72) | `Term.vars`, `Term.bind`, `Term.cells`, `Term.subst` | `InteractionCombinators/Core/Term.lean` | | map, now | | |
| Net: cells, free ports, wires, cyclic wires (p. 71-72) | `Net`, `Net.vars`, `Net.cells`, `Net.bind`, `Net.Linear`, `Net.Below` | `InteractionCombinators/Core/Net.lean` | | map, now | | Textual. A cyclic wire is the equation `x = x`. |
| Same net (graph equality) | `Wire`, `Equiv`, `Equiv.cells_eq`, `Equiv.free_iff`, `Equiv.linear_iff` | `InteractionCombinators/Core/Net.lean` | | map, now | | The two definitions were read now; the three lemmas by the earlier map. |
| Renaming of internal wires gives the same net | `Net.equiv_rename` | `InteractionCombinators/Text/Rename.lean` | | no | | |
| The same, several names at once | `Net.equiv_bind_var` | `InteractionCombinators/Text/RenameMany.lean` | | no | | |
| Equality of nets is closed under context | `Equiv.add_right` | `InteractionCombinators/Text/EquivAdd.lean` | `Checks/Misc/WantedCheck.lean` | no | | |
| A net as a graph: cells, ports, wires (p. 71) | `End`, `Graph`, `Graph.ends`, `Graph.WF`, `Graph.free`, `Graph.Iso`, `Graph.raw`, `Graph.Contract`, `Net.ofList`, `Net.HasGraph` | `InteractionCombinators/Core/Graph.lean` | `Checks/Core/GraphCheck.lean`, `Checks/Core/GraphReview.lean` | now | | Port `0` of a cell is the principal one, port `i + 1` the `i`-th auxiliary. `loops` counts cyclic wires. |
| The raw graph of a text | `Graph.wireEnds`, `Graph.raw_ends`, `Graph.raw_port`, `Graph.raw_cell`, `Graph.raw_count_name` | `InteractionCombinators/Graphs/GraphRaw.lean` | `Checks/Graphs/GraphRawCheck.lean` | no | | |
| **Every net has a graph**, and it is well formed | `Net.exists_graph`, `Net.Linear.exists_graph`, `Net.HasGraph.wf` | `InteractionCombinators/Graphs/GraphContract.lean` | `Checks/Graphs/GraphContractCheck.lean` | now | | `Results.lean`: `graph_exists`. Any type of names with decidable equality; no linearity. |
| The order of contraction does not matter | `Graph.contracts_unique` | `InteractionCombinators/Graphs/GraphContractUnique.lean` | `Checks/Graphs/GraphContractUniqueCheck.lean` | no | | |
| **The graph of a linear net is unique** up to the identity of the cells | `Net.Linear.hasGraph_iso` | `InteractionCombinators/Graphs/GraphIso.lean` | `Checks/Graphs/GraphIsoCheck.lean` | now | | `Results.lean`: `graph_unique`. |
| A wire substitution keeps the graph | `Wire.hasGraph_iso` | `InteractionCombinators/Graphs/GraphEquiv.lean` | `Checks/Graphs/GraphEquivCheck.lean` | no | | One direction of the next row. |
| **`Equiv` is isomorphism of graphs** | `Net.Linear.equiv_of_hasGraph_iso`, `Net.Linear.equiv_iff_hasGraph_iso` | `InteractionCombinators/Graphs/GraphIsoEquiv.lean` | `Checks/Graphs/GraphIsoEquivCheck.lean` | now | | `Results.lean`: `equiv_iff_graph_iso`. Linear nets over `ℕ`. |
| **Every well-formed graph is the graph of a linear net** | `Graph.WF.exists_net`, `Graph.WF.exists_net_free`, `Graph.WF.hasGraph_flatB` | `InteractionCombinators/Graphs/GraphRealize.lean` | `Checks/Graphs/GraphRealizeCheck.lean` | now | | `Results.lean`: `graph_of_net`. Up to `Graph.Iso`, with the same free ports. |
| Wiring; wiring of a permutation σ (p. 72) | no type. A wiring appears as a multiset of names (`erase_wiring`, `dup_wiring`), as equations `ts i = us (σ i)`, or as `TranspositorConverse.wiring` | | | | | not a declaration |

## Section 1.2, Interaction (page 73)

| Paper item | Lean declaration | File | Check file | Read | Figure | Notes |
|---|---|---|---|---|---|---|
| Interaction rule, right member | `Rule`, `Rule.inst`, `Rule.Linear` | `InteractionCombinators/Core/System.lean` | | map, now | | |
| The right member read from the other cell | `Rule.swap` | `InteractionCombinators/Core/System.lean` | `Checks/Universality/RecursionFree/SymmPermReview.lean` | map, now | | |
| Interaction system; "no other rule for α_i, α_j or α_j, α_i" | `System`, `System.WellFormed.unique` | `InteractionCombinators/Core/System.lean` | | map, now | | One orientation is stored; `Step` fires both because equations are unordered. |
| "if α_i interacts with itself then the right member is symmetric" | `System.WellFormed.symm` | `InteractionCombinators/Core/System.lean` | `Checks/Universality/RecursionFree/SymmPermCheck.lean`, `Checks/Universality/RecursionFree/SymmPermReview.lean` | map, now | | Up to `Equiv` and a permutation of the internal wires. |
| The same condition, named | `Rule.SymmPerm`, `Rule.SymmPerm.of_equiv` | `InteractionCombinators/Universality/RecursionFree/SymmPerm.lean` | `Checks/Universality/RecursionFree/SymmPermCheck.lean` | map | | Same formula as the field `symm`. |
| One step of reduction | `Step`, `Steps`, `StepE`, `StepsE` | `InteractionCombinators/Core/System.lean` | `Checks/Translations/SimulationECheck.lean` | map, now | | |
| Reduction keeps nets well formed | `Step.linear`, `StepsE.linear` | `InteractionCombinators/Core/System.lean` | | no | | |
| Reduction is local (context) | `Step.add_right` | `InteractionCombinators/Core/System.lean` | | no | | |
| Reduction of graphs is local | `StepE.add_right`, `StepsE.add_right` | `InteractionCombinators/Text/StepsEAdd.lean` | `Checks/Text/StepsEAddCheck.lean` | no | | The result is reached up to a renaming of new wires. |
| Reduction does not depend on names | `Step.bind_var`, `Steps.bind_var` | `InteractionCombinators/Text/RenameStep.lean` | | no | | |
| Proposition 1, two different active pairs | `Step.commute` | `InteractionCombinators/Reduction/Commute.lean` | | map | | |
| Proposition 1, the same pair fired twice the same way | `Rule.equiv_inst_same` | `InteractionCombinators/Reduction/RuleInstances.lean` | | no | | |
| Proposition 1, the same pair α-α read both ways | `equiv_inst_swap` | `InteractionCombinators/Reduction/StrongConfluence.lean` | | map | | |
| Proposition 1 for literal steps | `Step.strong_confluence` | `InteractionCombinators/Reduction/StrongConfluence.lean` | | map | | `Step` only: a named wire between two principal ports is not an active pair here. |
| **Proposition 1** (strong confluence) | `StepE.strong_confluence` | `InteractionCombinators/Reduction/StrongConfluenceE.lean` | `Checks/Reduction/StrongConfluenceECheck.lean`, `Checks/Reduction/StrongConfluenceEReview.lean` | map, now | | `Results.lean`: `proposition_1`. The disjunction `Equiv P P' ∨ …` replaces the hypothesis "P ≠ P'" of the paper. |
| Proposition 1 without the condition that right members are reduced | `Step.strong_confluence_of`, `StepE.strong_confluence_of` | `InteractionCombinators/Reduction/StrongConfluenceNoReduced.lean` | `Checks/Reduction/StrongConfluenceNoReducedCheck.lean` | no | | Hypotheses: the fields `linear`, `unique`, `symm` of `System.WellFormed`. |
| Irreducible net | `StepE.Normal`, `StepE.Normal.of_equiv` | `InteractionCombinators/Reduction/NormalFormE.lean` | `Checks/Reduction/NormalFormECheck.lean` | now | | The definition was read; the lemma was not. |
| **Consequence of Proposition 1**: one normal form, one length (p. 73-74) | `StepsEN.normal_of_stepsEN`, `StepsEN.le_of_normal`, `StepsEN.normal_unique` | `InteractionCombinators/Reduction/NormalFormE.lean` | `Checks/Reduction/NormalFormECheck.lean`, `Checks/Reduction/NormalFormEReview.lean` | now | | `Results.lean`: `normal_form_unique`, `normal_form_reached`. `StepsEN.le_of_normal` was not read. |
| Irreducible is "no cut" when every pair of symbols has a rule | `StepE.Normal.iff_not_hasCut`, `Comb.system_complete`, `Comb.normal_iff_not_hasCut` | `InteractionCombinators/Reduction/NormalFormCut.lean` | | no | | Not in the paper as a statement. |
| Interaction on graphs (p. 73) | `Graph.Interact`, `Graph.cutEnd`, `End.map`, `Graph.Interact.wf` | `InteractionCombinators/Graphs/GraphStep.lean` | `Checks/Graphs/GraphStepCheck.lean`, `Checks/Graphs/GraphStepReview.lean` | now | | Cut the pair, glue a graph of the rule, contract. The definition and `Graph.Interact.wf` were read. For a rule that is not linear, well-formedness does not mean the free ports are kept. |
| **A step of the text is an interaction of the graph** | `Net.Linear.stepE_interact` | `InteractionCombinators/Graphs/GraphStepE.lean` | `Checks/Graphs/GraphStepECheck.lean`, `Checks/Graphs/GraphStepEReview.lean` | now | | `Results.lean`: `step_is_interaction`. Rules linear; shown necessary in the review file. |
| **An interaction of the graph is a step of the text** | `Net.Linear.interact_stepE` | `InteractionCombinators/Graphs/GraphStepEConverse.lean` | `Checks/Graphs/GraphStepEConverseCheck.lean`, `Checks/Graphs/GraphStepEConverseReview.lean` | now | | `Results.lean`: `interaction_is_step`. |
| The result of an interaction is unique | `Graph.interact_unique`, `Graph.preInteract` | `InteractionCombinators/Graphs/GraphInteractUnique.lean` | `Checks/Graphs/GraphStepEConverseReview.lean` | now | | For a given pair of a well-formed graph and a linear rule. Not in `Results.lean`. `Graph.preInteract` was not read. |

## Sections 1.3 to 1.5, Examples (pages 74-78)

Turing machines (Section 1.3) and cellular automata (Section 1.4): not formalized. Unary
arithmetic (Section 1.5, pages 76-77, and Fig. 1 on page 78) is in `Demo/`, see "The demo" below.

## Section 1.6, Reduced nets (pages 77-80)

| Paper item | Lean declaration | File | Check file | Read | Figure | Notes |
|---|---|---|---|---|---|---|
| Cut (p. 77) | `Net.HasCut`, `Net.HasCut.of_equiv` | `InteractionCombinators/Reduced/Cut.lean` | `Checks/Reduced/CutCheck.lean` | map, now | | "Some `Equiv` net has an equation between two cells." |
| Cut, without the quantifier over `Equiv` nets | `ChainCut`, `hasCut_iff_chainCut` | `InteractionCombinators/Reduced/CutChain.lean` | `Checks/Reduced/CutCheck.lean` | no | | |
| Principal path (p. 78-79) | `Path` | `InteractionCombinators/Reduced/Vicious.lean` | `Checks/Reduced/ViciousCheck.lean` | no | | Auxiliary; used only inside the proofs about circles. |
| Vicious circle, cyclic wire (p. 79) | `Net.HasVicious`, `ChainVicious`, `hasVicious_iff_chainVicious` | `InteractionCombinators/Reduced/Vicious.lean` | `Checks/Reduced/ViciousCheck.lean`, `Checks/Reduced/ViciousReview.lean` | map, now | | `Net.HasVicious` was read: some `Equiv` net has `x = t` with `x` a leaf of `t`. |
| Reduced net (p. 79) | `Net.IsReduced` | `InteractionCombinators/Reduced/Vicious.lean` | `Checks/Reduced/ViciousReview.lean` | map, now | | |
| "Trees are typical examples of reduced nets" | `isReduced_tree` | `InteractionCombinators/Reduced/Vicious.lean` | | map | | |
| "All right members of rules are reduced nets" (p. 79) | `Rule.Reduced`, `System.WellFormed.reduced` | `InteractionCombinators/Core/System.lean` | `Checks/Translations/SimulationInvertibleReview.lean` | map, now | | Syntactic form, not `Net.IsReduced`: see the next row and the caveats. |
| The syntactic form and the reduced nets agree on instances | `Rule.Reduced.isTreesOnWiring_inst`, `Rule.Reduced.isReduced_inst`, `Rule.exists_reduced_of_isReduced` | `InteractionCombinators/Reduced/RuleReduced.lean` | `Checks/Reduced/RuleReducedCheck.lean`, `Checks/Reduced/RuleReducedReview.lean` | no | | Both directions, for distinct port names. |
| An instance of a reduced right member has no cut | `Rule.not_hasCut_inst` | `InteractionCombinators/Translations/SimulationStrict.lean` | `Checks/Translations/SimulationStrictCheck.lean` | no | | For distinct names on the ports. |
| The form "trees on a wiring" | `Net.IsTreesOnWiring`, `Net.IsTreesOnWiring.isReduced` | `InteractionCombinators/Reduced/ReducedDecomp.lean` | `Checks/Reduced/ReducedDecompCheck.lean`, `Checks/Reduced/ReducedDecompReview.lean` | now | | Every equation is `x = t` with `x` a free port. The definition was read. |
| **Proposition 2**, existence, and the converse | `Net.IsReduced.exists_treesOnWiring`, `Net.isReduced_iff_exists_treesOnWiring` | `InteractionCombinators/Reduced/ReducedDecomp.lean` | `Checks/Reduced/ReducedDecompCheck.lean`, `Checks/Reduced/ReducedDecompReview.lean` | now | | `Results.lean`: `reduced_iff_trees_on_wiring`. |
| **Proposition 2**, existence in normal form, and uniqueness | `Net.IsTreesOnWiringN`, `Net.IsReduced.exists_treesOnWiringN`, `Net.IsTreesOnWiringN.unique` | `InteractionCombinators/Reduced/ReducedDecompUnique.lean` | `Checks/Reduced/ReducedDecompUniqueCheck.lean`, `Checks/Reduced/ReducedDecompUniqueReview.lean` | now | | `Results.lean`: `proposition_2_exists`, `proposition_2_unique`. Unique up to an injective renaming that keeps the free ports. `unique` does not assume linearity. |
| Principal net of arity n, root, degenerate case (p. 79-80) | `PNet`, `PNet.inst`, `PNet.Strict`, `PNet.cell` | `InteractionCombinators/Core/Translation.lean` | | map, now | | |
| Lemma 1 (principal paths of a principal net) | none | | | | | Not needed: a `PNet` is a tree, the path is a branch. |
| **"A reduced net with no free port is empty"** (p. 80) | `Net.IsReduced.eq_zero_of_closed` | `InteractionCombinators/Reduced/ReducedClosed.lean` | `Checks/Reduced/ReducedClosedCheck.lean` | now | | `Results.lean`: `reduced_closed_empty`. |
| Package (p. 80) | `Term.IsPackage` | `InteractionCombinators/Universality/Menus/Package.lean` | `Checks/Universality/Menus/PackageCheck.lean` | map, fig, now | equal 1.16 | A tree in which every name occurs exactly twice. |

## Section 1.7, Translations (pages 80-81)

| Paper item | Lean declaration | File | Check file | Read | Figure | Notes |
|---|---|---|---|---|---|---|
| Translation, strict translation | `Translation`, `Translation.Strict` | `InteractionCombinators/Core/Translation.lean` | | map, now | | |
| "A translation extends to nets" | `Translation.TermTr`, `Translation.EqTr`, `Translation.NetTr` | `InteractionCombinators/Core/Translation.lean` | | map, now | | A relation, because of the names of the new wires. |
| Every linear net has a translation | `Translation.exists_netTr`, `Translation.trTerm` | `InteractionCombinators/Text/TranslationExists.lean` | `Checks/Text/TranslationExistsCheck.lean` | map | | |
| Two translations of a net are the same net | `Translation.NetTr.equiv` | `InteractionCombinators/Text/NetTrEquiv.lean` | `Checks/Text/NetTrEquivCheck.lean`, `Checks/Misc/WantedCheck.lean` | map | | |
| Equal nets have equal translations | `Translation.NetTr.of_equiv` | `InteractionCombinators/Text/NetTrWire.lean` | `Checks/Text/NetTrWireCheck.lean` | map | | |
| Prop. 3, "if Φ(ν) contains a cut, so does ν" | `Translation.NetTr.hasCut_reflect` | `InteractionCombinators/Reduced/CutChain.lean` | `Checks/Reduced/CutCheck.lean` | no | | |
| Prop. 3, "if Φ is strict and ν contains a cut, so does Φ(ν)" | `Translation.NetTr.hasCut_of_strict` | `InteractionCombinators/Reduced/Cut.lean` | `Checks/Reduced/CutCheck.lean` | no | | |
| Prop. 3, "if ν contains a vicious circle, so does Φ(ν)" | `Translation.NetTr.hasVicious` | `InteractionCombinators/Reduced/Vicious.lean` | `Checks/Reduced/ViciousCheck.lean` | map | | |
| Prop. 3, "if Φ(ν) contains a vicious circle, ν contains a vicious circle or a cut" | `Translation.NetTr.hasVicious_reflect` | `InteractionCombinators/Reduced/ViciousReflect.lean` | `Checks/Reduced/ViciousReflectCheck.lean` | no | | |
| **Proposition 3** and its converse for strict Φ | `Translation.NetTr.isReduced`, `Translation.NetTr.isReduced_of_strict` | `InteractionCombinators/Reduced/ViciousReflect.lean` | `Checks/Reduced/ViciousReflectCheck.lean`, `Checks/Reduced/ViciousReview.lean` | map, now | | `Results.lean`: `proposition_3`, `proposition_3_converse`. No extra hypothesis. |
| Composition of translations | `Translation.trPNet`, `Translation.comp`, `Translation.comp_id`, `Translation.id_comp` | `InteractionCombinators/Translations/TranslationComp.lean` | `Checks/Translations/TranslationCompCheck.lean`, `Checks/Translations/TranslationCompReview.lean` | map, now | | The definitions were read now; they go through `Translation.trTerm`. |
| Translating by Ψ ∘ Φ is translating twice | `Translation.NetTr.comp` | `InteractionCombinators/Translations/TranslationCompTr.lean` | `Checks/Translations/TranslationCompTrCheck.lean`, `Checks/Translations/TranslationCompTrReview.lean` | map | | |
| Composition is associative, respects equality | `Translation.comp_iso_right`, `Translation.comp_iso_left`, `Translation.comp_assoc` | `InteractionCombinators/Translations/TranslationCompAssoc.lean` | `Checks/Translations/TranslationCompAssocCheck.lean` | map | | `Translation.comp_assoc` was read. Up to `PNet.Iso`. |
| Equality of principal nets; invertible translation | `PNet.Iso`, `Translation.Invertible`, `Translation.invertible_id` | `InteractionCombinators/Translations/TranslationComp.lean` | `Checks/Translations/TranslationCompCheck.lean` | now | | The two definitions were read. The equalities of page 80 are read up to the names of internal wires. |
| Composite of invertibles is invertible | `Translation.Invertible.comp` | `InteractionCombinators/Translations/TranslationCompAssoc.lean` | `Checks/Translations/TranslationCompAssocCheck.lean` | no | | |
| Invertible ⇒ a renaming of symbols and a permutation of ports (p. 81, top) | `Translation.Invertible.net_eq`, `Translation.Invertible.symEquiv`, `Translation.Invertible.exists_symEquiv` | `InteractionCombinators/Translations/TranslationInvertible.lean` | `Checks/Translations/TranslationInvertibleCheck.lean`, `Checks/Translations/TranslationInvertibleReview.lean` | map | | |
| **The invertible translations**: the converse and the characterization (p. 81) | `PNet.permCell`, `Translation.renPermTr`, `Translation.renPermTr_invertible`, `Translation.invertible_iff_renPermTr` | `InteractionCombinators/Translations/TranslationRenPerm.lean` | `Checks/Translations/TranslationInvertibleReview.lean` | now | | `Results.lean`: `invertible_iff_renaming`. The two definitions and the last theorem were read. |
| Translation of interaction systems (the diagram of p. 81) | `Translation.Compatible`, `Translation.id_compatible` | `InteractionCombinators/Core/Translation.lean` | `Checks/Universality/General/CodeCompatibleReview.lean` | map, now | | Quantifies over every linear naming: more than the paper asks. |
| The same with any relation in place of →* | `Translation.CompatibleBy`, `Translation.compatible_iff_compatibleBy`, `Translation.CompatibleByDistinct` | `InteractionCombinators/Translations/Simulation.lean` | `Checks/Translations/SimulationCheck.lean` | map | | `Translation.CompatibleBy` was read. |
| Composite of two translations of systems | `Translation.Compatible.comp` | `InteractionCombinators/Translations/TranslationCompCompatible.lean` | `Checks/Translations/TranslationCompCompatibleCheck.lean` | map | | Rules of the middle and target systems linear. |
| L, M: least and greatest length | `StepsN`, `StepsEN`, `Translation.CompatibleWithin` | `InteractionCombinators/Translations/SimulationCount.lean` | `Checks/Translations/SimulationCountCheck.lean` | map, now | | `L ≤ k ≤ M` for every rule and naming; bounds, not shown attained. |
| **L, M exist** (finite alphabet); **L > 0 if Φ is strict** | `Translation.Compatible.exists_length`, `Translation.Compatible.len`, `Translation.Compatible.compatibleWithin_len`, `Translation.Compatible.exists_compatibleWithin`, `Translation.Compatible.exists_compatibleWithin_pos` | `InteractionCombinators/Translations/SimulationUniform.lean` | `Checks/Translations/SimulationUniformCheck.lean`, `Checks/Translations/SimulationUniformReview.lean` | map, now | | `Results.lean`: `bounds_exist`, `bounds_pos_of_strict` (the last two names). |
| "L > 0 if Φ is strict", for given bounds | `Translation.CompatibleWithin.distinct_pos`, `Translation.CompatibleWithin.pos` | `InteractionCombinators/Translations/SimulationStrict.lean` | `Checks/Translations/SimulationStrictCheck.lean`, `Checks/Translations/SimulationCorollaryReview.lean` | map | | `pos` was read. Its conclusion is `CompatibleWithin` with `max L 1`. |
| "L = M = 1 if Φ is invertible" | `Translation.Invertible.compatibleWithin_one_of_wellFormed` | `InteractionCombinators/Translations/PairStepE.lean` | `Checks/Translations/SimulationInvertibleCheck.lean`, `Checks/Translations/SimulationInvertibleReview.lean` | map | | Asks that the target system be well formed, more than it uses. |
| **"L = M = 1 if Φ is invertible"** from linear and reduced rules only | `Translation.Invertible.compatibleWithin_one_of_linear_reduced`, `Translation.Invertible.compatibleWithin_one_of_reduced` | `InteractionCombinators/Translations/PairStepEReduced.lean` | | map, now | | `Results.lean`: `bounds_one_of_invertible` (the first name). Examples in the same file. |
| Proposition 4, one step | `Translation.Compatible.step` | `InteractionCombinators/Translations/Simulation.lean` | `Checks/Translations/SimulationCheck.lean` | map | | |
| Proposition 4, without counts, literal source | `Translation.Compatible.steps` | `InteractionCombinators/Translations/Simulation.lean` | `Checks/Translations/SimulationCheck.lean` | map | | |
| Proposition 4 with counts, literal source | `Translation.CompatibleWithin.steps` | `InteractionCombinators/Translations/SimulationCount.lean` | `Checks/Translations/SimulationCountCheck.lean` | map | | |
| **Proposition 4**, without and with the lengths | `Translation.Compatible.stepsE`, `Translation.CompatibleWithin.stepsEN` | `InteractionCombinators/Translations/SimulationE.lean` | `Checks/Translations/SimulationECheck.lean` | map, now | | `Results.lean`: `proposition_4`, `proposition_4_bounds`. Rules of both systems linear; Φ(M) reached up to `Equiv`. |

## Section 2.1, The system (pages 81-82)

| Paper item | Lean declaration | File | Check file | Read | Figure | Notes |
|---|---|---|---|---|---|---|
| The three combinators | `Comb`, `sig`, `mkCon`, `mkDup`, `mkEra` | `InteractionCombinators/Core/Combinators.lean` | | map, now | | |
| Fig. 2, `con`-`con` | `ruleConCon`, `step_con_con` | `InteractionCombinators/Core/Combinators.lean` | `Checks/Universality/Codes/CodeFig8Review.lean` | map, fig, now | equal 1.1 | Exchanges the ports. |
| Fig. 2, `dup`-`dup` | `ruleDupDup`, `step_dup_dup` | `InteractionCombinators/Core/Combinators.lean` | `Checks/Universality/Codes/CodeFig8Review.lean` | map, fig, now | equal 1.2 | Does not exchange them. |
| Fig. 2, `era`-`era` | `ruleEraEra`, `step_era_era` | `InteractionCombinators/Core/Combinators.lean` | | map, fig, now | equal 1.3 | |
| Fig. 2, `era`-`con` and `era`-`dup` | `ruleEraBin`, `step_era_con`, `step_era_dup` | `InteractionCombinators/Core/Combinators.lean` | | map, fig, now | equal 1.4 | One rule for both. |
| Fig. 2, `con`-`dup`; the system | `ruleConDup`, `step_con_dup`, `system` | `InteractionCombinators/Core/Combinators.lean` | `Checks/Universality/General/CodeCompatibleReview.lean` | map, fig, now | equal 1.5 | Stored orientations: `era`-`con`, `era`-`dup`, `con`-`dup`. |
| **"The symmetry condition is satisfied"** | `system_wellFormed` | `InteractionCombinators/Core/Combinators.lean` | | map, now | | `Results.lean`: `combinators_wellFormed`. |
| Nets of combinators, literal reduction | `CNet`, `Red` | `InteractionCombinators/Core/Combinators.lean` | | now | | |
| Fig. 3, a net that reduces to itself in four steps | none | | | | | Not formalized. |
| **Theorem 1** (stated p. 82) | `universal`, `universal_strict` | `InteractionCombinators/Universality/Theorem1.lean` | `Checks/Universality/General/CodeCompatibleReview.lean` | map, now | | `Results.lean`: `theorem_1`, `theorem_1_strict`. See Section 2.7 below. |

## Section 2.2, Multiplexors and transpositors (pages 82-84)

| Paper item | Lean declaration | File | Check file | Read | Figure | Notes |
|---|---|---|---|---|---|---|
| Fig. 4, M_n | `mux` | `InteractionCombinators/Universality/Multiplexors/Multiplexor.lean` | `Checks/Universality/Multiplexors/BasicCheck.lean` | map, fig | equal 1.6 | Compared for n = 0, 1, 2, 3. M_0 is `era`, M_1 a wire, nested to the right. |
| Fig. 4, M_n* | `muxStar` | `InteractionCombinators/Universality/Multiplexors/Multiplexor.lean` | `Checks/Universality/Multiplexors/BasicCheck.lean` | map, fig | equal 1.7 | Compared for n = 0, 1, 2, 3. The mirror image, not the rotation. |
| **Property of the multiplexors** | `mux_muxStar` | `InteractionCombinators/Universality/Multiplexors/Multiplexor.lean` | `Checks/Universality/Multiplexors/BasicCheck.lean` | map, fig, now | equal 1.8 | `Results.lean`: `multiplexor_property`. Literal `Red`; result `ts[i] = us[i]`. |
| "Our implementation does not use δ" | `dupFree_mux`, `dupFree_muxStar` | `InteractionCombinators/Universality/Codes/Code.lean` | | no | | |
| Fig. 5, autodual T_n | `autoMux` | `InteractionCombinators/Universality/Multiplexors/AutoMux.lean` | `Checks/Universality/Multiplexors/AutoMuxCheck.lean` | map, fig | equal 1.9 | Same shape as `mux`, with `dup`. |
| **Property of T_n** | `autoMux_autoMux` | `InteractionCombinators/Universality/Multiplexors/AutoMux.lean` | `Checks/Universality/Multiplexors/AutoMuxCheck.lean` | map, fig, now | equal 1.10 | `Results.lean`: `autodual_multiplexor_property`. Literal `Red`. |
| Transpositor T_{p,q} (p. 83) | `pairCon`, `transpositor` | `InteractionCombinators/Universality/Multiplexors/Transpositor.lean` | `Checks/Universality/Multiplexors/TranspositorCheck.lean` | map, fig | equal 1.11 | Six instances. Accepts lists shorter than 2p, outside the paper. |
| The permutation ι_{p,q}; property of T_{p,q} | `swapPairs`, `transpositor_transpositor` | `InteractionCombinators/Universality/Multiplexors/Transpositor.lean` | `Checks/Universality/Multiplexors/TranspositorCheck.lean` | map, fig | equal 1.12 | Literal `Red`. |
| ι_{p,q} as a permutation | `swapPerm` | `InteractionCombinators/Universality/Multiplexors/TranspositorPerm.lean` | `Checks/Universality/Multiplexors/TranspositorPermCheck.lean` | no | | |
| "σ = ρ⁻¹ ∘ ι_{p,q} ∘ ρ" (p. 84) | `involutive_decomp` | `InteractionCombinators/Universality/Multiplexors/TranspositorPerm.lean` | `Checks/Universality/Multiplexors/TranspositorPermCheck.lean` | map, fig | n.c. 1.14 | The figure does not say in which direction the box ρ is read. |
| T_σ for an involution σ | `portList`, `transpositorPerm` | `InteractionCombinators/Universality/Multiplexors/TranspositorPerm.lean` | `Checks/Universality/Multiplexors/TranspositorPermCheck.lean` | map, fig | equal 1.13 | Equal up to the choice of ρ, which the paper leaves free. |
| **Property of T_σ** | `transpositorPerm_transpositorPerm` | `InteractionCombinators/Universality/Multiplexors/TranspositorPerm.lean` | `Checks/Universality/Multiplexors/TranspositorPermCheck.lean` | map, fig, now | equal 1.15 | `Results.lean`: `transpositor_property`. Result `ts i = us (σ i)`. |
| **"Conversely, if such a T_σ exists, σ is involutive"** | `TranspositorConverse.wiring`, `involutive_of_transpositor` | `InteractionCombinators/Universality/Multiplexors/TranspositorConverse.lean` | `Checks/Universality/Multiplexors/TranspositorConverseCheck.lean` | now | | `Results.lean`: `transpositor_involutive`. Stated in any interaction system, for a principal net. |

## Section 2.3, Menus and selectors (pages 84-85)

| Paper item | Lean declaration | File | Check file | Read | Figure | Notes |
|---|---|---|---|---|---|---|
| Menu and selector | `menu`, `selector` | `InteractionCombinators/Universality/Menus/Menu.lean` | `Checks/Universality/Menus/MenuCheck.lean` | fig | equal 1.20 | Compared for n = 1, 2, 3 and every index. The index counts from 0. |
| A menu of packages is a package | `IsPackage.menu` | `InteractionCombinators/Universality/Menus/Menu.lean` | | no | | |
| **Property of menus and selectors** | `menu_selector` | `InteractionCombinators/Universality/Menus/Menu.lean` | `Checks/Universality/Menus/MenuCheck.lean` | map, fig, now | equal 1.21 | `Results.lean`: `menu_selector_property`. `StepsE`; result literally `πs[i] = x`. |
| **Lemma 2 (i)**, erasing a tree | `erase_tree` | `InteractionCombinators/Universality/Multiplexors/Multiplexor.lean` | `Checks/Universality/Multiplexors/BasicCheck.lean` | map, fig | equal 1.17 | Literal `Red`; no hypothesis. |
| **Lemma 2 (ii)**, erasing a wiring | `erase_wiring` | `InteractionCombinators/Universality/Menus/Package.lean` | `Checks/Universality/Menus/PackageCheck.lean` | map, fig | equal 1.18 | `StepsE`; the wiring is the multiset of its wire names. |
| **Corollary: a package is erased** | `erase_package` | `InteractionCombinators/Universality/Menus/Package.lean` | `Checks/Universality/Menus/PackageCheck.lean` | map, fig, now | equal 1.19 | `Results.lean`: `lemma_2_erase_package`. |
| The same for a list of packages | `erase_packages` | `InteractionCombinators/Universality/Menus/Menu.lean` | | no | | |
| "(i) holds for principal nets, (ii) for reduced nets" | none | | | | | Only trees, wirings and packages. |

## Section 2.4, Translation, restricted case (pages 85-87)

| Paper item | Lean declaration | File | Check file | Read | Figure | Notes |
|---|---|---|---|---|---|---|
| Decomposition of a right member into φ, ψ, σ (figure of p. 85) | `Decomposition`, `Rule.plug`, `Rule.plug_linear` | `InteractionCombinators/Universality/RecursionFree/Decomposition.lean` | `Checks/Universality/RecursionFree/DecompositionCheck.lean`, `Checks/Universality/RecursionFree/DecompositionReview.lean` | map, fig | equal 2.1 | Compared on `con`-`dup`, `con`-`con` and the rule s-× of Section 1.5. |
| The direction of σ in the plugging | `Rule.plugR` | `InteractionCombinators/Universality/RecursionFree/Decomposition.lean` | | fig | n.c. 2.2 | The figure does not say whether σ goes from φ to ψ. The code: middle wire `l` of φ to `σ l` of ψ. |
| "plugging the sides gives the right member" | `Decomposition.Plugs` | `InteractionCombinators/Universality/RecursionFree/RecursionFree.lean` | | map, now | | Up to `Equiv` and an injective renaming of the internal wires of the rule. |
| One side of the canonical decomposition | `Half.half` | `InteractionCombinators/Universality/RecursionFree/DecompositionHalf.lean` | | fig | equal 2.1 | |
| "there is a canonical one" | `Rule.decompose`, `Rule.decompose_linear`, `Rule.decompose_reduced`, `Rule.decompose_cells`, `Rule.plug_decompose` | `InteractionCombinators/Universality/RecursionFree/Decomposition.lean` | `Checks/Universality/RecursionFree/DecompositionCheck.lean`, `Checks/Universality/RecursionFree/DecompositionReview.lean` | map, fig | different 2.3 | On the example of page 85 the numbering of the middle wires and the value of σ differ from the figure (identity instead of the reversal). Same net after plugging; no theorem uses the numbering. Not changed. |
| Expanded form of a rule (not in the paper; one tree per port) | `Rule.Expanded`, `Rule.exists_perm_of_equiv` | `InteractionCombinators/Universality/RecursionFree/ExpandedIso.lean` | `Checks/Universality/RecursionFree/ExpandedIsoCheck.lean` | map | | |
| Every linear reduced rule has an expanded form | `Rule.exists_expanded` | `InteractionCombinators/Universality/RecursionFree/Expand.lean` | `Checks/Universality/RecursionFree/ExpandCheck.lean`, `Checks/Universality/RecursionFree/ExpandTrReview.lean` | map | | |
| "φ_{i,i} = ψ_{i,i}, σ_{i,i} involutive" (p. 85-86), from the symmetry of page 73 | `Rule.exists_symm_decomposition_of_symmPerm` | `InteractionCombinators/Universality/RecursionFree/SymmPerm.lean` | `Checks/Universality/RecursionFree/SymmPermCheck.lean`, `Checks/Universality/RecursionFree/SymmPermReview.lean` | map, fig | equal 2.4 | The decomposition is not the canonical one. |
| "If i ≠ j, include the permutation into φ_{i,j}, so that σ_{i,j} is an identity" | `Decomposition.absorb`, `System.WellFormed.symmDec` | `InteractionCombinators/Universality/RecursionFree/DecompositionAbsorb.lean` | `Checks/Universality/RecursionFree/RecursionFreeCheck.lean` | map, fig | equal 2.4 | |
| "one can assume in all cases ..." (p. 86), as data | `System.DecData`, `System.exists_decData`, `System.DecData.side` | `InteractionCombinators/Universality/General/CodeData.lean` | `Checks/Universality/General/CodeDataCheck.lean`, `Checks/Universality/General/CodeDataReview.lean` | map, fig, now | equal 2.4 | The structure was read now. |
| "φ_{j,i} = ψ_{i,j}, σ_{j,i} = σ_{i,j}": the two sides of a rule | `System.DecData.sides_expand` | `InteractionCombinators/Universality/General/CodeDataSides.lean` | `Checks/Universality/General/CodeDataSidesCheck.lean` | map | | Needs a well-formed system (shown necessary in `Checks/Universality/General/CodeDataReview.lean`). |
| Recursion-free system (order on the alphabet, p. 86) | `System.RecursionFreeData`, `System.RecursionFree` | `InteractionCombinators/Universality/RecursionFree/RecursionFree.lean` | `Checks/Universality/RecursionFree/RecursionFreeCheck.lean` | map, fig, now | equal 2.5 | Order given by `rank`; the decomposition is part of the data. |
| **"Reduction always terminates in such a system"** | `System.RecursionFreeData.measure`, `System.RecursionFree.step_wellFounded`, `System.RecursionFree.stepE_wellFounded`, `System.RecursionFree.not_stepE_seq` | `InteractionCombinators/Universality/RecursionFree/RecursionFreeTerminates.lean` | `Checks/Universality/RecursionFree/RecursionFreeTerminatesCheck.lean` | now | | `Results.lean`: `recursion_free_terminates` (the last name). |
| Example of p. 87: the combinators without `con`-`dup` | `systemNoConDup`, `systemNoConDup_wellFormed`, `decEraBin`, `rankNoConDup`, `recursionFreeDataNoConDup`, `systemNoConDup_recursionFree` | `InteractionCombinators/Universality/RecursionFree/RecursionFree.lean` | `Checks/Universality/RecursionFree/RecursionFreeCheck.lean` | map, fig | equal 2.10 | |
| The side of α against β, in expanded form | `RawSide`, `ExpSide`, `RawSide.expand`, `System.RecursionFreeData.rawSide`, `System.RecursionFreeData.side` | `InteractionCombinators/Universality/RecursionFree/RecursionFreeSide.lean` | | fig, now | equal 2.5 | The two structures were read now; `rawSide` by the comparison. `expand` chooses by `Classical.choose`. |
| Fig. 6 left, the cell [α_i], as a tree | `cellSel`, `cellSkel` | `InteractionCombinators/Universality/RecursionFree/CellSkeleton.lean` | `Checks/Universality/RecursionFree/CellSkeletonCheck.lean`, `Checks/Universality/RecursionFree/CellSkeletonReview.lean` | fig | equal 2.6 | Instance n = 2, m = 3, i = 1. |
| The tree at a port of a side, [φ_{i,j}] | `Rule.portTree` | `InteractionCombinators/Universality/RecursionFree/PortTree.lean` | | no | | |
| The same, computable | `Rule.portTreeC`, `Rule.portTreeC_eq_portTree` | `InteractionCombinators/Universality/RecursionFree/PortTreeC.lean` | `Checks/Universality/RecursionFree/PortTreeCCheck.lean`, `Checks/Universality/RecursionFree/PortTreeCReview.lean` | no | | |
| Fig. 6 right, the package Γ_{i,j} | `gammaTree`, `gammaPort`, `gamma`, `gamma_isPackage` | `InteractionCombinators/Universality/RecursionFree/Gamma.lean` | `Checks/Universality/RecursionFree/GammaCheck.lean`, `Checks/Universality/RecursionFree/GammaReview.lean` | fig | equal 2.8 | `gamma` was compared, on a side with one port and two middle wires. |
| Fig. 6, the menu Γ_i and [α] as a principal net; the translation by induction on the order | `gammaOpt`, `cellPNet`, `symEnum`, `cellMenu`, `cellNet`, `System.RecursionFreeData.translation`, `System.RecursionFreeData.translation_net` | `InteractionCombinators/Universality/RecursionFree/RecursionFreeTr.lean` | `Checks/Universality/RecursionFree/RecursionFreeTrReview.lean` | map, fig | equal 2.6, 2.7 | Noncomputable. Not evaluated on any instance. |
| The translation of Fig. 6 is strict | `System.RecursionFreeData.translation_strict` | `InteractionCombinators/Universality/RecursionFree/RecursionFreeStrict.lean` | | map | | |
| Fig. 7, rows 1 to 3 (trees) | `cellSkel_cellSkel` | `InteractionCombinators/Universality/RecursionFree/CellSkeleton.lean` | `Checks/Universality/RecursionFree/CellSkeletonCheck.lean` | map, fig | equal 2.9 | Row 2 of the figure has no statement of its own. |
| Fig. 7, last rows; the whole figure (trees) | `mux_gamma_loop`, `mux_gamma_mux_gamma`, `cellSkel_gamma_cellSkel_gamma` | `InteractionCombinators/Universality/RecursionFree/Fig7End.lean` | `Checks/Universality/RecursionFree/Fig7EndCheck.lean`, `Checks/Universality/RecursionFree/Fig7EndReview.lean` | map, fig | equal 2.9 | Followed by hand on `con`-`con`. |
| The net at the end of Fig. 7 is a translation of the plugged sides | `plugTarget`, `netTr_plug_gamma`, `mux_gamma_mux_gamma_netTr` | `InteractionCombinators/Universality/RecursionFree/PlugTr.lean` | `Checks/Universality/RecursionFree/PlugTrCheck.lean`, `Checks/Universality/RecursionFree/PlugTrReview.lean` | no | | The comparison lists `netTr_plug_gamma` as not compared. |
| The same for any translated trees | `plugTermTarget`, `netTr_plug_termTr` | `InteractionCombinators/Universality/RecursionFree/PlugTermTr.lean` | `Checks/Universality/RecursionFree/PlugTermTrCheck.lean`, `Checks/Universality/RecursionFree/PlugTermTrReview.lean` | map, fig | equal 3.17 | `plugTermTarget` was compared in item 3.17. |
| ... hence a translation of the rule itself | `Decomposition.Plugs.netTr_inst`, `Decomposition.Plugs.netTr_inst_of_sides` | `InteractionCombinators/Universality/RecursionFree/PlugsNetTr.lean` | `Checks/Universality/RecursionFree/PlugsNetTrCheck.lean`, `Checks/Misc/PlugsReview.lean` | map | | |
| Expanded sides still plug the rule | `Decomposition.Plugs.of_expand`, `System.RecursionFreeData.plugs_expand` | `InteractionCombinators/Universality/RecursionFree/PlugsExpand.lean` | `Checks/Misc/PlugsReview.lean` | no | | |
| Fig. 7 for the translation itself | `translation_cells_meet`, `translation_cells_netTr_plug` | `InteractionCombinators/Universality/RecursionFree/RecursionFreeFig7.lean` | `Checks/Universality/RecursionFree/RecursionFreeFig7Check.lean` | map, fig | equal 2.9 | |
| **"In that way, one gets a translation of interaction systems (Fig. 7)"** | `System.RecursionFreeData.translation_compatible`, `recursionFree_strict`, `recursionFree_strict_noConDup` | `InteractionCombinators/Universality/RecursionFree/RecursionFreeCompatible.lean` | `Checks/Universality/RecursionFree/RecursionFreeCompatibleReview.lean` | map, fig, now | equal 2.9 | `Results.lean`: `recursion_free_compatible`, `recursion_free_strict`. |

## Section 2.5, Duplication (page 87)

| Paper item | Lean declaration | File | Check file | Read | Figure | Notes |
|---|---|---|---|---|---|---|
| "without δ" | `DupFree` | `InteractionCombinators/Universality/Duplication/Duplication.lean` | | map, now | | |
| **Lemma 3 (i)**, text form | `dupNet`, `dup_tree` | `InteractionCombinators/Universality/Duplication/Duplication.lean` | `Checks/Universality/Duplication/DuplicationExamples.lean` | map, fig | equal 2.11 | Literal `Red`; the result is a net computed by `dupNet`. |
| **Lemma 3 (i)**, as drawn (two copies, a `dup` on each leaf) | `Copy`, `nested`, `dup_tree_nested` | `InteractionCombinators/Universality/Duplication/Duplication.lean` | `Checks/Universality/Duplication/DuplicationExamples.lean` | map, fig | equal 2.11 | Instance: the tree `con(x0, x1)`. Up to `Equiv`. |
| **Lemma 3 (ii)**, duplicating a wiring | `dup_wiring` | `InteractionCombinators/Universality/Duplication/DupWiring.lean` | `Checks/Universality/Duplication/DupWiringExamples.lean` | map, fig | equal 2.12 | `StepsE`. |
| **Corollary: a package without `dup` is duplicated** | `dup_package` | `InteractionCombinators/Universality/Duplication/DupPackage.lean` | `Checks/Universality/Duplication/DupPackageCheck.lean` | map, fig, now | equal 2.13 | `Results.lean`: `lemma_3_dup_package`. The copies are the package renamed by maps injective on its names. |
| "δ cannot duplicate δ" (necessity of `DupFree`) | `dupDup_not_copies`, `dup_package_needs_dupFree`, `copier_package_needs_dupFree` | `Checks/Misc/DupDupCheck.lean` | | no | | In `Checks/`, not in the library: the conclusions of `dup_package` and `copier_package` are refuted on the package `dup(0, 0)`. |
| "(i) holds for principal nets, (ii) for reduced nets without δ" | none | | | | | |

## Section 2.6, Codes, copiers and decoder (pages 88-89)

`InteractionCombinators/Universality/Codes/Code.lean` and
`InteractionCombinators/Universality/Codes/Decode.lean` were changed after the comparison, to
correct Fig. 8 (rows 2 and 3 below).

| Paper item | Lean declaration | File | Check file | Read | Figure | Notes |
|---|---|---|---|---|---|---|
| Copier C_n | `copier` | `InteractionCombinators/Universality/Codes/Copier.lean` | `Checks/Universality/Codes/CopierCheck.lean` | map, fig | equal 3.4 | It is `autoMux`, as in the paper. |
| **Property of C_n** on a package without `dup` | `copier_package` | `InteractionCombinators/Universality/Codes/Copier.lean` | `Checks/Universality/Codes/CopierCheck.lean` | map, fig, now | equal 3.4 | `Results.lean`: `copier_property`. |
| "π can be decomposed ... π' with 3n + 1 free ports, no δ" | `Decomp`, `decomp`, `dupCount`, `package_decomp`, `package_decomp_exists` | `InteractionCombinators/Universality/Codes/PackageDecomp.lean` | `Checks/Universality/Codes/PackageDecompCheck.lean` | map, fig | equal 3.1 | Three instances. The count 3n + 1 is implicit: n cut names plus 2n + 1 trees. |
| Fig. 8, the code !π | `Decomp.code`, `code` | `InteractionCombinators/Universality/Codes/Code.lean` | `Checks/Universality/Codes/CodeCheck.lean`, `Checks/Universality/Codes/CodeFig8Check.lean`, `Checks/Universality/Codes/CodeFig8Review.lean` | fig, now | different 3.2, since corrected | The comparison found the second and third ports of M_4 exchanged. The definition was then changed and reviewed (`Checks/Universality/Codes/CodeFig8Review.lean`). Read now: it is the formula the report wrote from the figure, M_4 of M_n on the cut names, M_n* on the trees of port 0, M_n* on the trees of port 1, τ. |
| Fig. 8, the decoder D | `decoder` | `InteractionCombinators/Universality/Codes/Code.lean` | `Checks/Universality/Codes/CodeFig8Check.lean`, `Checks/Universality/Codes/CodeFig8Review.lean`, `Checks/Universality/Codes/DecodeReview.lean` | fig, now | different 3.3, since corrected | The same exchange, seen from the other end; corrected and reviewed with the code. Read now: M_4* of the `dup` cell, its port 0, its port 1, the free port, as the report read the figure. |
| "!π contains no δ"; "another package !π" | `code_dupFree`, `code_isPackage` | `InteractionCombinators/Universality/Codes/Code.lean` | `Checks/Universality/Codes/CodeCheck.lean` | map | | |
| Property of C_n on !π | `copier_code` | `InteractionCombinators/Universality/Codes/Code.lean` | `Checks/Universality/Codes/CodeCheck.lean` | map, fig | equal 3.4 | |
| Fig. 9, first stage (M_4 against M_4*) | `code_decoder` | `InteractionCombinators/Universality/Codes/Code.lean` | `Checks/Universality/Codes/CodeCheck.lean`, `Checks/Universality/Codes/CodeFig8Check.lean` | fig, now | equal 3.6 | Literal `Red`. Compared before the correction, which reordered its result; read now in its present form. |
| Fig. 9, the rest | `decodeNet`, `decode_cells` | `InteractionCombinators/Universality/Codes/Decode.lean` | `Checks/Universality/Codes/DecodeCheck.lean` | fig, now | equal 3.6, 3.7 | Row 3 of the figure is not stated: the proof takes one cell at a time. `decodeNet` was changed by the correction. |
| **Fig. 9**: the decoder extracts π from !π | `code_decoder_tree`, `code_decoder_package` | `InteractionCombinators/Universality/Codes/Decode.lean` | `Checks/Universality/Codes/DecodeCheck.lean`, `Checks/Universality/Codes/DecodeReview.lean` | map, fig, now | equal 3.5 | `Results.lean`: `decoder_property`. The package hypothesis of the second is not used: the first states it for any tree. |
| Fig. 9 on a copy made by the copier | `code_decoder_copy` | `InteractionCombinators/Universality/Codes/DecodeCopy.lean` | `Checks/Universality/Codes/DecodeCopyCheck.lean`, `Checks/Universality/Codes/DecodeCopyReview.lean` | map, fig | equal 3.8 | |

## Section 2.7, Translation, general case (pages 88-90)

The paper ends with "the reader is invited to complete the proof of Theorem 1 by working out the
analogue of Fig. 7 for this translation". Everything from `codeCells_meet` on is that analogue.

The files of this section were rewritten after the comparison: each construction now has a twin
that takes a numbering `e` of the symbols as an argument (`codeTreeE`, `codeNetE`,
`codeTranslationE`, `codeCellMenuE`, `codeMenusE`, `codeCells_plugE`), and the old names are the
twins at the noncomputable numbering `symEnum`. The progress notes say that the statements of the
old names did not change. The verdicts below are those of the comparison, on the definitions as
they were; the twins themselves were not compared with the figure.

| Paper item | Lean declaration | File | Check file | Read | Figure | Notes |
|---|---|---|---|---|---|---|
| Fig. 10 bottom left, the cell with an extra port | `codeCell` | `InteractionCombinators/Universality/General/CodeCell.lean` | `Checks/Universality/General/CodeCellCheck.lean`, `Checks/Universality/General/CodeCellReview.lean` | fig | equal 3.10 | A net of three equations, not one tree. |
| C_2 and D against a copy of !Γ | `copier_decoder_copy` | `InteractionCombinators/Universality/Codes/DecodeCopyChain.lean` | `Checks/Universality/Codes/DecodeCopyReview.lean` | map | | |
| The picture of p. 90: !Γ on the extra port gives [α_k] | `codeCell_code` | `InteractionCombinators/Universality/General/CodeCell.lean` | `Checks/Universality/General/CodeCellCheck.lean`, `Checks/Universality/General/CodeCellReview.lean` | map, fig | equal 3.15 | |
| The sides with their cells replaced; the trees on the extra ports | `codeExtra`, `codeTerm` | `InteractionCombinators/Universality/General/CodeGamma.lean` | `Checks/Universality/General/CodeGammaCheck.lean`, `Checks/Universality/General/CodeGammaReview.lean`, `Checks/Universality/Codes/CodeFig8Review.lean` | fig, now | equal 3.10; n.c. 3.11 | Each cell takes five new names. Not comparable: which port of C_2 goes to D. `codeExtra` holds a copy of the decoder and was changed by the correction of Fig. 8. |
| The order of the extra ports on the copier | `codeExtras`, `codeGammaExtras` | `InteractionCombinators/Universality/General/CodeGamma.lean` | `Checks/Universality/General/CodeGammaCheck.lean` | fig | n.c. 3.13 | The figure shows dots. The code: port by port of the side, prefix order in each tree. |
| Fig. 10 bottom right, Γ_{i,j} with the copier | `codeGamma`, `codeGamma_isPackage` | `InteractionCombinators/Universality/General/CodeGamma.lean` | `Checks/Universality/General/CodeGammaCheck.lean`, `Checks/Universality/General/CodeGammaReview.lean` | fig | equal 3.12 | `codeGamma` was compared. |
| The menus Γ_i and Γ | `codeCellMenu`, `codeMenus`, `codeCell_code_codeMenus` | `InteractionCombinators/Universality/General/CodeGamma.lean` | `Checks/Universality/General/CodeGammaCheck.lean` | fig | equal 3.14, 3.15 | |
| **Fig. 10 top left, [α_i]** | `codeTree`, `treePNet`, `codeNet`, `codeTranslation` | `InteractionCombinators/Universality/General/CodeTr.lean` | `Checks/Universality/General/CodeTrCheck.lean`, `Checks/Universality/General/CodeTrReview.lean` | map, fig, now | equal 3.9 | Compared through `cellSkel`, for two symbols of arity 2. Read now: `codeTree` is `codeTreeE` at `symEnum`. Noncomputable. |
| The same with the numbering of the symbols as an argument | `codeTreeE`, `codeNetE`, `codeTranslationE`, `wireNum` | `InteractionCombinators/Universality/General/CodeTr.lean` | `Checks/Universality/General/CodeTreeECheck.lean`, `Checks/Universality/General/CodeTreeEReview.lean`, `Checks/Universality/Codes/CodeNetEReview.lean` | now | | Computable. The three definitions were read; not compared with the figure. |
| The translation is strict | `codeTranslation_strict` | `InteractionCombinators/Universality/General/CodeTr.lean` | `Checks/Universality/General/CodeTrCheck.lean` | map | | |
| Renaming of the pieces; the extracted cell is an instance of the translated cell | `codeNet_inst_eq` | `InteractionCombinators/Universality/General/CodeShift.lean` | | no | | |
| "and we get the translation of φ_{i,j}", for one tree | `codeCopies`, `codeTerm_extract` | `InteractionCombinators/Universality/General/CodeTermExtract.lean` | `Checks/Universality/General/CodeTermExtractCheck.lean`, `Checks/Universality/General/CodeTermExtractECheck.lean` | map, fig | equal 3.15 | |
| The same for a whole side: C_p against !Γ | `codeGamma_extract` | `InteractionCombinators/Universality/General/CodeGammaExtract.lean` | `Checks/Universality/General/CodeGammaExtractCheck.lean`, `Checks/Universality/General/CodeGammaExtractECheck.lean` | fig | equal 3.15 | |
| Analogue of Fig. 7, rows 1 and 2 | `codeCells_meet` | `InteractionCombinators/Universality/General/CodeCellsMeet.lean` | `Checks/Universality/General/CodeCellsMeetCheck.lean`, `Checks/Universality/General/CodeCellsMeetECheck.lean`, `Checks/Universality/Codes/CodeMeetReview.lean` | fig | equal 3.16 | No figure in the paper: compared with what Fig. 7 and Fig. 10 force. |
| Analogue of Fig. 7, row 3 | `codeCells_meet_gamma` | `InteractionCombinators/Universality/General/CodeCellsMeet.lean` | `Checks/Universality/Codes/CodeMeetReview.lean` | fig | equal 3.17 | No library user. |
| Analogue of Fig. 7, last rows | `codeGamma_loop`, `codeGamma_meet`, `codeCells_meet_end` | `InteractionCombinators/Universality/General/CodeGammaMeet.lean` | `Checks/Universality/General/CodeGammaMeetCheck.lean`, `Checks/Universality/Codes/CodeMeetReview.lean` | fig | equal 3.17 | |
| Analogue of Fig. 7, the whole figure | `middle_reindex`, `codeCells_plug`, `codeCells_plugE` | `InteractionCombinators/Universality/General/CodeCellsPlug.lean` | `Checks/Universality/General/CodeCellsPlugCheck.lean`, `Checks/Universality/General/CodeCellsPlugReview.lean` | map, fig | equal 3.17 | `codeCells_plug` was read and compared; the other two were not. |
| **The translation of Fig. 10 is a translation of interaction systems** | `System.DecData.codeTranslation_compatible` | `InteractionCombinators/Universality/General/CodeCompatible.lean` | `Checks/Universality/General/CodeCompatibleReview.lean` | map, fig, now | equal 3.18 | Finite alphabet, well-formed system, any decomposition data. |
| **Theorem 1** | `universal_strict'`, `universal'` | `InteractionCombinators/Universality/General/CodeCompatible.lean` | `Checks/Universality/General/CodeCompatibleReview.lean` | map, now | | |
| **Theorem 1**, the target names | `universal`, `universal_strict` | `InteractionCombinators/Universality/Theorem1.lean` | `Checks/Universality/General/CodeCompatibleReview.lean` | map, now | | `Results.lean`: `theorem_1`, `theorem_1_strict`. |
| **Theorem 1 for a translation given by data** | `System.SidesPlug`, `codeTranslation_compatible_of_sides`, `codeTranslationE_compatible_of_sides`, `System.DecData.codeTranslationE_compatible`, `codeTranslationE_strict` | `InteractionCombinators/Universality/General/CodeCompatibleSides.lean` | `Checks/Universality/General/CodeCompatibleSidesCheck.lean`, `Checks/Universality/General/CodeCompatibleSidesReview.lean`, `Checks/Universality/General/CodeCompatibleECheck.lean` | fig, now | equal 3.18 | `Results.lean`: `theorem_1_explicit`. The definition and the second theorem were compared; all five were read now. No well-formedness, no finiteness beyond the numbering. |
| **Theorem 1 with step counts** (0 < L) | `codeTranslation_compatibleWithin` | `InteractionCombinators/Translations/SimulationUniform.lean` | `Checks/Translations/SimulationUniformReview.lean` | map, now | | `Results.lean`: `theorem_1_bounds`. The bounds exist; their values are not computed. |

## The demo (Section 1.5, pages 76-78)

| Paper item | Lean declaration | File | Check file | Read | Figure | Notes |
|---|---|---|---|---|---|---|
| Unary addition: the system, 2 + 2 = 4 | `Demo.Arith.system`, `Demo.Arith.system_wellFormed`, `Demo.Arith.two_plus_two` | `Demo/Arithmetic.lean` | | no | | |
| 2 + 2 = 4 through the translation of Theorem 1 | `Demo.Arith.two_plus_two_in_combinators`, `Demo.Arith.twoPlusTwo_has_translation` | `Demo/Arithmetic.lean` | | no | | The translation exists; it is not named. |
| The translation of addition, computed | `Demo.Arith.arithEnum`, `Demo.Arith.arithSide`, `Demo.Arith.arith_sidesPlug`, `Demo.Arith.arithTr`, `Demo.Arith.arithTr_strict`, `Demo.Arith.arithTr_compatible`, `Demo.Arith.two_plus_two_in_combinators_computed` | `Demo/ArithmeticTr.lean` | `Checks/Misc/ArithmeticTrReview.lean` | no | | Sides written by hand. Evaluated in the file: the translations of zero, successor and addition have 93, 128 and 95 cells and 23, 34 and 23 internal wires; the first is printed in full. |
| A printer for nets of combinators | `Comb.Term.toStr`, `Comb.netToStr`, `Comb.pnetToStr`, `Net.size` | `Demo/Print.lean` | `Checks/Misc/PrintCheck.lean` | no | | Not a construction of the paper. |
| Multiplication (the eight rules of p. 77), 2 × 2 = 4 | `Demo.Mul.system`, `Demo.Mul.ruleMulSucc`, `Demo.Mul.system_wellFormed`, `Demo.Mul.mul_num`, `Demo.Mul.times_reduces`, `Demo.Mul.two_times_two`, `Demo.Mul.two_times_two_in_combinators` | `Demo/Multiplication.lean` | `Checks/Misc/MultiplicationReview.lean` | no | | The rule s-× was first written with the duplicator's ports exchanged; a review found it and it was corrected (`ruleMulSucc_eq_paper` in the check file). Its translation is not computed. |

## What is not formalized

Checked by grep over `InteractionCombinators/`, `Checks/` and `Demo/` (words searched: "Turing",
"cellular", "Fig. 1", "Fig. 3", "Lemma 1", "more generally", "Section 2.8", "minimal",
"Section 3", "Proposition 5", "Proposition 6", "Proposition 7", "symmetric combinators").

| Paper item | Page | Status |
|---|---|---|
| Section 1.3, Turing machines; Section 1.4, cellular automata | 74-76 | not formalized |
| Fig. 1, the computation of 2 × 2 = 4 | 78 | the result is `Demo.Mul.two_times_two`; the reduction sequence drawn in the figure was not compared with the proof |
| Lemma 1 (principal paths of a principal net) | 80 | not formalized; avoided because a `PNet` is a tree |
| Fig. 3, a nonterminating net | 82 | not formalized (mentioned in two docstrings) |
| Lemma 2 and Lemma 3 "more generally for principal nets / reduced nets" | 85, 87 | not formalized: only trees, wirings and packages |
| Uniqueness of the canonical decomposition | 85 | not formalized; the symmetric decomposition is obtained another way (expanded forms). `Checks/Misc/ArithmeticTrReview.lean` has a non-canonical decomposition that plugs. |
| Section 2.8, minimality of the system | 90 | not formalized |
| Section 3, semantics: execution (Prop. 5, Fig. 11-13), equivalence (Prop. 6, Fig. 14), algebraic formulation (Fig. 15), directed combinators and 2-translations (Prop. 7, Fig. 16-19) | 90-99 | not formalized |
| Section 4, discussion | 99-100 | nothing to formalize |

The symmetric combinators (both annihilations alike) are not in the paper's Theorem 1 and not in
the code.

Proved since the first version of this map, and no longer in this list: the consequence of
Proposition 1 (`StepsEN.normal_unique`); Proposition 2 (`Net.IsReduced.exists_treesOnWiringN`,
`Net.IsTreesOnWiringN.unique`); "a reduced net with no free port is empty"
(`Net.IsReduced.eq_zero_of_closed`); "if such a T_σ exists, σ is involutive"
(`involutive_of_transpositor`); termination of recursion-free systems
(`System.RecursionFree.not_stepE_seq`); the multiplication of Section 1.5
(`Demo/Multiplication.lean`); the correspondence between texts and graphs
(`InteractionCombinators/Graphs/`).

## Known gaps and caveats

From the working notes of the development, the three comparison reports, and from reading the
statements. Each was checked against the
tree on 20 November 2026.

1. **Results that live only in `Checks/`.** "δ cannot duplicate δ" is proved as a refutation of
   `dup_package` and `copier_package` without `DupFree`, in `Checks/Misc/DupDupCheck.lean`. The
   necessity of other hypotheses is shown only there too: linearity in `Equiv.add_right`
   (`Checks/Misc/WantedCheck.lean`), well-formedness in `System.DecData.sides_expand`
   (`Checks/Universality/General/CodeDataReview.lean`), linear rules in
   `Net.Linear.stepE_interact` (`Checks/Graphs/GraphStepEReview.lean`), the hypotheses of
   `Rule.Reduced.isReduced_inst` (`Checks/Reduced/RuleReducedReview.lean`). `Checks/` is built and
   audited by the gate like the library, but nothing in `Results.lean` rests on it.
2. **`Rule.Reduced` is a syntactic form.** Every equation has an auxiliary port on one side.
   `System.WellFormed` asks for it. It is now related to `Net.IsReduced` on every instance with
   distinct port names, in both directions (`InteractionCombinators/Reduced/RuleReduced.lean`), but
   replacing a rule by its rewritten form inside a system is not proved: a rule whose text has an
   equation between an internal wire and a tree is rejected even if its graph is reduced. Whether
   the converse `Rule.exists_reduced_of_isReduced` needs its hypothesis of injective port names is
   open.
3. **Which results use which reduction.** Literal `Red`: `erase_tree`, `mux_muxStar`,
   `autoMux_autoMux`, `transpositor_transpositor`, `transpositorPerm_transpositorPerm`, `dup_tree`,
   `code_decoder`. Up to wires (`StepsE`, then `Equiv` to the stated net): `erase_wiring`,
   `erase_package`, `menu_selector`, `dup_wiring`, `dup_package`, `copier_package`, Fig. 7, Fig. 9,
   Fig. 10 and Theorem 1. A literal reduction is a reduction up to wires (`Steps.stepsE`), so the
   literal results are the stronger ones.
4. **`Translation.Compatible` asks more than the paper**: every naming of the ports for which the
   pair is linear, including two ports of one cell joined by a wire, and every naming of the
   internal wires. The internal wires of the result are existential. This makes Theorem 1
   stronger, and it is what lets Proposition 4 apply inside any net.
5. **`System.WellFormed.symm`** is symmetry up to `Equiv` and a permutation of the internal wires.
   The lemmas that took the stronger hypothesis of a plain `Equiv` have been deleted; the ones in
   `InteractionCombinators/Universality/RecursionFree/SymmPerm.lean` match page 73.
6. **Hypotheses known to be unused or stronger than needed.**
   `Translation.Invertible.compatibleWithin_one_of_wellFormed` asks a well-formed target system;
   linear and reduced rules suffice (`Translation.Invertible.compatibleWithin_one_of_linear_reduced`,
   the one `Results.lean` uses). `code_decoder_package` has an unused package hypothesis, kept in
   `decoder_property`. `Step.strong_confluence` and `StepE.strong_confluence` take
   `System.WellFormed` though the reducedness of the right members is not used
   (`StepE.strong_confluence_of`). Proposition 4 asks only linear rules on both sides.
7. **The old names and the `E` names of the translation.** The translation of Fig. 10 exists
   twice: `codeTreeE`, `codeNetE`, `codeTranslationE` take a numbering of the symbols and the
   sides as arguments and are computable; `codeTree`, `codeNet`, `codeTranslation` are the same at
   `symEnum`, which is `Finite.equivFin`, and are noncomputable. `universal_strict` is proved
   with the old names and with sides chosen by `Classical.choose` (`System.WellFormed.decData`,
   `System.DecData.side`, `RawSide.expand`, `System.WellFormed.symmDec`). So Theorem 1 itself
   still uses a translation that cannot be evaluated. The computable one needs sides from the
   user with a proof of `System.SidesPlug`; this has been done for one system, unary addition
   (`Demo/ArithmeticTr.lean`), and only the translation of zero is printed. The translation of
   Fig. 6 (`System.RecursionFreeData.translation`) has no computable twin. The bounds of
   `theorem_1_bounds` are shown to exist with 0 < L, not computed.
8. **`[Finite S.Sym]`** is assumed by `Universal`, `StrictlyUniversal` and the uniform bounds. The
   paper fixes a finite alphabet, so this is the paper's hypothesis. `theorem_1_explicit` does
   without it.
9. **The decomposition used is not the paper's canonical one.** For a rule of a symbol with
   itself the paper gets φ_{i,i} = ψ_{i,i} from uniqueness of the canonical decomposition. The
   code expands the rule (one tree per port, `Rule.exists_expanded`) and decomposes the expanded
   rule. The resulting `Decomposition.Plugs` is up to `Equiv` and an injective renaming of
   internal wires. On the example of page 85, `Rule.decompose` numbers the middle wires
   differently from the figure (report 2, item 3). The sides of the computed translation of
   addition are not canonical either (`Checks/Misc/ArithmeticTrReview.lean`).
10. **Fig. 8.** The comparison with the figures found the code and the decoder with two ports
    exchanged on both sides, which three earlier reviews had not seen. They were corrected and
    reviewed again (`Checks/Universality/Codes/CodeFig8Check.lean`,
    `Checks/Universality/Codes/CodeFig8Review.lean`). The code inside the printed translation of
    zero was not checked cell by cell against Fig. 8.
11. **The graph results** are over names in `ℕ`, except `Net.exists_graph` and
    `Net.Linear.hasGraph_iso`. The two directions between `StepE` and `Graph.Interact` assume
    linear rules and are stated one step at a time; no theorem lifts them to `StepsE`.
    `Graph.Interact` on a graph that is not well formed can give a meaningless result
    (`Checks/Graphs/GraphStepReview.lean`); every theorem assumes a well-formed graph or the graph
    of a linear net.
12. **Results with no adversarial review of their own**, according to the last summary: the
    necessity of `DupFree`, the closed reduced net, termination, the converse on T_σ, and the
    first four graph results (existence, uniqueness, `Equiv` against isomorphism, realization).
    Their check files have examples only.
13. **Page references that are slightly off.** Section 1.6 starts at the bottom of page 77, where
    the cut is defined; the header of `Results.lean` gives pages 78-80 for it. The docstring of
    `universal_strict'` still names the target file by its old name. Several docstrings cite
    "page 90: no order on the symbols is needed", a sentence that is not in the text of page 90.
14. **Leftover.** `codeCells_meet_gamma` has no library user.
