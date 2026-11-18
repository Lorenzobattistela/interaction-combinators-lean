# Interaction combinators in Lean

A Lean 4 formalization of Lafont's *Interaction Combinators* (Information and Computation 137,
1997), aimed at Theorem 1: any interaction system can be translated into the system of interaction
combinators.

Nets are presented textually, as equations between trees. Two nets are the same graph when they
differ by wire substitution (`Equiv`); only interactions count as reduction steps.

## Layout

- `InteractionCombinators/Term.lean` — signatures, trees, substitution
- `InteractionCombinators/Net.lean` — nets, linearity, equivalence up to wires
- `InteractionCombinators/System.lean` — rules, interaction systems, reduction
- `InteractionCombinators/Translation.lean` — principal nets, translations, universality
- `InteractionCombinators/Rename.lean` — renaming an internal wire gives the same graph
- `InteractionCombinators/Instance.lean` — instances of a principal net are the same graph
- `InteractionCombinators/Combinators.lean` — the three combinators and their six rules
- `InteractionCombinators/Lafont/` — results of the paper, and the target statement in
  `Universality.lean`

The target, `Comb.universal_strict`, is stated with `proof_wanted`: the statement is checked and
the proof is not yet written.

`docs/guia-de-revisao.pdf` is a review guide for the definitions (in Portuguese), with page
references to the paper.

## Building

```sh
lake exe cache get
lake build
```
