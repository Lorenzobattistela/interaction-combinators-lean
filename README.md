# Interaction combinators in Lean

A Lean 4 formalization of Yves Lafont's *Interaction Combinators* (Information and Computation
137, 1997), up to its main result:

> **Theorem 1.** Any interaction system can be translated into the system of interaction
> combinators.

The theorem is proved in the strict form (the translation of every symbol starts with a cell),
with no `sorry` and no axiom beyond `propext`, `Classical.choice` and `Quot.sound`:

```lean
theorem INet.Comb.universal_strict : StrictlyUniversal system
```

in `InteractionCombinators/Universality/Theorem1.lean`. The proof follows the paper: multiplexors
and transpositors, erasing and duplication, menus and selectors, codes, copiers and the decoder,
and the translation of Fig. 10. It includes the compatibility of that translation with reduction,
which the paper leaves to the reader.

The definitions and the statement of the theorem were written and reviewed by the author. Most of
the proofs were written by a swarm of autonomous language-model agents, and every proof is checked
by Lean. The paper in `docs/paper/` describes the formalization and how it was produced.

## Names

The code uses the following names for the three combinators: `con` is Lafont's γ (constructor), `dup` is δ (duplicator) and
`era` is ε (eraser). The system is Lafont's, not the symmetric one: `con`–`con` annihilation
exchanges the auxiliary ports, `dup`–`dup` does not.

## How nets are represented

Nets are text, not graphs: a net is a multiset of equations between trees, and a name is a wire.
A name that occurs twice is an internal wire; a name that occurs once is a free port. Two texts
are the same graph when they differ by wire substitution (`Equiv`). Only interactions count as
reduction steps: `Steps` is literal reduction, `StepsE` is reduction up to wires, and the theorem
is stated with the latter.

## Layout

- `InteractionCombinators/` — the library.
  - `Core/`: the setting (`Term`, `Net`, `System`, `Translation`, `Combinators`, `Graph`). These
    are the definitions the theorem depends on, and the ones to read first.
  - `Text/`, `Reduction/`, `Reduced/`, `Translations/`, `Graphs/`: the general theory of
    Section 1 of the paper, and the correspondence with nets as graphs.
  - `Universality/`: Section 2 of the paper. `Theorem1.lean` has the theorem.
  - `Results.lean`: the main results, in the order and with the numbering of the paper. Start
    here.
- `Checks/` — examples, non-vacuity tests and attempts to refute the statements of the library.
  The library never imports them.
- `Demo/` — worked examples. `Arithmetic.lean` translates unary addition, a recursive
  interaction system, into the combinators, and runs `2 + 2`.
- `PAPER.md` — a map from each definition, lemma, figure and theorem of the paper to the code.
- `docs/paper/` — the paper about this development, with its sources.
- `scripts/` — the gate (`check.sh`), the axiom audit (`Audit.lean`) and the fingerprint of the
  declarations (`Decls.lean`).

## Building

```sh
lake exe cache get
lake build
GATE_BASE=HEAD scripts/check.sh    # the gate: forbidden constructs, build, axiom audit
```

The project imports only the Mathlib modules it uses; a full build takes a few minutes and about
2 GB of memory per Lean process.

## What is not here

- Section 2.8 of the paper (minimality of the system) and Section 3 (semantics, directed
  combinators).
- The symmetric combinators, which the paper treats in Section 3 and which are not the system of
  Theorem 1.

The correspondence between the textual presentation used here and nets as graphs is proved, in
`InteractionCombinators/Graphs/`; `InteractionCombinators/Results.lean` lists it with the other
main results.

## Paper and citation

*A Machine-Checked Proof of the Universality of Interaction Combinators*, Lorenzo Battistela,
2026: `docs/paper/paper.pdf`. To cite this development, cite that paper.

## License

Copyright 2026 Lorenzo Battistela. Released under the Apache License 2.0 (see `LICENSE`).
