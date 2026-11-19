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

Most of the proofs were written by a pool of autonomous agents working from a roadmap, with every
new definition reviewed against the paper by another agent before anything was built on it. The
record of that process is in `history/`.

## Names

The code uses the names of HVM: `con` is Lafont's γ (constructor), `dup` is δ (duplicator) and
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
  - `Term.lean`, `Net.lean`, `System.lean`, `Translation.lean`, `Combinators.lean`: the setting.
    These are the definitions the theorem depends on, and the ones to read first.
  - `Lafont/`: the results of the paper. `Universality.lean` has the theorem.
- `Checks/` — examples, non-vacuity tests and attempts to refute the statements of the library.
  The library never imports them.
- `Demo/` — worked examples. `Arithmetic.lean` translates unary addition, a recursive
  interaction system, into the combinators, and runs `2 + 2`.
- `PAPER.md` — a map from each definition, lemma, figure and theorem of the paper to the code.
- `history/` — the roadmap, the plans and the progress notes of the agents.
- `scripts/` — the gate (`check.sh`), the axiom audit, and the launcher of the agent pool.

## Building

```sh
lake exe cache get
lake build
scripts/check.sh    # the gate: forbidden constructs, build, axiom audit
```

The project imports only the Mathlib modules it uses; a full build takes a few minutes and about
2 GB of memory per Lean process.

## What is not here

- The correspondence between this textual presentation and nets as graphs.
- The parts of the paper after Theorem 1 (Section 3).
