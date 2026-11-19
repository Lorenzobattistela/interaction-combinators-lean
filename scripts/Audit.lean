import InteractionCombinators
import Checks

/-!
Axiom audit, run by `scripts/check.sh`.

Fails if a module of the project declares an axiom, or if a theorem of the project depends on an
axiom other than the three standard ones. A `sorry` shows up here as the axiom `sorryAx`, and
`native_decide` as `Lean.ofReduceBool`.
-/

open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut bad : Array String := #[]
  let mut checked := 0
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    unless (`InteractionCombinators).isPrefixOf mods[idx.toNat]! ||
        (`Checks).isPrefixOf mods[idx.toNat]! do continue
    if ci matches .axiomInfo _ then
      bad := bad.push s!"axiom declared in the project: {n}"
      continue
    unless ci matches .thmInfo _ do continue
    checked := checked + 1
    for a in ← liftCoreM (collectAxioms n) do
      unless allowedAxioms.contains a do
        bad := bad.push s!"{n} depends on the axiom {a}"
  if bad.isEmpty then
    logInfo m!"axiom audit: {checked} theorems, all on the standard axioms"
  else
    throwError "axiom audit failed:\n{"\n".intercalate bad.toList}"
