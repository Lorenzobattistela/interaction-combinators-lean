import InteractionCombinators
import Checks
import Demo

/-!
A fingerprint of every declaration of the project, used to show that a reorganization changed
nothing: for each constant, its name, its kind, a hash of its type and, for definitions, a hash
of its body. Private names are printed without the module they sit in, so that moving a file
does not change the fingerprint. Proofs are not hashed: only what is stated and defined.

    lake env lean scripts/Decls.lean > decls.txt
-/

open Lean Elab Command

/-- A private name without its module prefix. -/
def normName (n : Name) : Name := (privateToUserName? n).getD n

/-- An expression with every constant name normalized. -/
def normExpr (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => some (.const (normName n) ls)
    | _ => none

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx.toNat]!
    unless (`InteractionCombinators).isPrefixOf m || (`Checks).isPrefixOf m ||
        (`Demo).isPrefixOf m do continue
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
    let body := match ci with
      | .defnInfo d => toString (normExpr d.value).hash
      | _ => "-"
    lines := lines.push s!"{normName n} {kind} {(normExpr ci.type).hash} {body}"
  let sorted := lines.qsort (· < ·)
  IO.println ("\n".intercalate sorted.toList)
