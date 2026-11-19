#!/usr/bin/env bash
# The merge gate. Run it before every push; the pull-request check runs the copy on main.
#
#   scripts/check.sh            compare against origin/main
#   GATE_BASE=<ref> scripts/check.sh
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
BASE="${GATE_BASE:-origin/main}"
LIBS="InteractionCombinators Checks Demo"

fail() { echo "GATE FAILED: $*" >&2; exit 1; }
step() { echo "== $*"; }

git rev-parse --verify -q "$BASE" >/dev/null || fail "base ref $BASE not found (run: git fetch origin main)"

step "protected files"
changed="$(git diff --name-only "$BASE"...HEAD; git diff --name-only HEAD; git ls-files --others --exclude-standard)"
while IFS= read -r prefix; do
  case "$prefix" in ''|'#'*) continue ;; esac
  hit="$(printf '%s\n' "$changed" | grep -F -x -e "$prefix" || true)"
  [ -n "$hit" ] || hit="$(printf '%s\n' "$changed" | awk -v p="$prefix" 'index($0, p) == 1 && substr(p, length(p)) == "/"' || true)"
  [ -z "$hit" ] || fail "protected path changed: $(printf '%s' "$hit" | tr '\n' ' ')"
done < <(git show "$BASE:scripts/protected.txt" 2>/dev/null || cat scripts/protected.txt)

step "forbidden constructs"
W="[^A-Za-z0-9_.']"
if grep -rnE "(^|$W)(sorry|admit|native_decide)($W|\$)|^[[:space:]]*(private |protected )?(axiom|unsafe)[[:space:]]|implemented_by|set_option[[:space:]]+debug" $LIBS InteractionCombinators.lean Checks.lean Demo.lean; then
  fail "forbidden construct in the sources (see lines above)"
fi

step "no new unproved statements"
# Compare with the commit this work started from, not with the tip of the base: the owner may
# have removed a proved statement from the base since then.
fork="$(git merge-base "$BASE" HEAD)"
base_wanted="$( (git grep -c -E '^[[:space:]]*proof_wanted[[:space:]]' "$fork" -- $LIBS || true) | awk -F: '{s+=$NF} END {print s+0}')"
head_wanted="$( (grep -rhcE '^[[:space:]]*proof_wanted[[:space:]]' $LIBS || true) | awk '{s+=$1} END {print s+0}')"
[ "$head_wanted" -le "$base_wanted" ] || fail "proof_wanted went from $base_wanted to $head_wanted"

step "every file is part of a library"
for lib in $LIBS; do
  while IFS= read -r f; do
    mod="$(printf '%s' "${f%.lean}" | tr '/' '.')"
    grep -q -x "import $mod" "$lib.lean" || fail "$f is not imported by $lib.lean, so it is neither built nor audited"
  done < <(find "$lib" -name '*.lean' | sort)
done

step "the library does not depend on the checks"
if grep -rnE '^import (Checks|Demo)' InteractionCombinators InteractionCombinators.lean; then
  fail "a library file imports a check"
fi

step "build"
mkdir -p .lake
log=".lake/gate-build.log"  # inside the checkout: the system temp directory may be read-only
scripts/build.sh >"$log" 2>&1 || true
grep -E "^error|✖|Build completed|declaration uses 'sorry'" "$log" || true
grep -q "Build completed successfully" "$log" || fail "build failed (log: $log)"
if grep -q "declaration uses 'sorry'" "$log"; then fail "a declaration uses sorry (log: $log)"; fi

step "declarations unchanged"
# While scripts/decls-baseline.txt exists, the project is being reformatted, not extended: the
# name, the type and (for definitions) the body of every declaration must stay what they were.
if [ -f scripts/decls-baseline.txt ]; then
  lake env lean scripts/Decls.lean > .lake/decls.txt 2>/dev/null || fail "could not fingerprint the declarations"
  if ! cmp -s scripts/decls-baseline.txt .lake/decls.txt; then
    diff scripts/decls-baseline.txt .lake/decls.txt | head -20
    fail "a declaration changed (lines above: < before, > now); only layout and comments may change"
  fi
fi

step "axiom audit"
lake env lean scripts/Audit.lean || fail "axiom audit"

echo "GATE PASSED"
