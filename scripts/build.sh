#!/usr/bin/env bash
# Build the project at low priority and with few threads, so the machine stays usable.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-3}"

# One build at a time on the machine. Each Lean process holds several GB once Mathlib is
# imported, and several builds together can exceed the memory ("exited with code 137").
# So wait while another build is running, for at most BUILD_WAIT seconds.
waited=0
while [ "$waited" -lt "${BUILD_WAIT:-1200}" ]; do
  others=$(pgrep -f "lake build" 2>/dev/null | wc -l | tr -d ' ') || others=0
  [ "$others" -eq 0 ] && break
  [ "$waited" -eq 0 ] && echo "build.sh: another build is running; waiting for it" >&2
  nap=$((5 + RANDOM % 10))
  sleep "$nap"
  waited=$((waited + nap))
done

if nice -n 15 true 2>/dev/null; then exec nice -n 15 lake build "$@"; fi
exec lake build "$@"
