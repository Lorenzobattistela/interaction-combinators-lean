#!/usr/bin/env bash
# Build the project at low priority and with few threads, so the machine stays usable.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-3}"

# One build at a time on the whole machine. Each Lean process holds several GB once Mathlib is
# imported; the builds of two agents, the pull-request check and the check of main together
# exceed the memory, and the system then kills Lean processes ("exited with code 137").
# So wait while another worktree is building, for at most BUILD_WAIT seconds.
waited=0
while [ "$waited" -lt "${BUILD_WAIT:-1200}" ]; do
  others=$(pgrep -f "lake build" 2>/dev/null | wc -l | tr -d ' ') || others=0
  [ "$others" -eq 0 ] && break
  [ "$waited" -eq 0 ] && echo "build.sh: another build is running; waiting for it" >&2
  nap=$((5 + RANDOM % 10))
  sleep "$nap"
  waited=$((waited + nap))
done

# Lower the priority when allowed. Inside the agents' sandbox `nice` is refused; there the
# launcher has already lowered the priority of the whole agent.
if nice -n 15 true 2>/dev/null; then exec nice -n 15 lake build "$@"; fi
exec lake build "$@"
