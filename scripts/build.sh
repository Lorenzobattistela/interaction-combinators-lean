#!/usr/bin/env bash
# Build the project at low priority and with few threads, so the machine stays usable.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-3}"
# Lower the priority when allowed. Inside the agents' sandbox `nice` is refused; there the
# launcher has already lowered the priority of the whole agent.
if nice -n 15 true 2>/dev/null; then exec nice -n 15 lake build "$@"; fi
exec lake build "$@"
