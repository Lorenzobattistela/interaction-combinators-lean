#!/usr/bin/env bash
# Build the project at low priority and with few threads, so the machine stays usable.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-3}"
exec nice -n 15 lake build "$@"
