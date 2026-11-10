#!/usr/bin/env bash
# Check the headline theorems with leanprover/comparator: each theorem of the solution has exactly
# the challenge's statement (and the same constants underneath), uses only `propext`, `Quot.sound`
# and `Classical.choice`, and the solution's environment replays in a fresh Lean kernel from
# `lean4export` output.
#
#   third_party/code-verification/comparator/install-tools.sh .lake/comparator-tools
#   set -a; source .lake/comparator-tools/env; set +a
#   comparator/run.sh
set -uo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
: "${COMPARATOR_BIN:?run install-tools.sh and source its env file}"
: "${COMPARATOR_LEAN4EXPORT:?run install-tools.sh and source its env file}"
: "${COMPARATOR_LANDRUN:?run install-tools.sh and source its env file}"
export COMPARATOR_LEAN4EXPORT COMPARATOR_LANDRUN

scripts/gen-challenge --check || exit 1
lean_prefix="$(lean --print-prefix)" || exit 1
export PATH="$lean_prefix/bin:$PATH"
lake build --no-ansi ComparatorChallenge ComparatorSolution || exit 1
ulimit -s 1048576 2> /dev/null || ulimit -s 524288 2> /dev/null || true

log="${COMPARATOR_LOG:-$(mktemp)}"
lake env "$COMPARATOR_BIN" comparator/chachapoly.json 2>&1 | tee "$log"
rc=${PIPESTATUS[0]}
if [[ "$rc" == 0 ]] && grep -q 'Lean default kernel accepts the solution' "$log" \
    && grep -q 'Your solution is okay!' "$log"; then
  echo "comparator: PASS"
else
  echo "comparator: FAIL (rc=$rc, log $log)"; exit 1
fi
