#!/usr/bin/env bash
# Build DistinctDistances.jsp_000900, check Challenge.lean is frozen, check its statement against
# the proof, check its axioms, and scan for forbidden constructs.
#
# Exit 0: every check passed. Exit 2: the proof still depends on sorryAx. Exit 1: any other failure,
# including an axiom outside propext, Classical.choice and Quot.sound, or a forbidden construct.
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
# Git blob id of the frozen Challenge.lean (unchanged since the statement was fixed; v1.0.0 has it).
FROZEN_BLOB=21648f72616ee8911640b58864ddd2f072ba4f9c

lake build DistinctDistances.Main || exit 1

# Challenge.lean is frozen: its content must hash to FROZEN_BLOB.
ACTUAL_BLOB=$(git hash-object Challenge.lean)
if [ "$ACTUAL_BLOB" != "$FROZEN_BLOB" ]; then
  echo "FAIL: Challenge.lean differs from the frozen statement (blob $ACTUAL_BLOB, expected $FROZEN_BLOB)" >&2
  exit 1
fi
echo "Challenge.lean matches the frozen statement (blob $FROZEN_BLOB)"

# The copied Formal Conjectures definitions are identical in Challenge.lean and the proof.
python3 scripts/check_target.py defs
# The statement and the definitions it uses elaborate identically in both (pp.all).
python3 scripts/check_target.py statement

result_dir=.lake/verification-results
mkdir -p "$result_dir"
axiom_log="$result_dir/axioms.log"
if ! lake env lean --trust=0 scripts/Axioms.lean >"$axiom_log" 2>&1; then
  cat "$axiom_log"
  exit 1
fi
cat "$axiom_log"
python3 scripts/check_axioms.py "$axiom_log"
ax_status=$?
if [ "$ax_status" -ne 0 ]; then
  exit "$ax_status"
fi

# No sorry, admit, added axioms, native_decide, implemented_by, extern or unsafe code in any
# Lean source of the repository (Challenge.lean keeps the sorry of its statement).
python3 scripts/check_forbidden.py
