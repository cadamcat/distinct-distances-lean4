#!/usr/bin/env bash
# Replay DistinctDistances.Main and every module it imports, Mathlib and OpenAI's library included, in a fresh
# Lean kernel environment. This takes much longer than scripts/verify.sh.
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
mkdir -p .lake/verification-results

lake build DistinctDistances.Main
lake env leanchecker --fresh DistinctDistances.Main 2>&1 | tee .lake/verification-results/replay.log
