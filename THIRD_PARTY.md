# Third-party code and mathematical sources

## OpenAI's Lean library

This project depends on [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean), commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, under the Apache-2.0 license. The upstream repository has no NOTICE file. Lake fetches the library; no OpenAI source file is copied into this repository.

The proof imports, among others, `OAI.Combinatorics.Distances.PolynomialIsolation`, which provides the physical separators and isolation polynomials for the distance problem. `grep -rn '^import OAI' DistinctDistances` lists the importing files.

## Formal Conjectures definitions

The definitions `distanceSet` and `distinctDistances` are copied from Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/tree/660712921cf75e22b926536e8430cb613517e3ff), commit `660712921cf75e22b926536e8430cb613517e3ff`, Copyright 2025 The Formal Conjectures Authors, under the Apache-2.0 license:

| Upstream file | Declarations | Copied into |
|---|---|---|
| `FormalConjecturesForMathlib/Geometry/Metric.lean` | `distanceSet`, `distinctDistances` | `Challenge.lean`, `DistinctDistances/Defs.lean` |
| `FormalConjectures/ErdosProblems/1083.lean` | `Erdos1083.erdos_1083` (statement only, not copied) | — |

The copies drop only the module-system wrappers; the header comments of `Challenge.lean` and `DistinctDistances/Defs.lean` record the source. Formal Conjectures' `erdos_1083` asks for the weaker `n^(2/d - o(1))` lower-bound form; the target `DistinctDistances.jsp_000900` states the exact-order two-sided bound with `n^(2/d)` (lower bound for every point set, matching upper bound by grid subsets), following the paper's Theorem `thm:main` and its grid optimality note. `scripts/check_target.py defs` checks that each copied declaration appears verbatim in the upstream file; [docs/verification.md](docs/verification.md#statement-fidelity) describes the check.

## Mathlib and other Lean packages

The project uses [Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612), commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, under the Apache-2.0 license. OpenAI's library pins Mathlib and further Lean packages; [lake-manifest.json](lake-manifest.json) records the exact revisions. These packages are fetched by Lake, not redistributed here, and their licenses and notices remain with them.

Lean is selected by [lean-toolchain](lean-toolchain) and installed separately.

## Mathematical sources

The formalized result is OpenAI, [*The higher-dimensional Erdős distinct-distances conjecture*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/paper.pdf), Theorem `thm:main` (with the grid upper bound of the introduction). It resolves the higher-dimensional Erdős distinct-distances conjecture. The repository formalizes the result and does not claim new mathematics.
