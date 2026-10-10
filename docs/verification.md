# Reproducing the verification

The project uses Lean `v4.34.1`, selected by [lean-toolchain](../lean-toolchain). Mathlib (commit `d13f23b723b8a846827a245b89c10fc7d3f11612`), OpenAI's library (commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`) and the other package revisions are locked in [lake-manifest.json](../lake-manifest.json).

## Fresh checkout

From the repository root, prepare the dependencies and build the project:

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

OpenAI's Lake hook exits with an error beginning `iut: Lake resolved an unexpected checkout at …`. It has still resolved the dependencies and written `lake-manifest.json`; run the patch script after that error. The script applies the `*-lean4341.patch` files from OpenAI's package to the fetched packages and skips patches that are already applied. The hook leaves unused package clones under `.lake/packages/OAI/lean/.lake/packages/`; those clones can be removed.

## Statement and axiom checks

```sh
LEAN_NUM_THREADS=4 ./scripts/verify.sh
```

The script runs six checks in order and stops at the first failure:

1. `lake build DistinctDistances.Main` builds the theorem and every project module it imports.
2. `git diff --quiet 324083b -- Challenge.lean` checks that `Challenge.lean` matches its frozen commit `324083b`.
3. `python3 scripts/check_target.py defs` checks that the block between the `BEGIN` and `END FORMAL CONJECTURES DEFINITIONS` markers is identical in `Challenge.lean` and `DistinctDistances/Defs.lean`, and that it holds only the copied declarations (`distanceSet`, `distinctDistances`). The proof never imports `Challenge.lean`; this block is what its definitions share with the challenge.
4. `python3 scripts/check_target.py statement` elaborates `Challenge.lean` and, in a separate Lean run, `DistinctDistances.Main`. Each run prints, with `set_option pp.all true`, the type of `DistinctDistances.jsp_000900` and the declarations `distanceSet` and `distinctDistances`. The two outputs must be identical. Separate runs are needed because both modules declare the same names.
5. `lake env lean --trust=0 scripts/Axioms.lean` prints the axioms of `DistinctDistances.jsp_000900`, and `scripts/check_axioms.py` parses the report. The accepted axioms are `propext`, `Classical.choice` and `Quot.sound`.
6. `python3 scripts/check_forbidden.py` scans every Lean source of the repository (`DistinctDistances.lean` and the files under `DistinctDistances/`, `Audit/` and `scripts/`) for `sorry`, `admit`, `axiom` declarations, `native_decide`, `implemented_by`, `extern` and unsafe code (comments stripped first). `Challenge.lean` states the target with `sorry` as its proof, as a challenge module does; it is scanned for every other construct.

The script exits with status 0 when all six checks pass. If the theorem or a dependency still has an open proof, the axiom report lists `sorryAx` and the script exits with status 2. Any other axiom, a missing or unparsable report, a Lean error, a failed build, statement or frozen-file check, or any forbidden-construct hit gives status 1. The axiom report is written to `.lake/verification-results/axioms.log`. `python3 scripts/check_target.py types` runs checks 1, 4 and 5 in one command and fails on `sorryAx` like on any other axiom outside the accepted set.

The build compiles the project's modules and the modules of OpenAI's library they import. For Mathlib it uses the compiled artifacts that `lake exe cache get` downloads for the pinned revision and does not rebuild Mathlib from source; `scripts/replay.sh` rechecks those artifacts in the kernel.

## Kernel replay

```sh
./scripts/replay.sh
```

The script builds `DistinctDistances.Main` and runs `lake env leanchecker --fresh DistinctDistances.Main`, which replays the declarations of the main module and of every module it imports, cached dependency artifacts included, in a fresh Lean kernel environment. The output is written to `.lake/verification-results/replay.log`. The replay covers the whole of Mathlib that the proof imports and takes much longer than `verify.sh`. It is a second check by the same Lean kernel, not by an independent one.

## Comparator

[Challenge.json](../Challenge.json) configures [Comparator](https://github.com/leanprover/comparator) with the challenge module `Challenge`, the solution module `DistinctDistances.Main`, the theorem `DistinctDistances.jsp_000900`, and the permitted axioms `propext`, `Quot.sound` and `Classical.choice`. Comparator requires every declaration used in the statement of the listed theorem to be the same in both modules, and the solution's theorem to be accepted by the kernel with only the permitted axioms.

`definition_names` is empty. Comparator treats the names listed there as definition holes, for which it checks only the name, type, universe levels and safety, not the definition itself. The Formal Conjectures definitions are fixed parts of the statement, so listing them would weaken the comparison. Running Comparator requires `lean4export` built for the project's Lean version and the `landrun` sandbox; the Comparator repository describes the setup.

## Size and build time

The project has 751 Lean modules (`DistinctDistances.lean` and the files under `DistinctDistances/`) with 7572 declarations, 5553 of them theorems. With OpenAI's library and Mathlib already compiled, `lake build` compiled all 751 project modules from a clean build directory in 1483 seconds of wall time (10181 jobs, exit status 0) on an 18-core workstation.

## Independent check of v1.0.0

On 10 October 2026 (UTC), release `v1.0.0` (commit `0e56d4c94cd6af4292479c961eb3dff10421ef56`) was cloned from GitHub into an empty scratch directory on a 32-core compute node and checked with the steps of [Fresh checkout](#fresh-checkout), in order:

| Step | Result |
|---|---|
| `lake update` | exit 1 with the `iut: Lake resolved an unexpected checkout at …` hook error described above; the revisions it resolved for all 43 packages equal those in `lake-manifest.json` |
| `scripts/apply-oai-patches.sh` | exit 0 |
| `lake exe cache get`, then `lake build` | exit 0 (10181 jobs, 65 minutes); no errors and no `sorry`. The Mathlib cache files were already in the local cache, so nothing was downloaded |
| `#print axioms DistinctDistances.jsp_000900` | `propext`, `Classical.choice` and `Quot.sound` only |
| `lake env leanchecker --fresh DistinctDistances.Main` | exit 0 (37 minutes): the kernel replayed the declarations of the main module and of everything it imports, including the cached dependency artifacts |

`scripts/verify.sh` and Comparator were not part of this run.

Software Heritage snapshot: [`swh:1:snp:f64f8482e9bef79632dd44dd664e6ba1bb0c3065`](https://archive.softwareheritage.org/api/1/snapshot/f64f8482e9bef79632dd44dd664e6ba1bb0c3065/) (visit of 2026-10-10 20:01 UTC).

## Statement fidelity

The statement is the paper's Theorem `thm:main` (with the grid upper bound of the introduction), clause by clause:

| Lean statement | Paper, Theorem `thm:main` and the introduction |
|---|---|
| `∀ d : ℕ, 3 ≤ d` | every fixed integer `d ≥ 3` |
| `∃ c C : ℝ, 0 < c ∧ 0 < C` before the point-set quantifiers | dimension-dependent constants, independent of the set and of `n` |
| `∀ P : Finset (EuclideanSpace ℝ (Fin d)), 2 ≤ P.card` | every finite set `P ⊂ ℝ^d` of `n ≥ 2` distinct points |
| `distanceSet P`: off-diagonal image of `dist`; `distinctDistances P`: its cardinality | `Δ(P) = {\|p − q\| : p, q ∈ P, p ≠ q}` and `\|Δ(P)\|` |
| `c * (P.card : ℝ) ^ ((2 : ℝ) / (d : ℝ)) ≤ (distinctDistances P : ℝ)`, a real power | `\|Δ(P)\| ≥ c_d n^{2/d}` |
| `∀ n : ℕ, 2 ≤ n → ∃ P, P.card = n ∧ (distinctDistances P : ℝ) ≤ C * (n : ℝ) ^ …` | the grid optimality note: some `n`-point set has `O(n^{2/d})` distances, so the exponent is sharp |

The count is the cardinality of the off-diagonal distance image, which is empty for sets with fewer than two points and a singleton for two-point sets; ordered pairs contribute one distance per unordered pair by symmetry of `dist`. The following kernel-checked files exclude misreadings:

- [Audit/TargetProbes.lean](../Audit/TargetProbes.lean): the distance set of empty and singleton sets is empty, a two-point set determines exactly one distance, the off-diagonal pair count, and at least one distance for every set with two or more points.
- [Audit/IndependentRestatement.lean](../Audit/IndependentRestatement.lean): `FidelityProbe.Indep` restates the target with the distance count written out as an off-diagonal image cardinality, without the copied definitions. `FidelityProbe.fc_iff_indep` proves it equivalent to the target. Further examples check the unfolding of `distanceSet` and the same boundary cases.
- [Audit/NonVacuity.lean](../Audit/NonVacuity.lean): applies both clauses of `jsp_000900` to explicit point sets in dimension three, computes `distinctDistances` on small sets (`{0, e₀}` gives one distance, `{0, e₀, 2e₀}` gives two), and derives the two-sided bound `c n^(2/d) ≤ g_d(n) ≤ C n^(2/d)` for the minimum `g_d(n)` over `n`-point sets, after showing that this minimum is attained.

After `lake build`, check them with:

```sh
lake env lean Audit/TargetProbes.lean
lake env lean Audit/IndependentRestatement.lean
lake env lean Audit/NonVacuity.lean
```

To check the copies against Formal Conjectures itself:

```sh
git clone https://github.com/google-deepmind/formal-conjectures
git -C formal-conjectures checkout 660712921cf75e22b926536e8430cb613517e3ff
python3 scripts/check_target.py defs formal-conjectures
```

With a checkout argument, `defs` also checks that each copied declaration, with its docstring, occurs verbatim in Formal Conjectures' `FormalConjecturesForMathlib/Geometry/Metric.lean`.

### Differences from Formal Conjectures' files

- The module-system wrappers (`module`, `public import`, `@[expose] public section`) are dropped; the project does not use the module system. They do not change the elaborated definitions.
- Formal Conjectures' `Erdos1083.erdos_1083` asks for the weaker `n^(2/d - o(1))` lower-bound form. The target states the exact-order two-sided bound with `n^(2/d)` proved in the paper: the lower bound for every point set and the matching upper bound by grid subsets.
- The two-sentence docstrings of `distanceSet` and `distinctDistances` are kept; only the module-system wrappers are dropped.
