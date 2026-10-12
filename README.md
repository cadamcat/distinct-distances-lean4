[English](README.md) | [简体中文](README_zh.md)

# The higher-dimensional Erdős distinct-distances bound, in Lean 4

For each fixed dimension `d ≥ 3`, every `n`-point set in `ℝ^d` determines at least `c_d · n^(2/d)` distinct distances for some constant `c_d > 0`, and this order is best possible: for every `n ≥ 2` some `n`-point set determines at most `C_d · n^(2/d)` distinct distances.

- **Author:** Yao Xu ([@cadamcat](https://github.com/cadamcat)); see [authors and attribution](AUTHORS.md).
- **Mathematical result:** OpenAI, [*The higher-dimensional Erdős distinct-distances conjecture*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/paper.pdf), Theorem `thm:main` (with the matching grid upper bound of the introduction).
- Developed by the author with AI assistance; all proofs are verified by the Lean 4 kernel.

## Main result

The repository proves JSP-000900 as stated in [Challenge.lean](Challenge.lean):

```lean
namespace DistinctDistances

theorem jsp_000900 :
    ∀ d : ℕ, 3 ≤ d →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        (∀ P : Finset (EuclideanSpace ℝ (Fin d)), 2 ≤ P.card →
          c * (P.card : ℝ) ^ ((2 : ℝ) / (d : ℝ)) ≤ (distinctDistances P : ℝ)) ∧
        (∀ n : ℕ, 2 ≤ n → ∃ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n ∧
          (distinctDistances P : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)))
```

`distanceSet P` is the finite set of distances `dist p q` over the off-diagonal pairs of `P`, and `distinctDistances P` is its cardinality. Points live in `EuclideanSpace ℝ (Fin d)`; the powers are real powers (`Real.rpow`). The lower bound holds for every finite point set with at least two points, and the upper bound is realized, for every `n ≥ 2`, by some `n`-point set (a subset of an integer grid), so the exponent `2/d` is sharp, with no exact leading constant claimed.

[Challenge.lean](Challenge.lean) holds this statement and the definitions it uses, copied from Formal Conjectures, and imports only Mathlib. [DistinctDistances/Defs.lean](DistinctDistances/Defs.lean) holds an identical copy of the definitions used by the proof. [DistinctDistances/Main.lean](DistinctDistances/Main.lean) proves a theorem of the same name and statement from the lower-bound clause (`lower_bound`, track E) and the upper-bound clause (`upper_bound`). [Challenge.json](Challenge.json) configures Comparator to compare the two modules. [docs/verification.md](docs/verification.md) describes the statement checks and the differences from Formal Conjectures' files.

## How the proof is organized

The formal proof follows the paper. OpenAI's Lean library supplies the polynomial isolation interface (physical separators and isolation polynomials for the distance problem). This repository formalizes the rest of the paper: the polynomial method, incidence and ruling geometry, motion and planar inputs, curve and rank bridges, the secant/partition assembly, and the final induction establishing the lower bound, together with the grid construction for the matching upper bound.

| Path | Content |
| --- | --- |
| `DistinctDistances/Defs.lean` | verbatim copy of the Formal Conjectures definitions used by the proof |
| `DistinctDistances/Upper.lean` | `upper_bound`: the grid construction giving `C · n^(2/d)` distances |
| `DistinctDistances/Framework/` | failure regimes, asymptotic counting notation, diagonal induction setup |
| `DistinctDistances/Foundations/` | shared geometric model: affine and projective varieties, local algebra, projections |
| `DistinctDistances/TrackA/` | polynomial-method nodes: Bézout bounds, interpolation, Hilbert estimates, regularity, compression, projections |
| `DistinctDistances/TrackB/` | incidence geometry: Segre data, skew pencils, null-rigidity, incidence Hilbert bounds, refinement |
| `DistinctDistances/TrackC/` | motion and planar inputs: rich motions, weak planar bounds, canonical gradients |
| `DistinctDistances/Bridges/` | curve, component, rank and line bridges between the tracks |
| `DistinctDistances/TrackD/` | secant, tangent and partition assembly |
| `DistinctDistances/TrackE/` | final assembly: common inputs and `lower_bound` by strong induction on `d ≥ 3` |
| `DistinctDistances/Main.lean` | `DistinctDistances.jsp_000900` |
| `Audit/TargetProbes.lean`, `Audit/IndependentRestatement.lean` | kernel-checked probes of the target's definitions, and a restatement of the target with the distance count written out, proved equivalent to it |

## Build and verify

Requirements: Git, Python 3, and [elan](https://github.com/leanprover/elan), with `lake` available on `PATH`. From the repository root, a fresh checkout is prepared with:

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

OpenAI's `lake update` hook exits with an error beginning `iut: Lake resolved an unexpected checkout at …` after resolving the dependencies and writing `lake-manifest.json`. Run the patch script next; it applies OpenAI's Lean 4.34.1 compatibility patches to the fetched packages and can be run again after another `lake update`.

To check the frozen statement, the definitions, the axioms and the absence of forbidden constructs, run:

```sh
LEAN_NUM_THREADS=4 ./scripts/verify.sh
```

The script builds `DistinctDistances.Main`, checks that `Challenge.lean` matches its frozen commit, checks that the definitions and the elaborated statement of `DistinctDistances.jsp_000900` agree with `Challenge.lean`, checks that the theorem depends only on `propext`, `Classical.choice` and `Quot.sound`, and scans every Lean source of the repository for `sorry`, `admit`, added axioms, `native_decide`, `implemented_by`, `extern` and unsafe code. It exits with status 0 when every check passes, 2 when the proof still depends on `sorryAx`, and 1 on any other failure. `./scripts/replay.sh` replays the theorem's module and everything it imports in a fresh Lean kernel environment. [docs/verification.md](docs/verification.md) describes each check and the Comparator configuration.

## Fixed dependencies

- Lean `v4.34.1`, selected by [lean-toolchain](lean-toolchain).
- [Mathlib](https://github.com/leanprover-community/mathlib4), commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- OpenAI's [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean), commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- The remaining dependency revisions, pinned by OpenAI's library, are fixed in [lake-manifest.json](lake-manifest.json).

## Mathematical references

- OpenAI, [*The higher-dimensional Erdős distinct-distances conjecture*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/paper.pdf), September 23, 2026.
- P. Erdős, [On sets of distances of `n` points](https://www.renyi.hu/~p_erdos/1946-03.pdf), *American Mathematical Monthly* 53 (1946), 248–250. The planar problem has a different conjectural order.
- JSP-000900, "What is the minimum distinct-distance count for a prescribed number of points in fixed higher dimension?" (TheJustinSunPrize/awards at `16877004`, catalog section JSP-000900).

## License

Apache-2.0; see [LICENSE](LICENSE), [NOTICE](NOTICE), and [third-party attribution](THIRD_PARTY.md).
