# Authors and attribution

Yao Xu is the author and maintainer of this formalization project. The author planned, dispatched and reviewed the work, set its acceptance criteria (only the standard axioms, fidelity of every frozen statement, checking by the Lean kernel) and decided on its publication.

The mathematical theorem was proved by OpenAI, in the paper [*The higher-dimensional Erdős distinct-distances conjecture*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/paper.pdf). It resolves the higher-dimensional Erdős distinct-distances conjecture. This repository formalizes the theorem; it does not claim a new mathematical solution. The formal proof follows the paper and takes the polynomial isolation interface (physical separators and isolation polynomials) from OpenAI's Lean library.

AI coding agents wrote the Lean code under acceptance criteria set by the author. Model agreement was not treated as verification: the resulting proofs and their dependencies were checked by the Lean kernel.

The project uses Mathlib, OpenAI's `openai/math` library and the packages it pins, and definitions copied from Google DeepMind's Formal Conjectures. Their authors and licenses are credited in [THIRD_PARTY.md](THIRD_PARTY.md) and [NOTICE](NOTICE).
