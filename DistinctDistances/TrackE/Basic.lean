import DistinctDistances.Defs
import DistinctDistances.Framework.Regime
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Track E: shared elementary notions

`RPoint`, `LowerBound` and `IH` are the frozen framework's (`Framework/Regime.lean`).
Definitions used by the reduction (paper §2, `reduction.tex`) and the sparse-cones statement
(paper §6, `sparse-cones.tex`). They need Mathlib only, so the statements built from them can be
frozen before track A's variety model is on `main`. Notation follows the paper:
`N = |P|`, `M = 1 + |Δ(P)|`, `B = N^{1/d}`, `A = B^2` (`reduction.tex:12-19`).

Node IDs (`FW.*`, `red:*`, `sc:*`) refer to `BLUEPRINT.md` and the lane's `DESIGN.md`.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

/-! ## FW.regime: the paper's scales -/

/-- `M = 1 + |Δ(P)|`, the paper's convention (`reduction.tex:16`). -/
def Mcount {d : ℕ} (P : Finset (RPoint d)) : ℝ := (distinctDistances P : ℝ) + 1

/-- `A = N^{2/d}` (`reduction.tex:16-17`). -/
def Ascale (d N : ℕ) : ℝ := (N : ℝ) ^ ((2 : ℝ) / (d : ℝ))

/-- `B = N^{1/d}` (`reduction.tex:16-17`). -/
def Bscale (d N : ℕ) : ℝ := (N : ℝ) ^ ((1 : ℝ) / (d : ℝ))

/-- The testing degree `D = ⌊A⌋` (`reduction.tex:209, 465`). -/
def testDegree (d N : ℕ) : ℕ := ⌊Ascale d N⌋₊

/-! ## Complex directions -/

/-- The complexification `ℝ^d → ℂ^d` of a Euclidean point or vector. -/
def cplx {d : ℕ} (v : RPoint d) : Fin d → ℂ := fun i => ((v i : ℝ) : ℂ)

/-! ## Restriction ranks -/

/-- Restriction of polynomials of total degree at most `D` to a set `T`. -/
def restrictionMap {σ : Type*} (T : Set (σ → ℂ)) (D : ℕ) :
    MvPolynomial.restrictTotalDegree σ ℂ D →ₗ[ℂ] (T → ℂ) :=
  LinearMap.pi fun x : T =>
    (MvPolynomial.aeval (x : σ → ℂ)).toLinearMap.comp
      (MvPolynomial.restrictTotalDegree σ ℂ D).subtype

/-- `H_T(D)`, the rank of restriction of polynomials of degree at most `D` to `T`
(`polynomial.tex:19-22`, `reduction.tex:74-78`). This is the number track A's
`hilbertOfSet T D` computes; the bridge is an impl node. -/
def restrictionRank {σ : Type*} (T : Set (σ → ℂ)) (D : ℕ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (restrictionMap T D))

/-- Evaluation of homogeneous polynomials of degree `D` at a vector of `ℂ^d`. -/
def homEval (d D : ℕ) (v : Fin d → ℂ) :
    Module.Dual ℂ (MvPolynomial.homogeneousSubmodule (Fin d) ℂ D) :=
  (MvPolynomial.aeval v).toLinearMap.comp (MvPolynomial.homogeneousSubmodule (Fin d) ℂ D).subtype

/-! ## Stars and symmetric selections -/

section Stars

variable {d : ℕ}

/-- A symmetric selection of ordered pairs of distinct points of `P` (an undirected graph). -/
def IsSymmSelection (P : Finset (RPoint d)) (S : Finset (RPoint d × RPoint d)) : Prop :=
  S ⊆ P.offDiag ∧ ∀ e ∈ S, e.swap ∈ S

open Classical in
/-- The star of `p` in a set of ordered pairs: its partners. -/
def star (S : Finset (RPoint d × RPoint d)) (p : RPoint d) : Finset (RPoint d) :=
  (S.filter fun e => e.1 = p).image Prod.snd

/-- Homogeneous degree-`D` rank of the directions from `p` to the points of `T`
(`reduction.tex:215-230`). -/
def starRank (D : ℕ) (p : RPoint d) (T : Finset (RPoint d)) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ
    (Set.range fun q : T => homEval d D (cplx ((q : RPoint d) - p))))

/-- The direction-evaluation vectors from `p` to `T` are linearly independent for homogeneous
polynomials of degree `D` (`reduction.tex:204-212`). -/
def IndependentStar (D : ℕ) (p : RPoint d) (T : Finset (RPoint d)) : Prop :=
  LinearIndependent ℂ (fun q : T => homEval d D (cplx ((q : RPoint d) - p)))

end Stars

end

end DistinctDistances
