import DistinctDistances.TrackE.CommonImageData
import DistinctDistances.TrackD.RationalFunctionField
import DistinctDistances.Foundations.ImageOpen

/-! Reciprocal-coordinate polynomial graphs for the literal rational image,
consumed in `sc:retained-products.family`, sparse-cones.tex:158–178. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

/-- Original source coordinates in the tail of the reciprocal graph. -/
def commonTailRename {n : ℕ} : Poly n →ₐ[ℂ] Poly (n + 1) :=
  { MvPolynomial.rename Fin.succ with commutes' := by intro c; simp }

/-- The reciprocal coordinate and every original source coordinate in the
actual coordinate function field; its kernel defines the graph. -/
def commonReciprocalEvaluation {n : ℕ} (K : Type*) [Field K] [Algebra ℂ K]
    (φ : Poly n →ₐ[ℂ] K) (g : Poly n) : Poly (n + 1) →ₐ[ℂ] K :=
  MvPolynomial.aeval (Fin.cons (φ g)⁻¹ (fun i => φ (MvPolynomial.X i)))

/-- A polynomial map on the graph, using the one reciprocal denominator. -/
def commonReciprocalLabelMap {n m : ℕ} (f : Fin m → Poly n) :
    Poly m →ₐ[ℂ] Poly (n + 1) :=
  MvPolynomial.aeval (fun i => MvPolynomial.X 0 * commonTailRename (f i))

end
end DistinctDistances.SparseCones
