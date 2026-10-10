import DistinctDistances.TrackA.FormalJacobianPolynomialSupport
import OAI.Algebra.AlgebraicObstruction.EtaleCharts

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open MvPowerSeries
open OAI.BoundaryOnly.FormalObstruction.FormalCorrection

variable {K α ι : Type} [Field K] [Fintype α] [Fintype ι]

/-- Extension from the literal origin localization sends the polynomial
system ideal to the same formal polynomial system ideal. -/
theorem formalOrigin_localized_span_map
    (F : ι → MvPolynomial (α ⊕ ι) K) :
    (((Ideal.span (Set.range F)).map (algebraMap (MvPolynomial (α ⊕ ι) K)
      (AffineEtaleChart.base (K := K) (α := α ⊕ ι)).LocalRing)).map
        (AffineEtaleChart.base (K := K) (α := α ⊕ ι)).localExpansion.toRingHom) =
      Ideal.span (Set.range (fun i => (F i).toMvPowerSeries)) := by
  let E : AffineEtaleChart K (α ⊕ ι) := .base
  rw [Ideal.map_map, Ideal.map_span, ← Set.range_comp]
  apply congrArg (fun g : ι → MvPowerSeries (α ⊕ ι) K => Ideal.span (Set.range g))
  funext i
  change E.localExpansion (algebraMap (MvPolynomial (α ⊕ ι) K) E.LocalRing (F i)) = _
  change E.localExpansion (algebraMap E.S E.LocalRing (F i)) = _
  exact E.localExpansion_map (F i)

/-- Faithfully flat formal expansion contracts the nonsingular prime ideal
back to the actual localized polynomial equations. -/
theorem localCenteredPolynomial_ideal_isPrime
    (F : ι → MvPolynomial (α ⊕ ι) K) (hF : ∀ i, (F i).coeff 0 = 0)
    (hdet : IsUnit (internalJacobian F).det) :
    ((Ideal.span (Set.range F)).map (algebraMap (MvPolynomial (α ⊕ ι) K)
      (AffineEtaleChart.base (K := K) (α := α ⊕ ι)).LocalRing)).IsPrime := by
  let E : AffineEtaleChart K (α ⊕ ι) := .base
  let I := (Ideal.span (Set.range F)).map
    (algebraMap (MvPolynomial (α ⊕ ι) K) E.LocalRing)
  let : Module.FaithfullyFlat E.LocalRing (MvPowerSeries (α ⊕ ι) K) :=
    E.localFaithfullyFlat
  have hmap : I.map (algebraMap E.LocalRing (MvPowerSeries (α ⊕ ι) K)) =
      Ideal.span (Set.range (fun i => (F i).toMvPowerSeries)) :=
    formalOrigin_localized_span_map F
  have : (I.map (algebraMap E.LocalRing (MvPowerSeries (α ⊕ ι) K))).IsPrime := by
    rw [hmap]
    exact formalPolynomial_ideal_isPrime F hF hdet
  have hprime := Ideal.comap_isPrime (algebraMap E.LocalRing (MvPowerSeries (α ⊕ ι) K))
    (I.map (algebraMap E.LocalRing (MvPowerSeries (α ⊕ ι) K)))
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hprime
  exact hprime

end
end DistinctDistances.TrackA
