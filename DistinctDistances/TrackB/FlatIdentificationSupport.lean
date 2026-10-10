import DistinctDistances.TrackB.FlatEndpointSupport
import DistinctDistances.TrackB.IncidenceLinearSupport

namespace DistinctDistances.TrackB
noncomputable section
open LinearMap (BilinForm)

/-- An affine fiber of a linear coordinate map is already Zariski closed. -/
theorem affine_linear_fiber_closed {n m : ℕ} (E : Point n →ₗ[ℂ] Point m) (y : Point m) :
    (AffineVariety.closure {z | E z = y}).points = {z | E z = y} := by
  apply Set.Subset.antisymm ?_ (AffineVariety.subset_closure _)
  intro z hz
  let ψ : AffineProjection n m := ⟨E, 0⟩
  funext i
  let f : Poly n := ψ.pullback (MvPolynomial.X i - MvPolynomial.C (y i))
  have hf : f ∈ (AffineVariety.closure {z | E z = y}).ideal := by
    intro x hx
    change E x = y at hx
    change MvPolynomial.aeval x (ψ.pullback _) = 0
    rw [AffineProjection.eval_pullback]
    simp [AffineProjection.apply, ψ, hx]
  have heq := hz f hf
  rw [AffineProjection.eval_pullback] at heq
  simp only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C] at heq
  have heq' : E z i - y i = 0 := by simpa [AffineProjection.apply, ψ] using heq
  exact sub_eq_zero.mp heq'

theorem evaluationFlat_closed {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) :
    (AffineVariety.closure (evaluationFlat C p)).points = evaluationFlat C p := by
  let E : Point (skewDim e) →ₗ[ℂ] Point e :=
    (covectorPointLinear e).comp ((alternatingEvaluation (firstPoint p.rep)).comp C.decode.toLinearMap)
  have hset : evaluationFlat C p = {z | E z = secondPoint p.rep} := by
    ext z
    constructor
    · intro hz
      change pointOfCovector ((C.decode z).val (firstPoint p.rep)) = secondPoint p.rep
      rw [hz, point_covector_inverse]
    · intro hz
      have heq := congrArg covectorOfPoint hz
      change covectorOfPoint (pointOfCovector ((C.decode z).val (firstPoint p.rep))) =
        covectorOfPoint (secondPoint p.rep) at heq
      change (C.decode z).val (firstPoint p.rep) = covectorOfPoint (secondPoint p.rep)
      rwa [covector_point_inverse] at heq
  rw [hset]
  exact affine_linear_fiber_closed E _

/-- For e≥3, inclusion between evaluation flats determines their projective parameter. -/
theorem evaluationFlat_parameter_injective {e : ℕ} (C : SkewCoordinates e) (he : 3 ≤ e)
    (p q : ProjectivePoint (e + e)) (hp : p ∈ affineParameters e)
    (hq : q ∈ affineParameters e) (hsub : evaluationFlat C p ⊆ evaluationFlat C q) : p = q := by
  let v := firstPoint p.rep
  let w := firstPoint q.rep
  let y := covectorOfPoint (secondPoint p.rep)
  let η := covectorOfPoint (secondPoint q.rep)
  obtain ⟨b, φ, hφ, hset⟩ := evaluationFlat_affine_coordinates C p hp
  have hbp : b ∈ evaluationFlat C p := by rw [hset]; exact ⟨0, by simp⟩
  have hbq : b ∈ evaluationFlat C q := hsub hbp
  have hwv : w ∈ Submodule.span ℂ {v} := by
    apply alternating_kernel_common_radical he v w hp.2
    intro D hD hDv
    let zD := C.decode.symm ⟨D, hD⟩
    have hzDp : b + zD ∈ evaluationFlat C p := by
      change (C.decode (b + zD)).val v = y
      rw [map_add, Submodule.coe_add, LinearMap.add_apply]
      have hDz : (C.decode zD).val = D := by simp [zD]
      rw [hDz, hDv, add_zero]
      exact hbp
    have hzDq : b + zD ∈ evaluationFlat C q := hsub hzDp
    change (C.decode (b + zD)).val w = η at hzDq
    have heq : (C.decode b).val w + D w = η := by simpa [zD] using hzDq
    have hbq' : (C.decode b).val w = η := hbq
    rw [hbq'] at heq
    exact add_left_cancel (heq.trans (add_zero η).symm)
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hwv
  have hw : w = t • v := ht.symm
  have hη : η = t • y := by
    calc
      η = (C.decode b).val w := hbq.symm
      _ = t • ((C.decode b).val v) := by rw [hw, map_smul]
      _ = t • y := by rw [show (C.decode b).val v = y from hbp]
  have hsecond : secondPoint q.rep = t • secondPoint p.rep := by
    have h := congrArg pointOfCovector hη
    simpa only [η, y, point_covector_inverse, pointOfCovector_smul] using h
  have hrep : q.rep = t • p.rep := by
    calc
      q.rep = joinPoints w (secondPoint q.rep) := (joinPoints_eta q.rep).symm
      _ = joinPoints (t • v) (t • secondPoint p.rep) := by rw [hw, hsecond]
      _ = t • p.rep := by rw [joinPoints_smul, joinPoints_eta]
  symm
  rw [← Projectivization.mk_rep q, ← Projectivization.mk_rep p]
  exact (Projectivization.mk_eq_mk_iff' ℂ q.rep p.rep q.rep_nonzero p.rep_nonzero).mpr
    ⟨t, hrep.symm⟩

theorem carrier_eq_evaluationFlat_closure {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (hp : p ∈ affineParameters e)
    (V : AffineVariety (skewDim e)) (hV : V.IsIrreducible)
    (hdim : V.dimension = flatDim e) (hsub : evaluationFlat C p ⊆ V.points) :
    V = AffineVariety.closure (evaluationFlat C p) := by
  let W := AffineVariety.closure (evaluationFlat C p)
  letI : V.ideal.IsPrime := hV
  letI : W.ideal.IsPrime := evaluationFlat_vanishingIdeal_prime C p hp
  have hle : V.ideal ≤ W.ideal := by
    intro f hf z hz
    exact hsub hz f hf
  apply AffineVariety.ext
  exact Request.affine_prime_same_dimension_eq V.ideal W.ideal hle hdim
    (evaluationFlat_closure_dimension C p hp)

theorem same_dimension_carrier_unique_parameter {e : ℕ} (C : SkewCoordinates e) (he : 3 ≤ e)
    (V : AffineVariety (skewDim e)) (hV : V.IsIrreducible) (hdim : V.dimension = flatDim e)
    (p q : ProjectivePoint (e + e)) (hp : p ∈ affineParameters e)
    (hq : q ∈ affineParameters e) (hVp : evaluationFlat C p ⊆ V.points)
    (hVq : evaluationFlat C q ⊆ V.points) : p = q := by
  apply evaluationFlat_parameter_injective C he p q hp hq
  have hqeq := carrier_eq_evaluationFlat_closure C q hq V hV hdim hVq
  rw [hqeq, evaluationFlat_closed] at hVp
  exact hVp

#print axioms affine_linear_fiber_closed
#print axioms evaluationFlat_closed
#print axioms evaluationFlat_parameter_injective
#print axioms carrier_eq_evaluationFlat_closure
#print axioms same_dimension_carrier_unique_parameter
end
end DistinctDistances.TrackB
