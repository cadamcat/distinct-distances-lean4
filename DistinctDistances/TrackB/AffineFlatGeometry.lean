import DistinctDistances.TrackB.GeometryModel
import Mathlib.Algebra.MvPolynomial.Funext

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators

def affineLinearPullback {n m : ℕ} (a : Point n) (φ : Point m →ₗ[ℂ] Point n) :
    Poly n →ₐ[ℂ] Poly m :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (a i) +
    ∑ j : Fin m, MvPolynomial.C (φ (Pi.single j 1) i) * MvPolynomial.X j)

theorem eval_affineLinearPullback {n m : ℕ} (a : Point n)
    (φ : Point m →ₗ[ℂ] Point n) (t : Point m) (f : Poly n) :
    MvPolynomial.aeval t (affineLinearPullback a φ f) =
      MvPolynomial.aeval (a + φ t) f := by
  have ht : (∑ j : Fin m, t j • Pi.single j (1 : ℂ)) = t := by
    simpa using (Pi.basisFun ℂ (Fin m)).sum_repr t
  have hφ (i : Fin n) : φ t i = ∑ j : Fin m, φ (Pi.single j 1) i * t j := by
    conv_lhs => rw [← ht, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [affineLinearPullback, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun g : Point n => MvPolynomial.aeval g f)
  funext i
  simp [hφ, Pi.add_apply]

/-- The B38 affine-flat component argument uses a polynomial-domain pullback.
No dimension or degree convention is introduced. -/
theorem vanishingIdeal_affineLinearImage_prime {n m : ℕ} (a : Point n)
    (φ : Point m →ₗ[ℂ] Point n) :
    (MvPolynomial.vanishingIdeal ℂ {x | ∃ t : Point m, x = a + φ t}).IsPrime := by
  let ψ := affineLinearPullback a φ
  have hmem (f : Poly n) :
      f ∈ MvPolynomial.vanishingIdeal ℂ {x | ∃ t : Point m, x = a + φ t} ↔ ψ f = 0 := by
    constructor
    · intro hf
      apply MvPolynomial.funext
      intro t
      change MvPolynomial.aeval t (ψ f) = MvPolynomial.aeval t 0
      rw [eval_affineLinearPullback]
      simpa using hf (a + φ t) ⟨t, rfl⟩
    · intro hf x hx
      obtain ⟨t, rfl⟩ := hx
      have hz := congrArg (MvPolynomial.aeval t) hf
      simpa only [ψ, eval_affineLinearPullback, map_zero] using hz
  have hI : MvPolynomial.vanishingIdeal ℂ {x | ∃ t : Point m, x = a + φ t} =
      RingHom.ker ψ.toRingHom := by
    ext f
    exact hmem f
  rw [hI]
  exact RingHom.ker_isPrime _

/-- The actual nonempty evaluation flat has a prime vanishing ideal, sufficient
to put a flat contained in a hypersurface into one of its components. -/
theorem evaluationFlat_vanishingIdeal_prime {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (hp : p ∈ affineParameters e) :
    (MvPolynomial.vanishingIdeal ℂ (evaluationFlat C p)).IsPrime := by
  let v := firstPoint p.rep
  let y := covectorOfPoint (secondPoint p.rep)
  have hv : v ≠ 0 := hp.2
  have hy : y v = 0 := hp.1
  obtain ⟨D, hD, hDv⟩ := alternating_evaluation_surjective v hv y hy
  let z0 := C.decode.symm ⟨D, hD⟩
  have hz0 : z0 ∈ evaluationFlat C p := by
    change (C.decode z0).val v = y
    simpa [z0] using hDv
  let E : Point (skewDim e) →ₗ[ℂ] Module.Dual ℂ (Point e) :=
    (alternatingEvaluation v).comp C.decode.toLinearMap
  let K := LinearMap.ker E
  let b := Module.finBasis ℂ K
  let φ : Point (Module.finrank ℂ K) →ₗ[ℂ] Point (skewDim e) :=
    K.subtype.comp b.equivFun.symm.toLinearMap
  have hset : evaluationFlat C p =
      {z | ∃ t : Point (Module.finrank ℂ K), z = z0 + φ t} := by
    ext z
    constructor
    · intro hz
      have hEz : E z = y := hz
      have hE0 : E z0 = y := hz0
      have hk : z - z0 ∈ K := by
        rw [LinearMap.mem_ker, map_sub, hEz, hE0, sub_self]
      let k : K := ⟨z - z0, hk⟩
      refine ⟨b.equivFun k, ?_⟩
      have hφk : φ (b.equivFun k) = z - z0 := by simp [φ, k]
      rw [hφk]
      abel
    · rintro ⟨t, rfl⟩
      have hk : E (φ t) = 0 := by
        exact (b.equivFun.symm t).property
      change E (z0 + φ t) = y
      rw [map_add, hk, add_zero]
      exact hz0
  rw [hset]
  exact vanishingIdeal_affineLinearImage_prime z0 φ

theorem evaluationFlat_in_component {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (hp : p ∈ affineParameters e)
    (V : AffineVariety (skewDim e)) (hsub : evaluationFlat C p ⊆ V.points) :
    ∃ W : V.Component, evaluationFlat C p ⊆ W.variety.points := by
  let I := MvPolynomial.vanishingIdeal ℂ (evaluationFlat C p)
  letI : I.IsPrime := evaluationFlat_vanishingIdeal_prime C p hp
  have hle : V.ideal ≤ I := by
    intro f hf z hz
    exact hsub hz f hf
  obtain ⟨Q, hQ, hQI⟩ := Ideal.exists_minimalPrimes_le hle
  refine ⟨⟨Q, hQ⟩, ?_⟩
  intro z hz f hf
  exact hQI hf z hz

end
end DistinctDistances.TrackB
