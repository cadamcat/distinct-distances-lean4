import DistinctDistances.TrackA.ProjectiveConeFamily
import DistinctDistances.TrackA.RegularityAlgebraSupport
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

theorem homogeneous_equation_list {n : ℕ} (F : ProjectiveFamily.Family n) (D : ℕ) :
    ∃ E : List (Poly n),
      (∀ f ∈ E, f ∈ (ProjectiveFamily.locus F).ideal ∧ f.IsHomogeneous D) ∧
      ∀ f : Poly n, f ∈ (ProjectiveFamily.locus F).ideal → f.IsHomogeneous D →
        f ∈ Submodule.span ℂ {f | f ∈ E} := by
  let U := MvPolynomial.homogeneousSubmodule (Fin n) ℂ D ⊓
    (ProjectiveFamily.locus F).ideal.restrictScalars ℂ
  letI := OAI.QuarticPowerFree.totalSpace_finite (n := n) (K := ℂ) D
  have hle : U ≤ OAI.QuarticPowerFree.totalSpace D := by
    intro f hf
    exact OAI.QuarticPowerFree.mem_totalSpace.mpr hf.1.totalDegree_le
  letI : FiniteDimensional ℂ U := FiniteDimensional.of_injective
    (Submodule.inclusion hle) (Submodule.inclusion_injective _)
  have hspan : Submodule.span ℂ (U : Set (Poly n)) = U := Submodule.span_eq U
  letI : FiniteDimensional ℂ (Submodule.span ℂ (U : Set (Poly n))) := hspan.symm ▸
    (inferInstance : FiniteDimensional ℂ U)
  obtain ⟨s, hs, _, hsp, _⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℂ
    (U : Set (Poly n))
  refine ⟨s.toList, ?_, ?_⟩
  · intro f hf
    have hU := hs (by simpa using hf)
    exact ⟨hU.2, hU.1⟩
  · intro f hf hh
    have he : {f : Poly n | f ∈ s.toList} = (s : Set (Poly n)) := by ext; simp
    rw [he, hsp, hspan]
    exact ⟨hh, hf⟩

theorem derivativeEvaluation_mul {n : ℕ} (x v : Point n) (a b : Poly n) :
    derivativeEvaluation x v (a*b) = MvPolynomial.eval x a * derivativeEvaluation x v b +
      MvPolynomial.eval x b * derivativeEvaluation x v a := by
  simp [derivativeEvaluation, Derivation.leibniz, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

theorem homogeneous_span_kernel {n : ℕ} (F : ProjectiveFamily.Family n)
    (E : List (Poly n)) (D : ℕ)
    (hspan : ∀ f : Poly n, f ∈ (ProjectiveFamily.locus F).ideal → f.IsHomogeneous D →
      f ∈ Submodule.span ℂ {f | f ∈ E})
    (x v : Point n) (hx : x ∈ (ProjectiveFamily.locus F).affineCone.points)
    (hv : ∀ f ∈ E, differential f x v = 0)
    (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1) (hxℓ : MvPolynomial.eval x ℓ ≠ 0)
    (f : Poly n) (hf : f ∈ (ProjectiveFamily.locus F).ideal) (hd : f.totalDegree ≤ D) :
    differential f x v = 0 := by
  have hker : Submodule.span ℂ {f : Poly n | f ∈ E} ≤
      LinearMap.ker (derivativeEvaluation x v) := by
    apply Submodule.span_le.mpr
    intro f hf
    change derivativeEvaluation x v f = 0
    rw [derivativeEvaluation_apply]
    exact hv f hf
  have hc (i : ℕ) (hi : i ≤ D) :
      derivativeEvaluation x v (MvPolynomial.homogeneousComponent i f) = 0 := by
    let c := MvPolynomial.homogeneousComponent i f
    have hcI : c ∈ (ProjectiveFamily.locus F).ideal :=
      MvPolynomial.homogeneousComponent_mem_of_mem (ProjectiveFamily.locus F).isHomogeneous hf i
    have hpI : ℓ^(D-i)*c ∈ (ProjectiveFamily.locus F).ideal :=
      Ideal.mul_mem_left _ _ hcI
    have hpH : (ℓ^(D-i)*c).IsHomogeneous D := by
      convert (hℓ.pow (D-i)).mul (MvPolynomial.homogeneousComponent_isHomogeneous i f) using 1 <;> omega
    have hp0 := hker (hspan _ hpI hpH)
    change derivativeEvaluation x v (ℓ^(D-i)*c) = 0 at hp0
    have hc0 : MvPolynomial.eval x c = 0 := by
      simpa [MvPolynomial.aeval_eq_eval] using hx c hcI
    rw [derivativeEvaluation_mul, hc0, zero_mul, add_zero, map_pow] at hp0
    exact (mul_eq_zero.mp hp0).resolve_left (pow_ne_zero _ hxℓ)
  rw [← derivativeEvaluation_apply, ← chart_components_sum f hd, map_sum]
  exact Finset.sum_eq_zero (fun i hi => hc i (by simpa using Finset.mem_range.mp hi))

theorem homogeneous_evaluatedJacobian_kernel {n : ℕ} (F : ProjectiveFamily.Family n)
    (E : List (Poly n)) (D : ℕ)
    (hE : ∀ f ∈ E, f ∈ (ProjectiveFamily.locus F).ideal ∧ f.IsHomogeneous D)
    (hspan : ∀ f : Poly n, f ∈ (ProjectiveFamily.locus F).ideal → f.IsHomogeneous D →
      f ∈ Submodule.span ℂ {f | f ∈ E})
    (x : Point n) (hx : x ∈ (ProjectiveFamily.locus F).affineCone.points)
    (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1) (hxℓ : MvPolynomial.eval x ℓ ≠ 0) :
    LinearMap.ker (evaluatedJacobian E x).mulVecLin = boundedJacobianKernel (coneFamily F) D x := by
  ext v
  have hmatrix : v ∈ LinearMap.ker (evaluatedJacobian E x).mulVecLin ↔
      ∀ f ∈ E, differential f x v = 0 := by
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff]
    have hget : (∀ i : Fin E.length, differential (E.get i) x v = 0) ↔
        ∀ f ∈ E, differential f x v = 0 := by
      constructor
      · intro h f hf
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hf
        exact h i
      · intro h i
        exact h _ (List.get_mem _ _)
    rw [← hget]
    simp [evaluatedJacobian, jacobian, Matrix.mulVec, dotProduct, differential,
      MvPolynomial.aeval_eq_eval]
  rw [hmatrix]
  simp only [boundedJacobianKernel, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hv f
    have hf : f.val ∈ (ProjectiveFamily.locus F).ideal := by
      simpa only [coneFamily_locus, ProjectiveVariety.affineCone] using f.property.1
    exact homogeneous_span_kernel F E D hspan x v hx hv ℓ hℓ hxℓ f.val hf f.property.2
  · intro hv f hf
    have hfI : f ∈ (AffineFamily.locus (coneFamily F)).ideal := by
      simpa only [coneFamily_locus, ProjectiveVariety.affineCone] using (hE f hf).1
    exact hv ⟨f, hfI, (hE f hf).2.totalDegree_le⟩

end
end DistinctDistances.TrackA
