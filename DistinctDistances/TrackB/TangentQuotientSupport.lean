import DistinctDistances.TrackB.ParameterDifferentialSupport
import DistinctDistances.TrackB.NullProjectiveSupport
import DistinctDistances.TrackB.IncidenceLinearSupport

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators

/-- A linear section of the quotient by one direction, used only to write
covectors on that quotient. All geometric formulas are independent of it. -/
def directionQuotientSection {e : ℕ} (v : Point e) :
    (Point e ⧸ Submodule.span ℂ {v}) →ₗ[ℂ] Point e :=
  (Submodule.span ℂ {v}).mkQ.exists_rightInverse_of_surjective
    (Submodule.range_mkQ _ ) |>.choose

theorem directionQuotientSection_rightInverse {e : ℕ} (v : Point e) :
    (Submodule.span ℂ {v}).mkQ.comp (directionQuotientSection v) = LinearMap.id :=
  ((Submodule.span ℂ {v}).mkQ.exists_rightInverse_of_surjective
    (Submodule.range_mkQ _)).choose_spec

/-- Restrict an annihilating covector to the quotient by the direction. -/
theorem directionQuotientSection_covector {e : ℕ} (v : Point e)
    (f : Module.Dual ℂ (Point e)) (hf : f v = 0) (w : Point e) :
    f (directionQuotientSection v ((Submodule.span ℂ {v}).mkQ w)) = f w := by
  let S := Submodule.span ℂ {v}
  have hq : S.mkQ (directionQuotientSection v (S.mkQ w) - w) = 0 := by
    rw [map_sub]
    have h := congrArg (fun L => L (S.mkQ w)) (directionQuotientSection_rightInverse v)
    apply sub_eq_zero.mpr
    simpa only [S, LinearMap.comp_apply, LinearMap.id_apply] using h
  have hm : directionQuotientSection v (S.mkQ w) - w ∈ S := by
    have hk : directionQuotientSection v (S.mkQ w) - w ∈ LinearMap.ker S.mkQ :=
      LinearMap.mem_ker.mpr hq
    simpa only [Submodule.ker_mkQ] using hk
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hm
  have hz : f (directionQuotientSection v (S.mkQ w) - w) = 0 := by
    rw [← ht, map_smul, hf, smul_zero]
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

def firstBlockLinear (e : ℕ) : Point (e + e) →ₗ[ℂ] Point e :=
  LinearMap.pi (fun k => LinearMap.proj (Fin.castAdd e k))

/-- The actual (alpha,beta) coordinate map on cone tangent vectors. -/
def tangentCoordinateLinear {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (z0 : Point (skewDim e)) :
    Point (e + e) →ₗ[ℂ]
      ((Point e ⧸ Submodule.span ℂ {firstPoint p.rep}) ×
        Module.Dual ℂ (Point e ⧸ Submodule.span ℂ {firstPoint p.rep})) :=
  ((Submodule.span ℂ {firstPoint p.rep}).mkQ.comp (firstBlockLinear e)).prod
    ((directionQuotientSection (firstPoint p.rep)).dualMap.comp
      ((pointCovectorLinear e).comp (secondBlockLinear e) -
        LinearMap.comp (C.decode z0).val (firstBlockLinear e)))

theorem tangentCoordinateLinear_first {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (z0 : Point (skewDim e)) (u : Point (e + e)) :
    (tangentCoordinateLinear C p z0 u).1 =
      (Submodule.span ℂ {firstPoint p.rep}).mkQ (firstPoint u) := rfl

theorem tangentCoordinateLinear_second {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (z0 : Point (skewDim e)) (u : Point (e + e))
    (hann : (covectorOfPoint (secondPoint u) - (C.decode z0).val (firstPoint u))
      (firstPoint p.rep) = 0) (w : Point e) :
    (tangentCoordinateLinear C p z0 u).2
      ((Submodule.span ℂ {firstPoint p.rep}).mkQ w) =
      covectorOfPoint (secondPoint u) w - (C.decode z0).val (firstPoint u) w := by
  change (covectorOfPoint (secondPoint u) - (C.decode z0).val (firstPoint u))
      (directionQuotientSection (firstPoint p.rep)
        ((Submodule.span ℂ {firstPoint p.rep}).mkQ w)) = _
  exact directionQuotientSection_covector (firstPoint p.rep)
    (covectorOfPoint (secondPoint u) - (C.decode z0).val (firstPoint u)) hann w

theorem differential_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Poly n) (x u : Point n) :
    differential (∑ i ∈ s, f i) x u = ∑ i ∈ s, differential (f i) x u := by
  classical
  simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  simp_rw [map_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem differential_parameterQuadricPolynomial {e : ℕ} (x u : Point (e + e)) :
    differential (parameterQuadricPolynomial e) x u =
      covectorOfPoint (secondPoint u) (firstPoint x) +
        covectorOfPoint (secondPoint x) (firstPoint u) := by
  classical
  rw [parameterQuadricPolynomial, differential_finset_sum]
  simp only [differential_mul_X]
  have hX (i : Fin (e + e)) : differential (MvPolynomial.X i : Poly (e + e)) x u = u i := by
    simp [differential, Pi.single_apply]
  simp only [hX, MvPolynomial.aeval_X]
  simp only [covectorOfPoint, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, firstPoint, secondPoint]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- differentiate the actual quadric equation, then use z0 v=y
and alternation to see beta annihilates v (concentration.tex:797–812). -/
theorem parameter_quadric_tangent_annihilates {e : ℕ} (C : SkewCoordinates e)
    (Y : ProjectiveVariety (e + e)) (hQ : Y.points ⊆ parameterQuadric e)
    (p : ProjectivePoint (e + e)) (hpY : p ∈ Y.points)
    (z0 : Point (skewDim e)) (hz0 : z0 ∈ evaluationFlat C p)
    (u : Point (e + e)) (hu : u ∈ Y.affineCone.tangentSpace p.rep) :
    (covectorOfPoint (secondPoint u) - (C.decode z0).val (firstPoint u))
      (firstPoint p.rep) = 0 := by
  have hf : parameterQuadricPolynomial e ∈ Y.ideal := by
    rw [← Y.vanishingIdeal_points]
    exact parameterQuadricPolynomial_mem_closure Y.points hQ
  have ht : differential (parameterQuadricPolynomial e) p.rep u = 0 :=
    LinearMap.mem_ker.mp (((Submodule.mem_iInf _).mp hu) ⟨_, hf⟩)
  rw [differential_parameterQuadricPolynomial] at ht
  have hskew : (C.decode z0).val (firstPoint u) (firstPoint p.rep) =
      - (C.decode z0).val (firstPoint p.rep) (firstPoint u) :=
    ((C.decode z0).property.neg_eq _ _).symm
  rw [LinearMap.sub_apply, hskew, hz0]
  linear_combination ht

/-- A quotient pencil whose pulled-back covectors lie in a smaller space is
singular. B22 supplies this smaller space by evaluating the carrier tangent. -/
theorem skewPencil_singular_of_covector_image {e : ℕ} (v : Point e)
    (Θ : Submodule ℂ ((Point e ⧸ Submodule.span ℂ {v}) ×
      Module.Dual ℂ (Point e ⧸ Submodule.span ℂ {v})))
    (B : LinearMap.BilinForm ℂ (Point e ⧸ Submodule.span ℂ {v}))
    (A : Submodule ℂ (Module.Dual ℂ (Point e)))
    (hrank : Module.finrank ℂ A < Module.finrank ℂ (Point e ⧸ Submodule.span ℂ {v}))
    (himage : ∀ x : Θ, (skewPencil Θ B x).comp (Submodule.span ℂ {v}).mkQ ∈ A) :
    ¬ Function.Bijective (skewPencil Θ B) := by
  intro hbij
  let S := Submodule.span ℂ {v}
  let f := S.mkQ.dualMap
  have hf : Function.Injective f := by
    intro β γ h
    apply LinearMap.ext
    intro q
    obtain ⟨w, rfl⟩ := S.mkQ_surjective q
    exact congrArg (fun F : Module.Dual ℂ (Point e) => F w) h
  have hle : LinearMap.range f ≤ A := by
    rintro y ⟨β, rfl⟩
    obtain ⟨x, hx⟩ := hbij.2 β
    change β.comp S.mkQ ∈ A
    rw [← hx]
    exact himage x
  have hdim := Submodule.finrank_mono hle
  rw [LinearMap.finrank_range_of_inj hf, Subspace.dual_finrank_eq] at hdim
  exact (not_le_of_gt hrank) hdim

#print axioms skewPencil_singular_of_covector_image
#print axioms directionQuotientSection_covector
#print axioms tangentCoordinateLinear_second
#print axioms parameter_quadric_tangent_annihilates
end
end DistinctDistances.TrackB
