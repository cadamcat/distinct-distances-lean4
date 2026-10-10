import DistinctDistances.TrackC.MotionCoordinates
import DistinctDistances.TrackC.CanonicalNullFlat

open scoped BigOperators

noncomputable section

namespace DistinctDistances.TrackC

def motionChartAxis (R : E 3 ≃ₗᵢ[ℝ] E 3) : E 3 :=
  R.symm (EuclideanSpace.single (2 : Fin 3) 1)

def motionOrthogonalPart (a : E 3) : E 3 →ₗ[ℝ] E 3 :=
  LinearMap.id - (innerSL ℝ a).toLinearMap.smulRight a

def motionChartOffset (R : E 3 ≃ₗᵢ[ℝ] E 3) (d₀ d₁ : ℝ) : E 3 :=
  R.symm (WithLp.toLp 2 ![d₀,d₁,0])

@[simp] theorem motionOrthogonalPart_apply (a x : E 3) :
    motionOrthogonalPart a x = x-inner ℝ a x • a := rfl

@[simp] theorem motionChartAxis_map (R : E 3 ≃ₗᵢ[ℝ] E 3) :
    R (motionChartAxis R) = EuclideanSpace.single (2 : Fin 3) 1 := by
  simp [motionChartAxis]

theorem motionChartAxis_unit (R : E 3 ≃ₗᵢ[ℝ] E 3) : ‖motionChartAxis R‖ = 1 := by
  simp [motionChartAxis]

theorem motionChartAxis_inner (R : E 3 ≃ₗᵢ[ℝ] E 3) (x : E 3) :
    inner ℝ (motionChartAxis R) x = (R x) 2 := by
  have h := R.inner_map_map (motionChartAxis R) x
  rw [motionChartAxis_map] at h
  simpa [PiLp.inner_apply,Fin.sum_univ_three,PiLp.single_apply] using h.symm

theorem motionChartOffset_perp (R : E 3 ≃ₗᵢ[ℝ] E 3) (d₀ d₁ : ℝ) :
    inner ℝ (motionChartAxis R) (motionChartOffset R d₀ d₁) = 0 := by
  rw [motionChartAxis_inner]
  simp [motionChartOffset]

theorem motionChartOrthogonalPart (R : E 3 ≃ₗᵢ[ℝ] E 3) (x : E 3) :
    motionOrthogonalPart (motionChartAxis R) x = R.symm (WithLp.toLp 2 ![(R x) 0,(R x) 1,0]) := by
  apply R.injective
  rw [motionOrthogonalPart_apply,map_sub,map_smul,motionChartAxis_map,
    motionChartAxis_inner,R.apply_symm_apply]
  ext i
  fin_cases i <;> simp [PiLp.single_apply]

theorem cross3_sub_right (a x y : E 3) : cross3 a (x-y) = cross3 a x-cross3 a y := by
  ext i
  fin_cases i <;> simp [cross3] <;> ring

theorem cross3_inner_self_right (a x : E 3) : inner ℝ x (cross3 a x) = 0 := by
  simp [cross3,PiLp.inner_apply,Fin.sum_univ_three]
  ring

/-- Both a whole chart flat and its matched sections project to this axis plane. -/
theorem canonical_rotated_w_projection (R : E 3 ≃ₗᵢ[ℝ] E 3) (s ω d₀ d₁ : ℝ) :
    wCoord '' (sixRotate R.symm '' Set.range (canonicalMotionParameter s ω d₀ d₁)) =
      {w : E 3 | inner ℝ (motionChartAxis R) w = ω} := by
  ext w
  constructor
  · rintro ⟨z,⟨z₀,⟨u,rfl⟩,rfl⟩,rfl⟩
    change inner ℝ (motionChartAxis R)
      (wCoord (sixRotate R.symm (canonicalMotionParameter s ω d₀ d₁ u))) = ω
    rw [wCoord_sixRotate,motionChartAxis_inner]
    simp [canonicalMotionParameter,wCoord]
  · intro hw
    change inner ℝ (motionChartAxis R) w = ω at hw
    rw [motionChartAxis_inner] at hw
    let u : E 3 := WithLp.toLp 2 ![-(R w) 1,(R w) 0,0]
    refine ⟨sixRotate R.symm (canonicalMotionParameter s ω d₀ d₁ u),
      ⟨canonicalMotionParameter s ω d₀ d₁ u,Set.mem_range_self u,rfl⟩,?_⟩
    rw [wCoord_sixRotate]
    apply R.injective
    rw [R.apply_symm_apply]
    ext i
    fin_cases i
    · simp [canonicalMotionParameter,wCoord,u]
    · simp [canonicalMotionParameter,wCoord,u]
    · simpa [canonicalMotionParameter,wCoord,u] using hw.symm

/-- The intrinsic mean-axis and transverse Cayley equations determine the image
of a physical point. This is the uniqueness step behind both distinctness claims. -/
theorem intrinsic_graph_point_unique (a : E 3) (ω : ℝ) (x y y' : E 3)
    (haxis : inner ℝ a (x+y) = inner ℝ a (x+y'))
    (hperp : motionOrthogonalPart a (x-y)-ω • cross3 a (x+y) =
      motionOrthogonalPart a (x-y')-ω • cross3 a (x+y')) : y = y' := by
  have horth : inner ℝ a (y-y') = 0 := by
    rw [inner_sub_right]
    apply sub_eq_zero.mpr
    simpa only [inner_add_right,add_right_inj] using haxis
  have hpart : motionOrthogonalPart a (y-y') = y-y' := by simp [horth]
  have hdir : (y-y')+ω • cross3 a (y-y') = 0 := by
    have hdiff : motionOrthogonalPart a ((x-y)-(x-y'))-
        ω • cross3 a ((x+y)-(x+y')) = 0 := by
      rw [map_sub,cross3_sub_right,smul_sub]
      rw [← sub_sub_sub_comm]
      exact sub_eq_zero.mpr hperp
    have hxsub : (x-y)-(x-y') = -(y-y') := by abel
    have hxadd : (x+y)-(x+y') = y-y' := by abel
    rw [hxsub,hxadd,map_neg,hpart] at hdiff
    have hneg : -((y-y')+ω • cross3 a (y-y')) = 0 := by
      calc
        -((y-y')+ω • cross3 a (y-y')) = -(y-y')-ω • cross3 a (y-y') := by abel
        _ = 0 := hdiff
    exact neg_eq_zero.mp hneg
  have hinner := congrArg (fun v : E 3 => inner ℝ (y-y') v) hdir
  simp only [inner_add_right,inner_smul_right,cross3_inner_self_right,mul_zero,
    add_zero,inner_zero_right] at hinner
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hinner)

end DistinctDistances.TrackC
