import DistinctDistances.TrackC.IntrinsicMotionCoordinates
import DistinctDistances.TrackC.MotionConjugation
import DistinctDistances.TrackC.MotionRotationTransport

open Classical

noncomputable section

namespace DistinctDistances.TrackC

set_option maxHeartbeats 1000000 in
/-- In a matched pair flat, the canonical section projects onto the complete
axis-normal plane, motions.tex:350–356. -/
theorem canonical_pair_w_projection (x y : E 3) (s ω d₀ d₁ : ℝ)
    (hgraph : ((x+y) 2)/2 = s ∧ ((x-y) 0)/2 = d₀-ω*((x+y) 1)/2 ∧
      ((x-y) 1)/2 = d₁+ω*((x+y) 0)/2) :
    wCoord '' (pairFlatSet x y ∩ Set.range (canonicalMotionParameter s ω d₀ d₁)) =
      {w : E 3 | w 2 = ω} := by
  ext w
  constructor
  · rintro ⟨z,⟨hz,⟨u,rfl⟩⟩,rfl⟩
    simp [wCoord,canonicalMotionParameter]
  · intro hw
    change w 2 = ω at hw
    let u : E 3 := WithLp.toLp 2 ![-w 1,w 0,(x-y) 2/2+w 1*(x+y) 0/2-w 0*(x+y) 1/2]
    let z := canonicalMotionParameter s ω d₀ d₁ u
    have hcoord : wCoord z = w := by
      ext i
      fin_cases i <;> simp [z,wCoord,canonicalMotionParameter,u,← hw]
    have hpair : z ∈ pairFlatSet x y := by
      obtain ⟨hs,h₀,h₁⟩ := hgraph
      simp only [PiLp.add_apply,PiLp.sub_apply] at hs h₀ h₁
      have hs₀ := congrArg (fun q : ℝ => w 0*q) hs
      have hs₁ := congrArg (fun q : ℝ => w 1*q) hs
      change (1/2 : ℝ) • (x-y) = cross3 (wCoord z) ((1/2 : ℝ) • (x+y))+cCoord z
      ext i
      fin_cases i
      all_goals simp [z,wCoord,cCoord,canonicalMotionParameter,cross3,u]
      all_goals nlinarith only [h₀,h₁,hs₀,hs₁]
    exact ⟨z,⟨hpair,Set.mem_range_self u⟩,hcoord⟩

/-- The same section projection in the common physical parameter space. -/
theorem rotated_pair_w_projection (R : E 3 ≃ₗᵢ[ℝ] E 3)
    (hR : LinearMap.det R.toLinearMap = 1) (x y : E 3) (s ω d₀ d₁ : ℝ)
    (hgraph : ((R x+R y) 2)/2 = s ∧ ((R x-R y) 0)/2 = d₀-ω*((R x+R y) 1)/2 ∧
      ((R x-R y) 1)/2 = d₁+ω*((R x+R y) 0)/2) :
    wCoord '' (pairFlatSet x y ∩
      (sixRotate R.symm '' Set.range (canonicalMotionParameter s ω d₀ d₁))) =
        {w : E 3 | inner ℝ (motionChartAxis R) w = ω} := by
  ext w
  constructor
  · rintro ⟨z,hz,hw⟩
    have hfull : w ∈ wCoord ''
        (sixRotate R.symm '' Set.range (canonicalMotionParameter s ω d₀ d₁)) :=
      ⟨z,hz.2,hw⟩
    rw [canonical_rotated_w_projection] at hfull
    exact hfull
  · intro hw
    change inner ℝ (motionChartAxis R) w = ω at hw
    rw [motionChartAxis_inner] at hw
    have hcan : R w ∈ wCoord ''
        (pairFlatSet (R x) (R y) ∩ Set.range (canonicalMotionParameter s ω d₀ d₁)) := by
      rw [canonical_pair_w_projection (R x) (R y) s ω d₀ d₁ hgraph]
      exact hw
    obtain ⟨z,hzPair,hzW⟩ := hcan
    have hrotate := pair_flat_rotate R.symm (proper_rotation_symm R hR) (R x) (R y)
    simp only [R.symm_apply_apply] at hrotate
    refine ⟨sixRotate R.symm z,⟨?_,?_⟩,?_⟩
    · rw [hrotate]
      exact Set.mem_image_of_mem _ hzPair.1
    · exact Set.mem_image_of_mem _ hzPair.2
    · rw [wCoord_sixRotate,hzW,R.symm_apply_apply]

end DistinctDistances.TrackC
