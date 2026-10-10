import DistinctDistances.TrackC.NullFlatCalculus
import DistinctDistances.TrackC.ModelDirectionTransverse

namespace DistinctDistances.TrackC

/-- A transverse triple-dual point kills the raised gradient,
motions.tex:416–431. -/
theorem motion_triple_gradient_zero (g : Motion 3) (S : Finset (E 3))
    (G : Flat 6 3) (hmodel : MotionFlatModel g S G) (f : Poly 6)
    (hfG : onPolynomial f G)
    (hpair : ∀ x ∈ S, ∀ u ∈ pairFlatSet x (g x), evalR f u = 0)
    (z : E 6) (hzG : z ∈ G.1) (x₀ x₁ x₂ : E 3)
    (hx₀ : x₀ ∈ S) (hx₁ : x₁ ∈ S) (hx₂ : x₂ ∈ S)
    (htri : ¬ Collinear ℝ ({x₀,x₁,x₂} : Set (E 3)))
    (hz₀ : z ∈ pairFlatSet x₀ (g x₀)) (hz₁ : z ∈ pairFlatSet x₁ (g x₁))
    (hz₂ : z ∈ pairFlatSet x₂ (g x₂)) : raisedGradient f z = 0 := by
  let v := raisedGradient f z
  have hvG : v ∈ G.1.direction := raised_gradient_null_flat G hmodel.1 f hfG z hzG
  have hshift (x : E 3) (hx : x ∈ S) (hz : z ∈ pairFlatSet x (g x)) :
      v+z ∈ pairFlatSet x (g x) := by
    obtain ⟨F,hF,hnull⟩ := pair_flat_geometry x (g x)
    have hzF : z ∈ F.1 := by
      change z ∈ (F.1 : Set (E 6))
      rw [hF]
      exact hz
    have hfF : onPolynomial f F := by
      intro u hu
      apply hpair x hx u
      have hu' : u ∈ (F.1 : Set (E 6)) := hu
      rw [hF] at hu'
      exact hu'
    have hvF := raised_gradient_null_flat F hnull f hfF z hzF
    have hpoint : v+z ∈ F.1 := by
      simpa only [vadd_eq_add] using F.1.vadd_mem_of_mem_direction hvF hzF
    change v+z ∈ (F.1 : Set (E 6)) at hpoint
    rw [hF] at hpoint
    exact hpoint
  exact motion_model_direction_transverse g S G hmodel z v hzG hvG x₀ x₁ x₂
    hx₀ hx₁ hx₂ htri hz₀ hz₁ hz₂ (hshift x₀ hx₀ hz₀) (hshift x₁ hx₁ hz₁) (hshift x₂ hx₂ hz₂)

set_option maxHeartbeats 1000000 in
/-- The raised-gradient coordinate swap is invertible. -/
theorem partials_zero_of_raised_gradient_zero (f : Poly 6) (z : E 6)
    (hzero : raisedGradient f z = 0) :
    ∀ i : Fin 6, evalR (MvPolynomial.pderiv i f) z = 0 := by
  intro i
  fin_cases i
  · have h := congrArg (fun v : E 6 => v 3) hzero
    simpa [raisedGradient,Fin.addCases] using h
  · have h := congrArg (fun v : E 6 => v 4) hzero
    simpa [raisedGradient,Fin.addCases] using h
  · have h := congrArg (fun v : E 6 => v 5) hzero
    simpa [raisedGradient,Fin.addCases] using h
  · have h := congrArg (fun v : E 6 => v 0) hzero
    simpa [raisedGradient,Fin.addCases] using h
  · have h := congrArg (fun v : E 6 => v 1) hzero
    simpa [raisedGradient,Fin.addCases] using h
  · have h := congrArg (fun v : E 6 => v 2) hzero
    simpa [raisedGradient,Fin.addCases] using h

end DistinctDistances.TrackC
