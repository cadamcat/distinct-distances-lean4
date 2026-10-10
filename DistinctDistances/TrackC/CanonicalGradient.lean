import DistinctDistances.TrackC.MotionLocal
import DistinctDistances.TrackC.CanonicalMotionModel

open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Third pair-flat direction equation in the common parameter coordinates. -/
theorem pair_flat_direction_third (x y : E 3) (F : Flat 6 3)
    (hF : (F.1:Set (E 6)) = pairFlatSet x y) (z v : E 6) (hz : z ∈ F.1) (hv : v ∈ F.1.direction) :
    v 5+v 0*((x+y) 1/2)-v 1*((x+y) 0/2) = 0 := by
  have hz' : v+z ∈ F.1 := by simpa using F.1.vadd_mem_of_mem_direction hv hz
  have h₀ : z ∈ pairFlatSet x y := hF ▸ hz
  have h₁ : v+z ∈ pairFlatSet x y := hF ▸ hz'
  change (1/2:ℝ) • (x-y) = cross3 (wCoord z) ((1/2:ℝ) • (x+y))+cCoord z at h₀
  change (1/2:ℝ) • (x-y) = cross3 (wCoord (v+z)) ((1/2:ℝ) • (x+y))+cCoord (v+z) at h₁
  have h₂ := congrArg (fun u : E 3 => u 2) h₀
  have h₃ := congrArg (fun u : E 3 => u 2) h₁
  simp [wCoord,cCoord,cross3] at h₂ h₃
  have hd : v 5+v 0*(2⁻¹*x 1+2⁻¹*y 1)-v 1*(2⁻¹*x 0+2⁻¹*y 0) = 0 := by nlinarith only [h₂,h₃]
  convert hd using 1 <;> simp only [PiLp.add_apply] <;> ring

theorem canonical_flat_direction (s ω d₀ d₁ : ℝ) (G : Flat 6 3)
    (hG : (G.1:Set (E 6)) = Set.range (canonicalMotionParameter s ω d₀ d₁)) :
    G.1.direction = LinearMap.range (canonicalMotionLinear s) := by
  let φ := canonicalMotionParameter s ω d₀ d₁
  have heq : G.1 = (⊤:AffineSubspace ℝ (E 3)).map φ := by
    apply SetLike.coe_injective
    change (G.1:Set (E 6)) = φ '' (Set.univ:Set (E 3))
    simpa only [Set.image_univ] using hG
  rw [heq,AffineSubspace.map_direction,AffineSubspace.direction_top,Submodule.map_top]
  rfl

/-- The raised-gradient transversality step of dual propagation in canonical axis coordinates. -/
theorem canonical_null_gradient_triple (s ω d₀ d₁ : ℝ) (G : Flat 6 3)
    (hG : (G.1:Set (E 6)) = Set.range (canonicalMotionParameter s ω d₀ d₁))
    (hNull : maximalNull G) (f : Poly 6) (hfG : onPolynomial f G) (z : E 6) (hzG : z ∈ G.1)
    (x₀ y₀ x₁ y₁ x₂ y₂ : E 3)
    (hdet : Matrix.det !![(x₀+y₀) 0/2,(x₀+y₀) 1/2,1;
      (x₁+y₁) 0/2,(x₁+y₁) 1/2,1;(x₂+y₂) 0/2,(x₂+y₂) 1/2,1] ≠ 0)
    (hz₀ : z ∈ pairFlatSet x₀ y₀) (hz₁ : z ∈ pairFlatSet x₁ y₁) (hz₂ : z ∈ pairFlatSet x₂ y₂)
    (hf₀ : ∀ u ∈ pairFlatSet x₀ y₀,evalR f u = 0)
    (hf₁ : ∀ u ∈ pairFlatSet x₁ y₁,evalR f u = 0)
    (hf₂ : ∀ u ∈ pairFlatSet x₂ y₂,evalR f u = 0) : raisedGradient f z = 0 := by
  have hgrad := raised_gradient_null_flat G hNull f hfG z hzG
  rw [canonical_flat_direction s ω d₀ d₁ G hG] at hgrad
  have hpair : ∀ x y : E 3,z ∈ pairFlatSet x y →
      (∀ u ∈ pairFlatSet x y,evalR f u = 0) →
      (raisedGradient f z) 5+(raisedGradient f z) 0*((x+y) 1/2)-
        (raisedGradient f z) 1*((x+y) 0/2) = 0 := by
    intro x y hz hf
    obtain ⟨F,hF,hNullF⟩ := pair_flat_geometry x y
    have hzF : z ∈ F.1 := by change z ∈ (F.1:Set (E 6));rw [hF];exact hz
    have hfF : onPolynomial f F := by intro u hu;exact hf u (hF ▸ hu)
    exact pair_flat_direction_third x y F hF z (raisedGradient f z) hzF
      (raised_gradient_null_flat F hNullF f hfF z hzF)
  have h₀ := hpair x₀ y₀ hz₀ hf₀
  have h₁ := hpair x₁ y₁ hz₁ hf₁
  have h₂ := hpair x₂ y₂ hz₂ hf₂
  let v₀ : E 3 := (1/2:ℝ) • (x₀+y₀)
  let v₁ : E 3 := (1/2:ℝ) • (x₁+y₁)
  let v₂ : E 3 := (1/2:ℝ) • (x₂+y₂)
  apply canonical_motion_direction_transverse s v₀ v₁ v₂ (raisedGradient f z) hgrad
  · have heq : !![v₀ 0,v₀ 1,1;v₁ 0,v₁ 1,1;v₂ 0,v₂ 1,1] =
        !![(x₀+y₀) 0/2,(x₀+y₀) 1/2,1;(x₁+y₁) 0/2,(x₁+y₁) 1/2,1;(x₂+y₂) 0/2,(x₂+y₂) 1/2,1] := by
      ext i j
      fin_cases i <;> fin_cases j
      all_goals simp only [v₀,v₁,v₂,PiLp.smul_apply,smul_eq_mul] <;> ring
    rw [heq]
    exact hdet
  · convert h₀ using 1 <;> simp only [v₀,PiLp.smul_apply,smul_eq_mul] <;> ring
  · convert h₁ using 1 <;> simp only [v₁,PiLp.smul_apply,smul_eq_mul] <;> ring
  · convert h₂ using 1 <;> simp only [v₂,PiLp.smul_apply,smul_eq_mul] <;> ring

end DistinctDistances.TrackC
