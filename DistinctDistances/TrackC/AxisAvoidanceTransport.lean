import DistinctDistances.TrackC.MotionConjugation

namespace DistinctDistances.TrackC

/-- Axis avoidance is preserved by changing the physical orthonormal frame,
motions.tex:298–300; input to canonical_projection_triples. -/
theorem axis_avoidance_conjugate (R : E 3 ≃ₗᵢ[ℝ] E 3) (g : Motion 3) (S : Finset (E 3))
    (havoid : axisAvoidsTriples g S) :
    axisAvoidsTriples (motionConjugate R g) (S.image R) := by
  intro x hx y hy z hz hncol
  rcases Finset.mem_image.mp hx with ⟨x₀, hx₀, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨y₀, hy₀, rfl⟩
  rcases Finset.mem_image.mp hz with ⟨z₀, hz₀, rfl⟩
  have hAI_image : AffineIndependent ℝ ![R x₀, R y₀, R z₀] := by
    simpa using (affineIndependent_iff_not_collinear_set (k := ℝ)
      (p₁ := R x₀) (p₂ := R y₀) (p₃ := R z₀)).2 hncol
  have hcomp : R.toLinearEquiv.toAffineEquiv ∘ ![x₀, y₀, z₀] = ![R x₀, R y₀, R z₀] := by
    funext i
    fin_cases i <;> rfl
  have hAI_comp : AffineIndependent ℝ
      (R.toLinearEquiv.toAffineEquiv ∘ ![x₀, y₀, z₀]) := by
    rw [hcomp]
    exact hAI_image
  have hAI_source : AffineIndependent ℝ ![x₀, y₀, z₀] := by
    exact (R.toLinearEquiv.toAffineEquiv.affineIndependent_iff
      (p := ![x₀, y₀, z₀])).mp hAI_comp
  have hncol_source : ¬ Collinear ℝ ({x₀, y₀, z₀} : Set (E 3)) := by
    simpa using (affineIndependent_iff_not_collinear_set (k := ℝ)
      (p₁ := x₀) (p₂ := y₀) (p₃ := z₀)).mp hAI_source
  have hRlin : R.toAffineIsometryEquiv.toAffineEquiv.linear.toLinearMap =
      R.toLinearMap := by
    ext v
    rfl
  have hspan :
      (vectorSpan ℝ ({x₀, y₀, z₀} : Set (E 3))).map
          R.toAffineIsometryEquiv.toAffineEquiv.linear.toLinearMap =
        vectorSpan ℝ ({R x₀, R y₀, R z₀} : Set (E 3)) := by
    simpa using (AffineMap.map_vectorSpan
      (f := R.toAffineIsometryEquiv.toAffineEquiv.toAffineMap)
      (s := ({x₀, y₀, z₀} : Set (E 3))))
  have hmap :
      (axis g ⊓ vectorSpan ℝ ({x₀, y₀, z₀} : Set (E 3))).map
          R.toAffineIsometryEquiv.toAffineEquiv.linear.toLinearMap =
        (axis g).map R.toAffineIsometryEquiv.toAffineEquiv.linear.toLinearMap ⊓
          (vectorSpan ℝ ({x₀, y₀, z₀} : Set (E 3))).map
            R.toAffineIsometryEquiv.toAffineEquiv.linear.toLinearMap := by
    apply le_antisymm
    · exact le_inf (Submodule.map_mono inf_le_left) (Submodule.map_mono inf_le_right)
    · intro v hv
      rcases Submodule.mem_map.mp hv.1 with ⟨u, hu, huv⟩
      rcases Submodule.mem_map.mp hv.2 with ⟨w, hw, hwv⟩
      have huw : u = w := by
        apply R.toLinearEquiv.injective
        simpa only [hRlin, LinearEquiv.coe_toLinearMap] using huv.trans hwv.symm
      subst w
      exact Submodule.mem_map.mpr ⟨u, ⟨hu, hw⟩, huv⟩
  have havoid_source := havoid x₀ hx₀ y₀ hy₀ z₀ hz₀ hncol_source
  rw [axis_motionConjugate, hRlin.symm, ← hspan, ← hmap, havoid_source]
  simp

end DistinctDistances.TrackC
