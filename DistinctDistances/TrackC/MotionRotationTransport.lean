import DistinctDistances.TrackC.RotationCross

namespace DistinctDistances.TrackC

/-- Pair flats rotate in the common six-dimensional parameter space,
motions.tex:342–346. -/
theorem pair_flat_rotate (R : E 3 ≃ₗᵢ[ℝ] E 3) (hR : LinearMap.det R.toLinearMap = 1)
    (x y : E 3) :
    pairFlatSet (R x) (R y) = sixRotate R '' pairFlatSet x y := by
  have hcross_symm (u v : E 3) :
      R.symm (cross3 u v) = cross3 (R.symm u) (R.symm v) := by
    apply R.injective
    simpa using (cross3_rotation R hR (R.symm u) (R.symm v)).symm
  ext z
  constructor
  · intro hz
    change (1 / 2 : ℝ) • (R x - R y) =
      cross3 (wCoord z) ((1 / 2 : ℝ) • (R x + R y)) + cCoord z at hz
    have hz' : sixRotate R.symm z ∈ pairFlatSet x y := by
      change (1 / 2 : ℝ) • (x - y) =
        cross3 (wCoord (sixRotate R.symm z)) ((1 / 2 : ℝ) • (x + y)) +
          cCoord (sixRotate R.symm z)
      have h := congrArg R.symm hz
      simpa [map_smul, map_sub, map_add, hcross_symm] using h
    refine ⟨sixRotate R.symm z, hz', ?_⟩
    calc
      sixRotate R (sixRotate R.symm z) = sixRotate R ((sixRotate R).symm z) := by
        rw [← sixRotate_symm]
      _ = z := (sixRotate R).apply_symm_apply z
  · rintro ⟨z₀, hz₀, rfl⟩
    change (1 / 2 : ℝ) • (x - y) =
      cross3 (wCoord z₀) ((1 / 2 : ℝ) • (x + y)) + cCoord z₀ at hz₀
    change (1 / 2 : ℝ) • (R x - R y) =
      cross3 (wCoord (sixRotate R z₀)) ((1 / 2 : ℝ) • (R x + R y)) +
        cCoord (sixRotate R z₀)
    have h := congrArg R hz₀
    simpa [map_smul, map_sub, map_add, cross3_rotation R hR] using h

/-- Transport the graph-dual model back from a proper axis frame,
motions.tex:342–346; input to normalized_motion_flats. -/
theorem motion_flat_model_rotate (R : E 3 ≃ₗᵢ[ℝ] E 3)
    (hR : LinearMap.det R.toLinearMap = 1) (g : Motion 3) (S : Finset (E 3))
    (G : Flat 6 3) (hmodel : MotionFlatModel g S G) :
    ∃ G' : Flat 6 3,
      (G'.1 : Set (E 6)) = sixRotate R '' (G.1 : Set (E 6)) ∧
      MotionFlatModel (motionConjugate R g) (S.image R) G' := by
  classical
  rcases hmodel with ⟨hnull, T, φ, hφ, hrange, hinter, hnoncol⟩
  let A : E 6 ≃ᵃ[ℝ] E 6 := (sixRotate R).toAffineEquiv
  let RA : E 3 ≃ᵃ[ℝ] E 3 := R.toLinearEquiv.toAffineEquiv
  let T' : E 3 ≃ᵃ[ℝ] E 3 := RA.symm.trans T
  let φ' : E 3 →ᵃ[ℝ] E 6 := A.toAffineMap.comp φ
  let H : AffineSubspace ℝ (E 6) := G.1.map A.toAffineMap
  have hHne : (H : Set (E 6)).Nonempty := by
    rcases G.2.1 with ⟨z, hz⟩
    exact ⟨A z, AffineSubspace.mem_map_of_mem A.toAffineMap hz⟩
  have hHrank : Module.finrank ℝ H.direction = 3 := by
    rw [AffineSubspace.map_direction]
    exact (A.linear.finrank_map_eq G.1.direction).trans G.2.2
  let G' : Flat 6 3 := ⟨H, hHne, hHrank⟩
  have hGcoe : (G'.1 : Set (E 6)) = sixRotate R '' (G.1 : Set (E 6)) := by
    change ((G.1.map A.toAffineMap : AffineSubspace ℝ (E 6)) : Set (E 6)) = _
    rw [AffineSubspace.coe_map]
    rfl
  have hdir : G'.1.direction = Submodule.map (sixRotate R).toLinearMap G.1.direction := by
    change (G.1.map A.toAffineMap).direction = _
    rw [AffineSubspace.map_direction]
    rfl
  have hnull' : maximalNull G' := by
    intro z hz
    rw [hdir] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := Submodule.mem_map.mp hz
    have hq : splitQuadratic ((sixRotate R).toLinearMap z₀) = splitQuadratic z₀ := by
      simpa only [LinearEquiv.coe_toLinearMap] using sixRotate_quadratic R z₀
    exact hq.trans (hnull z₀ hz₀)
  have hφ' : Function.Injective φ' := by
    intro u v huv
    apply hφ
    exact A.injective (by simpa [φ'] using huv)
  have hrange' : Set.range φ' = (G'.1 : Set (E 6)) := by
    calc
      Set.range φ' = sixRotate R '' Set.range φ := by
        change Set.range (A.toAffineMap ∘ φ) = sixRotate R '' Set.range φ
        rw [Set.range_comp]
        rfl
      _ = sixRotate R '' (G.1 : Set (E 6)) := congrArg (fun U : Set (E 6) => sixRotate R '' U) hrange
      _ = (G'.1 : Set (E 6)) := hGcoe.symm
  have hT' (x : E 3) : T' (R x) = T x := by
    change T (RA.symm (RA x)) = T x
    simp
  have hinter' : ∀ x ∈ S.image R,
      pairFlatSet x ((motionConjugate R g) x) ∩ (G'.1 : Set (E 6)) =
        φ' '' graphDualPlane (T' x) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨x₀, hx₀, rfl⟩
    rw [motionConjugate_apply, R.symm_apply_apply]
    rw [hGcoe]
    calc
      pairFlatSet (R x₀) (R (g x₀)) ∩
          (sixRotate R '' (G.1 : Set (E 6))) =
          sixRotate R '' (pairFlatSet x₀ (g x₀) ∩ (G.1 : Set (E 6))) := by
        rw [pair_flat_rotate R hR x₀ (g x₀)]
        rw [← Set.image_inter (sixRotate R).injective]
      _ = sixRotate R '' (φ '' graphDualPlane (T x₀)) := by
        rw [hinter x₀ hx₀]
      _ = φ' '' graphDualPlane (T' (R x₀)) := by
        rw [hT']
        simp [φ', A, Set.image_image]
  have hnoncol' : ∀ x ∈ S.image R, ∀ y ∈ S.image R, ∀ z ∈ S.image R,
      ¬ Collinear ℝ ({x, y, z} : Set (E 3)) →
        ¬ Collinear ℝ
          ({WithLp.toLp 2 ![T' x 0, T' x 1], WithLp.toLp 2 ![T' y 0, T' y 1],
            WithLp.toLp 2 ![T' z 0, T' z 1]} : Set (E 2)) := by
    intro x hx y hy z hz hncol
    rcases Finset.mem_image.mp hx with ⟨x₀, hx₀, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨y₀, hy₀, rfl⟩
    rcases Finset.mem_image.mp hz with ⟨z₀, hz₀, rfl⟩
    have hAIimage : AffineIndependent ℝ ![R x₀, R y₀, R z₀] := by
      simpa using (affineIndependent_iff_not_collinear_set (k := ℝ)
        (p₁ := R x₀) (p₂ := R y₀) (p₃ := R z₀)).2 hncol
    have hcomp : RA ∘ ![x₀, y₀, z₀] = ![R x₀, R y₀, R z₀] := by
      funext i
      fin_cases i <;> rfl
    have hAIcomp : AffineIndependent ℝ (RA ∘ ![x₀, y₀, z₀]) := by
      rw [hcomp]
      exact hAIimage
    have hAIsource : AffineIndependent ℝ ![x₀, y₀, z₀] :=
      (RA.affineIndependent_iff (p := ![x₀, y₀, z₀])).mp hAIcomp
    have hncolsource : ¬ Collinear ℝ ({x₀, y₀, z₀} : Set (E 3)) := by
      simpa using (affineIndependent_iff_not_collinear_set (k := ℝ)
        (p₁ := x₀) (p₂ := y₀) (p₃ := z₀)).mp hAIsource
    have hprojected := hnoncol x₀ hx₀ y₀ hy₀ z₀ hz₀ hncolsource
    simpa only [hT'] using hprojected
  exact ⟨G', hGcoe, ⟨hnull', T', φ', hφ', hrange', hinter', hnoncol'⟩⟩

end DistinctDistances.TrackC
