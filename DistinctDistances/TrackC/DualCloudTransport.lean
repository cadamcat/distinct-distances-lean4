import DistinctDistances.TrackC.MotionGeometry

namespace DistinctDistances.TrackC

private theorem affineMap_linear_injective (φ : E 3 →ᵃ[ℝ] E 3)
    (hφ : Function.Injective φ) : Function.Injective φ.linear := by
  intro u v huv
  have hpoints : φ (u +ᵥ (0 : E 3)) = φ (v +ᵥ (0 : E 3)) := by
    calc
      φ (u +ᵥ (0 : E 3)) = φ.linear u +ᵥ φ 0 := φ.map_vadd 0 u
      _ = φ.linear v +ᵥ φ 0 := by rw [huv]
      _ = φ (v +ᵥ (0 : E 3)) := (φ.map_vadd 0 v).symm
  have h := hφ hpoints
  simpa using h

private theorem affineMap_finrank_direction (φ : E 3 →ᵃ[ℝ] E 3)
    (hφ : Function.Injective φ) (s : AffineSubspace ℝ (E 3)) :
    Module.finrank ℝ (s.map φ).direction = Module.finrank ℝ s.direction := by
  rw [AffineSubspace.map_direction]
  let g : s.direction →ₗ[ℝ] E 3 := φ.linear.comp s.direction.subtype
  have hginj : Function.Injective g := by
    intro u v huv
    apply Subtype.ext
    exact affineMap_linear_injective φ hφ (by simpa [g] using huv)
  have hrange : LinearMap.range g = s.direction.map φ.linear := by
    ext z
    constructor
    · intro hz
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hz
      exact Submodule.mem_map.mpr ⟨u.1, u.2, rfl⟩
    · intro hz
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hz
      exact LinearMap.mem_range.mpr ⟨⟨u, hu⟩, rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hginj]

private noncomputable def affineMapFlat {k : ℕ} (φ : E 3 →ᵃ[ℝ] E 3)
    (hφ : Function.Injective φ) (H : Flat 3 k) : Flat 3 k := by
  refine ⟨H.1.map φ, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := H.2.1
    exact ⟨φ x, AffineSubspace.mem_map.mpr ⟨x, hx, rfl⟩⟩
  · rw [affineMap_finrank_direction φ hφ H.1]
    exact H.2.2

private theorem affine_image_pointsOn_card {k : ℕ}
    (T : E 3 ≃ᵃ[ℝ] E 3) (S : Finset (E 3)) (H : Flat 3 k) :
    (pointsOn (S.image T) H).card =
      (pointsOn S (affineMapFlat T.symm.toAffineMap T.symm.injective H)).card := by
  classical
  let H' := affineMapFlat T.symm.toAffineMap T.symm.injective H
  have hmem (x : E 3) : x ∈ H'.1 ↔ T x ∈ H.1 := by
    change x ∈ H.1.map T.symm.toAffineMap ↔ T x ∈ H.1
    simpa using
      (AffineSubspace.mem_map_iff_mem_of_injective
        (f := T.symm.toAffineMap) (x := T x) (s := H.1) T.symm.injective)
  have hfilter : pointsOn (S.image T) H = (pointsOn S H').image T := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_filter.mp hy with ⟨hyS, hyH⟩
      rcases Finset.mem_image.mp hyS with ⟨x, hxS, rfl⟩
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxS, (hmem x).2 hyH⟩, rfl⟩
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      rcases Finset.mem_filter.mp hx with ⟨hxS, hxH⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨x, hxS, rfl⟩, (hmem x).1 hxH⟩
  rw [hfilter, Finset.card_image_of_injective _ T.injective]

/-- Affine graph coordinates preserve both occupancy caps, motions.tex:434–436. -/
theorem affine_cloud_caps (T : E 3 ≃ᵃ[ℝ] E 3) (S : Finset (E 3)) (L B : ℝ)
    (hline : ∀ l : Line 3, ((pointsOn S l).card : ℝ) < L)
    (hplane : ∀ H : Plane 3, ((pointsOn S H).card : ℝ) < B) :
    (S.image T).card = S.card ∧
      (∀ l : Line 3, ((pointsOn (S.image T) l).card : ℝ) < L) ∧
      (∀ H : Plane 3, ((pointsOn (S.image T) H).card : ℝ) < B) := by
  refine ⟨Finset.card_image_of_injective _ T.injective, ?_, ?_⟩
  · intro l
    rw [affine_image_pointsOn_card T S l]
    exact hline (affineMapFlat T.symm.toAffineMap T.symm.injective l)
  · intro H
    rw [affine_image_pointsOn_card T S H]
    exact hplane (affineMapFlat T.symm.toAffineMap T.symm.injective H)

end DistinctDistances.TrackC
