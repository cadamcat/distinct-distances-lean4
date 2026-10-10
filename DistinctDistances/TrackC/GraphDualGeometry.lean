import DistinctDistances.TrackC.MotionGeometry

open Classical

noncomputable section

namespace DistinctDistances.TrackC

private def graphDualPlaneLinear (x : E 3) : E 2 →ₗ[ℝ] E 3 where
  toFun q := WithLp.toLp 2 ![q 0, q 1, -(q 0 * x 0 + q 1 * x 1)]
  map_add' u v := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r u := by
    ext i
    fin_cases i <;> simp <;> ring

private theorem graphDualPlaneLinear_injective (x : E 3) :
    Function.Injective (graphDualPlaneLinear x) := by
  intro u v huv
  ext i
  fin_cases i
  · have h := congrArg (fun z : E 3 => z 0) huv
    simpa [graphDualPlaneLinear] using h
  · have h := congrArg (fun z : E 3 => z 1) huv
    simpa [graphDualPlaneLinear] using h

private def graphDualPlaneSubspace (x : E 3) : AffineSubspace ℝ (E 3) :=
  AffineSubspace.mk' (WithLp.toLp 2 ![0, 0, x 2])
    (LinearMap.range (graphDualPlaneLinear x))

private theorem graphDualPlaneSubspace_coe (x : E 3) :
    (graphDualPlaneSubspace x : Set (E 3)) = graphDualPlane x := by
  classical
  let p : E 3 := WithLp.toLp 2 ![0, 0, x 2]
  ext u
  constructor
  · intro hu
    have hu' : u -ᵥ p ∈ LinearMap.range (graphDualPlaneLinear x) := by
      simpa [graphDualPlaneSubspace, p, AffineSubspace.mem_mk'] using hu
    obtain ⟨q, hq⟩ := LinearMap.mem_range.mp hu'
    have h0 : q 0 = u 0 := by
      have h := congrArg (fun z : E 3 => z 0) hq
      simpa [graphDualPlaneLinear, p, vsub_eq_sub] using h
    have h1 : q 1 = u 1 := by
      have h := congrArg (fun z : E 3 => z 1) hq
      simpa [graphDualPlaneLinear, p, vsub_eq_sub] using h
    have h2 : -(q 0 * x 0 + q 1 * x 1) = u 2 - x 2 := by
      have h := congrArg (fun z : E 3 => z 2) hq
      simpa [graphDualPlaneLinear, p, vsub_eq_sub] using h
    change u 2 + u 0 * x 0 + u 1 * x 1 = x 2
    rw [← h0, ← h1]
    linarith
  · intro hu
    change u 2 + u 0 * x 0 + u 1 * x 1 = x 2 at hu
    let q : E 2 := WithLp.toLp 2 ![u 0, u 1]
    have hq : graphDualPlaneLinear x q = u - p := by
      apply (WithLp.ext_iff 2).2
      funext i
      fin_cases i
      · simp [graphDualPlaneLinear, q, p, vsub_eq_sub]
      · simp [graphDualPlaneLinear, q, p, vsub_eq_sub]
      · simp [graphDualPlaneLinear, q, p, vsub_eq_sub]
        linarith
    have hu' : u -ᵥ p ∈ LinearMap.range (graphDualPlaneLinear x) := by
      rw [vsub_eq_sub, ← hq]
      exact LinearMap.mem_range.mpr ⟨q, rfl⟩
    simpa [graphDualPlaneSubspace, p, AffineSubspace.mem_mk'] using hu'

private noncomputable def graphDualPlaneFlat (x : E 3) : Flat 3 2 := by
  let p : E 3 := WithLp.toLp 2 ![0, 0, x 2]
  refine ⟨graphDualPlaneSubspace x, ?_, ?_⟩
  · refine ⟨p, ?_⟩
    simp [graphDualPlaneSubspace, p, AffineSubspace.mem_mk']
  · rw [graphDualPlaneSubspace, AffineSubspace.direction_mk']
    change Module.finrank ℝ (LinearMap.range (graphDualPlaneLinear x)) = 2
    rw [LinearMap.finrank_range_of_inj (graphDualPlaneLinear_injective x)]
    simp [E]

private theorem graphDualPlaneFlat_coe (x : E 3) :
    (graphDualPlaneFlat x).1 = graphDualPlane x := graphDualPlaneSubspace_coe x

private theorem affineMap_linear_injective (φ : E 3 →ᵃ[ℝ] E 6)
    (hφ : Function.Injective φ) : Function.Injective φ.linear := by
  intro u v huv
  have hpoints : φ (u +ᵥ (0 : E 3)) = φ (v +ᵥ (0 : E 3)) := by
    calc
      φ (u +ᵥ (0 : E 3)) = φ.linear u +ᵥ φ 0 := φ.map_vadd 0 u
      _ = φ.linear v +ᵥ φ 0 := by rw [huv]
      _ = φ (v +ᵥ (0 : E 3)) := (φ.map_vadd 0 v).symm
  have h := hφ hpoints
  simpa using h

private theorem finrank_affineMap_map_direction (φ : E 3 →ᵃ[ℝ] E 6)
    (hφ : Function.Injective φ) (s : AffineSubspace ℝ (E 3)) :
    Module.finrank ℝ (s.map φ).direction = Module.finrank ℝ s.direction := by
  rw [AffineSubspace.map_direction]
  let g : s.direction →ₗ[ℝ] E 6 := φ.linear.comp s.direction.subtype
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


/-- A graph-dual plane is an ordinary affine two-flat. -/
theorem graph_dual_plane_geometry (x : E 3) :
    ∃ H : Plane 3, (H.1 : Set (E 3)) = graphDualPlane x := by
  exact ⟨graphDualPlaneFlat x,graphDualPlaneFlat_coe x⟩

/-- Injective parameter maps preserve the ranks of the line and plane flats
used in propagation. -/
noncomputable def mapped_parameter_flat {k : ℕ} (φ : E 3 →ᵃ[ℝ] E 6)
    (hφ : Function.Injective φ) (H : Flat 3 k) : Flat 6 k := by
  refine ⟨H.1.map φ,?_,?_⟩
  · obtain ⟨x,hx⟩ := H.2.1
    exact ⟨φ x,AffineSubspace.mem_map.mpr ⟨x,hx,rfl⟩⟩
  · rw [finrank_affineMap_map_direction φ hφ H.1,H.2.2]

theorem mapped_parameter_flat_coe {k : ℕ} (φ : E 3 →ᵃ[ℝ] E 6)
    (hφ : Function.Injective φ) (H : Flat 3 k) :
    ((mapped_parameter_flat φ hφ H).1 : Set (E 6)) = φ '' (H.1 : Set (E 3)) := by
  change ((H.1.map φ) : Set (E 6)) = φ '' (H.1 : Set (E 3))
  rw [AffineSubspace.coe_map]

theorem mapped_parameter_flat_injective {k : ℕ} (φ : E 3 →ᵃ[ℝ] E 6)
    (hφ : Function.Injective φ) : Function.Injective (mapped_parameter_flat (k := k) φ hφ) := by
  intro H K heq
  apply Subtype.ext
  apply SetLike.coe_injective
  have hsets : φ '' (H.1 : Set (E 3)) = φ '' (K.1 : Set (E 3)) := by
    rw [← mapped_parameter_flat_coe φ hφ H,← mapped_parameter_flat_coe φ hφ K]
    exact congrArg (fun Q : Flat 6 k => (Q.1 : Set (E 6))) heq
  ext x
  constructor
  · intro hx
    have h := Set.mem_image_of_mem φ hx
    rw [hsets] at h
    obtain ⟨y,hy,hyx⟩ := h
    have hyx' := hφ hyx
    subst y
    exact hy
  · intro hx
    have h := Set.mem_image_of_mem φ hx
    rw [← hsets] at h
    obtain ⟨y,hy,hyx⟩ := h
    have hyx' := hφ hyx
    subst y
    exact hy

theorem graph_dual_plane_set_injective : Function.Injective graphDualPlane := by
  intro x y hsets
  have h₀ : WithLp.toLp 2 ![0,0,x 2] ∈ graphDualPlane y := by
    rw [← hsets]
    simp [graphDualPlane]
  have h₁ : WithLp.toLp 2 ![1,0,x 2-x 0] ∈ graphDualPlane y := by
    rw [← hsets]
    simp [graphDualPlane]
  have h₂ : WithLp.toLp 2 ![0,1,x 2-x 1] ∈ graphDualPlane y := by
    rw [← hsets]
    simp [graphDualPlane]
  simp [graphDualPlane] at h₀ h₁ h₂
  ext i
  fin_cases i
  · change x 0 = y 0
    linarith
  · change x 1 = y 1
    linarith
  · change x 2 = y 2
    linarith

end DistinctDistances.TrackC
