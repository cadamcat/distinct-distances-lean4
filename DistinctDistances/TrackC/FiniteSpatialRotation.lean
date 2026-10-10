import DistinctDistances.TrackC.RotationAvoidPolynomial
import DistinctDistances.TrackC.RotationAxisCertificate

open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- One proper rotation makes each of finitely many reversing axes transverse to all listed normal planes. -/
theorem finite_spatial_rotation_normals {ι : Type*} (I : Finset ι)
    (S : ι → E 3 ≃ₗᵢ[ℝ] E 3) (N : ι → Finset (E 3))
    (hS : ∀ i ∈ I,LinearMap.det (S i).toLinearMap = -1)
    (hN : ∀ i ∈ I,∀ n ∈ N i,n ≠ 0) (hne : ∀ i ∈ I,(N i).Nonempty) :
    ∃ R : E 3 ≃ₗᵢ[ℝ] E 3,LinearMap.det R.toLinearMap = 1 ∧
      ∀ i ∈ I,Module.finrank ℝ (LinearMap.ker (((S i).trans R).toLinearMap+LinearMap.id)) = 1 ∧
        ∀ n ∈ N i,LinearMap.ker (((S i).trans R).toLinearMap+LinearMap.id) ⊓
          LinearMap.ker (spatialNormalFunctional n) = ⊥ := by
  obtain ⟨u,hD,hcert⟩ := finite_rotation_normal_certificates I (fun i => spatialIsometryMatrix (S i)) N
    (fun i hi => (LinearMap.det_toMatrix homRotationStdBasis (S i).toLinearMap).trans (hS i hi)) hN
  let R := homRationalRotation (u 0) (rotationParameterVector u) hD
  have hR : LinearMap.det R.toLinearMap = 1 := homRationalRotation_det _ _ hD
  have hmat : ∀ i,spatialIsometryMatrix ((S i).trans R) =
      homRotationMatrix (u 0) (rotationParameterVector u)*spatialIsometryMatrix (S i) := by
    intro i
    change LinearMap.toMatrix homRotationStdBasis homRotationStdBasis
      ((homRationalRotationLinear (u 0) (rotationParameterVector u)).comp (S i).toLinearMap) = _
    rw [LinearMap.toMatrix_comp homRotationStdBasis homRotationStdBasis homRotationStdBasis,homRationalRotation_toMatrix]
    rfl
  refine ⟨R,hR,?_⟩
  intro i hi
  have hSi : LinearMap.det ((S i).trans R).toLinearMap = -1 := by
    change LinearMap.det (R.toLinearMap.comp (S i).toLinearMap) = -1
    rw [LinearMap.det_comp,hR,hS i hi,one_mul]
  have hc : ∀ n ∈ N i,
      Module.finrank ℝ (LinearMap.ker (((S i).trans R).toLinearMap+LinearMap.id)) = 1 ∧
      LinearMap.ker (((S i).trans R).toLinearMap+LinearMap.id) ⊓ LinearMap.ker (spatialNormalFunctional n) = ⊥ := by
    intro n hn
    apply reversing_axis_certificate ((S i).trans R) hSi n
    rw [hmat]
    exact hcert i hi n hn
  obtain ⟨n,hn⟩ := hne i hi
  exact ⟨(hc n hn).1,fun n hn => (hc n hn).2⟩

/-- Every triple direction span in three dimensions has a nonzero normal. -/
theorem triple_direction_normal (x y z : E 3) :
    ∃ n : E 3,n ≠ 0 ∧ vectorSpan ℝ ({x,y,z}:Set (E 3)) ≤ LinearMap.ker (spatialNormalFunctional n) := by
  let V := vectorSpan ℝ ({x,y,z}:Set (E 3))
  have hdim : Module.finrank ℝ V ≤ 2 := by
    have h := finrank_vectorSpan_range_le ℝ (![x,y,z]:Fin 3 → E 3) (by norm_num : Fintype.card (Fin 3) = 2+1)
    have hr : Set.range (![x,y,z]:Fin 3 → E 3) = ({x,y,z}:Set (E 3)) := by
      ext a
      constructor
      · rintro ⟨i,rfl⟩
        fin_cases i <;> simp
      · simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
        rintro (rfl | rfl | rfl)
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
        · exact ⟨2,rfl⟩
    rw [hr] at h
    exact h
  have hOrth : Vᗮ ≠ ⊥ := by
    intro hz
    have h := V.finrank_add_finrank_orthogonal
    rw [hz] at h
    have hE3 : Module.finrank ℝ (E 3) = 3 := by simp [E]
    rw [hE3] at h
    norm_num at h
    omega
  have hex : ∃ n ∈ Vᗮ,n ≠ 0 := by
    by_contra! hz
    apply hOrth
    apply le_antisymm _ bot_le
    intro n hn
    change n = 0
    exact hz n hn
  obtain ⟨n,hn,hn0⟩ := hex
  refine ⟨n,hn0,?_⟩
  intro v hv
  change inner ℝ n v = 0
  exact (V.mem_orthogonal' n).mp hn v hv

end DistinctDistances.TrackC
