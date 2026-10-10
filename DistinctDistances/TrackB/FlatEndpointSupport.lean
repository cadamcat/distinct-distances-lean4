import DistinctDistances.TrackB.AffineFlatGeometry
import DistinctDistances.TrackB.Requests

namespace DistinctDistances.TrackB
noncomputable section
open LinearMap (BilinForm)

/-- A nonempty evaluation flat has explicit affine coordinates of dimension s₀.
This supplies the h=0 case of concentration.tex:1027–1033. -/
theorem evaluationFlat_affine_coordinates {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (hp : p ∈ affineParameters e) :
    ∃ b : Point (skewDim e), ∃ φ : Point (flatDim e) →ₗ[ℂ] Point (skewDim e),
      Function.Injective φ ∧ evaluationFlat C p = {z | ∃ t, z = b + φ t} := by
  let v := firstPoint p.rep
  let y := covectorOfPoint (secondPoint p.rep)
  have hv : v ≠ 0 := hp.2
  have hy : y v = 0 := hp.1
  obtain ⟨D, hD, hDv⟩ := alternating_evaluation_surjective v hv y hy
  let z0 := C.decode.symm ⟨D, hD⟩
  have hz0 : z0 ∈ evaluationFlat C p := by
    change (C.decode z0).val v = y
    simpa [z0] using hDv
  let E : Point (skewDim e) →ₗ[ℂ] Module.Dual ℂ (Point e) :=
    (alternatingEvaluation v).comp C.decode.toLinearMap
  let K := LinearMap.ker E
  have hKdim : Module.finrank ℂ K = flatDim e := by
    have hEq := (C.decode.ofSubmodule' (LinearMap.ker (alternatingEvaluation v))).finrank_eq
    change Module.finrank ℂ K =
      Module.finrank ℂ (LinearMap.ker (alternatingEvaluation v)) at hEq
    rw [hEq, alternatingEvaluation_kernel_finrank v hv, Module.finrank_fin_fun]
    rfl
  let b : Module.Basis (Fin (flatDim e)) ℂ K := (Module.finBasis ℂ K).reindex (finCongr hKdim)
  let kEquiv : K ≃ₗ[ℂ] Point (flatDim e) := b.equivFun
  let φ : Point (flatDim e) →ₗ[ℂ] Point (skewDim e) :=
    K.subtype.comp kEquiv.symm.toLinearMap
  refine ⟨z0, φ, ?_, ?_⟩
  · exact Subtype.val_injective.comp kEquiv.symm.injective
  · ext z
    constructor
    · intro hz
      have hEz : E z = y := hz
      have hE0 : E z0 = y := hz0
      have hk : z - z0 ∈ K := by
        rw [LinearMap.mem_ker, map_sub, hEz, hE0, sub_self]
      let k : K := ⟨z - z0, hk⟩
      refine ⟨kEquiv k, ?_⟩
      have hφ : φ (kEquiv k) = z - z0 := by simp [φ, k]
      rw [hφ]
      abel
    · rintro ⟨t, rfl⟩
      have hk : E (φ t) = 0 := (kEquiv.symm t).property
      change E (z0 + φ t) = y
      rw [map_add, hk, add_zero]
      exact hz0

theorem evaluationFlat_closure_dimension {e : ℕ} (C : SkewCoordinates e)
    (p : ProjectivePoint (e + e)) (hp : p ∈ affineParameters e) :
    (AffineVariety.closure (evaluationFlat C p)).dimension = flatDim e := by
  obtain ⟨b, φ, hφ, hset⟩ := evaluationFlat_affine_coordinates C p hp
  have hdim := Request.affine_linear_principal_open_dimension b φ hφ (1 : Poly (skewDim e))
    0 (by simp)
  simpa [hset] using hdim

/-- In dimension at least two, the common radical of all alternating forms is zero. -/
theorem alternating_common_radical_zero {U : Type*} [AddCommGroup U] [Module ℂ U]
    [FiniteDimensional ℂ U] (hdim : 2 ≤ Module.finrank ℂ U) (w : U)
    (hw : ∀ D : BilinForm ℂ U, D.IsAlt → D w = 0) : w = 0 := by
  by_contra hw0
  let S := Submodule.span ℂ {w}
  have hAnn : S.dualAnnihilator = ⊥ := by
    apply bot_unique
    intro y hy
    have hyw : y w = 0 := (Submodule.mem_dualAnnihilator _).mp hy w
      (Submodule.mem_span_singleton_self _)
    obtain ⟨D, hD, hDw⟩ := alternating_evaluation_surjective w hw0 y hyw
    have hy0 : y = 0 := hDw.symm.trans (hw D hD)
    simpa [hy0]
  have hspan : Module.finrank ℂ S = 1 := by
    exact finrank_span_singleton hw0
  have hsum := Subspace.finrank_add_finrank_dualAnnihilator_eq S
  rw [hAnn, finrank_bot, hspan] at hsum
  omega

/-- The common radical of forms annihilating v is precisely the line ℂv. -/
theorem alternating_kernel_common_radical {e : ℕ} (he : 3 ≤ e)
    (v w : Point e) (hv : v ≠ 0)
    (hw : ∀ D : BilinForm ℂ (Point e), D.IsAlt → D v = 0 → D w = 0) :
    w ∈ Submodule.span ℂ {v} := by
  let S := Submodule.span ℂ {v}
  have hSv : S.mkQ v = 0 := by
    apply LinearMap.mem_ker.mp
    rw [Submodule.ker_mkQ]
    exact Submodule.mem_span_singleton_self _
  have hdim : 2 ≤ Module.finrank ℂ (Point e ⧸ S) := by
    have hsum := Submodule.finrank_quotient_add_finrank (R := ℂ) (M := Point e) S
    have hspan : Module.finrank ℂ S = 1 := finrank_span_singleton hv
    rw [hspan, Module.finrank_fin_fun] at hsum
    omega
  have hquot : S.mkQ w = 0 := by
    apply alternating_common_radical_zero hdim
    intro D hD
    let D' := D.compl₁₂ S.mkQ S.mkQ
    have hAlt : D'.IsAlt := fun x => hD (S.mkQ x)
    have hDv : D' v = 0 := by
      ext x
      simp [D', hSv]
    have hDw := hw D' hAlt hDv
    apply LinearMap.ext
    intro x
    obtain ⟨u, rfl⟩ := S.mkQ_surjective x
    exact LinearMap.congr_fun hDw u
  have hmem : w ∈ LinearMap.ker S.mkQ := LinearMap.mem_ker.mpr hquot
  simpa only [Submodule.ker_mkQ] using hmem

#print axioms evaluationFlat_affine_coordinates
#print axioms evaluationFlat_closure_dimension
#print axioms alternating_common_radical_zero
#print axioms alternating_kernel_common_radical
end
end DistinctDistances.TrackB
