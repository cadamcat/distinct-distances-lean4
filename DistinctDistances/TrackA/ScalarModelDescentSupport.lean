import DistinctDistances.TrackA.ReducedScalarExtensionSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped TensorProduct

/-- A scalar-model inclusion over a field is injective. It detects
nilpotents and an explicitly supplied inverse relation. -/
theorem scalar_model_reduced_and_unit {R K A B : Type}
    [Field R] [Field K] [Algebra R K] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra K B] [IsReduced B]
    (e : (K ⊗[R] A) ≃ₐ[K] B) (a u : A)
    (h : e (1 ⊗ₜ[R] a) * e (1 ⊗ₜ[R] u) = 1) :
    IsReduced A ∧ IsUnit a := by
  let g : A →+* B := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom
  have hg : Function.Injective g := e.injective.comp
    (Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap R K)))
  refine ⟨isReduced_of_injective g hg, isUnit_iff_exists_inv.mpr ⟨u, ?_⟩⟩
  apply hg
  rw [map_mul, map_one]
  exact h

end
end DistinctDistances.TrackA
