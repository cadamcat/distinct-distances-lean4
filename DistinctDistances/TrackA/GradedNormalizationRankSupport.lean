import DistinctDistances.OAIInterface.NormalizationSpecialization

namespace DistinctDistances.TrackA
noncomputable section
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- Assemble the original homogeneous generic basis and common-degree
selection with its original generic-rank comparison. -/
theorem graded_common_degree_rank_independent
    {K A M : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [AddCommGroup M] [Module K M] [Module A M] [Module.Finite A M]
    (𝓐 : ℕ → Submodule K A) [GradedAlgebra 𝓐]
    (𝓜 : ℕ → Submodule K M) [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝓐 𝓜]
    {a : A} (ha0 : a ≠ 0) (ha1 : a ∈ 𝓐 1) :
    ∃ D : ℕ, ∃ w : Fin (Module.finrank A M) → M,
      LinearIndependent A w ∧ ∀ i, w i ∈ 𝓜 D := by
  letI : Module (FractionRing A) (LocalizedModule (nonZeroDivisors A) M) :=
    LocalizedModule.moduleOfIsLocalization
  let f := LocalizedModule.mkLinearMap (nonZeroDivisors A) M
  obtain ⟨v, _, _, hhom, hv⟩ :=
    OAI.Erdos970.WeightedTorusJets.Geometry.exists_homogeneous_generic_basis
      (F := FractionRing A) 𝓜 f
  have hr : Module.finrank (FractionRing A) (LocalizedModule (nonZeroDivisors A) M) =
      Module.finrank A M :=
    OAI.Erdos970.WeightedTorusJets.Geometry.generic_fiber_finrank_eq (F := FractionRing A) f
  have h := OAI.Erdos970.WeightedTorusJets.Geometry.exists_common_degree_independent
    𝓐 𝓜 ha0 ha1 hv hhom
  rw [hr] at h
  exact h

end
end DistinctDistances.TrackA
