import DistinctDistances.TrackA.HomogeneousNormalizationSupport

set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Quotient coordinate evaluation uses the inherited quotient module
scalar action, through the actual quotient algebra homomorphism. -/
theorem quotient_linearCoordinate_eq_sum {n s : ℕ} (I : Ideal (Poly n))
    (ψ : LinearProjection n s) (j : Fin s) :
    Ideal.Quotient.mk I (linearCoordinate ψ j) =
      ∑ i, ψ (Pi.single i 1) j • Ideal.Quotient.mk I (MvPolynomial.X i) := by
  rw [linearCoordinate, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← MvPolynomial.smul_eq_C_mul]
  exact (Ideal.Quotient.mkₐ ℂ I).toLinearMap.map_smul _ _

/-- Coordinate-span parameters are represented by an actual linear
projection in the original ambient coordinates. -/
theorem quotient_parameters_linear_projection {n s : ℕ} (I : Ideal (Poly n))
    (z : Fin s → Poly n ⧸ I)
    (hz : ∀ j, z j ∈ Submodule.span ℂ
      (Set.range (fun i : Fin n => Ideal.Quotient.mk I (MvPolynomial.X i)))) :
    ∃ ψ : LinearProjection n s, ∀ j,
      Ideal.Quotient.mk I (linearCoordinate ψ j) = z j := by
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hz j)
  let ψ : LinearProjection n s := Matrix.mulVecLin c
  have hcoeff (j : Fin s) (i : Fin n) : ψ (Pi.single i 1) j = c j i := by
    simp [ψ, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite]
  refine ⟨ψ, fun j => ?_⟩
  rw [quotient_linearCoordinate_eq_sum]
  simpa only [hcoeff] using hc j

/-- Algebraically independent quotient coordinates force the representing
linear projection to be surjective. -/
theorem quotient_parameters_projection_surjective {n s : ℕ}
    (I : Ideal (Poly n)) (z : Fin s → Poly n ⧸ I) (ψ : LinearProjection n s)
    (hz : ∀ j, Ideal.Quotient.mk I (linearCoordinate ψ j) = z j)
    (hi : Function.Injective (MvPolynomial.aeval (R := ℂ) z)) :
    Function.Surjective ψ := by
  let c : Matrix (Fin s) (Fin n) ℂ := fun j i => ψ (Pi.single i 1) j
  let T : Point n →ₗ[ℂ] (Poly n ⧸ I) :=
    ∑ i : Fin n, (LinearMap.proj i).smulRight (Ideal.Quotient.mk I (MvPolynomial.X i))
  have hT (j : Fin s) : T (c j) = z j := by
    have he := hz j
    rw [quotient_linearCoordinate_eq_sum] at he
    simpa only [T, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply, c] using he
  have hLI : LinearIndependent ℂ (fun j => c j) := by
    apply LinearIndependent.of_comp T
    have hzLI := (algebraicIndependent_iff_injective_aeval.mpr hi).linearIndependent
    simpa only [Function.comp_def, hT] using hzLI
  have hψ : c.mulVecLin = ψ := by
    apply (Pi.basisFun ℂ (Fin n)).ext
    intro i
    ext j
    simp [c, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite]
  have hrank : c.rank = s := by
    simpa only [Fintype.card_fin] using hLI.rank_matrix
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [← hψ]
  change c.rank = Module.finrank ℂ (Point s)
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using hrank

/-- The finite polynomial parameter map is exactly the shared model's
finite affine projection, with zero offset. -/
theorem finite_affine_projection_of_quotient_parameters {n s : ℕ}
    (V : AffineVariety n) (z : Fin s → Poly n ⧸ V.ideal) (ψ : LinearProjection n s)
    (hz : ∀ j, Ideal.Quotient.mk V.ideal (linearCoordinate ψ j) = z j)
    (hf : (MvPolynomial.aeval (R := ℂ) z).Finite) :
    FiniteAffineProjection (⟨ψ, 0⟩ : AffineProjection n s) V := by
  let q := Ideal.Quotient.mkₐ ℂ V.ideal
  have he : q.comp (AffineProjection.pullback (⟨ψ, 0⟩ : AffineProjection n s)) =
      MvPolynomial.aeval (R := ℂ) z := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa only [q, AlgHom.comp_apply, AffineProjection.pullback, MvPolynomial.aeval_X,
      Pi.zero_apply, MvPolynomial.C_0, add_zero, Ideal.Quotient.mkₐ_eq_mk] using hz j
  change ((q.comp (AffineProjection.pullback (⟨ψ, 0⟩ : AffineProjection n s))).toRingHom).Finite
  rw [he]
  exact hf

/-- Actual homogeneous affine varieties admit finite surjective linear
projections with parameter count equal to quotient Krull dimension. This
asserts no generic-degree identity. -/
theorem homogeneous_affine_finite_linear_projection {n : ℕ} (V : AffineVariety n)
    (hV : V.ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ))
    (hne : V.ideal ≠ ⊤) :
    ∃ (s : ℕ) (ψ : LinearProjection n s), s ≤ n ∧ Function.Surjective ψ ∧
      FiniteAffineProjection (⟨ψ, 0⟩ : AffineProjection n s) V ∧
      ringKrullDim (Poly n ⧸ V.ideal) = (s : WithBot ℕ∞) := by
  obtain ⟨s, hs, z, _, hz, hi, hf⟩ :=
    homogeneous_quotient_linear_normalization V.ideal hV hne
  obtain ⟨ψ, hψ⟩ := quotient_parameters_linear_projection V.ideal z hz
  exact ⟨s, ψ, hs, quotient_parameters_projection_surjective V.ideal z ψ hψ hi,
    finite_affine_projection_of_quotient_parameters V z ψ hψ hf,
    homogeneous_normalization_dimension V.ideal z hi hf⟩

end
end DistinctDistances.TrackA
