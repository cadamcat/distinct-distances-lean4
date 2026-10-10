import DistinctDistances.TrackA.NormalizationSpecializationSupport
import DistinctDistances.TrackA.GradedNormalizationRankSupport

set_option backward.isDefEq.respectTransparency false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Identify the actual affine parameter map with the shared projection
pullback followed by the source coordinate quotient. -/
theorem affineNormalizationMap_eq_projection_pullback {n k : ℕ}
    (V : AffineVariety n) (ψ : LinearProjection n k) :
    affineNormalizationMap V ψ = (Ideal.Quotient.mkₐ ℂ V.ideal).comp
      (AffineProjection.pullback (⟨ψ, 0⟩ : AffineProjection n k)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [affineNormalizationMap, AffineProjection.pullback,
    AlgHom.comp_apply, MvPolynomial.aeval_X, Pi.zero_apply, MvPolynomial.C_0,
    add_zero, Ideal.Quotient.mkₐ_eq_mk]

theorem affineNormalizationMap_finite_iff {n k : ℕ}
    (V : AffineVariety n) (ψ : LinearProjection n k) :
    (affineNormalizationMap V ψ).Finite ↔
      FiniteAffineProjection (⟨ψ, 0⟩ : AffineProjection n k) V := by
  rw [affineNormalizationMap_eq_projection_pullback]
  rfl

theorem affineNormalizationMap_injective {n k : ℕ}
    (V : AffineVariety n) (hV : V.IsIrreducible) (hd : V.dimension = k)
    (ψ : LinearProjection n k) (hf : (affineNormalizationMap V ψ).Finite) :
    Function.Injective (affineNormalizationMap V ψ) := by
  have h := finite_affine_projection_pullback_injective V hV hd (⟨ψ, 0⟩ : AffineProjection n k)
    ((affineNormalizationMap_finite_iff V ψ).mp hf)
  rw [affineNormalizationMap_eq_projection_pullback]
  exact h

/-- A finite full-dimensional affine normalization has positive actual
module rank, independently of its projective degree comparison. -/
theorem affineNormalizationRank_pos_of_finite {n k : ℕ}
    (V : AffineVariety n) (hV : V.IsIrreducible) (hd : V.dimension = k)
    (ψ : LinearProjection n k) (hf : (affineNormalizationMap V ψ).Finite) :
    0 < affineNormalizationRank V ψ := by
  letI : V.ideal.IsPrime := hV
  letI := (affineNormalizationMap V ψ).toRingHom.toAlgebra
  letI : Module (Poly k) (Poly n ⧸ V.ideal) :=
    (affineNormalizationMap V ψ).toRingHom.toAlgebra.toModule
  letI : Module.Finite (Poly k) (Poly n ⧸ V.ideal) := hf
  letI : Module.IsTorsionFree (Poly k) (Poly n ⧸ V.ideal) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (affineNormalizationMap_injective V hV hd ψ hf)
  exact Module.finrank_pos

/-- Setting the original X0 to one preserves the rank of the actual
finite cone normalization. Common-degree independence transfers in both
directions; no flatness of the special fiber is assumed. -/
theorem normalization_cone_rank_eq_affine_rank {n k : ℕ}
    (V : AffineVariety n) (ψ : LinearProjection n k)
    (hf : (coneNormalizationMap V ψ).Finite) :
    coneNormalizationRank V ψ = affineNormalizationRank V ψ := by
  let Q := Poly (n+1) ⧸ (projectiveClosure V).ideal
  let A := Poly n ⧸ V.ideal
  letI := (coneNormalizationMap V ψ).toRingHom.toAlgebra
  letI : Module (Poly (k+1)) Q := (coneNormalizationMap V ψ).toRingHom.toAlgebra.toModule
  letI : SMul (Poly (k+1)) Q := (coneNormalizationMap V ψ).toRingHom.toAlgebra.toSMul
  letI : IsScalarTower ℂ (Poly (k+1)) Q := IsScalarTower.of_algHom (coneNormalizationMap V ψ)
  letI : Module.Finite (Poly (k+1)) Q := hf
  letI := (affineNormalizationMap V ψ).toRingHom.toAlgebra
  letI : Module (Poly k) A := (affineNormalizationMap V ψ).toRingHom.toAlgebra.toModule
  letI : SMul (Poly k) A := (affineNormalizationMap V ψ).toRingHom.toAlgebra.toSMul
  letI : Module.Finite (Poly k) A := affineNormalizationMap_finite_of_cone V ψ hf
  let 𝓜 := OAI.PiExponentJets.W64.quotientSection (projectiveClosure V).ideal
  letI : GradedAlgebra 𝓜 :=
    homogeneousQuotientGrading (projectiveClosure V).ideal (projectiveClosure V).isHomogeneous
  letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (k+1)) ℂ) 𝓜 :=
    OAI.Erdos970.WeightedTorusJets.Geometry.linear_quotient_map_gradedSMul _
      (coneNormalizationMap V ψ) (coneNormalizationMap_linear V ψ)
  change Module.finrank (Poly (k+1)) Q = Module.finrank (Poly k) A
  apply le_antisymm
  · obtain ⟨D, w, hw, hD⟩ := graded_common_degree_rank_independent
        (MvPolynomial.homogeneousSubmodule (Fin (k+1)) ℂ) 𝓜
        (a := MvPolynomial.X 0) (MvPolynomial.X_ne_zero _) (MvPolynomial.isHomogeneous_X ℂ 0)
    have hex (j) : ∃ p : Poly (n+1), p.IsHomogeneous D ∧
        Ideal.Quotient.mk (projectiveClosure V).ideal p = w j := hD j
    choose p hp hpw using hex
    have hli := normalization_common_degree_independent_dehomogenize V ψ p hp
      (by simpa only [hpw] using hw)
    have hcount := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hcount
    exact hcount
  · obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank
      (R := Poly k) (M := A) le_rfl
    have hex (j) : ∃ p : Poly n, Ideal.Quotient.mk V.ideal p = v j :=
      Ideal.Quotient.mk_surjective (v j)
    choose p hp using hex
    let D := Finset.univ.sup (fun j => (p j).totalDegree)
    have hpD (j) : (p j).totalDegree ≤ D := by
      dsimp [D]
      exact Finset.le_sup (f := fun j => (p j).totalDegree) (Finset.mem_univ j)
    let w := fun j => projectiveHomogenize D (p j)
    have hw (j) : (w j).IsHomogeneous D := projectiveHomogenize_homogeneous D (p j)
    have hdehom (j) : normalizationDehomogenize (w j) = p j :=
      normalizationDehomogenize_projectiveHomogenize D (p j) (hpD j)
    have hli := normalization_common_degree_independent_of_dehomogenize V ψ w hw
      (by simpa only [hdehom, hp] using hv)
    simpa only [Fintype.card_fin] using hli.fintype_card_le_finrank

/-- The actual affine normalization rank is the original degree when
the original parameters are finite on the literal infinity quotient. -/
theorem infinity_normalization_affine_rank_eq_degree {n k : ℕ}
    (V : AffineVariety n) (hV : V.IsIrreducible) (hd : V.dimension = k)
    (ψ : LinearProjection n k)
    (hf : (MvPolynomial.aeval (R := ℂ) (fun i =>
      Ideal.Quotient.mk ((projectiveClosure V).ideal ⊔ Ideal.span {MvPolynomial.X 0})
        (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))).Finite) :
    (affineNormalizationRank V ψ : ℚ) = V.degree := by
  rw [← normalization_cone_rank_eq_affine_rank V ψ (coneNormalizationMap_finite V ψ hf)]
  exact infinity_normalization_rank_eq_degree V hV hd ψ hf

end
end DistinctDistances.TrackA
