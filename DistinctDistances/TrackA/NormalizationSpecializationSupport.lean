import DistinctDistances.TrackA.NormalizationRankSupport
import DistinctDistances.OAIInterface.NormalizationSpecialization

set_option backward.isDefEq.respectTransparency false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Set the literal first coordinate to one. -/
def normalizationDehomogenize {n : ℕ} : Poly (n+1) →ₐ[ℂ] Poly n :=
  MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X)

theorem normalizationDehomogenize_projectiveHomogenize {n : ℕ}
    (D : ℕ) (f : Poly n) (hf : f.totalDegree ≤ D) :
    normalizationDehomogenize (projectiveHomogenize D f) = f := by
  simp only [normalizationDehomogenize, projectiveHomogenize, map_sum, map_mul,
    map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_rename,
    Function.comp_def, Fin.cons_zero, Fin.cons_succ, one_pow, one_mul,
    MvPolynomial.aeval_X_left_apply]
  exact chart_components_sum f hf

/-- On a fixed homogeneous degree, dehomogenization has zero kernel.
The original OAI chart nonvanishing theorem supplies the detector. -/
theorem normalizationDehomogenize_homogeneous_zero {n D : ℕ}
    (f : Poly (n+1)) (hf : f.IsHomogeneous D)
    (hz : normalizationDehomogenize f = 0) : f = 0 := by
  by_contra hne
  obtain ⟨c, hc⟩ :=
    OAI.Erdos970.WeightedTorusJets.LinearNormalization.exists_eval_cons_one_ne_zero hf hne
  have h := congrArg (MvPolynomial.aeval c) hz
  have he : (MvPolynomial.aeval c).comp (normalizationDehomogenize (n := n)) =
      MvPolynomial.aeval (Fin.cons 1 c) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases <;>
      simp [normalizationDehomogenize, AlgHom.comp_apply]
  have hzero : MvPolynomial.aeval (Fin.cons 1 c) f = 0 := by
    simpa only [← he, AlgHom.comp_apply, map_zero] using h
  exact hc (by simpa only [MvPolynomial.aeval_eq_eval] using hzero)

/-- The original zero-offset affine parameter map on its coordinate quotient. -/
def affineNormalizationMap {n k : ℕ} (V : AffineVariety n) (ψ : LinearProjection n k) :
    Poly k →ₐ[ℂ] (Poly n ⧸ V.ideal) :=
  MvPolynomial.aeval (fun i => Ideal.Quotient.mk V.ideal (linearCoordinate ψ i))

/-- The cone parameter map before passage to the source quotient. -/
def coneCoordinateMap {n k : ℕ} (ψ : LinearProjection n k) :
    Poly (k+1) →ₐ[ℂ] Poly (n+1) :=
  MvPolynomial.aeval (Fin.cons (MvPolynomial.X 0)
    (fun i => MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))

theorem coneCoordinateMap_homogeneous {n k D : ℕ} (ψ : LinearProjection n k)
    (f : Poly (k+1)) (hf : f.IsHomogeneous D) :
    (coneCoordinateMap ψ f).IsHomogeneous D := by
  let v : Fin (k+1) → Poly (n+1) := Fin.cons (MvPolynomial.X 0)
    (fun j => MvPolynomial.rename Fin.succ (linearCoordinate ψ j))
  have hlin : ∀ i : Fin (k+1), (v i).IsHomogeneous 1 := by
    intro i
    cases i using Fin.cases with
    | zero => exact MvPolynomial.isHomogeneous_X ℂ 0
    | succ j => exact (linearCoordinate_homogeneous ψ j).rename_isHomogeneous
  simpa only [coneCoordinateMap, one_mul] using hf.aeval v hlin

theorem coneCoordinateMap_quotient {n k : ℕ} (V : AffineVariety n)
    (ψ : LinearProjection n k) (f : Poly (k+1)) :
    Ideal.Quotient.mk (projectiveClosure V).ideal (coneCoordinateMap ψ f) =
      coneNormalizationMap V ψ f := by
  have he : (Ideal.Quotient.mkₐ ℂ (projectiveClosure V).ideal).comp
      (coneCoordinateMap ψ) = coneNormalizationMap V ψ := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases <;>
      simp only [coneCoordinateMap, coneNormalizationMap, AlgHom.comp_apply,
        MvPolynomial.aeval_X, Fin.cons_zero, Fin.cons_succ, Ideal.Quotient.mkₐ_eq_mk]
  exact congrArg (fun g => g f) he

theorem normalization_dehomogenization_comp {n k : ℕ} (V : AffineVariety n)
    (ψ : LinearProjection n k) :
    (projectiveClosureDehomogenization V).comp (coneNormalizationMap V ψ) =
      (affineNormalizationMap V ψ).comp (normalizationDehomogenize (n := k)) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases <;>
    simp only [AlgHom.comp_apply, coneNormalizationMap, affineNormalizationMap,
      normalizationDehomogenize, MvPolynomial.aeval_X, Fin.cons_zero, Fin.cons_succ,
      projectiveClosureDehomogenization_mk, map_one, MvPolynomial.aeval_rename,
      Function.comp_def, MvPolynomial.aeval_X_left_apply]

/-- The actual affine module rank induced by the original parameter map. -/
def affineNormalizationRank {n k : ℕ} (V : AffineVariety n) (ψ : LinearProjection n k) : ℕ :=
  let g := affineNormalizationMap V ψ
  letI := g.toRingHom.toAlgebra
  letI : Module (Poly k) (Poly n ⧸ V.ideal) := g.toRingHom.toAlgebra.toModule
  Module.finrank (Poly k) (Poly n ⧸ V.ideal)

theorem affineNormalizationMap_finite_of_cone {n k : ℕ}
    (V : AffineVariety n) (ψ : LinearProjection n k)
    (hf : (coneNormalizationMap V ψ).Finite) : (affineNormalizationMap V ψ).Finite := by
  have h := affine_finite_parameters_from_projective_cone V
    (fun i => MvPolynomial.rename Fin.succ (linearCoordinate ψ i)) hf
  simpa only [affineNormalizationMap, MvPolynomial.aeval_rename, Function.comp_def, Fin.cons_succ,
    MvPolynomial.aeval_X_left_apply] using h

/-- A common-degree cone-independent list stays independent over the
original affine parameter ring. Homogenize every coefficient of an affine
relation to one common degree, then use the literal closure ideal. -/
theorem normalization_common_degree_independent_dehomogenize {n k r D : ℕ}
    (V : AffineVariety n) (ψ : LinearProjection n k)
    (w : Fin r → Poly (n+1)) (hw : ∀ i, (w i).IsHomogeneous D)
    (hli : letI := (coneNormalizationMap V ψ).toRingHom.toAlgebra
      letI : Module (Poly (k+1)) (Poly (n+1) ⧸ (projectiveClosure V).ideal) :=
        (coneNormalizationMap V ψ).toRingHom.toAlgebra.toModule
      LinearIndependent (Poly (k+1))
        (fun i => Ideal.Quotient.mk (projectiveClosure V).ideal (w i))) :
    letI := (affineNormalizationMap V ψ).toRingHom.toAlgebra
    letI : Module (Poly k) (Poly n ⧸ V.ideal) :=
      (affineNormalizationMap V ψ).toRingHom.toAlgebra.toModule
    LinearIndependent (Poly k)
      (fun i => Ideal.Quotient.mk V.ideal (normalizationDehomogenize (w i))) := by
  letI := (coneNormalizationMap V ψ).toRingHom.toAlgebra
  letI : Module (Poly (k+1)) (Poly (n+1) ⧸ (projectiveClosure V).ideal) :=
    (coneNormalizationMap V ψ).toRingHom.toAlgebra.toModule
  letI : SMul (Poly (k+1)) (Poly (n+1) ⧸ (projectiveClosure V).ideal) :=
    (coneNormalizationMap V ψ).toRingHom.toAlgebra.toSMul
  letI := (affineNormalizationMap V ψ).toRingHom.toAlgebra
  letI : Module (Poly k) (Poly n ⧸ V.ideal) :=
    (affineNormalizationMap V ψ).toRingHom.toAlgebra.toModule
  letI : SMul (Poly k) (Poly n ⧸ V.ideal) :=
    (affineNormalizationMap V ψ).toRingHom.toAlgebra.toSMul
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  let E := Finset.univ.sup (fun j => (c j).totalDegree)
  let C : Fin r → Poly (k+1) := fun j => projectiveHomogenize E (c j)
  have hC (j) : (C j).IsHomogeneous E := projectiveHomogenize_homogeneous E (c j)
  have hCd (j) : normalizationDehomogenize (C j) = c j :=
    normalizationDehomogenize_projectiveHomogenize E (c j)
      (by
        dsimp [E]
        exact Finset.le_sup (f := fun j : Fin r => (c j).totalDegree) (Finset.mem_univ j))
  have hbase (j) : projectiveClosureDehomogenization V (coneNormalizationMap V ψ (C j)) =
      affineNormalizationMap V ψ (c j) := by
    have h := congrArg (fun g => g (C j)) (normalization_dehomogenization_comp V ψ)
    simpa only [AlgHom.comp_apply, hCd] using h
  let p : Poly (n+1) := ∑ j, coneCoordinateMap ψ (C j) * w j
  have hp : p.IsHomogeneous (E+D) := by
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact (coneCoordinateMap_homogeneous ψ _ (hC j)).mul (hw j)
  have hzero : projectiveClosureDehomogenization V
      (Ideal.Quotient.mk (projectiveClosure V).ideal p) = 0 := by
    simp only [p, map_sum, map_mul, coneCoordinateMap_quotient, hbase,
      projectiveClosureDehomogenization_mk]
    exact hc
  have hpI : p ∈ (projectiveClosure V).ideal :=
    (projectiveClosure_homogeneous_mem V p hp).mpr
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  have hrel : ∑ j, C j • Ideal.Quotient.mk (projectiveClosure V).ideal (w j) = 0 := by
    change ∑ j, coneNormalizationMap V ψ (C j) *
      Ideal.Quotient.mk (projectiveClosure V).ideal (w j) = 0
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hpI
    simpa only [p, map_sum, map_mul, coneCoordinateMap_quotient] using h
  have hCi := Fintype.linearIndependent_iff.mp hli C hrel i
  simpa only [hCd, map_zero] using congrArg normalizationDehomogenize hCi

/-- Affine independence of the dehomogenized common-degree list detects
cone independence. Decompose a cone relation by coefficient degree;
every homogeneous coefficient has an injective dehomogenization. -/
theorem normalization_common_degree_independent_of_dehomogenize {n k r D : ℕ}
    (V : AffineVariety n) (ψ : LinearProjection n k)
    (w : Fin r → Poly (n+1)) (hw : ∀ i, (w i).IsHomogeneous D)
    (hli : letI := (affineNormalizationMap V ψ).toRingHom.toAlgebra
      letI : Module (Poly k) (Poly n ⧸ V.ideal) :=
        (affineNormalizationMap V ψ).toRingHom.toAlgebra.toModule
      LinearIndependent (Poly k)
        (fun i => Ideal.Quotient.mk V.ideal (normalizationDehomogenize (w i)))) :
    letI := (coneNormalizationMap V ψ).toRingHom.toAlgebra
    letI : Module (Poly (k+1)) (Poly (n+1) ⧸ (projectiveClosure V).ideal) :=
      (coneNormalizationMap V ψ).toRingHom.toAlgebra.toModule
    LinearIndependent (Poly (k+1))
      (fun i => Ideal.Quotient.mk (projectiveClosure V).ideal (w i)) := by
  letI := (coneNormalizationMap V ψ).toRingHom.toAlgebra
  letI : Module (Poly (k+1)) (Poly (n+1) ⧸ (projectiveClosure V).ideal) :=
    (coneNormalizationMap V ψ).toRingHom.toAlgebra.toModule
  letI : SMul (Poly (k+1)) (Poly (n+1) ⧸ (projectiveClosure V).ideal) :=
    (coneNormalizationMap V ψ).toRingHom.toAlgebra.toSMul
  letI := (affineNormalizationMap V ψ).toRingHom.toAlgebra
  letI : Module (Poly k) (Poly n ⧸ V.ideal) :=
    (affineNormalizationMap V ψ).toRingHom.toAlgebra.toModule
  letI : SMul (Poly k) (Poly n ⧸ V.ideal) :=
    (affineNormalizationMap V ψ).toRingHom.toAlgebra.toSMul
  let 𝓜 := OAI.PiExponentJets.W64.quotientSection (projectiveClosure V).ideal
  letI : GradedAlgebra 𝓜 :=
    homogeneousQuotientGrading (projectiveClosure V).ideal (projectiveClosure V).isHomogeneous
  letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (k+1)) ℂ) 𝓜 :=
    OAI.Erdos970.WeightedTorusJets.Geometry.linear_quotient_map_gradedSMul _
      (coneNormalizationMap V ψ) (coneNormalizationMap_linear V ψ)
  have hmem (j) : Ideal.Quotient.mk (projectiveClosure V).ideal (w j) ∈ 𝓜 D :=
    ⟨w j, hw j, rfl⟩
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hrel (d : ℕ) : ∑ j, (MvPolynomial.homogeneousComponent d (c j)) •
      Ideal.Quotient.mk (projectiveClosure V).ideal (w j) = 0 := by
    have he (j) :
        (DirectSum.decompose 𝓜 (c j • Ideal.Quotient.mk (projectiveClosure V).ideal (w j)) (d+D) :
          Poly (n+1) ⧸ (projectiveClosure V).ideal) =
        (MvPolynomial.homogeneousComponent d (c j)) •
          Ideal.Quotient.mk (projectiveClosure V).ideal (w j) := by
      have h := OAI.Erdos970.WeightedTorusJets.decompose_smul_of_homogeneous_right
        (MvPolynomial.homogeneousSubmodule (Fin (k+1)) ℂ) 𝓜 (c j) (hmem j) d
      have hb : (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (k+1)) ℂ)
          (c j) d : Poly (k+1)) = MvPolynomial.homogeneousComponent d (c j) := by
        change (MvPolynomial.decomposition.decompose' (c j) d : Poly (k+1)) = _
        exact MvPolynomial.decomposition.decompose'_apply (c j) d
      rw [hb] at h
      exact h
    have h := congrArg (fun a => (DirectSum.decompose 𝓜 a (d+D) :
      Poly (n+1) ⧸ (projectiveClosure V).ideal)) hc
    simpa only [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum,
      he, DirectSum.decompose_zero, DirectSum.zero_apply, Submodule.coe_zero] using h
  have hcoeff (d : ℕ) : normalizationDehomogenize (MvPolynomial.homogeneousComponent d (c i)) = 0 := by
    have h := congrArg (projectiveClosureDehomogenization V) (hrel d)
    have hbase (p : Poly (k+1)) :
        projectiveClosureDehomogenization V (coneNormalizationMap V ψ p) =
          affineNormalizationMap V ψ (normalizationDehomogenize p) :=
      congrArg (fun g => g p) (normalization_dehomogenization_comp V ψ)
    have haff : ∑ j, normalizationDehomogenize (MvPolynomial.homogeneousComponent d (c j)) •
        Ideal.Quotient.mk V.ideal (normalizationDehomogenize (w j)) = 0 := by
      change ∑ j, affineNormalizationMap V ψ
        (normalizationDehomogenize (MvPolynomial.homogeneousComponent d (c j))) *
          Ideal.Quotient.mk V.ideal (normalizationDehomogenize (w j)) = 0
      change projectiveClosureDehomogenization V
        (∑ j, coneNormalizationMap V ψ (MvPolynomial.homogeneousComponent d (c j)) *
          Ideal.Quotient.mk (projectiveClosure V).ideal (w j)) =
        projectiveClosureDehomogenization V 0 at h
      simpa only [map_sum, map_mul, hbase, projectiveClosureDehomogenization_mk,
        normalizationDehomogenize, map_zero] using h
    exact Fintype.linearIndependent_iff.mp hli _ haff i
  rw [← MvPolynomial.sum_homogeneousComponent (c i)]
  apply Finset.sum_eq_zero
  intro d _
  exact normalizationDehomogenize_homogeneous_zero _
    (MvPolynomial.homogeneousComponent_isHomogeneous d (c i)) (hcoeff d)

end
end DistinctDistances.TrackA
