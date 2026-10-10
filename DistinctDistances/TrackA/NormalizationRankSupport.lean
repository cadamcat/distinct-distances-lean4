import DistinctDistances.TrackA.AffineFiniteNormalizationSupport
import DistinctDistances.OAIInterface.NormalizationRank
import DistinctDistances.TrackA.ADepthAux

set_option backward.isDefEq.respectTransparency false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite polynomial map with the full source dimension has zero
kernel. A nonzero kernel element would lower the quotient dimension. -/
theorem finite_polynomial_map_injective_of_dimension {s : ℕ} {A : Type*}
    [CommRing A] (g : Poly s →+* A) (hf : g.Finite)
    (hd : ringKrullDim A = (s : WithBot ℕ∞)) : Function.Injective g := by
  let K := RingHom.ker g
  have he : (RingHom.kerLift g).comp (Ideal.Quotient.mk K) = g := by
    exact RingHom.ext (fun p => RingHom.kerLift_mk g p)
  have hi : (RingHom.kerLift g).IsIntegral := by
    intro a
    apply RingHom.IsIntegralElem.of_comp (f := Ideal.Quotient.mk K)
    rw [he]
    exact hf.to_isIntegral a
  have hKdim := OAI.PiExponentJets.W24.ringKrullDim_eq_of_integral_injective
    (RingHom.kerLift g) (RingHom.kerLift_injective g) hi
  rw [RingHom.injective_iff_ker_eq_bot]
  apply eq_bot_iff.mpr
  intro p hp
  change p = 0
  by_contra hp0
  have h := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk K)
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hp0)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  rw [← hKdim, hd, MvPolynomial.ringKrullDim_of_isNoetherianRing] at h
  simp only [ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_natCard,
    Nat.card_fin, zero_add, WithBot.coe_natCast] at h
  have hbad : s + 1 ≤ s := by exact_mod_cast h
  omega

/-- The actual finite homogeneous coordinate map has rank equal to the
shared project's rational degree. Reuse the original OAI graded rank
comparison; no degree/rank identity is built into a model definition. -/
theorem projective_finite_linear_degree_eq_rank {n k : ℕ}
    (V : ProjectiveVariety n) (hV : V.IsIrreducible)
    (g : Poly (k+1) →ₐ[ℂ] (Poly n ⧸ V.ideal))
    (hg : Function.Injective g) (hf : g.Finite)
    (hlin : ∀ i, ∃ l : Poly n,
      l.IsHomogeneous 1 ∧ g (MvPolynomial.X i) = Ideal.Quotient.mk V.ideal l) :
    let _ := g.toRingHom.toAlgebra
    let _ : Module (Poly (k+1)) (Poly n ⧸ V.ideal) := g.toRingHom.toAlgebra.toModule
    V.dimension = k ∧
      V.degree = (Module.finrank (Poly (k+1)) (Poly n ⧸ V.ideal) : ℚ) := by
  letI : V.ideal.IsPrime := hV
  letI := g.toRingHom.toAlgebra
  letI : Module (Poly (k+1)) (Poly n ⧸ V.ideal) := g.toRingHom.toAlgebra.toModule
  letI : SMul (Poly (k+1)) (Poly n ⧸ V.ideal) := g.toRingHom.toAlgebra.toSMul
  letI : IsScalarTower ℂ (Poly (k+1)) (Poly n ⧸ V.ideal) := IsScalarTower.of_algHom g
  letI : Module.Finite (Poly (k+1)) (Poly n ⧸ V.ideal) := hf
  letI : Module.IsTorsionFree (Poly (k+1)) (Poly n ⧸ V.ideal) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hg
  letI : GradedAlgebra (OAI.PiExponentJets.W64.quotientSection V.ideal) :=
    homogeneousQuotientGrading V.ideal V.isHomogeneous
  letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (k+1)) ℂ)
      (OAI.PiExponentJets.W64.quotientSection V.ideal) :=
    OAI.Erdos970.WeightedTorusJets.Geometry.linear_quotient_map_gradedSMul V.ideal g hlin
  have hdim (D : ℕ) :
      Module.finrank ℂ (MvPolynomial.homogeneousSubmodule (Fin (k+1)) ℂ D) =
        (D+k).choose k := by
    rw [OAI.PiExponentJets.W64.homogeneousSection_finrank,
      OAI.PiExponentJets.W64.card_exponents_degree, Fintype.card_fin, Nat.multichoose_eq]
    have he : k+1+D-1 = k+D := by omega
    rw [he, Nat.add_comm k D, Nat.choose_symm_add]
  have hP : ∀ᶠ D : ℕ in Filter.atTop,
      (Module.finrank ℂ (OAI.PiExponentJets.W64.quotientSection V.ideal D) : ℚ) =
        V.hilbertPolynomial.eval (D : ℚ) := by
    obtain ⟨N, hN⟩ := V.hilbert_eventually
    filter_upwards [Filter.eventually_gt_atTop N] with D hD
    exact hN D hD
  obtain ⟨hd, hdeg⟩ :=
    OAI.Erdos970.WeightedTorusJets.Geometry.hilbertPolynomial_degree_coefficient_eq_rank
      (MvPolynomial.homogeneousSubmodule (Fin (k+1)) ℂ)
      (OAI.PiExponentJets.W64.quotientSection V.ideal)
      (a := MvPolynomial.X 0) (MvPolynomial.X_ne_zero _)
      (MvPolynomial.isHomogeneous_X ℂ 0) k hdim V.hilbertPolynomial hP
  refine ⟨hd, ?_⟩
  change V.hilbertPolynomial.coeff V.dimension * (V.dimension.factorial : ℚ) = _
  change V.hilbertPolynomial.coeff V.hilbertPolynomial.natDegree *
    (V.hilbertPolynomial.natDegree.factorial : ℚ) = _
  rw [Polynomial.coeff_natDegree, hd, mul_comm]
  exact hdeg

/-- Retain the original homogenizing coordinate and the original
affine linear parameters in one literal cone normalization map. -/
def coneNormalizationMap {n k : ℕ} (V : AffineVariety n) (ψ : LinearProjection n k) :
    Poly (k+1) →ₐ[ℂ] (Poly (n+1) ⧸ (projectiveClosure V).ideal) :=
  MvPolynomial.aeval (R := ℂ)
    (Fin.cons (Ideal.Quotient.mk (projectiveClosure V).ideal (MvPolynomial.X 0))
      (fun i => Ideal.Quotient.mk (projectiveClosure V).ideal
        (MvPolynomial.rename Fin.succ (linearCoordinate ψ i))))

theorem coneNormalizationMap_finite {n k : ℕ} (V : AffineVariety n)
    (ψ : LinearProjection n k)
    (hf : (MvPolynomial.aeval (R := ℂ) (fun i =>
      Ideal.Quotient.mk ((projectiveClosure V).ideal ⊔ Ideal.span {MvPolynomial.X 0})
        (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))).Finite) :
    (coneNormalizationMap V ψ).Finite := by
  exact homogeneous_finite_parameters_from_coordinate_cut
    (projectiveClosure V).ideal (projectiveClosure V).isHomogeneous
    (MvPolynomial.X 0) (MvPolynomial.isHomogeneous_X ℂ 0)
    (fun i => MvPolynomial.rename Fin.succ (linearCoordinate ψ i))
    (fun i => (linearCoordinate_homogeneous ψ i).rename_isHomogeneous) hf

theorem coneNormalizationMap_linear {n k : ℕ} (V : AffineVariety n)
    (ψ : LinearProjection n k) :
    ∀ i, ∃ l : Poly (n+1), l.IsHomogeneous 1 ∧
      coneNormalizationMap V ψ (MvPolynomial.X i) =
        Ideal.Quotient.mk (projectiveClosure V).ideal l := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨MvPolynomial.X 0, MvPolynomial.isHomogeneous_X ℂ 0, by
      simp only [coneNormalizationMap, MvPolynomial.aeval_X, Fin.cons_zero]⟩
  · exact ⟨MvPolynomial.rename Fin.succ (linearCoordinate ψ j),
      (linearCoordinate_homogeneous ψ j).rename_isHomogeneous, by
        simp only [coneNormalizationMap, MvPolynomial.aeval_X, Fin.cons_succ]⟩

theorem coneNormalizationMap_injective {n k : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension = k) (ψ : LinearProjection n k)
    (hf : (coneNormalizationMap V ψ).Finite) :
    Function.Injective (coneNormalizationMap V ψ) := by
  have hPV := projectiveClosure_isIrreducible V hV
  have hne := V.points_nonempty_of_isIrreducible hV
  have hdP := projectiveClosure_dimension V hne
  have hdcone := (projectiveClosure V).dimension_cone
    (ProjectiveFamily.irreducible_points_nonempty _ hPV)
  apply finite_polynomial_map_injective_of_dimension (coneNormalizationMap V ψ).toRingHom hf
  rw [prime_coordinate_krull_dimension _ hPV]
  change ((projectiveClosure V).affineCone.dimension : WithBot ℕ∞) = _
  simpa only [hdP, hd] using congrArg (fun d : ℕ => (d : WithBot ℕ∞)) hdcone

/-- The degree of the original affine variety is the actual module rank
of its finite cone normalization retaining X0. -/
theorem infinity_normalization_degree_eq_cone_rank {n k : ℕ}
    (V : AffineVariety n) (hV : V.IsIrreducible) (hd : V.dimension = k)
    (ψ : LinearProjection n k)
    (hf : (MvPolynomial.aeval (R := ℂ) (fun i =>
      Ideal.Quotient.mk ((projectiveClosure V).ideal ⊔ Ideal.span {MvPolynomial.X 0})
        (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))).Finite) :
    let g := coneNormalizationMap V ψ
    let _ := g.toRingHom.toAlgebra
    let _ : Module (Poly (k+1)) (Poly (n+1) ⧸ (projectiveClosure V).ideal) :=
      g.toRingHom.toAlgebra.toModule
    V.degree = (Module.finrank (Poly (k+1))
      (Poly (n+1) ⧸ (projectiveClosure V).ideal) : ℚ) := by
  have hfinite := coneNormalizationMap_finite V ψ hf
  have h := (projective_finite_linear_degree_eq_rank (projectiveClosure V)
    (projectiveClosure_isIrreducible V hV) (coneNormalizationMap V ψ)
    (coneNormalizationMap_injective V hV hd ψ hfinite) hfinite
    (coneNormalizationMap_linear V ψ)).2
  simpa only [projectiveClosure_degree] using h

/-- The rank belongs to the actual finite cone map, with its induced
polynomial module structure, including the retained X0 parameter. -/
def coneNormalizationRank {n k : ℕ} (V : AffineVariety n) (ψ : LinearProjection n k) : ℕ :=
  let g := coneNormalizationMap V ψ
  letI := g.toRingHom.toAlgebra
  letI : Module (Poly (k+1)) (Poly (n+1) ⧸ (projectiveClosure V).ideal) :=
    g.toRingHom.toAlgebra.toModule
  Module.finrank (Poly (k+1)) (Poly (n+1) ⧸ (projectiveClosure V).ideal)

theorem infinity_normalization_rank_eq_degree {n k : ℕ}
    (V : AffineVariety n) (hV : V.IsIrreducible) (hd : V.dimension = k)
    (ψ : LinearProjection n k)
    (hf : (MvPolynomial.aeval (R := ℂ) (fun i =>
      Ideal.Quotient.mk ((projectiveClosure V).ideal ⊔ Ideal.span {MvPolynomial.X 0})
        (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))).Finite) :
    (coneNormalizationRank V ψ : ℚ) = V.degree :=
  (infinity_normalization_degree_eq_cone_rank V hV hd ψ hf).symm

/-- Positivity comes from the genuine finite torsion-free module,
independently of the Hilbert coefficient comparison. -/
theorem coneNormalizationRank_pos_of_finite {n k : ℕ}
    (V : AffineVariety n) (hV : V.IsIrreducible) (hd : V.dimension = k)
    (ψ : LinearProjection n k) (hf : (coneNormalizationMap V ψ).Finite) :
    0 < coneNormalizationRank V ψ := by
  let g := coneNormalizationMap V ψ
  letI : (projectiveClosure V).ideal.IsPrime := projectiveClosure_isIrreducible V hV
  letI := g.toRingHom.toAlgebra
  letI : Module (Poly (k+1)) (Poly (n+1) ⧸ (projectiveClosure V).ideal) :=
    g.toRingHom.toAlgebra.toModule
  letI : Module.Finite (Poly (k+1)) (Poly (n+1) ⧸ (projectiveClosure V).ideal) := hf
  letI : Module.IsTorsionFree (Poly (k+1)) (Poly (n+1) ⧸ (projectiveClosure V).ideal) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (coneNormalizationMap_injective V hV hd ψ hf)
  exact Module.finrank_pos

theorem infinity_normalization_rank_pos {n k : ℕ}
    (V : AffineVariety n) (hV : V.IsIrreducible) (hd : V.dimension = k)
    (ψ : LinearProjection n k)
    (hf : (MvPolynomial.aeval (R := ℂ) (fun i =>
      Ideal.Quotient.mk ((projectiveClosure V).ideal ⊔ Ideal.span {MvPolynomial.X 0})
        (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))).Finite) :
    0 < coneNormalizationRank V ψ := by
  exact coneNormalizationRank_pos_of_finite V hV hd ψ (coneNormalizationMap_finite V ψ hf)

/-- A finite affine map to the source dimension has injective pullback
on the actual coordinate algebra. -/
theorem finite_affine_projection_pullback_injective {n k : ℕ}
    (V : AffineVariety n) (hV : V.IsIrreducible) (hd : V.dimension = k)
    (φ : AffineProjection n k) (hf : FiniteAffineProjection φ V) :
    Function.Injective ((Ideal.Quotient.mkₐ ℂ V.ideal).comp φ.pullback) := by
  apply finite_polynomial_map_injective_of_dimension
    ((Ideal.Quotient.mkₐ ℂ V.ideal).comp φ.pullback).toRingHom hf
  rw [prime_coordinate_krull_dimension _ hV]
  simpa only [hd]

/-- The reduced image of this finite affine normalization is the whole
polynomial base, rather than a proper lower-dimensional subvariety. -/
theorem finite_affine_projection_image_ideal_bot {n k : ℕ}
    (V : AffineVariety n) (hV : V.IsIrreducible) (hd : V.dimension = k)
    (φ : AffineProjection n k) (hf : FiniteAffineProjection φ V) :
    (φ.image V).ideal = ⊥ := by
  let g := (Ideal.Quotient.mkₐ ℂ V.ideal).comp φ.pullback
  have hg := finite_affine_projection_pullback_injective V hV hd φ hf
  ext p
  change φ.pullback p ∈ V.ideal ↔ p = 0
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change g p = 0 ↔ p = 0
  exact map_eq_zero_iff g.toRingHom hg

/-- An irreducible affine zero-fold is one reduced complex point, so
its projection to the zero-dimensional base has generic degree one. -/
theorem zeroDim_linear_projection_generic_degree {n : ℕ}
    (V : AffineVariety n) (hV : V.IsIrreducible) (hd : V.dimension = 0)
    (ψ : LinearProjection n 0) :
    ∃ r : ℕ, (r : ℚ) = V.degree ∧
      (⟨ψ, 0⟩ : AffineProjection n 0).GenericallyFiniteOfDegree V r := by
  obtain ⟨x, hx, hdeg⟩ := zeroDim_irreducible_data V hV hd
  let φ : AffineProjection n 0 := ⟨ψ, 0⟩
  refine ⟨1, hdeg.symm, by decide, 1, ?_, ?_⟩
  · have hprime := φ.image_irreducible V hV
    exact hprime.one_notMem
  · intro y _ _
    have hfiber : φ.fiber V y = {x} := by
      ext z
      change (z ∈ V.points ∧ φ.apply z = y) ↔ z ∈ ({x} : Set (Point n))
      rw [hx]
      exact ⟨And.left, fun hz => ⟨hz, Subsingleton.elim _ _⟩⟩
    rw [hfiber]
    exact ⟨Set.finite_singleton x, Set.ncard_singleton x⟩

end
end DistinctDistances.TrackA
