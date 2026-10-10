import DistinctDistances.TrackA.ProjectionOrderSupport
import DistinctDistances.TrackA.ADepthAux

namespace DistinctDistances.TrackA
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical BigOperators

/-- The original affine chart of a projective closure is the original variety. -/
theorem projectiveClosure_chart_zero {n : ℕ} (V : AffineVariety n) :
    (projectiveClosure V).affineChart 0 = V := by
  apply AffineVariety.ext
  rw [affineChart_ideal_exact]
  have hchart : chartPullback (0 : Fin (n+1)) =
      MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X) := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j using Fin.cases <;> simp [chartPullback]
  rw [hchart]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    exact fun F hF => projectiveClosure_aeval_mem V F hF
  · intro g hg
    have hmem := Ideal.mem_map_of_mem
      (MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X)).toRingHom
      (projectiveClosure_homogenize_mem V g hg)
    change MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X)
      (projectiveHomogenize g.totalDegree g) ∈ _ at hmem
    rwa [projectiveHomogenize_aeval] at hmem

theorem chartCoordinates_affineEmbedding {n : ℕ} (p : Point n) :
    chartCoordinates 0 (affineEmbedding p) = p ∧ (affineEmbedding p).rep 0 ≠ 0 := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (Fin.cons (α := fun _ => ℂ) (1 : ℂ) p) (by
      intro hz
      have h0 := congrFun hz (0 : Fin (n+1))
      exact one_ne_zero (by simpa only [Fin.cons_zero, Pi.zero_apply] using h0))
  change (u : ℂ) • Fin.cons (1 : ℂ) p = (affineEmbedding p).rep at hu
  constructor
  · funext j
    simp [chartCoordinates, ← hu, Pi.smul_apply, smul_eq_mul, Units.ne_zero u]
  · simp [← hu, Pi.smul_apply, smul_eq_mul, Units.ne_zero u]

theorem projectiveClosure_multiplicity {n : ℕ} (V : AffineVariety n) (p : Point n) :
    (projectiveClosure V).multiplicity (affineEmbedding p) = V.multiplicity p := by
  rw [(projectiveClosure V).multiplicity_chart _ 0
    (chartCoordinates_affineEmbedding p).2, projectiveClosure_chart_zero,
    (chartCoordinates_affineEmbedding p).1]

/-- Full ambient dimension forces the reduced irreducible ideal to be zero. -/
theorem proper_affine_dimension_lt {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hproper : V.ideal ≠ ⊥) : V.dimension < n := by
  obtain ⟨j, hj, ha⟩ := OAI.QuarticPowerFree.affineDimension_independent_coordinates
    V.ideal hV.ne_top
  have hcard := Fintype.card_le_of_injective j hj
  have hle : V.dimension ≤ n := by simpa [AffineVariety.dimension] using hcard
  by_contra hlt
  have heq : V.dimension = n := by omega
  have hcards : Fintype.card (Fin (OAI.QuarticPowerFree.affineDimension V.ideal)) =
      Fintype.card (Fin n) := by simpa [AffineVariety.dimension] using heq
  have hbij : Function.Bijective j :=
    (Fintype.bijective_iff_injective_and_card j).mpr ⟨hj, hcards⟩
  let e := Equiv.ofBijective j hbij
  have hall : AlgebraicIndependent ℂ (fun i : Fin n => Ideal.Quotient.mk V.ideal (MvPolynomial.X i)) := by
    have hh := ha.comp e.symm e.symm.injective
    change AlgebraicIndependent ℂ (fun x =>
      Ideal.Quotient.mk V.ideal (MvPolynomial.X (e (e.symm x)))) at hh
    simpa only [Equiv.apply_symm_apply] using hh
  have hhom : MvPolynomial.aeval (fun i : Fin n => Ideal.Quotient.mk V.ideal (MvPolynomial.X i)) =
      Ideal.Quotient.mkₐ ℂ V.ideal := by ext i; simp
  have hker := algebraicIndependent_iff_ker_eq_bot.mp hall
  rw [hhom] at hker
  exact hproper (by simpa using hker)

/-- A reduced point has constant local Hilbert function one. -/
theorem point_multiplicity_one {n : ℕ} (V : AffineVariety n) (p : Point n)
    (hV : V.ideal = pointIdeal p) : V.multiplicity p = 1 := by
  letI : CommRing (PointLocalRing p) :=
    { __ := (inferInstance : Ring (PointLocalRing p))
      mul_comm := fun a b => mul_comm a b }
  have hH (t : ℕ) : V.localHilbert p t = 1 := by
    unfold AffineVariety.localHilbert localLengthAt localizedIdeal
    rw [hV, sup_eq_left.mpr (Ideal.pow_le_self (by omega)),
      IsLocalization.AtPrime.map_eq_maximalIdeal]
    apply Module.length_eq_one_iff.mpr
    exact isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal (PointLocalRing p)).out
  have hP : V.localHilbertPolynomial p = Polynomial.C 1 := by
    apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
    obtain ⟨N, hN⟩ := (V.localHilbert_eventually_polynomial p).choose_spec.2
    filter_upwards [Filter.eventually_atTop.mpr ⟨N, hN⟩] with t ht
    obtain ⟨a, ha, he⟩ := ht
    rw [hH] at ha
    have ha1 : a = 1 := by exact_mod_cast ha.symm
    change (V.localHilbertPolynomial p).eval (t : ℚ) = _ at he
    simpa [ha1] using he
  simp [AffineVariety.multiplicity, AffineVariety.localDimension, hP]

theorem linearCoordinate_homogeneous {n m : ℕ} (φ : LinearProjection n m) (j : Fin m) :
    (linearCoordinate φ j).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

theorem linearCoordinate_eval {n m : ℕ} (φ : LinearProjection n m) (p : Point n) (j : Fin m) :
    MvPolynomial.eval p (linearCoordinate φ j) = φ p j := by
  have h := (AffineProjection.eval_pullback (⟨φ, 0⟩ : AffineProjection n m) p
    (MvPolynomial.X j))
  simpa [AffineProjection.pullback, AffineProjection.apply, MvPolynomial.aeval_eq_eval] using h

theorem chartPullback_degree {n : ℕ} (i : Fin (n+1)) (F : Poly (n+1)) :
    (chartPullback i F).totalDegree ≤ F.totalDegree := by
  exact OAI.QuarticPowerFree.totalDegree_linear_substitute_le
    (Fin.insertNth i (MvPolynomial.C 1) MvPolynomial.X) (by
      intro j
      rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩ <;> simp) F

theorem affine_projection_coordinates {n m : ℕ} (φ : LinearProjection (n+1) m)
    (p : Point n) (j : Fin m) :
    MvPolynomial.eval p (chartPullback 0 (linearCoordinate φ j)) = φ (Fin.cons 1 p) j := by
  have hins : Fin.insertNth (0 : Fin (n+1)) (1 : ℂ) p = Fin.cons (α := fun _ => ℂ) 1 p := by
    ext j
    cases j using Fin.cases <;> simp
  rw [chartPullback_eval, linearCoordinate_eval, hins]

theorem projectiveMap_embedding_data {n m : ℕ} (φ : LinearProjection (n+1) m)
    (p : Point n) (hp : φ (affineEmbedding p).rep ≠ 0) :
    ∃ hv : φ (Fin.cons 1 p) ≠ 0,
      projectiveMap φ (affineEmbedding p) hp = Projectivization.mk ℂ (φ (Fin.cons 1 p)) hv := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (Fin.cons (α := fun _ => ℂ) (1 : ℂ) p) (by
      intro hz
      have h0 := congrFun hz (0 : Fin (n+1))
      exact one_ne_zero (by simpa only [Fin.cons_zero, Pi.zero_apply] using h0))
  change (u : ℂ) • Fin.cons (1 : ℂ) p = (affineEmbedding p).rep at hu
  have heq : φ (affineEmbedding p).rep = (u : ℂ) • φ (Fin.cons 1 p) := by
    rw [← hu, map_smul]
  have hv : φ (Fin.cons 1 p) ≠ 0 := by
    intro hz
    apply hp
    rw [heq, hz, smul_zero]
  refine ⟨hv, ?_⟩
  exact (Projectivization.mk_eq_mk_iff ℂ _ _ hp hv).mpr ⟨u, heq.symm⟩

theorem chartCoordinates_mk {m : ℕ} (v : Point (m+1)) (hv : v ≠ 0)
    (i : Fin (m+1)) (hi : (Projectivization.mk ℂ v hv).rep i ≠ 0) :
    v i ≠ 0 ∧ chartCoordinates i (Projectivization.mk ℂ v hv) =
      fun j => v (i.succAbove j) / v i := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  change (u : ℂ) • v = (Projectivization.mk ℂ v hv).rep at hu
  have hvi : v i ≠ 0 := by
    intro hz
    apply hi
    simp [← hu, Pi.smul_apply, smul_eq_mul, hz]
  refine ⟨hvi, ?_⟩
  funext j
  simp only [chartCoordinates, ← hu, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ (Units.ne_zero u)

end
end DistinctDistances.TrackA
