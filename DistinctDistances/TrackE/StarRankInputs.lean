import DistinctDistances.TrackE.Directions
import DistinctDistances.TrackE.GlobalRankInputs
import DistinctDistances.TrackE.RequestsStar
import DistinctDistances.Bridges.StarRank

/-! Literal physical-star inputs for `eq:star-rank`, reduction.tex:214–230. -/

namespace DistinctDistances.Reduction
open scoped BigOperators Classical
noncomputable section

variable {d : ℕ}

/-- The actual projective directions of the original physical partners. -/
def starDirections (p : RPoint d) (T : Finset (RPoint d)) : Set (ProjectivePoint d) :=
  {z | ∃ q ∈ T, ∃ h : cplx q ≠ cplx p,
    radialProjection (cplx p) (cplx q) h = z}

/-- The degree-D envelope kernel on all representatives of the direction set
is the physical evaluation kernel, even when directions coincide. -/
theorem star_envelope_physical_kernel (p : RPoint d) (T : Finset (RPoint d)) (hp : p ∉ T)
    (D : ℕ) (V : ProjectiveVariety d)
    (hkernel : ∀ f : Poly d, f.IsHomogeneous D →
      (f ∈ V.ideal ↔ ∀ v ∈ ProjectiveVariety.nonzeroRepresentatives (starDirections p T),
        MvPolynomial.eval v f = 0)) :
    ∀ f : Poly d, f.IsHomogeneous D →
      (f ∈ V.ideal ↔ ∀ q ∈ T, MvPolynomial.eval (cplx (q - p)) f = 0) := by
  intro f hf
  have hdisp (q : RPoint d) : cplx (q - p) = cplx q - cplx p := by
    ext i
    simp [cplx, PiLp.sub_apply]
  have hneq (q : RPoint d) (hq : q ∈ T) : cplx q ≠ cplx p := by
    intro h
    have hqp : q = p := Bridges.cplx_injective h
    exact hp (hqp ▸ hq)
  constructor
  · intro hfV q hq
    have hqc := hneq q hq
    have hdispNe : cplx (q - p) ≠ 0 := by
      rw [hdisp]
      exact sub_ne_zero.mpr hqc
    have hz : radialProjection (cplx p) (cplx q) hqc ∈ starDirections p T :=
      ⟨q, hq, hqc, rfl⟩
    have hproj : Projectivization.mk ℂ (cplx (q - p)) hdispNe =
        radialProjection (cplx p) (cplx q) hqc := by
      unfold radialProjection
      apply (Projectivization.mk_eq_mk_iff' ℂ (cplx (q - p))
        (cplx q - cplx p) hdispNe (sub_ne_zero.mpr hqc)).2
      exact ⟨1, by simpa [hdisp]⟩
    have hrep : cplx (q - p) ∈
        ProjectiveVariety.nonzeroRepresentatives (starDirections p T) := by
      refine ⟨hdispNe, ?_⟩
      rw [hproj]
      exact hz
    exact (hkernel f hf).mp hfV (cplx (q - p)) hrep
  · intro hphysical
    apply (hkernel f hf).mpr
    intro v hv
    obtain ⟨hv0, hz⟩ := hv
    change Projectivization.mk ℂ v hv0 ∈ starDirections p T at hz
    obtain ⟨q, hq, hqc, hdir⟩ := hz
    have hdispNe : cplx (q - p) ≠ 0 := by
      rw [hdisp]
      exact sub_ne_zero.mpr hqc
    have hproj : Projectivization.mk ℂ v hv0 =
        Projectivization.mk ℂ (cplx (q - p)) hdispNe := by
      calc
        Projectivization.mk ℂ v hv0 = radialProjection (cplx p) (cplx q) hqc := hdir.symm
        _ = Projectivization.mk ℂ (cplx (q - p)) hdispNe := by
          unfold radialProjection
          apply (Projectivization.mk_eq_mk_iff' ℂ (cplx q - cplx p)
            (cplx (q - p)) (sub_ne_zero.mpr hqc) hdispNe).2
          exact ⟨1, by simpa [hdisp]⟩
    obtain ⟨a, ha⟩ :=
      (Projectivization.mk_eq_mk_iff' ℂ v (cplx (q - p)) hv0 hdispNe).mp hproj
    rw [← ha, Bridges.homogeneous_eval_smul f hf a (cplx (q - p)),
      hphysical q hq, mul_zero]

/-- A component cover of the actual direction envelope covers every physical
partner by DirMem, with no injectivity assumption on its projective direction. -/
theorem star_family_covers_partners (p : RPoint d) (T : Finset (RPoint d)) (hp : p ∉ T)
    (V : ProjectiveVariety d) (F : ProjectiveFamily.Family d)
    (hpoints : starDirections p T ⊆ V.points) (hlocus : ProjectiveFamily.locus F = V) :
    ∀ q ∈ T, ∃ Y ∈ F, DirMem Y p q := by
  intro q hq
  have hqc : cplx q ≠ cplx p := by
    intro h
    have hqp : q = p := Bridges.cplx_injective h
    exact hp (hqp ▸ hq)
  have hz : radialProjection (cplx p) (cplx q) hqc ∈ starDirections p T :=
    ⟨q, hq, hqc, rfl⟩
  have hzV := hpoints hz
  rw [← hlocus, ProjectiveFamily.points_locus] at hzV
  obtain ⟨Y, hY⟩ := Set.mem_iUnion.mp hzV
  obtain ⟨hYF, hzY⟩ := Set.mem_iUnion.mp hY
  exact ⟨Y, hYF, hqc, hzY⟩

/-- Sum direction caps over every containing component while counting physical
partners. The finite union count is bounded above by the sum of filter counts. -/
theorem star_rank_weighted_count (p : RPoint d) (T : Finset (RPoint d))
    (F : ProjectiveFamily.Family d) (C A : ℝ) (hC : 0 < C) (hA : 1 ≤ A)
    (hcover : ∀ q ∈ T, ∃ Y ∈ F, DirMem Y p q)
    (hcount : ∀ Y ∈ F,
      ((T.filter fun q => DirMem Y p q).card : ℝ) ≤ C * (Y.degree : ℝ) * A ^ Y.dimension) :
    (T.card : ℝ) ≤ C * ∑ Y ∈ F, (Y.degree : ℝ) * A ^ Y.dimension := by
  classical
  have hcover' : T ⊆ F.biUnion fun Y => T.filter fun q => DirMem Y p q := by
    intro q hq
    obtain ⟨Y, hY, hdir⟩ := hcover q hq
    exact Finset.mem_biUnion.mpr
      ⟨Y, hY, Finset.mem_filter.mpr ⟨hq, hdir⟩⟩
  have hcard : (T.card : ℝ) ≤
      ∑ Y ∈ F, ((T.filter fun q => DirMem Y p q).card : ℝ) := by
    have hnat : T.card ≤ (F.biUnion fun Y => T.filter fun q => DirMem Y p q).card :=
      Finset.card_le_card hcover'
    have hsumNat : (F.biUnion fun Y => T.filter fun q => DirMem Y p q).card ≤
        ∑ Y ∈ F, (T.filter fun q => DirMem Y p q).card := Finset.card_biUnion_le
    exact_mod_cast hnat.trans hsumNat
  calc
    (T.card : ℝ) ≤ ∑ Y ∈ F, ((T.filter fun q => DirMem Y p q).card : ℝ) := hcard
    _ ≤ ∑ Y ∈ F, C * (Y.degree : ℝ) * A ^ Y.dimension :=
      Finset.sum_le_sum fun Y hY => hcount Y hY
    _ = C * ∑ Y ∈ F, (Y.degree : ℝ) * A ^ Y.dimension := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Y hY
      ring

/-- Compare complete projective degree weights at A and D, uniformly over the
bounded component dimensions. Consumer: reduction.tex:223–230. -/
theorem star_rank_weighted_compare (F : ProjectiveFamily.Family d) (A : ℝ) (hA : 1 ≤ A)
    (D : ℕ) (hD : 1 ≤ D) (hAD : A ≤ 2 * (D : ℝ))
    (hF : ∀ Y ∈ F, Y.IsIrreducible ∧ Y.dimension ≤ d) :
    (∑ Y ∈ F, (Y.degree : ℝ) * A ^ Y.dimension) ≤
      (2 : ℝ) ^ d * (TrackA.projectiveWeightedDegree F D : ℝ) := by
  have hterm (Y : ProjectiveVariety d) (hY : Y ∈ F) :
      (Y.degree : ℝ) * A ^ Y.dimension ≤
        (2 : ℝ) ^ d * ((Y.degree : ℝ) * (D : ℝ) ^ Y.dimension) := by
    obtain ⟨hYi, hdim⟩ := hF Y hY
    have hdegreeCone : 1 ≤ Y.affineCone.degree :=
      AffineVariety.one_le_degree _ hYi.ne_top
    have hdegreeQ : 1 ≤ Y.degree := by
      rw [← ProjectiveVariety.degree_cone Y]
      exact hdegreeCone
    have hdegree : 0 ≤ (Y.degree : ℝ) := by
      have hdegreeQ0 : (0 : ℚ) ≤ Y.degree := le_trans (by norm_num) hdegreeQ
      exact_mod_cast hdegreeQ0
    have hpow : A ^ Y.dimension ≤ (2 : ℝ) ^ d * (D : ℝ) ^ Y.dimension := by
      calc
        A ^ Y.dimension ≤ (2 * (D : ℝ)) ^ Y.dimension :=
          pow_le_pow_left₀ (by linarith [hA]) hAD _
        _ = (2 : ℝ) ^ Y.dimension * (D : ℝ) ^ Y.dimension := by rw [mul_pow]
        _ ≤ (2 : ℝ) ^ d * (D : ℝ) ^ Y.dimension := by
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hdim)
            (by positivity)
    calc
      (Y.degree : ℝ) * A ^ Y.dimension ≤
          (Y.degree : ℝ) * ((2 : ℝ) ^ d * (D : ℝ) ^ Y.dimension) :=
        mul_le_mul_of_nonneg_left hpow hdegree
      _ = (2 : ℝ) ^ d * ((Y.degree : ℝ) * (D : ℝ) ^ Y.dimension) := by ring
  have hsum :
      (∑ Y ∈ F, (Y.degree : ℝ) * A ^ Y.dimension) ≤
        (2 : ℝ) ^ d * ∑ Y ∈ F, (Y.degree : ℝ) * (D : ℝ) ^ Y.dimension := by
    calc
      (∑ Y ∈ F, (Y.degree : ℝ) * A ^ Y.dimension) ≤
          ∑ Y ∈ F, (2 : ℝ) ^ d * ((Y.degree : ℝ) * (D : ℝ) ^ Y.dimension) := by
        apply Finset.sum_le_sum
        intro Y hY
        exact hterm Y hY
      _ = (2 : ℝ) ^ d * ∑ Y ∈ F, (Y.degree : ℝ) * (D : ℝ) ^ Y.dimension := by
        rw [Finset.mul_sum]
  have hcast :
      (TrackA.projectiveWeightedDegree F D : ℝ) =
        ∑ Y ∈ F, (Y.degree : ℝ) * (D : ℝ) ^ Y.dimension := by
    simp [TrackA.projectiveWeightedDegree]
  simpa only [hcast] using hsum

end
end DistinctDistances.Reduction
