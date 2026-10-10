import DistinctDistances.TrackD.TripleDegrees
import DistinctDistances.TrackD.TriplePlaneBudget

/-! The exact geometric data used by `secants.tex:433–485`.
This records actual radial images from one source point, with the residual
branches at the projected original centres. It introduces no new variety model. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

structure TripleProjectionData (Y₁ Y₂ Y₃ : AffineVariety 3) (Pc : Finset (Point 3)) where
  viewpoint : Point 3
  viewpoint_mem : viewpoint ∈ Y₁.points
  z : Point 3 → ProjectivePoint 3
  radial : ∀ p ∈ Pc, ∃ hp : p ≠ viewpoint, z p = radialProjection viewpoint p hp
  injective : Set.InjOn z (Pc : Set (Point 3))
  image₂_curve : (radialImage viewpoint Y₂).IsIrreducible ∧ (radialImage viewpoint Y₂).dimension = 1
  image₃_curve : (radialImage viewpoint Y₃).IsIrreducible ∧ (radialImage viewpoint Y₃).dimension = 1
  image₂_degree : (radialImage viewpoint Y₂).degree ≤ Y₂.degree
  image₃_degree : (radialImage viewpoint Y₃).degree ≤ Y₃.degree
  distinct : Y₂ ≠ Y₃ → radialImage viewpoint Y₂ ≠ radialImage viewpoint Y₃
  points : ∀ p ∈ Pc, z p ∈ (radialImage viewpoint Y₂).points ∧ z p ∈ (radialImage viewpoint Y₃).points
  branches₂ : ∀ p ∈ Pc,
    ((radialMapDegree p Y₂ - (if Y₁ = Y₂ then 1 else 0) : ℕ) : ℚ) ≤
      (radialImage viewpoint Y₂).multiplicity (z p)
  branches₃ : ∀ p ∈ Pc,
    ((radialMapDegree p Y₃ - (if Y₁ = Y₃ then 1 else 0) : ℕ) : ℚ) ≤
      (radialImage viewpoint Y₃).multiplicity (z p)

/-- The complete quantitative half of `geo:terminal.triple`, conditional on
the geometric generic-projection data. The constant 48 is universal; neither
the source curves nor the finite centre list enters its choice. -/
theorem terminal_triple_bound_of_projection_data
    (Y₁ Y₂ Y₃ : AffineVariety 3) (hY₂ : IsCurve Y₂) (hY₃ : IsCurve Y₃)
    (Pc : Finset (Point 3)) (hvalid : ∀ p ∈ Pc, CurveTripleValid p Y₁ Y₂ Y₃)
    (data : TripleProjectionData Y₁ Y₂ Y₃ Pc) :
    ∑ p ∈ Pc, (((radialImage p Y₁).degree : ℝ))⁻¹ ^ 2 ≤ 48 := by
  let C := radialImage data.viewpoint Y₂
  let D := radialImage data.viewpoint Y₃
  let e : Point 3 → ℝ := fun p => ((radialImage p Y₁).degree : ℝ)
  let μ : Point 3 → ℝ := fun p => (C.multiplicity (data.z p) : ℝ)
  let ν : Point 3 → ℝ := fun p => (D.multiplicity (data.z p) : ℝ)
  have hA : 0 < (Y₂.degree : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) (Y₂.one_le_degree hY₂.1.ne_top))
  have hB : 0 < (Y₃.degree : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) (Y₃.one_le_degree hY₃.1.ne_top))
  have he : ∀ p ∈ Pc, 0 < e p := by
    intro p hp
    have h := (hvalid p hp).2.2.2.1
    have hq : (0 : ℚ) < (radialImage p Y₁).degree := lt_of_lt_of_le (by norm_num) h
    dsimp [e]
    exact_mod_cast hq
  have hμ : ∀ p ∈ Pc, 0 ≤ μ p := by
    intro p hp
    have hq : (0 : ℚ) ≤ C.multiplicity (data.z p) :=
      (Nat.cast_nonneg _).trans (data.branches₂ p hp)
    dsimp [μ]
    exact_mod_cast hq
  have hν : ∀ p ∈ Pc, 0 ≤ ν p := by
    intro p hp
    have hq : (0 : ℚ) ≤ D.multiplicity (data.z p) :=
      (Nat.cast_nonneg _).trans (data.branches₃ p hp)
    dsimp [ν]
    exact_mod_cast hq
  have hbudget : ∑ p ∈ Pc, μ p * ν p ≤ 3 * (Y₂.degree : ℝ) * (Y₃.degree : ℝ) := by
    have hq : ∑ p ∈ Pc, C.multiplicity (data.z p) * D.multiplicity (data.z p) ≤
        3 * Y₂.degree * Y₃.degree := by
      by_cases hsame : Y₂ = Y₃
      · have hCD : C = D := congrArg (radialImage data.viewpoint) hsame
        have hbranches : ∀ p ∈ Pc, 2 ≤ C.multiplicity (data.z p) := by
          intro p hp
          have hv : CurveTripleValid p Y₁ Y₂ Y₂ := by simpa only [← hsame] using hvalid p hp
          have hr := curveTripleValid_repeated_target_residual_ge_two p Y₁ Y₂ hv
          have hrq : (2 : ℚ) ≤
              ((radialMapDegree p Y₂ - (if Y₁ = Y₂ then 1 else 0) : ℕ) : ℚ) := by exact_mod_cast hr
          exact hrq.trans (data.branches₂ p hp)
        have hpolar := projective_plane_polar_budget_pullback Pc data.z data.injective C
          data.image₂_curve.1 data.image₂_curve.2 hbranches
        have hC0 : 0 ≤ C.degree := (projective_irreducible_degree_pos C data.image₂_curve.1).le
        have hY0 : 0 ≤ Y₂.degree := le_trans (by norm_num) (Y₂.one_le_degree hY₂.1.ne_top)
        have hgap := mul_nonneg (sub_nonneg.mpr data.image₂_degree) (add_nonneg hY0 hC0)
        have hsq : C.degree ^ 2 ≤ Y₂.degree ^ 2 := by nlinarith
        calc
          ∑ p ∈ Pc, C.multiplicity (data.z p) * D.multiplicity (data.z p) =
              ∑ p ∈ Pc, C.multiplicity (data.z p) ^ 2 := by rw [← hCD]; simp only [sq]
          _ ≤ 2 * C.degree ^ 2 := hpolar
          _ ≤ 3 * Y₂.degree * Y₃.degree := by rw [← hsame]; nlinarith [sq_nonneg Y₂.degree]
      · have hprod := projective_plane_product_budget_pullback Pc data.z data.injective C D
          data.image₂_curve.1 data.image₃_curve.1 data.image₂_curve.2 data.image₃_curve.2
          (data.distinct hsame) data.points
        have hC0 : 0 ≤ C.degree := (projective_irreducible_degree_pos C data.image₂_curve.1).le
        have hD0 : 0 ≤ D.degree := (projective_irreducible_degree_pos D data.image₃_curve.1).le
        have hY0 : 0 ≤ Y₂.degree := le_trans (by norm_num) (Y₂.one_le_degree hY₂.1.ne_top)
        have hdegrees := mul_le_mul data.image₂_degree data.image₃_degree hD0 hY0
        apply hprod.trans
        nlinarith only [hdegrees]
    dsimp [μ, ν]
    exact_mod_cast hq
  have hsum := inverse_square_sum_of_multiplicity_budget Pc e μ ν
    (Y₂.degree : ℝ) (Y₃.degree : ℝ) 3 hA hB he hμ hν
    (by
      intro p hp
      apply curveTripleValid_target_multiplicity_lower p Y₁ Y₂ Y₃ Y₂ (hvalid p hp) (by simp) hY₂ (μ p)
      dsimp [μ, C]
      exact_mod_cast data.branches₂ p hp)
    (by
      intro p hp
      apply curveTripleValid_target_multiplicity_lower p Y₁ Y₂ Y₃ Y₃ (hvalid p hp) (by simp) hY₃ (ν p)
      dsimp [ν, D]
      exact_mod_cast data.branches₃ p hp) hbudget
  simpa only [e, show (16 : ℝ) * 3 = 48 by norm_num] using hsum

end
end DistinctDistances.TrackD
