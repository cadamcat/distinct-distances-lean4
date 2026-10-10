import DistinctDistances.TrackE.StrictRankInputs

/-! Numerical propagation of the literal direction target σT/A across
cut clusters, sparse-cones.tex:741–780. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- Multiplying sigma_cluster_growth by T/A raises the plateau growth
exponent by one and preserves the independent dκ cluster loss. -/
theorem direction_target_cluster_growth {B A s a z b κ : ℝ}
    (hB : 0 ≤ B) (hA : 0 < A) (hs : 0 ≤ s)
    (haz : a ≤ z) (hzb : z ≤ b) (hgap : z - a ≤ κ)
    (t : Fin d → ℝ) (j : ℕ) (hj : j ≤ d)
    (hz : TrackD.OnPlateau t j 0 z) (hb : TrackD.OnPlateau t j 0 b) :
    TrackD.sigma B s t b * TrackD.testDeg B s b / A ≤
      (TrackD.sigma B s t a * TrackD.testDeg B s a / A) *
        Real.exp ((((d - j : ℕ) : ℝ) + 1) * (b - a) * s + (d : ℝ) * κ * s) := by
  have hg := TrackD.RankCore.sigma_cluster_growth hB hs haz hzb hgap t j hj hz hb
  have hTa : 0 ≤ TrackD.testDeg B s a := mul_nonneg hB (Real.exp_nonneg _)
  have hTb : 0 ≤ TrackD.testDeg B s b := mul_nonneg hB (Real.exp_nonneg _)
  calc
    TrackD.sigma B s t b * TrackD.testDeg B s b / A ≤
        (TrackD.sigma B s t a *
          Real.exp ((((d - j : ℕ) : ℝ) * (b - a) + (d : ℝ) * κ) * s)) *
          TrackD.testDeg B s b / A :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hg hTb) hA.le
    _ = _ := by
      rw [TrackD.RankCore.testDeg_shift B s a b]
      rw [show ((((d - j : ℕ) : ℝ) + 1) * (b - a) * s + (d : ℝ) * κ * s) =
        ((((d - j : ℕ) : ℝ) * (b - a) + (d : ℝ) * κ) * s) + ((b - a) * s) by ring,
        Real.exp_add]
      ring

/-- Borrowing a previous strict rank bound loses only μ+dκ. The input
comparison acts on a genuine dense physical subrow with dimension h≥l+1. -/
theorem direction_target_propagate_step {B A s a z b κ m μ c R R' : ℝ}
    (hB : 0 < B) (hA : 0 < A) (hs : 0 ≤ s)
    (haz : a ≤ z) (hzb : z ≤ b) (hgap : z - a ≤ κ)
    (t : Fin d → ℝ) (j h : ℕ) (hj : j ≤ d) (hdim : d - j + 1 ≤ h)
    (hz : TrackD.OnPlateau t j 0 z) (hb : TrackD.OnPlateau t j 0 b)
    (hc : Real.exp (-μ * s) ≤ c)
    (hstart : (TrackD.sigma B s t a * TrackD.testDeg B s a / A) *
      Real.exp (m * s) ≤ R')
    (hcompare : c * R' * (TrackD.testDeg B s b / TrackD.testDeg B s a)^h ≤ R) :
    (TrackD.sigma B s t b * TrackD.testDeg B s b / A) *
      Real.exp ((m - μ - (d : ℝ) * κ) * s) ≤ R := by
  have htarget : 0 ≤ TrackD.sigma B s t a * TrackD.testDeg B s a / A :=
    div_nonneg (mul_nonneg (TrackD.RankCore.sigma_nonneg hB.le _ _ _)
      (TrackD.RankCore.testDeg_pos hB _ _).le) hA.le
  have hR' : 0 ≤ R' := (mul_nonneg htarget (Real.exp_nonneg _)).trans hstart
  have hg := direction_target_cluster_growth hB.le hA hs haz hzb hgap t j hj hz hb
  have hcmp := TrackD.RankCore.comparison_exp hB hc hR' h (by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hcompare)
  have hdim' : ((d - j : ℕ) : ℝ) + 1 ≤ (h : ℝ) := by exact_mod_cast hdim
  have hab : 0 ≤ b - a := sub_nonneg.mpr (haz.trans hzb)
  calc
    (TrackD.sigma B s t b * TrackD.testDeg B s b / A) *
        Real.exp ((m - μ - (d : ℝ) * κ) * s) ≤
      ((TrackD.sigma B s t a * TrackD.testDeg B s a / A) *
        Real.exp ((((d - j : ℕ) : ℝ) + 1) * (b - a) * s + (d : ℝ) * κ * s)) *
          Real.exp ((m - μ - (d : ℝ) * κ) * s) :=
      mul_le_mul_of_nonneg_right hg (Real.exp_nonneg _)
    _ = ((TrackD.sigma B s t a * TrackD.testDeg B s a / A) * Real.exp (m * s)) *
        Real.exp (((((d - j : ℕ) : ℝ) + 1) * (b - a) - μ) * s) := by
      simp only [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ R' * Real.exp (((((d - j : ℕ) : ℝ) + 1) * (b - a) - μ) * s) :=
      mul_le_mul_of_nonneg_right hstart (Real.exp_nonneg _)
    _ ≤ R' * Real.exp (((h : ℝ) * (b - a) - μ) * s) := by
      apply mul_le_mul_of_nonneg_left _ hR'
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right
        (sub_le_sub_right (mul_le_mul_of_nonneg_right hdim' hab) μ) hs
    _ ≤ R := hcmp

end
end DistinctDistances.SparseCones
