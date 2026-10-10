import DistinctDistances.TrackD.TripleDefs
import DistinctDistances.TrackD.TripleCore
import DistinctDistances.TrackA.Projection

/-! Projection-degree and repetition bookkeeping for `secants.tex:464–482`.
The singular-centre comparison is the frozen track-A radial projection formula. -/

namespace DistinctDistances.TrackD

open scoped Classical
noncomputable section

theorem radialMapDegree_pos_has_degree {d : ℕ} (p : Point d) (Y : AffineVariety d)
    (ht : 0 < radialMapDegree p Y) :
    GenericallyFiniteRadialDegree p Y (radialMapDegree p Y) := by
  by_cases h : ∃ r, GenericallyFiniteRadialDegree p Y r
  · simpa only [radialMapDegree, dif_pos h] using Nat.find_spec h
  · have hz : radialMapDegree p Y = 0 := by simp only [radialMapDegree, dif_neg h]
    omega

theorem curveTripleValid_mapDegree_pos (p : Point 3) (Y₁ Y₂ Y₃ Y : AffineVariety 3)
    (hvalid : CurveTripleValid p Y₁ Y₂ Y₃) (hY : Y ∈ ({Y₁, Y₂, Y₃} : Finset _)) :
    0 < radialMapDegree p Y := by
  have hc := hvalid.2.2.2.2.2 Y hY
  have hmem : Y = Y₁ ∨ Y = Y₂ ∨ Y = Y₃ := by simpa using hY
  rcases hmem with rfl | rfl | rfl
  all_goals
    simp only [ite_true, eq_self] at hc
    split_ifs at hc <;> omega

/-- Validity bounds the singular-centre multiplicity by half the source degree,
so the source degree is at most twice the map degree times the common image degree. -/
theorem curveTripleValid_projection_comparison
    (p : Point 3) (Y₁ Y₂ Y₃ Y : AffineVariety 3)
    (hvalid : CurveTripleValid p Y₁ Y₂ Y₃) (hY : Y ∈ ({Y₁, Y₂, Y₃} : Finset _))
    (hcurve : IsCurve Y) :
    (Y.degree : ℝ) / 2 ≤ (radialMapDegree p Y : ℝ) *
      ((radialImage p Y₁).degree : ℝ) := by
  have hv := hvalid
  obtain ⟨h12, h13, hdim, _, hmult, _⟩ := hv
  have hmem : Y = Y₁ ∨ Y = Y₂ ∨ Y = Y₃ := by simpa using hY
  have himage : radialImage p Y = radialImage p Y₁ := by
    rcases hmem with rfl | rfl | rfl
    · rfl
    · exact h12.symm
    · exact h13.symm
  have hdimY : (radialImage p Y).dimension = 1 := by rw [himage]; exact hdim
  have hproj := TrackA.poly_projection_radial Y hcurve.1 1 (by omega) hcurve.2 p
    hdimY (radialMapDegree p Y)
    (radialMapDegree_pos_has_degree p Y (curveTripleValid_mapDegree_pos p Y₁ Y₂ Y₃ Y hvalid hY))
  rw [himage] at hproj
  have hmultY := hmult Y hY
  have hbound : Y.degree / 2 ≤ (radialMapDegree p Y : ℚ) * (radialImage p Y₁).degree := by
    linarith
  exact_mod_cast hbound

/-- For either target index, removing the first index (when repeated) removes
at most half the original fibre. This is precisely the validity hypothesis. -/
theorem curveTripleValid_target_removal_bound
    (p : Point 3) (Y₁ Y₂ Y₃ Y : AffineVariety 3)
    (hvalid : CurveTripleValid p Y₁ Y₂ Y₃) (hY : Y ∈ ({Y₂, Y₃} : Finset _)) :
    2 * (if Y₁ = Y then 1 else 0 : ℕ) ≤ radialMapDegree p Y := by
  by_cases hs : Y₁ = Y
  · have hmem : Y = Y₂ ∨ Y = Y₃ := by simpa using hY
    have hYall : Y ∈ ({Y₁, Y₂, Y₃} : Finset _) := by simp [← hs]
    have hc := hvalid.2.2.2.2.2 Y hYall
    rw [if_pos hs]
    rcases hmem with rfl | rfl
    all_goals
      simp only [ite_true, eq_self] at hc
      split_ifs at hc <;> omega
  · simp [hs]

/-- Once distinct surviving preimages give branches of multiplicity at least
their residual count, the paper's `d/(4e)` lower bound follows. -/
theorem curveTripleValid_target_multiplicity_lower
    (p : Point 3) (Y₁ Y₂ Y₃ Y : AffineVariety 3)
    (hvalid : CurveTripleValid p Y₁ Y₂ Y₃) (hY : Y ∈ ({Y₂, Y₃} : Finset _))
    (hcurve : IsCurve Y) (μ : ℝ)
    (hbranches : ((radialMapDegree p Y - (if Y₁ = Y then 1 else 0) : ℕ) : ℝ) ≤ μ) :
    (Y.degree : ℝ) ≤ 4 * ((radialImage p Y₁).degree : ℝ) * μ := by
  have hYall : Y ∈ ({Y₁, Y₂, Y₃} : Finset _) := by
    have hmem : Y = Y₂ ∨ Y = Y₃ := by simpa using hY
    rcases hmem with rfl | rfl <;> simp
  have hdegree := hvalid.2.2.2.1
  apply residual_branch_degree_lower (Y.degree : ℝ) ((radialImage p Y₁).degree : ℝ) μ
    (radialMapDegree p Y) (if Y₁ = Y then 1 else 0)
  · exact_mod_cast (le_trans (by norm_num : (0 : ℚ) ≤ 2) hdegree)
  · exact curveTripleValid_target_removal_bound p Y₁ Y₂ Y₃ Y hvalid hY
  · exact curveTripleValid_projection_comparison p Y₁ Y₂ Y₃ Y hvalid hYall hcurve
  · exact hbranches

/-- In the coincident-target case the residual multiplicity is at least two,
including the triple in which all three original indices coincide. -/
theorem curveTripleValid_repeated_target_residual_ge_two
    (p : Point 3) (Y₁ Y₂ : AffineVariety 3) (hvalid : CurveTripleValid p Y₁ Y₂ Y₂) :
    2 ≤ radialMapDegree p Y₂ - (if Y₁ = Y₂ then 1 else 0) := by
  have hc := hvalid.2.2.2.2.2 Y₂ (by simp)
  simp only [ite_true, eq_self] at hc
  by_cases hs : Y₁ = Y₂
  · simp only [if_pos hs] at hc ⊢
    omega
  · simp only [if_neg hs] at hc ⊢
    omega

end
end DistinctDistances.TrackD
