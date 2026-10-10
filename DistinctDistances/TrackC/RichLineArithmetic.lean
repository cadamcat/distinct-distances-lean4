import DistinctDistances.TrackC.Basic

namespace DistinctDistances.TrackC

/-- The three terms of the high-richness line budget. -/
noncomputable def richLineBudget (L B k : ℝ) : ℝ := L^((3:ℝ)/2)/k^2+L*B/k^3+L/k

theorem richLineBudget_nonneg (L B k : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B) (hk : 0 ≤ k) :
    0 ≤ richLineBudget L B k := by unfold richLineBudget;positivity

/-- The sparse supporting subfamily gives an ample contraction even with k halved. -/
theorem richLineBudget_sparse (L L' B k k' : ℝ) (hL : 0 ≤ L) (hL' : 0 ≤ L')
    (hsmall : L' ≤ L/100) (hB : 0 ≤ B) (hk : 0 < k) (hk' : k/2 ≤ k') :
    richLineBudget L' B k' ≤ richLineBudget L B k/4 := by
  have hkpos : 0 < k' := lt_of_lt_of_le (by positivity) hk'
  have hLpow : L'^((3:ℝ)/2) ≤ L^((3:ℝ)/2)/100 := by
    calc
      _ ≤ (L/100)^((3:ℝ)/2) := Real.rpow_le_rpow hL' hsmall (by norm_num)
      _ = L^((3:ℝ)/2)/(100:ℝ)^((3:ℝ)/2) := Real.div_rpow hL (by norm_num) _
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
        exact Real.self_le_rpow_of_one_le (by norm_num) (by norm_num)
  have h₁ : L'^((3:ℝ)/2)/k'^2 ≤ (L^((3:ℝ)/2)/k^2)/25 := by
    calc
      _ ≤ (L^((3:ℝ)/2)/100)/(k/2)^2 := by gcongr
      _ = _ := by field_simp;ring
  have h₂ : L'*B/k'^3 ≤ (2/25:ℝ)*(L*B/k^3) := by
    calc
      _ ≤ (L/100)*B/(k/2)^3 := by gcongr
      _ = _ := by field_simp;ring
  have h₃ : L'/k' ≤ (L/k)/50 := by
    calc
      _ ≤ (L/100)/(k/2) := by gcongr
      _ = _ := by field_simp;ring
  have hn₁ : 0 ≤ L^((3:ℝ)/2)/k^2 := by positivity
  have hn₂ : 0 ≤ L*B/k^3 := by positivity
  have hn₃ : 0 ≤ L/k := by positivity
  unfold richLineBudget
  linarith

theorem richLineBudget_double (L B k : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B) (hk : 0 < k) :
    richLineBudget L B (2*k) ≤ richLineBudget L B k/2 := by
  have h₁ : L^((3:ℝ)/2)/(2*k)^2 = (L^((3:ℝ)/2)/k^2)/4 := by field_simp;ring
  have h₂ : L*B/(2*k)^3 = (L*B/k^3)/8 := by field_simp;ring
  have h₃ : L/(2*k) = (L/k)/2 := by ring
  have hn₁ : 0 ≤ L^((3:ℝ)/2)/k^2 := by positivity
  have hn₂ : 0 ≤ L*B/k^3 := by positivity
  unfold richLineBudget
  rw [h₁,h₂,h₃]
  linarith

end DistinctDistances.TrackC
