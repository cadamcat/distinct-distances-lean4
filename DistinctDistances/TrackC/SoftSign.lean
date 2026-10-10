import DistinctDistances.TrackC.Basic

open Filter
open scoped Topology

namespace DistinctDistances.TrackC

/-- A bounded continuous odd approximation to strict signs. -/
noncomputable def softSign (t : ℝ) : ℝ := t / (1 + |t|)

@[simp] theorem softSign_neg (t : ℝ) : softSign (-t) = -softSign t := by
  simp [softSign, neg_div]

theorem softSign_continuous : Continuous softSign := by
  change Continuous (fun t : ℝ => t / (1 + |t|))
  apply continuous_id.div (continuous_const.add continuous_abs)
  intro t
  change 1 + |t| ≠ 0
  exact ne_of_gt (by linarith [abs_nonneg t])

theorem softSign_le_one (t : ℝ) : softSign t ≤ 1 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1 + |t|)).mpr
  linarith [le_abs_self t]

theorem neg_one_le_softSign (t : ℝ) : -1 ≤ softSign t := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + |t|)).mpr
  linarith [neg_abs_le t]

theorem softSign_pos_formula (t : ℝ) (ht : 0 ≤ t) :
    softSign t = 1 - (1 + t)⁻¹ := by
  rw [softSign, abs_of_nonneg ht]
  field_simp
  ring

theorem tendsto_softSign_atTop : Tendsto softSign atTop (𝓝 (1 : ℝ)) := by
  have hAdd : Tendsto (fun t : ℝ => 1 + t) atTop atTop :=
    tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
  have hInv : Tendsto (fun t : ℝ => (1 + t)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hAdd
  have h : Tendsto (fun t : ℝ => 1 - (1 + t)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub hInv)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (softSign_pos_formula t ht).symm

end DistinctDistances.TrackC
