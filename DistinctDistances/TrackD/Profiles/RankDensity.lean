import DistinctDistances.TrackD.Profiles.RankStart

namespace DistinctDistances.TrackD.RankCore

noncomputable section

def density (α : ℝ) (d j : ℕ) : ℝ := α / (2*(d+1 : ℝ))^(d-j)

theorem density_pos {α : ℝ} (hα : 0 < α) (d j : ℕ) : 0 < density α d j := by
  unfold density
  positivity

theorem density_mono {α : ℝ} (hα : 0 ≤ α) (d : ℕ) {r j : ℕ} (hrj : r ≤ j) :
    density α d r ≤ density α d j := by
  apply div_le_div_of_nonneg_left hα (by positivity)
  apply pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) d; nlinarith : (1 : ℝ) ≤ 2*(d+1))
  omega

theorem density_le_initial {α : ℝ} (hα : 0 ≤ α) (d j : ℕ) : density α d j ≤ α := by
  unfold density
  exact div_le_self hα (one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; nlinarith))

theorem density_preceding {α : ℝ} (hα : 0 ≤ α) (d : ℕ) {r j : ℕ}
    (hrj : r < j) (hj : j ≤ d) :
    density α d r ≤ density α d j / (2*(d+1 : ℝ)) := by
  have hexp : d-j+1 ≤ d-r := by omega
  have hp : (2*(d+1 : ℝ))^(d-j+1) ≤ (2*(d+1))^(d-r) :=
    pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) d; nlinarith) hexp
  calc
    density α d r ≤ α / (2*(d+1 : ℝ))^(d-j+1) :=
      div_le_div_of_nonneg_left hα (by positivity) hp
    _ = density α d j / (2*(d+1 : ℝ)) := by
      unfold density
      rw [pow_succ, div_mul_eq_div_div]

theorem selected_density {α n card card' : ℝ} (hα : 0 < α) (hn : 0 < n)
    (d j r : ℕ) (hj : j ≤ d) (hrj : r < j)
    (hcard : density α d j * n ≤ card)
    (hselected : (card - (density α d 0 / 2)*n)/(d+1 : ℝ) ≤ card') :
    density α d r * n ≤ card' := by
  have hmin := density_mono hα.le d (Nat.zero_le j)
  have hden : (0 : ℝ) < d+1 := by positivity
  have hstep : density α d j / (2*(d+1 : ℝ)) * n ≤
      (card - (density α d 0 / 2)*n)/(d+1 : ℝ) := by
    apply (le_div_iff₀ hden).mpr
    have heq : (density α d j / (2*(d+1 : ℝ)) * n) * (d+1) =
        density α d j * n / 2 := by field_simp
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_right hmin hn.le]
  exact (mul_le_mul_of_nonneg_right (density_preceding hα.le d hrj hj) hn.le).trans
    (hstep.trans hselected)

end
end DistinctDistances.TrackD.RankCore
