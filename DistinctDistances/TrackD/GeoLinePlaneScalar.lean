import DistinctDistances.TrackD.GeoLinePlaneIncidence

/-! Absorption of the two linear terms in the paraboloid incidence estimate. -/

namespace DistinctDistances.TrackD.GeoLinePlane
noncomputable section

theorem rpow_two_thirds_cube (x : ℝ) (hx : 0 ≤ x) :
    (x ^ ((2 : ℝ)/3)) ^ 3 = x ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem absorb (b h M c : ℝ) (hb0 : 0 ≤ b) (hh0 : 0 ≤ h) (hM : 1 ≤ M)
    (hc : 1 ≤ c) (hb : b ≤ 2*M) (hh : h ≤ 2*M^2)
    (hi : b*h ≤ c * ((b*h*M)^((2 : ℝ)/3)+h+b*M)) :
    b*h ≤ (8*c+8*c^3)*M^2 := by
  have hM0 : 0 ≤ M := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hpow : 0 ≤ c^3 := by positivity
  by_cases hbsmall : b ≤ 4*c
  · calc
      b*h ≤ (4*c)*(2*M^2) := by gcongr
      _ ≤ (8*c+8*c^3)*M^2 := by nlinarith [mul_nonneg hpow (sq_nonneg M)]
  by_cases hhsmall : h ≤ 4*c*M
  · calc
      b*h ≤ (2*M)*(4*c*M) := by gcongr
      _ ≤ (8*c+8*c^3)*M^2 := by nlinarith [mul_nonneg hpow (sq_nonneg M)]
  have hx : 0 < b*h := mul_pos (by linarith) (by nlinarith)
  have hbterm : c*h ≤ b*h/4 := by nlinarith [mul_nonneg (show 0 ≤ b-4*c by linarith) hh0]
  have hhterm : c*b*M ≤ b*h/4 := by
    nlinarith [mul_nonneg hb0 (show 0 ≤ h-4*c*M by linarith)]
  have hmain : b*h ≤ 2*c*(b*h*M)^((2 : ℝ)/3) := by linarith
  have hcube := pow_le_pow_left₀ (mul_nonneg hb0 hh0) hmain 3
  simp only [mul_pow] at hcube
  rw [rpow_two_thirds_cube (b*h*M) (by positivity)] at hcube
  have hcub : (b*h)^2*(b*h) ≤ (b*h)^2*(8*c^3*M^2) := by nlinarith only [hcube]
  have hfin : b*h ≤ 8*c^3*M^2 := (mul_le_mul_iff_right₀ (sq_pos_of_pos hx)).mp
    (by simpa only [mul_comm] using hcub)
  nlinarith [mul_nonneg hc0 (sq_nonneg M)]

theorem lineplane (d : ℕ) (hST : STIncidence 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset (Pt d)) (ℓ H : AffineSubspace ℝ (Pt d)),
      IsRealLine ℓ → IsRealPlane H → ℓ ≤ H →
        (occ P ℓ : ℝ)*occ P H ≤ C * cfgM P^2 := by
  obtain ⟨C, hC, hST⟩ := hST
  let c := max (2*C) 1
  have hc : 1 ≤ c := le_max_right _ _
  refine ⟨8*c+8*c^3, by positivity, ?_⟩
  intro P ℓ H hℓ hH hℓH
  have hi := occupancy_incidence C hC hST P ℓ H hℓ hH hℓH
  have hM : 1 ≤ cfgM P := by
    unfold cfgM
    have := Nat.cast_nonneg (α := ℝ) (distinctDistances P)
    linarith
  apply absorb _ _ _ c (Nat.cast_nonneg _) (Nat.cast_nonneg _) hM hc
    (line_card P ℓ hℓ) (plane_card P H hH)
  exact hi.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

end
end DistinctDistances.TrackD.GeoLinePlane
