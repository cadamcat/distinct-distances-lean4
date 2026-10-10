import DistinctDistances.TrackC.LineImages

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Count a finite family carrying substantial pooled line-match mass. -/
theorem line_weights_cardinality_bound (C D ν A k x : ℝ)
    (hC : 0 < C) (hD : 1 ≤ D) (hν : 0 < ν) (hA : 0 ≤ A) (hk : 0 < k) (hx : 0 < x)
    (hlarge : 4*A ≤ ν*k)
    (X Y : Finset (E 3)) (LX LY : Finset (Line 3)) (G : Finset (Motion 3))
    (w : Motion 3 → Line 3 → ℝ) (hX : cloudLineCap X (2*A)) (hY : cloudLineCap Y (2*A))
    (hLX : (LX.card:ℝ) ≤ D*x) (hLY : (LY.card:ℝ) ≤ D*x)
    (hw : ∀ g ∈ G,∀ l ∈ LX,0 ≤ w g l ∧ w g l ≤ (matchCount (pointsOn X l) Y g:ℝ) ∧
      (0 < w g l → ∃ l' ∈ LY,mapsLine g l l'))
    (hmass : ∀ g ∈ G,ν*k ≤ ∑ l ∈ LX,w g l)
    (hSum : (∑ g ∈ G,∑ ll ∈ LX.offDiag,w g ll.1*w g ll.2) ≤
      C*((2*A)^2*(LX.card:ℝ)^2*(LY.card:ℝ)^2+
        (2*A)^3*(LX.card:ℝ)^2*(LY.card:ℝ)^((3:ℝ)/2))) :
    (G.card:ℝ)*k^2 ≤ (16*C*D^4/ν^2)*(A^2*x^4+A^3*x^((7:ℝ)/2)) := by
  have hDpos : 0 < D := by linarith
  have hweight : ∀ g ∈ G,∀ l ∈ LX,0 ≤ w g l ∧ w g l ≤ 2*A := by
    intro g hg l hl
    refine ⟨(hw g hg l hl).1,(hw g hg l hl).2.1.trans ?_⟩
    have hc : (matchPoints (pointsOn X l) Y g).card ≤ (pointsOn X l).card := Finset.card_filter_le _ _
    exact (Nat.cast_le.mpr hc).trans (hX l)
  have hlower : (G.card:ℝ)*(ν^2*k^2/2) ≤ ∑ g ∈ G,∑ ll ∈ LX.offDiag,w g ll.1*w g ll.2 := by
    calc
      _ = ∑ _g ∈ G,ν^2*k^2/2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro g hg
        have hW := hmass g hg
        have hWpos : 0 ≤ ∑ l ∈ LX,w g l := Finset.sum_nonneg (fun l hl => (hweight g hg l hl).1)
        have hpair := distinct_line_pair_mass LX (w g) (2*A) (by positivity)
          (hweight g hg) (by nlinarith [hlarge,hW])
        have hsquare := (sq_le_sq₀ (by positivity : 0 ≤ ν*k) hWpos).mpr hW
        nlinarith
  have hfirst : (2*A)^2*(LX.card:ℝ)^2*(LY.card:ℝ)^2 ≤ 4*A^2*D^4*x^4 := by
    calc
      _ ≤ (2*A)^2*(D*x)^2*(D*x)^2 := by gcongr
      _ = _ := by ring
  have hsecond : (2*A)^3*(LX.card:ℝ)^2*(LY.card:ℝ)^((3:ℝ)/2) ≤ 8*A^3*D^4*x^((7:ℝ)/2) := by
    have hDpow : D^((7:ℝ)/2) ≤ D^4 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hD (by norm_num : (7:ℝ)/2 ≤ 4)
    calc
      _ ≤ (2*A)^3*(D*x)^2*(D*x)^((3:ℝ)/2) := by gcongr
      _ = 8*A^3*(D*x)^((7:ℝ)/2) := by
        have hpow : (D*x)^2*(D*x)^((3:ℝ)/2) = (D*x)^((7:ℝ)/2) := by
          rw [← Real.rpow_natCast,← Real.rpow_add (mul_pos hDpos hx)]
          congr 1 <;> norm_num
        rw [mul_assoc,hpow]
        ring
      _ = 8*A^3*D^((7:ℝ)/2)*x^((7:ℝ)/2) := by rw [Real.mul_rpow hDpos.le hx.le];ring
      _ ≤ _ := by gcongr
  have hbudget : (∑ g ∈ G,∑ ll ∈ LX.offDiag,w g ll.1*w g ll.2) ≤
      8*C*D^4*(A^2*x^4+A^3*x^((7:ℝ)/2)) := by
    apply hSum.trans
    have hc := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hC.le
    calc
      _ ≤ C*(4*A^2*D^4*x^4+8*A^3*D^4*x^((7:ℝ)/2)) := hc
      _ ≤ _ := by nlinarith [mul_nonneg (by positivity : 0 ≤ C*D^4) (by positivity : 0 ≤ A^2*x^4)]
  have hlow : (G.card:ℝ)*ν^2*k^2 ≤ 16*C*D^4*(A^2*x^4+A^3*x^((7:ℝ)/2)) := by linarith
  have heq : (16*C*D^4/ν^2)*(A^2*x^4+A^3*x^((7:ℝ)/2)) =
      (16*C*D^4*(A^2*x^4+A^3*x^((7:ℝ)/2)))/ν^2 := by ring
  rw [heq]
  apply (le_div_iff₀ (by positivity : (0:ℝ) < ν^2)).mpr
  convert hlow using 1 <;> ring

end DistinctDistances.TrackC
