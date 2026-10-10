import DistinctDistances.TrackD.Profiles.Budget

/-! Capture margins and the recorded cut-scale product. The constant-time example
below refutes an unrestricted recorded-product bound; it does not refute a
regularity theorem whose admissible output plateaux may be empty. -/

namespace DistinctDistances.TrackD
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

theorem pieceGood_margin_mono (P : Finset (Pt d)) (X : Piece d)
    (θ η ξ K : ℝ) (hmargin : η ≤ ξ) (hX : PieceGood P θ η K X) :
    PieceGood P θ ξ K X := by
  refine { hX with noCapture := ?_ }
  intro j hj b hb hT g hg
  apply hX.noCapture j hj b (fun i => ?_) hT g hg
  obtain ⟨hbefore, hafter⟩ := hb i
  constructor
  · intro hi
    have h := hbefore hi
    linarith
  · intro hi
    have h := hafter hi
    linarith

theorem poolGood_margin_mono (P : Finset (Pt d)) (pl : Finset (Piece d))
    (θ η ξ K ρ s : ℝ) (t : Fin d → ℝ) (hmargin : η ≤ ξ)
    (hpl : PoolGood P θ η K ρ pl s t) : PoolGood P θ ξ K ρ pl s t := by
  refine { hpl with pieces := ?_ }
  intro X hX
  exact pieceGood_margin_mono P X θ η ξ K hmargin (hpl.pieces X hX)

/-- At capture margin 2, paths recorded at time 1/2 have no admissible
testing degree on any plateau before the final cut, when width = log B. -/
theorem constant_times_no_admissible_capture (hd : 0 < d) (B : ℝ) (hB : 1 < B)
    (π : CutPath d) (htime : ∀ i, π.time i = 1 / 2) :
    ∀ j : ℕ, j < d → ∀ b : ℝ, OnPlateau π.time j 2 b →
      ¬ 1 ≤ testDeg B (Real.log B) b := by
  intro j hj b hb
  let i₀ : Fin d := ⟨0, hd⟩
  by_cases hj0 : j = 0
  · subst j
    have hafter := (hb i₀).2 (Nat.zero_le _)
    rw [htime i₀] at hafter
    have hlog : 0 < Real.log B := Real.log_pos hB
    have harg : Real.log B + b * Real.log B < 0 := by
      nlinarith [mul_pos (by linarith : 0 < -(1 + b)) hlog]
    have hT : testDeg B (Real.log B) b = Real.exp (Real.log B + b * Real.log B) := by
      rw [Real.exp_add, Real.exp_log (by linarith : 0 < B)]
      rfl
    rw [hT]
    exact not_le.mpr (Real.exp_lt_one_iff.mpr harg)
  · have hjpos : 0 < j := by omega
    have hbefore := (hb i₀).1 hjpos
    have hafter := (hb ⟨j, hj⟩).2 le_rfl
    rw [htime i₀] at hbefore
    rw [htime ⟨j, hj⟩] at hafter
    linarith

theorem constant_times_full_product (B s β : ℝ) (π : CutPath d)
    (htime : ∀ i, π.time i = β) :
    (∏ i, cutScale B s π.time i) = B ^ d * Real.exp ((d : ℝ) * β * s) := by
  simp only [cutScale, testDeg, htime, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.exp_nat_mul]
  congr 2
  ring

/-- The constant-time recorded product has a fixed exponential excess over B^d.
This is the exact scalar obstruction to the proposed arbitrary-margin budget. -/
theorem constant_times_product_excess (hd : 0 < d) (B ε : ℝ) (hB : 1 < B)
    (hε : ε < (d : ℝ) / 2) (π : CutPath d) (htime : ∀ i, π.time i = 1 / 2) :
    B ^ d * Real.exp (ε * Real.log B) <
      ∏ i, cutScale B (Real.log B) π.time i := by
  rw [constant_times_full_product B (Real.log B) (1 / 2) π htime]
  apply mul_lt_mul_of_pos_left _ (pow_pos (by linarith : 0 < B) d)
  apply Real.exp_lt_exp.mpr
  have hlog := Real.log_pos hB
  nlinarith [mul_pos (sub_pos.mpr hε) hlog]

end
end DistinctDistances.TrackD
