import DistinctDistances.TrackD.Profiles.Defs

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

theorem dprofiles2_pieceGood_mono {d : ℕ} (P : Finset (Pt d)) (X : Piece d)
    {θ θ' ξ K : ℝ} (hθ : θ ≤ θ') (hs : 0 ≤ X.width)
    (hX : PieceGood P θ ξ K X) : PieceGood P θ' ξ K X := by
  have hB : 0 ≤ cfgB P := by
    dsimp [cfgB]
    positivity
  refine ⟨hX.subset, hX.width_dyadic, ?_, hX.mono, ?_, ?_, hX.vanish, hX.proper, ?_, ?_⟩
  · calc
      cfgN P * Real.exp (-θ' * X.width) ≤ cfgN P * Real.exp (-θ * X.width) := by
        apply mul_le_mul_of_nonneg_left _ (by dsimp [cfgN]; positivity)
        apply Real.exp_le_exp.mpr
        nlinarith
      _ ≤ X.pts.card := hX.size
  · intro i
    exact ⟨(hX.time_range i).1, le_trans (hX.time_range i).2 (by linarith)⟩
  · obtain ⟨i, hi⟩ := hX.imbalance
    exact ⟨i, le_trans (by nlinarith) hi⟩
  · intro i
    calc
      ((X.path.cut i).totalDegree : ℝ) ≤ testDeg (cfgB P) X.width (X.path.time i + θ) := hX.degree i
      _ ≤ testDeg (cfgB P) X.width (X.path.time i + θ') := by
        unfold testDeg
        apply mul_le_mul_of_nonneg_left _ hB
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (by linarith) hs
  · intro j hj b hb hT g hg
    have h := hX.noCapture j hj b hb hT g hg
    exact h.trans (mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg _))


end
end DistinctDistances.TrackD
