import DistinctDistances.TrackD.Profiles.PartitionWindowAdvance
import DistinctDistances.TrackA.Intersections

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- The sample scale satisfies A=B^2, including the zero-cardinality case. -/
theorem partition_cfgA_eq_sq (P : Finset (Pt d)) : cfgA P = cfgB P ^ 2 := by
  unfold cfgA cfgB
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg P.card)]
  congr 1
  ring

/-- `profiles.tex:85–90`: the physical separator equations provide the
outer entry; every low test there has degree below one and captures nothing. -/
theorem partition_initial_entry (P : Finset (Pt d)) (π : CutPath d) (θ ξ K : ℝ)
    (hθ : 0 < θ) (hK : 1 ≤ K) (hB : 1 < cfgB P)
    (hM : cfgM P ≤ (1 / 3) * cfgA P)
    (hmult : Real.log K < ξ / 4 * Real.log (cfgB P)) :
    Nonempty (PartitionWindowEntry P P θ ξ K (Real.log (cfgB P)) π) := by
  classical
  obtain ⟨E, hdegree, hisolate⟩ := TrackA.poly_separators_isolation P
  have hBpos : 0 < cfgB P := by linarith
  have hlog : 0 ≤ Real.log (cfgB P) := (Real.log_pos hB).le
  refine ⟨⟨Finset.Subset.refl _, (E : Set (Poly d)), ?_, ?_, ?_⟩⟩
  · intro f hf
    have hMone : 1 ≤ cfgM P := by
      unfold cfgM
      have h : (0 : ℝ) ≤ (distinctDistances P : ℝ) := Nat.cast_nonneg _
      linarith
    have hdegreeR : (f.totalDegree : ℝ) ≤ 2 * cfgM P + 1 := by
      have h := hdegree f hf
      have h' : (f.totalDegree : ℝ) ≤
          2 * (1 + ((OAI.ErdosDistinctDistances.distances P).card : ℝ)) + 1 := by
        exact_mod_cast h
      simpa [cfgM, distinctDistances, distanceSet, OAI.ErdosDistinctDistances.distances,
        add_comm] using h'
    have hdegreeA : (f.totalDegree : ℝ) ≤ cfgA P := by nlinarith
    have hscale : cfgA P = testDeg (cfgB P) (Real.log (cfgB P)) 1 := by
      rw [partition_cfgA_eq_sq]
      unfold testDeg
      rw [one_mul, Real.exp_log hBpos]
      ring
    rw [hscale] at hdegreeA
    exact hdegreeA.trans (RankCore.testDeg_mono hBpos.le hlog (by linarith))
  · exact hisolate
  · intro b hb g hg
    rw [partition_outer_low_capture π P (cfgB P) ξ K hB hK hmult b hb g hg]
    simp only [Finset.card_empty, Nat.cast_zero]
    unfold cfgN
    positivity

end
end DistinctDistances.TrackD
