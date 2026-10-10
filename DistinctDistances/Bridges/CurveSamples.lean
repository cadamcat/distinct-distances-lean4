import DistinctDistances.TrackD.Basic
import DistinctDistances.TrackA.Intersections

/-! The pure-variety sample bound specialized to track D's irreducible curves. -/

namespace DistinctDistances.Bridges

open scoped Classical
noncomputable section

theorem irreducible_isPure {n : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible) :
    V.IsPure V.dimension := by
  letI : V.ideal.IsPrime := hV
  intro W
  have hW : W.val = V.ideal := by
    simpa only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] using W.property
  have he : W.variety = V := AffineVariety.ext hW
  rw [he]

theorem curve_sample_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset (TrackD.Pt d)) (Y : AffineVariety d),
      TrackD.IsCurve Y →
      (TrackD.massOn P Y.points : ℝ) ≤ C * (Y.degree : ℝ) * TrackD.cfgM P := by
  obtain ⟨C, hC, hbound⟩ := TrackA.poly_separators_sample_bound d
  refine ⟨(C : ℝ), by exact_mod_cast hC, ?_⟩
  intro P Y hY
  have hpure : Y.IsPure 1 := by
    simpa only [hY.2] using irreducible_isPure Y hY.1
  have h := hbound P Y 1 hpure
  have hq :
      ((P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ Y)).card : ℚ) ≤
        C * Y.degree * (1 + ((OAI.ErdosDistinctDistances.distances P).card : ℚ)) := by
    simpa only [pow_one] using h
  have hr :
      ((P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ Y)).card : ℝ) ≤
        (C : ℝ) * (Y.degree : ℝ) *
          (1 + ((OAI.ErdosDistinctDistances.distances P).card : ℝ)) := by
    exact_mod_cast hq
  change ((P.filter (fun p => OAI.ErdosDistinctDistances.complexPoint p ∈ Y)).card : ℝ) ≤
    (C : ℝ) * (Y.degree : ℝ) * ((distinctDistances P : ℝ) + 1)
  simpa only [distinctDistances, distanceSet, OAI.ErdosDistinctDistances.distances, add_comm]
    using hr

end
end DistinctDistances.Bridges
