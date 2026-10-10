import DistinctDistances.Bridges.CurveSamples
import DistinctDistances.TrackA.Intersections

/-! An infinite irreducible subvariety of an irreducible curve is the whole curve. -/

namespace DistinctDistances.Bridges

noncomputable section

theorem curve_eq_of_infinite_subvariety {n : ℕ} (V W : AffineVariety n)
    (hV : V.IsIrreducible) (hdim : V.dimension = 1) (hW : W.IsIrreducible)
    (hVW : V.ideal ≤ W.ideal) (hinfinite : W.points.Infinite) : V = W := by
  classical
  apply AffineVariety.ext
  by_contra hne
  obtain ⟨f, hfW, hfV⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hVW hne)
  let : W.ideal.IsPrime := hW
  obtain ⟨P, hP, hPW⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hVW (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfW)))
  let Y : AffineVariety n := ⟨P, hP.isPrime.isRadical⟩
  have hY : Y.IsIrreducible := hP.isPrime
  have hYdim : Y.dimension = 0 := TrackA.fa_bezout_proper_dimension V Y hV f hfV hP 0 hdim
  have hpure : Y.IsPure 0 := by
    simpa only [hYdim] using irreducible_isPure Y hY
  have hfinite := (TrackA.fa_bezout_zero_dimensional Y hpure).1
  have hsubset : W.points ⊆ Y.points := MvPolynomial.zeroLocus_anti_mono hPW
  exact hinfinite (hfinite.subset hsubset)

end
end DistinctDistances.Bridges
