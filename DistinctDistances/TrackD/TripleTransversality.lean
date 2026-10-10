import DistinctDistances.TrackD.GenericTangent
import DistinctDistances.TrackD.GeoTangent
import DistinctDistances.TrackD.PairGenericity

/-! The non-tangency claim at `secants.tex:442–447`.
At a general smooth point of a curve its tangent flat is a line. A curve
contained in no line therefore has general chords transverse at both ends. -/

namespace DistinctDistances.TrackD

open scoped Classical
noncomputable section
variable {d : ℕ}

theorem curve_generic_nontangency (X Y : AffineVariety d)
    (hX : IsCurve X) (hY : IsCurve Y)
    (hproperX : ∀ L : AffineSubspace ℂ (Point d), Module.finrank ℂ L.direction = 1 →
      ¬ X.points ⊆ L)
    (hproperY : ∀ L : AffineSubspace ℂ (Point d), Module.finrank ℂ L.direction = 1 →
      ¬ Y.points ⊆ L) :
    ForGeneralPair X Y (fun x y =>
      y - x ∉ X.tangentSpace x ∧ y - x ∉ Y.tangentSpace y) := by
  obtain ⟨x, hx, hdimX⟩ := (general_tangent_finrank X hX.1).exists
  obtain ⟨y, hy, hdimY⟩ := (general_tangent_finrank Y hY.1).exists
  have hsource : ForGeneralPair X Y (fun x y => y - x ∉ X.tangentSpace x) := by
    rcases GeoTangent.perW_source X x hx Y with h | h
    · exact h
    · exfalso
      apply hproperY (AffineSubspace.mk' x (X.tangentSpace x)) ?_ h
      rw [AffineSubspace.direction_mk', hdimX, hX.2]
  have htarget : ForGeneralPair X Y (fun x y => y - x ∉ Y.tangentSpace y) := by
    rcases GeoTangent.perW Y y hy X with h | h
    · exact h
    · exfalso
      apply hproperX (AffineSubspace.mk' y (Y.tangentSpace y)) ?_ h
      rw [AffineSubspace.direction_mk', hdimY, hY.2]
  exact hsource.and hX.1 hY.1 htarget

end
end DistinctDistances.TrackD
