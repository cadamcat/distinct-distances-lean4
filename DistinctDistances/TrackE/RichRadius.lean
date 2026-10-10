import DistinctDistances.TrackE.RadiusEnergy
import DistinctDistances.TrackE.RadiusClass
import DistinctDistances.TrackE.RadiusRepresentatives
import DistinctDistances.TrackE.DirectionalGeometry

/-! The assembled rich-span branch of `red:directions.count` (`reduction.tex:151–192`). -/

namespace DistinctDistances

noncomputable section

namespace Reduction

variable {d : ℕ}

open Classical in
/-- For counted span dimension at least four, the previous-dimensional direction bounds
give the next bound. The small ratio is uniform over every variety, star and inductive constant.
Inputs from A and OAI remain explicit in the dependency closure. -/
theorem exists_rich_span_direction_bound (hd : 3 ≤ d) (hIH : IH d)
    (hsections : Request.DirectionHyperplaneSections d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (P : Finset (RPoint d)) (p : RPoint d), p ∈ P →
      Mcount P ≤ ε * Ascale d P.card → ∀ (T : Finset (RPoint d)), T ⊆ P →
      4 ≤ Module.finrank ℝ (Submodule.span ℝ
        ((fun q => q - p) '' (T : Set (RPoint d)))) →
      ∀ (Y : ProjectiveVariety d), Y.IsIrreducible → 1 ≤ Y.dimension →
        0 ≤ (Y.degree : ℝ) → (∀ q ∈ T, DirMem Y p q) → ∀ (C : ℝ), 0 ≤ C →
      (∀ V : ProjectiveVariety d, V.IsIrreducible → V.dimension + 1 = Y.dimension →
        ((T.filter fun q => DirMem V p q).card : ℝ) ≤
          C * (V.degree : ℝ) * Ascale d P.card ^ (Y.dimension - 1)) →
      (T.card : ℝ) ≤ 2 * C * (Y.degree : ℝ) * Ascale d P.card ^ Y.dimension := by
  classical
  obtain ⟨εr, hεr, hradius⟩ := exists_rich_radius_of_small_ratio hd hIH
  refine ⟨min 1 εr, lt_min (by norm_num) hεr, ?_⟩
  intro P p hp hMP T hTP hspan Y hY ha hdegree hdir C hC hcap
  let U := Submodule.span ℝ ((fun q => q - p) '' (T : Set (RPoint d)))
  have hA : 0 ≤ Ascale d P.card := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hM : 0 < Mcount P := by dsimp [Mcount]; positivity
  have hMA : Mcount P ≤ Ascale d P.card := hMP.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_left 1 εr) hA)
  have hMr : Mcount P ≤ εr * Ascale d P.card :=
    hMP.trans (mul_le_mul_of_nonneg_right (min_le_right 1 εr) hA)
  obtain ⟨r, _, hlarge⟩ := hradius P p hp hMr U hspan
  obtain ⟨Z, hZ, hcard, hproj⟩ := exists_radius_representatives P p U r
  have hlargeZ : 2 * Mcount P ≤ (Z.card : ℝ) := by
    rw [hcard]
    exact hlarge
  have hZP : Z ⊆ P := hZ.trans (Finset.filter_subset _ _)
  have hZne : Z.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < Z.card := lt_of_lt_of_le (by positivity) hlargeZ
    exact_mod_cast hpos
  apply direction_count_of_rich_radius_sections p T Z Y (Ascale d P.card) (Mcount P) C
    hA hM hMA hC hdegree ha hdir hZne
  · intro z hz z' hz'
    exact (Finset.mem_filter.mp (hZ hz)).2.trans (Finset.mem_filter.mp (hZ hz')).2.symm
  · exact hproj
  · intro q hq
    simpa only [pointDistancePairs, dist_comm] using
      pointDistancePairs_lower_bound P Z q hZP (hTP hq) hlargeZ
  · intro n hn
    obtain ⟨F, hF, hdegreeF, hcover⟩ := hsections Y hY ha n hn
    exact ⟨F, hF, hdegreeF, fun q hq hinner => hcover p q (hdir q hq) hinner⟩
  · exact hcap

end Reduction

end

end DistinctDistances
