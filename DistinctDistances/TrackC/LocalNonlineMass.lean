import DistinctDistances.TrackC.MotionLocal
import DistinctDistances.TrackC.DyadicLocalMass
import DistinctDistances.TrackC.FiniteIncidence

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Local non-line match mass, summed across all dyadic richness buckets. -/
theorem local_nonline_mass_sum (X Y : Finset (E 3)) (G : Finset (Motion 3))
    (η K m b : ℝ) (hK : 0 ≤ K) (hm : 0 ≤ m) (hb : 0 < b)
    (hCount : ∀ ℓ : ℝ,b ≤ ℓ →
      FiniteCardBound {g : Motion 3 | g ∈ motionBucket X Y ℓ ∧ nonLineType η ℓ X Y g}
        (K*m^3/ℓ^((3:ℝ)/2))) :
    (∑ g ∈ G,if b ≤ (matchCount X Y g:ℝ) ∧
      nonLineType η (b*(2:ℝ)^(dyadicLocalLevel b (matchCount X Y g) hb)) X Y g
      then (matchCount X Y g:ℝ) else 0) ≤
      2*K*m^3/(Real.sqrt b*(1-(2:ℝ)^((-1:ℝ)/2))) := by
  have h := dyadic_local_mass_bound G (fun g => (matchCount X Y g:ℝ))
    (fun g j => nonLineType η (b*(2:ℝ)^j) X Y g) b (K*m^3) hb (by positivity) ?_
  · convert h using 1 <;> ring
  · intro j
    let ℓ := b*(2:ℝ)^j
    have hℓ : b ≤ ℓ := le_mul_of_one_le_right hb.le (one_le_pow₀ (by norm_num))
    have hc := hCount ℓ hℓ
    let A := G.filter (fun g => ℓ ≤ (matchCount X Y g:ℝ) ∧ (matchCount X Y g:ℝ) < 2*ℓ ∧ nonLineType η ℓ X Y g)
    have hsub : (A:Set (Motion 3)) ⊆ {g : Motion 3 | g ∈ motionBucket X Y ℓ ∧ nonLineType η ℓ X Y g} := by
      intro g hg
      obtain ⟨hgG,hlo,hhi,hη⟩ := Finset.mem_filter.mp hg
      exact ⟨⟨hlo,hhi⟩,hη⟩
    exact (Nat.cast_le.mpr (finset_card_le_ncard A _ hc.1 hsub)).trans hc.2

end DistinctDistances.TrackC
