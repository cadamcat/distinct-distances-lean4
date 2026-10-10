import DistinctDistances.TrackC.MotionLocal
import DistinctDistances.TrackC.FiniteIncidence

open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- The affine image of a line under a rigid motion. -/
def motionImageLine (g : Motion 3) (l : Line 3) : Line 3 := by
  refine ⟨l.1.map g.toAffineEquiv,?_,?_⟩
  · obtain ⟨x,hx⟩ := l.2.1
    exact ⟨g x,Set.mem_image_of_mem g hx⟩
  · rw [AffineSubspace.map_direction]
    exact (g.toAffineEquiv.linear.finrank_map_eq l.1.direction).trans l.2.2

@[simp] theorem motionImageLine_maps (g : Motion 3) (l : Line 3) : mapsLine g l (motionImageLine g l) := by
  rfl

/-- Above square-root richness, ST supplies at most O(N/q) ambient lines. -/
theorem ambient_rich_line_list (X : Finset (E 3)) (N q C : ℝ)
    (hN : 1 ≤ N) (hX : (X.card:ℝ) ≤ N) (hq : 1 < q) (hQ : N ≤ q^2) (hC : 0 < C)
    (hRich : ∀ j : ℕ,2 ≤ j → FiniteCardBound (richLines X j)
      (C*((X.card:ℝ)^2/(j:ℝ)^3+(X.card:ℝ)/j))) :
    ∃ L : Finset (Line 3),(∀ l : Line 3,l ∈ L ↔ q ≤ ((pointsOn X l).card:ℝ)) ∧
      (L.card:ℝ) ≤ 2*C*N/q := by
  let j := ⌈q⌉₊
  have hj : q ≤ (j:ℝ) := Nat.le_ceil q
  have hj2 : 2 ≤ j := by
    by_contra hnot
    have hle : (j:ℝ) ≤ 1 := by exact_mod_cast (by omega : j ≤ 1)
    linarith
  have hc := hRich j hj2
  let L := hc.1.toFinset
  have hmem : ∀ l : Line 3,l ∈ L ↔ q ≤ ((pointsOn X l).card:ℝ) := by
    intro l
    rw [hc.1.mem_toFinset]
    change (j:ℝ) ≤ ((pointsOn X l).card:ℝ) ↔ _
    rw [Nat.cast_le]
    exact Nat.ceil_le
  refine ⟨L,hmem,?_⟩
  have hcard : (L.card:ℝ) ≤ C*((X.card:ℝ)^2/(j:ℝ)^3+(X.card:ℝ)/j) := by
    rw [← Set.ncard_eq_toFinset_card (richLines X j) hc.1]
    exact hc.2
  have hqpos : 0 < q := by linarith
  have hnpos : 0 < N := by linarith
  have hterm : N^2/q^3 ≤ N/q := by
    calc
      _ = (N/q)*(N/q^2) := by field_simp <;> ring
      _ ≤ (N/q)*1 := mul_le_mul_of_nonneg_left ((div_le_one (by positivity : (0:ℝ) < q^2)).mpr hQ) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ C*((X.card:ℝ)^2/(j:ℝ)^3+(X.card:ℝ)/j) := hcard
    _ ≤ C*(N^2/q^3+N/q) := by gcongr
    _ ≤ C*(N/q+N/q) := mul_le_mul_of_nonneg_left (add_le_add hterm le_rfl) hC.le
    _ = _ := by ring

end DistinctDistances.TrackC
