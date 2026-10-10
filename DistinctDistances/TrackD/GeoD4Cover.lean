import DistinctDistances.TrackD.GeoD4Groups

/-! Cover nonlinear terminal pairs by capped span centers and exterior planar groups. -/

namespace DistinctDistances.TrackD.GeoD4

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

def planarCurves (𝒴 : Finset (AffineVariety d)) : Finset (AffineVariety d) :=
  𝒴.filter (fun Y => ¬ IsLine Y ∧ Module.finrank ℂ (complexSpan Y).direction = 2)

def boundedCurves (𝒴 : Finset (AffineVariety d)) : Finset (AffineVariety d) :=
  𝒴.filter (fun Y => ¬ IsLine Y ∧ Module.finrank ℂ (complexSpan Y).direction ≤ 3)

def innerCenters (P : Finset (Pt d)) (Y : AffineVariety d) : Finset (Pt d) :=
  P.filter (fun p => toC p ∈ complexSpan Y)

def outerCenters (P : Finset (Pt d)) (Cf : Pt d → ProjectiveFamily.Family d)
    (Y : AffineVariety d) : Finset (Pt d) :=
  P.filter (fun p => (exteriorGroup Cf p Y).isSome)

theorem nonlinear_pair_bound (d : ℕ) (hd : 4 ≤ d) (P : Finset (Pt d))
    (c₀ : ℝ) (hcap : RealFlatCap P c₀)
    (Cf : Pt d → ProjectiveFamily.Family d) (hCf : ∀ p ∈ P, IsDirectionalFamily (Cf p))
    (𝒴 : Finset (AffineVariety d)) (S : AffineVariety d → Finset (Pt d))
    (hS : Assignment P 𝒴 S) (hcurves : ∀ Y ∈ 𝒴, IsCurve Y) :
    (((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧
        ∃ Y ∈ 𝒴, ¬ IsLine Y ∧ pq.2 ∈ S Y ∧ ProjectsInto (Cf pq.1) pq.1 Y)).card : ℝ) ≤
      cfgN P ^ 2 * cfgB P ^ (-c₀) +
        ∑ p ∈ P, ∑ Y ∈ (planarCurves 𝒴).filter (fun Y => (exteriorGroup Cf p Y).isSome),
          ((S Y).card : ℝ) := by
  let T := (P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧
    ∃ Y ∈ 𝒴, ¬ IsLine Y ∧ pq.2 ∈ S Y ∧ ProjectsInto (Cf pq.1) pq.1 Y)
  have hcover : ∀ t ∈ T,
      (∃ Y ∈ boundedCurves 𝒴, t ∈ innerCenters P Y ×ˢ S Y) ∨
        (∃ Y ∈ planarCurves 𝒴, t ∈ outerCenters P Cf Y ×ˢ S Y) := by
    intro t ht
    obtain ⟨htP, _, Y, hY, hnl, hq, hproj⟩ := Finset.mem_filter.mp ht
    have hpP := (Finset.mem_product.mp htP).1
    have hYC := hcurves Y hY
    by_cases hp : toC t.1 ∈ complexSpan Y
    · left
      refine ⟨Y, Finset.mem_filter.mpr ⟨hY, hnl, ?_⟩, ?_⟩
      · exact (GeoRadial.projects_span t.1 Y hYC hnl (Cf t.1) (hCf _ hpP) hproj).1
      · exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hpP, hp⟩, hq⟩
    · right
      refine ⟨Y, Finset.mem_filter.mpr ⟨hY, hnl, ?_⟩, ?_⟩
      · exact GeoRadial.exterior_planar t.1 Y hYC hnl (Cf t.1) (hCf _ hpP) hproj hp
      · apply Finset.mem_product.mpr
        refine ⟨Finset.mem_filter.mpr ⟨hpP, ?_⟩, hq⟩
        simp [exteriorGroup, hp, hproj]
  have hcount := GeoCounting.two_cover_card_le T (boundedCurves 𝒴) (planarCurves 𝒴)
    S (innerCenters P) (outerCenters P Cf) hcover
  have hinner : ∀ Y ∈ boundedCurves 𝒴,
      ((innerCenters P Y).card : ℝ) ≤ cfgN P * cfgB P ^ (-c₀) := by
    intro Y hY
    have hspan := (Finset.mem_filter.mp hY).2.2
    exact complexFlatCap_of_real P c₀ hcap (complexSpan Y) (GeoRadial.proper_span d hd Y hspan)
  have hsum := GeoCounting.assignment_sum_le P 𝒴 S hS (boundedCurves 𝒴)
    (Finset.filter_subset _ _)
  have hN0 : 0 ≤ cfgN P := by unfold cfgN; positivity
  have hB0 : 0 ≤ cfgB P ^ (-c₀) := Real.rpow_nonneg (by unfold cfgB; positivity) _
  have hinner_sum : (∑ Y ∈ boundedCurves 𝒴, ((innerCenters P Y).card : ℝ) * (S Y).card) ≤
      cfgN P ^ 2 * cfgB P ^ (-c₀) := by
    calc
      _ ≤ ∑ Y ∈ boundedCurves 𝒴, (cfgN P * cfgB P ^ (-c₀)) * ((S Y).card : ℝ) :=
        Finset.sum_le_sum (fun Y hY => mul_le_mul_of_nonneg_right (hinner Y hY) (Nat.cast_nonneg _))
      _ = (cfgN P * cfgB P ^ (-c₀)) * ∑ Y ∈ boundedCurves 𝒴, ((S Y).card : ℝ) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (cfgN P * cfgB P ^ (-c₀)) * cfgN P :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hN0 hB0)
      _ = _ := by ring
  have houter : (∑ Y ∈ planarCurves 𝒴, ((outerCenters P Cf Y).card : ℝ) * (S Y).card) =
      ∑ p ∈ P, ∑ Y ∈ (planarCurves 𝒴).filter (fun Y => (exteriorGroup Cf p Y).isSome),
        ((S Y).card : ℝ) := by
    convert GeoCounting.filtered_weight_eq P (planarCurves 𝒴)
      (fun Y => ((S Y).card : ℝ)) (fun p Y => (exteriorGroup Cf p Y).isSome) using 1
    · apply Finset.sum_congr rfl
      intro Y hY
      congr 3
      ext p
      simp only [outerCenters, Finset.mem_filter]
    · apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr
      · ext Y
        simp only [Finset.mem_filter]
      · intro Y hY
        rfl
  calc
    _ ≤ _ := hcount
    _ ≤ cfgN P ^ 2 * cfgB P ^ (-c₀) +
        ∑ Y ∈ planarCurves 𝒴, ((outerCenters P Cf Y).card : ℝ) * (S Y).card :=
      add_le_add hinner_sum le_rfl
    _ = _ := by
      exact congrArg (fun r : ℝ => cfgN P ^ 2 * cfgB P ^ (-c₀) + r) houter

end
end DistinctDistances.TrackD.GeoD4
