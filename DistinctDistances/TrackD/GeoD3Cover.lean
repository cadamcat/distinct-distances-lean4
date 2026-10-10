import DistinctDistances.TrackD.GeoD3Groups

/-! Delete high-multiplicity centers and degree-one images before grouping. -/

namespace DistinctDistances.TrackD.GeoD3
open scoped BigOperators Classical
noncomputable section

 def nonlinearCurves (𝒴 : Finset (AffineVariety 3)) := 𝒴.filter (fun Y => ¬ IsLine Y)

 def badCenters (P : Finset (Pt 3)) (Y : AffineVariety 3) : Finset (Pt 3) :=
  P.filter (fun p => Y.degree / 2 < Y.multiplicity (toC p) ∨
    (Module.finrank ℂ (complexSpan Y).direction = 2 ∧ toC p ∈ complexSpan Y))

 def groupCenters (P : Finset (Pt 3)) (Cf : Pt 3 → ProjectiveFamily.Family 3)
    (Y : AffineVariety 3) : Finset (Pt 3) := P.filter (fun p => (group Cf p Y).isSome)

 theorem bad_card_le (P : Finset (Pt 3)) (Y : AffineVariety 3)
    (c₀ C : ℝ) (hcap : RealFlatCap P c₀)
    (hfin : {p : Point 3 | Y.degree / 2 < Y.multiplicity p}.Finite)
    (hcard : ({p : Point 3 | Y.degree / 2 < Y.multiplicity p}.ncard : ℝ) ≤ C) :
    ((badCenters P Y).card : ℝ) ≤ C + cfgN P * cfgB P ^ (-c₀) := by
  let H := P.filter (fun p => Y.degree / 2 < Y.multiplicity (toC p))
  let L := P.filter (fun p => Module.finrank ℂ (complexSpan Y).direction = 2 ∧
    toC p ∈ complexSpan Y)
  have hbad : badCenters P Y = H ∪ L := by
    ext p; simp [badCenters, H, L, and_or_left]
  have hH : (H.card : ℝ) ≤ C := by
    convert GeoCounting.center_card_le P
      {p : Point 3 | Y.degree / 2 < Y.multiplicity p} hfin C hcard using 1
    congr 2; ext p; simp [H]
  have hL : (L.card : ℝ) ≤ cfgN P * cfgB P ^ (-c₀) := by
    by_cases hdim : Module.finrank ℂ (complexSpan Y).direction = 2
    · have hproper : complexSpan Y ≠ ⊤ := by
        intro he
        rw [he, AffineSubspace.direction_top, finrank_top, GeoCommon.finrank_point] at hdim
        omega
      have h := complexFlatCap_of_real P c₀ hcap (complexSpan Y) hproper
      convert h using 1
      congr 2; ext p; simp [L, hdim]
    · simp only [L, hdim, false_and, Finset.filter_false, Finset.card_empty, Nat.cast_zero]
      unfold cfgN cfgB; positivity
  rw [hbad]
  have hu : ((H ∪ L).card : ℝ) ≤ H.card + L.card := by exact_mod_cast Finset.card_union_le H L
  linarith

 theorem nonlinear_pair_bound (P : Finset (Pt 3))
    (c₀ : ℝ) (hcap : RealFlatCap P c₀)
    (Cf : Pt 3 → ProjectiveFamily.Family 3) (hCf : ∀ p ∈ P, IsDirectionalFamily (Cf p))
    (𝒴 : Finset (AffineVariety 3)) (S : AffineVariety 3 → Finset (Pt 3))
    (hS : Assignment P 𝒴 S) (hcurves : ∀ Y ∈ 𝒴, IsCurve Y)
    (C : ℝ) (hC : 0 ≤ C)
    (hhigh : ∀ Y ∈ 𝒴, ¬ IsLine Y →
      {p : Point 3 | Y.degree / 2 < Y.multiplicity p}.Finite ∧
      ({p : Point 3 | Y.degree / 2 < Y.multiplicity p}.ncard : ℝ) ≤ C) :
    (((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧
      ∃ Y ∈ 𝒴, ¬ IsLine Y ∧ pq.2 ∈ S Y ∧ ProjectsInto (Cf pq.1) pq.1 Y)).card : ℝ) ≤
      C * cfgN P + cfgN P ^ 2 * cfgB P ^ (-c₀) +
        ∑ p ∈ P, ∑ Y ∈ (nonlinearCurves 𝒴).filter (fun Y => (group Cf p Y).isSome),
          ((S Y).card : ℝ) := by
  let T := (P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧
    ∃ Y ∈ 𝒴, ¬ IsLine Y ∧ pq.2 ∈ S Y ∧ ProjectsInto (Cf pq.1) pq.1 Y)
  let I := nonlinearCurves 𝒴
  have hcover : ∀ t ∈ T,
      (∃ Y ∈ I, t ∈ badCenters P Y ×ˢ S Y) ∨
      (∃ Y ∈ I, t ∈ groupCenters P Cf Y ×ˢ S Y) := by
    intro t ht
    obtain ⟨htP, _, Y, hY, hnl, hq, hproj⟩ := Finset.mem_filter.mp ht
    have hpP := (Finset.mem_product.mp htP).1
    have hYC := hcurves Y hY
    have hYI : Y ∈ I := Finset.mem_filter.mpr ⟨hY, hnl⟩
    by_cases hmult : Y.degree / 2 < Y.multiplicity (toC t.1)
    · left
      exact ⟨Y, hYI, Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hpP, Or.inl hmult⟩, hq⟩⟩
    · have himage := (GeoRadial.radial_member t.1 Y hYC hnl (Cf t.1) (hCf _ hpP) hproj).2
      have hirr := radialImage_irreducible (toC t.1) Y hYC.1
        (GeoRadial.curve_point_off _ Y hYC)
      rcases degree_ge_two_or_one _ hirr himage with hdeg | hdeg
      · right
        refine ⟨Y, hYI, Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hpP, ?_⟩, hq⟩⟩
        simp [group, hproj, hdeg, le_of_not_gt hmult]
      · left
        have hplane := degree_one_center_in_span t.1 Y hYC hnl himage hdeg
        exact ⟨Y, hYI, Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨hpP, Or.inr hplane⟩, hq⟩⟩
  have hcount := GeoCounting.two_cover_card_le T I I S (badCenters P) (groupCenters P Cf) hcover
  have hbad : ∀ Y ∈ I, ((badCenters P Y).card : ℝ) ≤ C + cfgN P * cfgB P ^ (-c₀) := by
    intro Y hY
    obtain ⟨hYm, hnl⟩ := Finset.mem_filter.mp hY
    obtain ⟨hfin, hcard⟩ := hhigh Y hYm hnl
    exact bad_card_le P Y c₀ C hcap hfin hcard
  have hsum := GeoCounting.assignment_sum_le P 𝒴 S hS I (Finset.filter_subset _ _)
  have hbad_sum : (∑ Y ∈ I, ((badCenters P Y).card : ℝ) * (S Y).card) ≤
      C * cfgN P + cfgN P ^ 2 * cfgB P ^ (-c₀) := by
    calc
      _ ≤ ∑ Y ∈ I, (C + cfgN P * cfgB P ^ (-c₀)) * ((S Y).card : ℝ) :=
        Finset.sum_le_sum fun Y hY => mul_le_mul_of_nonneg_right (hbad Y hY) (Nat.cast_nonneg _)
      _ = (C + cfgN P * cfgB P ^ (-c₀)) * ∑ Y ∈ I, ((S Y).card : ℝ) :=
        (Finset.mul_sum ..).symm
      _ ≤ (C + cfgN P * cfgB P ^ (-c₀)) * cfgN P :=
        mul_le_mul_of_nonneg_left hsum (by unfold cfgN cfgB; positivity)
      _ = _ := by ring
  have houter : (∑ Y ∈ I, ((groupCenters P Cf Y).card : ℝ) * (S Y).card) =
      ∑ p ∈ P, ∑ Y ∈ I.filter (fun Y => (group Cf p Y).isSome), ((S Y).card : ℝ) := by
    convert GeoCounting.filtered_weight_eq P I (fun Y => ((S Y).card : ℝ))
      (fun p Y => (group Cf p Y).isSome) using 1
    · apply Finset.sum_congr rfl
      intro Y hY; congr 3; ext p; simp only [groupCenters, Finset.mem_filter]
    · apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr
      · ext Y; simp only [Finset.mem_filter]
      · intro Y hY; rfl
  calc
    _ ≤ _ := hcount
    _ ≤ C * cfgN P + cfgN P ^ 2 * cfgB P ^ (-c₀) +
        ∑ Y ∈ I, ((groupCenters P Cf Y).card : ℝ) * (S Y).card := add_le_add hbad_sum le_rfl
    _ = _ := congrArg (fun r : ℝ => C * cfgN P + cfgN P ^ 2 * cfgB P ^ (-c₀) + r) houter

end
end DistinctDistances.TrackD.GeoD3
