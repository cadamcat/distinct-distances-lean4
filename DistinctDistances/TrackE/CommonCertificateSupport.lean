import DistinctDistances.TrackE.CommonLabelGroupData
import DistinctDistances.TrackE.CommonLabelCylinder
import DistinctDistances.TrackE.CommonPhysical
import DistinctDistances.TrackE.CommonImageTesting
import DistinctDistances.TrackE.CommonProductLists
import DistinctDistances.TrackE.CommonRadialImages
import DistinctDistances.TrackE.CommonSourceSections
import DistinctDistances.TrackE.CommonRadialDimension
import DistinctDistances.TrackE.CommonDepthImages
import DistinctDistances.TrackE.CommonProjectionBudgets
import DistinctDistances.TrackE.CommonBlockTangents
import DistinctDistances.TrackE.CommonImageSections
import DistinctDistances.TrackE.CommonImagePooling
import DistinctDistances.TrackE.CommonChartGraphMass
import DistinctDistances.TrackE.CommonIsolation

/-! Pair deletions, envelope containment and labels used by the common
image certificates, sparse-cones.tex:99–150, 239–261. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Product of the two physical retentions misses a negligible part of the
product of the original pools. -/
theorem common_retained_pair_omissions {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T} {J : ℕ} {τ : ℝ}
    (W : CommonPhysicalSequence T M J τ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
      (((TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i)) \
        (W.sources i ×ˢ W.targets i)).card : ℝ) ≤
        η * ((TrackD.poolPts (T.sources i)).card : ℝ) * (TrackD.poolPts (T.targets i)).card := by
  intro η hη
  have h1 := W.source_omissions.bound (show 0 < η / 2 by positivity)
  have h2 := W.target_omissions.bound (show 0 < η / 2 by positivity)
  filter_upwards [h1, h2] with i hi1 hi2
  set A := TrackD.poolPts (T.sources i)
  set B := TrackD.poolPts (T.targets i)
  have hA' : W.sources i ⊆ A := Finset.filter_subset _ _
  have hB' : W.targets i ⊆ B := Finset.filter_subset _ _
  have hsub : (A ×ˢ B) \ (W.sources i ×ˢ W.targets i) ⊆
      ((A \ W.sources i) ×ˢ B) ∪ (A ×ˢ (B \ W.targets i)) := by
    intro pq hpq
    simp only [Finset.mem_sdiff, Finset.mem_product, Finset.mem_union] at hpq ⊢
    by_cases hp : pq.1 ∈ W.sources i
    · exact Or.inr ⟨hpq.1.1, hpq.1.2, fun hq => hpq.2 ⟨hp, hq⟩⟩
    · exact Or.inl ⟨⟨hpq.1.1, hp⟩, hpq.1.2⟩
  have hcard : (((A ×ˢ B) \ (W.sources i ×ˢ W.targets i)).card : ℝ) ≤
      ((A \ W.sources i).card : ℝ) * B.card + A.card * ((B \ W.targets i).card : ℝ) := by
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simp only [Finset.card_product] at this
    exact_mod_cast this
  have e1 : ((A \ W.sources i).card : ℝ) ≤ (η / 2) * A.card := by
    simpa [Real.norm_eq_abs, abs_of_nonneg, CommonPhysicalSequence.sources] using hi1
  have e2 : ((B \ W.targets i).card : ℝ) ≤ (η / 2) * B.card := by
    simpa [Real.norm_eq_abs, abs_of_nonneg, CommonPhysicalSequence.targets] using hi2
  have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  calc _ ≤ ((A \ W.sources i).card : ℝ) * B.card + A.card * ((B \ W.targets i).card : ℝ) := hcard
    _ ≤ (η / 2) * A.card * B.card + A.card * ((η / 2) * B.card) := by
        gcongr
    _ = η * A.card * B.card := by ring

/-- Retained pairs whose target owner is outside a list of the source owner
number at most the discarded product mass of that list. -/
theorem common_pairs_outside_lists_card {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T} {J : ℕ} {τ : ℝ}
    (W : CommonPhysicalSequence T M J τ) (Lp : AffineVariety d → AffineFamily.Family d)
    (i : ℕ) :
    (((W.sources i ×ˢ W.targets i).filter (fun pq =>
      W.owner i pq.2 ∉ Lp (W.owner i pq.1))).card : ℝ) ≤
      commonDiscardedProductMass W Lp i := by
  have hsub : (W.sources i ×ˢ W.targets i).filter (fun pq =>
      W.owner i pq.2 ∉ Lp (W.owner i pq.1)) ⊆
      (W.sourceCarriers i).biUnion (fun X => (W.targetCarriers i \ Lp X).biUnion
        (fun Y => W.sourceAssigned i X ×ˢ W.targetAssigned i Y)) := by
    intro pq hpq
    simp only [Finset.mem_filter, Finset.mem_product] at hpq
    simp only [Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_product]
    refine ⟨W.owner i pq.1, ?_, W.owner i pq.2, ⟨?_, hpq.2⟩, ?_, ?_⟩
    · exact Finset.mem_image_of_mem _ hpq.1.1
    · exact Finset.mem_image_of_mem _ hpq.1.2
    · exact Finset.mem_filter.mpr ⟨hpq.1.1, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hpq.1.2, rfl⟩
  have h' : ((W.sourceCarriers i).biUnion (fun X => (W.targetCarriers i \ Lp X).biUnion
        (fun Y => W.sourceAssigned i X ×ˢ W.targetAssigned i Y))).card ≤
      ∑ X ∈ W.sourceCarriers i, ∑ Y ∈ W.targetCarriers i \ Lp X,
        (W.sourceAssigned i X).card * (W.targetAssigned i Y).card := by
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun X _ => ?_)
    refine Finset.card_biUnion_le.trans (le_of_eq ?_)
    simp [Finset.card_product]
  unfold commonDiscardedProductMass
  have := (Finset.card_le_card hsub).trans h'
  exact_mod_cast this

/-- Retained pairs whose target owner is outside the fixed list of the source
owner have at most the discarded product mass. -/
theorem common_list_pair_loss {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T} {J : ℕ} {τ ε : ℝ}
    (W : CommonPhysicalSequence T M J τ) (L : CommonProductLists W ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
      (((W.sources i ×ˢ W.targets i).filter (fun pq =>
        W.owner i pq.2 ∉ L.lists i (W.owner i pq.1))).card : ℝ) ≤
        η * ((W.sources i).card : ℝ) * (W.targets i).card := by
  intro η hη
  filter_upwards [L.loss.bound hη] with i hi
  have hmass : (((W.sources i ×ˢ W.targets i).filter (fun pq =>
      W.owner i pq.2 ∉ L.lists i (W.owner i pq.1))).card : ℝ) ≤
      commonDiscardedProductMass W (L.lists i) i := by
    have hsub : (W.sources i ×ˢ W.targets i).filter (fun pq =>
        W.owner i pq.2 ∉ L.lists i (W.owner i pq.1)) ⊆
        (W.sourceCarriers i).biUnion (fun X => (W.targetCarriers i \ L.lists i X).biUnion
          (fun Y => W.sourceAssigned i X ×ˢ W.targetAssigned i Y)) := by
      intro pq hpq
      simp only [Finset.mem_filter, Finset.mem_product] at hpq
      simp only [Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_product]
      refine ⟨W.owner i pq.1, ?_, W.owner i pq.2, ⟨?_, hpq.2⟩, ?_, ?_⟩
      · exact Finset.mem_image_of_mem _ hpq.1.1
      · exact Finset.mem_image_of_mem _ hpq.1.2
      · exact Finset.mem_filter.mpr ⟨hpq.1.1, rfl⟩
      · exact Finset.mem_filter.mpr ⟨hpq.1.2, rfl⟩
    have h := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
    have h' : ((W.sourceCarriers i).biUnion (fun X => (W.targetCarriers i \ L.lists i X).biUnion
          (fun Y => W.sourceAssigned i X ×ˢ W.targetAssigned i Y))).card ≤
        ∑ X ∈ W.sourceCarriers i, ∑ Y ∈ W.targetCarriers i \ L.lists i X,
          (W.sourceAssigned i X).card * (W.targetAssigned i Y).card := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun X _ => ?_)
      refine Finset.card_biUnion_le.trans (le_of_eq ?_)
      simp [Finset.card_product]
    unfold commonDiscardedProductMass
    have := (Finset.card_le_card hsub).trans h'
    exact_mod_cast this
  have hnn : 0 ≤ commonDiscardedProductMass W (L.lists i) i := by
    unfold commonDiscardedProductMass
    positivity
  have hi' : commonDiscardedProductMass W (L.lists i) i ≤
      η * (((W.sources i).card : ℝ) * (W.targets i).card) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ ((W.sources i).card : ℝ) * (W.targets i).card)] using hi
  linarith

/-- An image on which every degree-`L` label equation of `Γ` vanishes lies in
the degree-`L` envelope of the labels of `Γ`. -/
theorem common_image_subvariety_envelope (i₀ : Fin d) (Γ : Finset (RPoint d × RPoint d))
    (L : ℕ) (Z : AffineVariety (d + d))
    (hZ : ∀ G : TrackD.PairPoly d, G.totalDegree ≤ L →
      (∀ pq ∈ Γ, MvPolynomial.eval (TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) G
        = 0) → commonPairEquation G ∈ Z.ideal) :
    Z.Subvariety (envelope (commonLabelPoints i₀ Γ) L) := by
  change (Ideal.span _).radical ≤ Z.ideal
  rw [Z.isRadical.radical_le_iff]
  rw [Ideal.span_le]
  rintro f ⟨hf, hdeg⟩
  let G : TrackD.PairPoly d := MvPolynomial.rename finSumFinEquiv.symm f
  have hG : commonPairEquation G = f := by
    simp only [commonPairEquation, G, MvPolynomial.rename_rename]
    simp
  rw [← hG]
  apply hZ G ((MvPolynomial.totalDegree_rename_le _ _).trans hdeg)
  intro pq hpq
  have hmem : (fun k => TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)
      (finSumFinEquiv.symm k)) ∈ commonLabelPoints i₀ Γ := ⟨pq, hpq, rfl⟩
  have h0 := (MvPolynomial.mem_vanishingIdeal_iff.mp hf) _ hmem
  simpa [G, MvPolynomial.eval_rename, MvPolynomial.coe_aeval_eq_eval, Function.comp_def]
    using h0

/-- The label of an actual chart pair lies on its complete product image. -/
theorem common_label_mem_product_image (i₀ : Fin d) (X Y : AffineVariety d)
    (p q : RPoint d) (hp : TrackD.toC p ∈ X) (hq : TrackD.toC q ∈ Y)
    (hi : (TrackD.toC q - TrackD.toC p) i₀ ≠ 0) :
    (fun k => TrackD.labelPt i₀ (TrackD.toC p) (TrackD.toC q) (finSumFinEquiv.symm k)) ∈
      (commonProductImage i₀ X Y).points := by
  have h := common_product_label_mem i₀ X Y _ _ hp hq hi
  have heq : TrackD.productPoint (TrackD.toC p)
      (TrackD.dirChart (LinearMap.proj i₀) (TrackD.toC q - TrackD.toC p)) =
      (fun k => TrackD.labelPt i₀ (TrackD.toC p) (TrackD.toC q) (finSumFinEquiv.symm k)) := by
    funext k
    simp only [TrackD.productPoint, TrackD.labelPt, TrackD.dirChart, LinearMap.proj_apply,
      Function.comp_apply]
  rw [heq] at h
  exact h

end
end DistinctDistances.SparseCones
