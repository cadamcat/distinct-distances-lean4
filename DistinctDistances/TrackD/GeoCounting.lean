import DistinctDistances.TrackD.GeoRadialDegree
import DistinctDistances.TrackD.GeoSpan

/-! Assignment mass and finite covers used by the terminal counting cores. -/

namespace DistinctDistances.TrackD.GeoCounting

open scoped BigOperators Classical
noncomputable section

theorem toC_injective {d : ℕ} : Function.Injective (toC (d := d)) := by
  intro x y h
  ext i
  exact Complex.ofReal_injective (congrFun h i)

theorem projective_degree_ge_one {d : ℕ} (V : ProjectiveVariety d)
    (hV : V.IsIrreducible) : (1 : ℝ) ≤ V.degree := by
  have h := V.affineCone.one_le_degree hV.ne_top
  rw [V.degree_cone] at h
  exact_mod_cast h

theorem assignment_sum_le {d : ℕ} (P : Finset (Pt d)) (𝒴 : Finset (AffineVariety d))
    (S : AffineVariety d → Finset (Pt d)) (hS : Assignment P 𝒴 S)
    (I : Finset (AffineVariety d)) (hI : I ⊆ 𝒴) :
    (∑ Y ∈ I, ((S Y).card : ℝ)) ≤ cfgN P := by
  have hdisj : (I : Set (AffineVariety d)).PairwiseDisjoint S := by
    intro Y hY Z hZ hne
    exact hS.disjoint (hI hY) (hI hZ) hne
  have hsub : I.biUnion S ⊆ P := by
    intro q hq
    obtain ⟨Y, hY, hq⟩ := Finset.mem_biUnion.mp hq
    exact hS.subset Y (hI hY) hq
  have hcard : ∑ Y ∈ I, (S Y).card ≤ P.card := by
    rw [← Finset.card_biUnion hdisj]
    exact Finset.card_le_card hsub
  change (∑ Y ∈ I, ((S Y).card : ℝ)) ≤ (P.card : ℝ)
  exact_mod_cast hcard

theorem assigned_mass_le {d : ℕ} (P : Finset (Pt d)) (𝒴 : Finset (AffineVariety d))
    (S : AffineVariety d → Finset (Pt d)) (hS : Assignment P 𝒴 S)
    (Y : AffineVariety d) (hY : Y ∈ 𝒴) : (S Y).card ≤ massOn P Y.points := by
  apply Finset.card_le_card
  intro q hq
  exact Finset.mem_filter.mpr ⟨hS.subset Y hY hq, hS.mem Y hY q hq⟩

theorem two_cover_card_le {α ι : Type*} (T : Finset (α × α))
    (I J : Finset ι) (S Q R : ι → Finset α)
    (hcover : ∀ t ∈ T,
      (∃ i ∈ I, t ∈ Q i ×ˢ S i) ∨ (∃ j ∈ J, t ∈ R j ×ˢ S j)) :
    (T.card : ℝ) ≤
      ∑ i ∈ I, ((Q i).card : ℝ) * (S i).card +
        ∑ j ∈ J, ((R j).card : ℝ) * (S j).card := by
  have hsub : T ⊆ I.biUnion (fun i => Q i ×ˢ S i) ∪
      J.biUnion (fun j => R j ×ˢ S j) := by
    intro t ht
    rcases hcover t ht with ⟨i, hi, hti⟩ | ⟨j, hj, htj⟩
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨i, hi, hti⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨j, hj, htj⟩))
  have hcard : T.card ≤
      ∑ i ∈ I, (Q i).card * (S i).card + ∑ j ∈ J, (R j).card * (S j).card := by
    calc
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ (∑ i ∈ I, (Q i ×ˢ S i).card) + ∑ j ∈ J, (R j ×ˢ S j).card :=
        add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
      _ = _ := by simp only [Finset.card_product]
  exact_mod_cast hcard

theorem filtered_weight_eq {α ι : Type*} (P : Finset α) (I : Finset ι)
    (n : ι → ℝ) (Q : α → ι → Prop) :
    (∑ i ∈ I, ((P.filter (fun p => Q p i)).card : ℝ) * n i) =
      ∑ p ∈ P, ∑ i ∈ I.filter (fun i => Q p i), n i := by
  calc
    _ = ∑ i ∈ I, ∑ p ∈ P, if Q p i then n i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter]
      simp
    _ = ∑ p ∈ P, ∑ i ∈ I, if Q p i then n i else 0 := Finset.sum_comm
    _ = _ := by simp only [Finset.sum_filter]

theorem center_card_le {d : ℕ} (P : Finset (Pt d)) (T : Set (Point d))
    (hT : T.Finite) (r : ℝ) (hcard : (T.ncard : ℝ) ≤ r) :
    ((P.filter (fun p => toC p ∈ T)).card : ℝ) ≤ r := by
  have hsub : (↑((P.filter (fun p => toC p ∈ T)).image toC) : Set (Point d)) ⊆ T := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hp).2
  have h := Set.ncard_le_ncard hsub hT
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ toC_injective] at h
  exact (by exact_mod_cast h :
    ((P.filter (fun p => toC p ∈ T)).card : ℝ) ≤ T.ncard).trans hcard

end
end DistinctDistances.TrackD.GeoCounting
