import DistinctDistances.TrackC.Basic

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Counting mass of a finite cloud on a set. -/
def cloudMass {d : ℕ} (X : Finset (E d)) (S : Set (E d)) : ℝ :=
  (pointsIn X S).card

theorem cloudMass_nonneg {d : ℕ} (X : Finset (E d)) (S : Set (E d)) :
    0 ≤ cloudMass X S := Nat.cast_nonneg _

theorem cloudMass_mono {d : ℕ} (X : Finset (E d)) {S T : Set (E d)} (h : S ⊆ T) :
    cloudMass X S ≤ cloudMass X T := by
  dsimp [cloudMass, pointsIn]
  have hs : X.filter (fun x => x ∈ S) ⊆ X.filter (fun x => x ∈ T) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, h (Finset.mem_filter.mp hx).2⟩
  exact_mod_cast Finset.card_le_card hs

theorem cloudMass_le_card {d : ℕ} (X : Finset (E d)) (S : Set (E d)) :
    cloudMass X S ≤ X.card := by
  dsimp [cloudMass, pointsIn]
  exact_mod_cast Finset.card_filter_le X (fun x => x ∈ S)

@[simp] theorem cloudMass_empty {d : ℕ} (X : Finset (E d)) :
    cloudMass X ∅ = 0 := by simp [cloudMass, pointsIn]

theorem cloudMass_diff_add {d : ℕ} (X : Finset (E d)) {S T : Set (E d)} (h : T ⊆ S) :
    cloudMass X (S \ T) + cloudMass X T = cloudMass X S := by
  have hsub : pointsIn X T ⊆ pointsIn X S := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, h (Finset.mem_filter.mp hx).2⟩
  have heq : pointsIn X (S \ T) = pointsIn X S \ pointsIn X T := by
    ext x
    simp [pointsIn]
    tauto
  simp only [cloudMass, heq, ← Nat.cast_add]
  exact_mod_cast Finset.card_sdiff_add_card_eq_card hsub

theorem cloudMass_iUnion {d : ℕ} {ι : Type*} (X : Finset (E d))
    (s : Finset ι) (A : ι → Set (E d))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j)) :
    cloudMass X (⋃ i ∈ s, A i) = ∑ i ∈ s, cloudMass X (A i) := by
  have heq : pointsIn X (⋃ i ∈ s, A i) = s.biUnion (fun i => pointsIn X (A i)) := by
    ext x
    simp only [pointsIn, Finset.mem_filter, Set.mem_iUnion, exists_prop, Finset.mem_biUnion]
    aesop
  have hdisj : (s : Set ι).PairwiseDisjoint (fun i => pointsIn X (A i)) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    exact Set.disjoint_left.mp (hd i hi j hj hij)
      (Finset.mem_filter.mp hxi).2 (Finset.mem_filter.mp hxj).2
  simp only [cloudMass, heq, Finset.card_biUnion hdisj, Nat.cast_sum]

/-- A finite list of positive distances has a uniform positive lower bound. -/
theorem finite_cloud_separation (X : Finset (E 3)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ dist x y := by
  have hfinite : ∀ (s : Finset (E 3 × E 3)),
      (∀ z ∈ s, z.1 ≠ z.2) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ s, δ ≤ dist z.1 z.2 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨1, by norm_num, by simp⟩
    | @insert z s hz ih =>
      intro h
      obtain ⟨δ, hδ, hbound⟩ := ih (fun w hw => h w (Finset.mem_insert_of_mem hw))
      have hzpos : 0 < dist z.1 z.2 := dist_pos.mpr (h z (Finset.mem_insert_self _ _))
      refine ⟨min δ (dist z.1 z.2), lt_min hδ hzpos, ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound w hw)
  let s := (X ×ˢ X).filter (fun z => z.1 ≠ z.2)
  obtain ⟨δ, hδ, hb⟩ := hfinite s (fun z hz => (Finset.mem_filter.mp hz).2)
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  exact hb (x,y) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩, hxy⟩)

end DistinctDistances.TrackC
