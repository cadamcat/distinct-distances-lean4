import DistinctDistances.TrackD.Profiles.PartitionTreeData
import DistinctDistances.TrackD.Profiles.PartitionPackages

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d G : ℕ}

theorem partition_complete_prefix_forest (grid : Fin G → ℝ) (hgrid : Monotone grid)
    (L : Fin G → ℕ) (s u : ℝ) (a : Fin (G * d) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (r : Fin G) (π : CutPath d) (S : Finset (Pt d)) (hne : S.Nonempty)
    (hmono : Monotone π.time)
    (hvan : ∀ x ∈ S, ∀ i, MvPolynomial.eval (toC x) (π.cut i) = 0)
    (hproper : ∀ x ∈ S, π.ProperAt (toC x))
    (hfinal : ∀ i, π.time i ≤ grid r) :
    Nonempty (PartitionGridForest grid L s u a r π d S) := by
  let X : Piece d := ⟨S, s, π⟩
  have hX : PartitionGridLeaf grid L r π d S s X := by
    refine ⟨Finset.Subset.refl _, hne, rfl, ?_, ?_, hmono, hvan, hproper⟩
    · intro i hi; exact ⟨rfl, rfl⟩
    · intro i hi; omega
  exact partition_terminal_forest grid hgrid L s u a ha r π d S X hX rfl hfinal

theorem partition_finish_node_forest (grid : Fin G → ℝ) (hgrid : Monotone grid)
    (L : Fin G → ℕ) (s u : ℝ) (a : Fin (G * d) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (r : Fin G) (S S₀ : Finset (Pt d)) (hne : S.Nonempty) (hsubset : S ⊆ S₀)
    (E : Set (Poly d)) (hdegree : ∀ f ∈ E, f.totalDegree ≤ L r)
    (hisolate : MvPolynomial.zeroLocus ℂ (Ideal.span E) = toC '' (S₀ : Set (Pt d)))
    (π : CutPath d) (j : ℕ) (hj : j ≤ d)
    (hvan : ∀ x ∈ S, ∀ i : Fin d, i.val < j → MvPolynomial.eval (toC x) (π.cut i) = 0)
    (hproper : ∀ x ∈ S, ∀ i : Fin d, i.val < j →
      ∀ Z ∈ π.localCarriers i.val (toC x), π.cut i ∉ Z.ideal)
    (hmono : ∀ i k : Fin d, i.val < j → k.val < j → i ≤ k → π.time i ≤ π.time k)
    (hfinal : ∀ i : Fin d, i.val < j → π.time i ≤ grid r) :
    Nonempty (PartitionGridForest grid L s u a r π j S) := by
  obtain ⟨π', hprefix, hnew, hmono', hvan', hproper'⟩ :=
    partition_finish_prefix S S₀ hsubset E (L r) hdegree hisolate π j hj
      (grid r) hvan hproper hmono hfinal
  let X : Piece d := ⟨S, s, π'⟩
  have hX : PartitionGridLeaf grid L r π j S s X := by
    refine ⟨Finset.Subset.refl _, hne, rfl, hprefix, ?_, hmono', hvan', hproper'⟩
    intro i hi
    exact ⟨r, le_rfl, (hnew i hi).1, (hnew i hi).2⟩
  have htimes : ∀ i, π'.time i ≤ grid r := by
    intro i
    by_cases hi : i.val < j
    · rw [(hprefix i hi).2]
      exact hfinal i hi
    · rw [(hnew i (by omega)).2]
  exact partition_terminal_forest grid hgrid L s u a ha r π j S X hX rfl htimes

/-- The unextracted residual and the disjoint greedy batches exactly cover
the original node. -/
theorem partition_greedy_residual {α : Type*} (S : Finset α) (bs : Finset (Finset α))
    (hsubset : ∀ T ∈ bs, T ⊆ S) (hdisj : (bs : Set (Finset α)).PairwiseDisjoint id) :
    (S \ bs.biUnion id) ⊆ S ∧
      (∀ T ∈ bs, Disjoint T (S \ bs.biUnion id)) ∧
      (∑ T ∈ bs, (T.card : ℝ)) + ((S \ bs.biUnion id).card : ℝ) = S.card ∧
      ((S \ bs.biUnion id).Nonempty → (S \ bs.biUnion id) ∉ bs) := by
  classical
  have hTR : ∀ T ∈ bs, Disjoint T (S \ bs.biUnion id) := by
    intro T hT
    apply Finset.disjoint_left.mpr
    intro x hxT hxR
    exact (Finset.mem_sdiff.mp hxR).2 (Finset.mem_biUnion.mpr ⟨T, hT, hxT⟩)
  refine ⟨Finset.sdiff_subset, hTR, ?_, ?_⟩
  · have hUsub : bs.biUnion id ⊆ S := Finset.biUnion_subset.mpr hsubset
    have hN : (∑ T ∈ bs, T.card) + (S \ bs.biUnion id).card = S.card := by
      have hBi : (∑ T ∈ bs, T.card) = (bs.biUnion id).card := (Finset.card_biUnion hdisj).symm
      rw [hBi, Finset.card_sdiff_of_subset hUsub]
      have hle := Finset.card_le_card hUsub
      omega
    exact_mod_cast hN
  · intro hne hR
    obtain ⟨x, hx⟩ := hne
    exact Finset.disjoint_left.mp (hTR _ hR) hx hx

end
end DistinctDistances.TrackD
