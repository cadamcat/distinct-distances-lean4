import DistinctDistances.TrackA.Definitions
import DistinctDistances.TrackA.ProjectiveChartComponents

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

def linearSliceFamily {n : ℕ} (F : ProjectiveFamily.Family n) (ℓ : Poly n) :
    AffineFamily.Family n := F.image (fun V => projectiveLinearSlice V ℓ)

theorem chart_affine_family_mem {n : ℕ} (F : AffineFamily.Family n) (f : Poly n) :
    f ∈ (AffineFamily.locus F).ideal ↔ ∀ V ∈ F, f ∈ V.ideal := by
  have hr : (⨅ V ∈ F, V.ideal).IsRadical :=
    Ideal.isRadical_iInf _ (fun V => Ideal.isRadical_iInf _ (fun _ => V.isRadical))
  change f ∈ (⨅ V ∈ F, V.ideal).radical ↔ _
  rw [hr.radical]
  simp only [Ideal.mem_iInf]

theorem chart_projective_family_mem {n : ℕ} (F : ProjectiveFamily.Family n) (f : Poly n) :
    f ∈ (ProjectiveFamily.locus F).ideal ↔ ∀ V ∈ F, f ∈ V.ideal := by
  change f ∈ ProjectiveVariety.vanishingIdeal (⋃ V ∈ F, V.points) ↔ _
  constructor
  · intro hf V hV
    rw [← V.vanishingIdeal_points]
    intro v hv
    obtain ⟨hv, hp⟩ := hv
    apply hf v
    exact ⟨hv, Set.mem_iUnion.mpr ⟨V, Set.mem_iUnion.mpr ⟨hV, hp⟩⟩⟩
  · intro hf v hv
    obtain ⟨hv, hp⟩ := hv
    obtain ⟨V, hp⟩ := Set.mem_iUnion.mp hp
    obtain ⟨hV, hp⟩ := Set.mem_iUnion.mp hp
    have hfV : f ∈ ProjectiveVariety.vanishingIdeal V.points := by
      rw [V.vanishingIdeal_points]
      exact hf V hV
    exact hfV v ⟨hv, hp⟩

theorem linearSliceFamily_mem {n : ℕ} (F : ProjectiveFamily.Family n)
    (ℓ f : Poly n) : f ∈ (AffineFamily.locus (linearSliceFamily F ℓ)).ideal ↔
      ∀ V ∈ F, f ∈ (projectiveLinearSlice V ℓ).ideal := by
  rw [chart_affine_family_mem]
  simp only [linearSliceFamily, Finset.mem_image]
  constructor
  · intro h V hV
    exact h _ ⟨V, hV, rfl⟩
  · intro h A hA
    obtain ⟨V, hV, rfl⟩ := hA
    exact h V hV

theorem linearSliceFamily_hilbert {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ∀ V ∈ F, V.IsIrreducible) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hℓF : ∀ V ∈ F, ℓ ∉ V.ideal) (D : ℕ) :
    AffineFamily.hilbert (linearSliceFamily F ℓ) D = ProjectiveFamily.hilbert F D := by
  apply linearChart_hilbert (ProjectiveFamily.locus F)
    (AffineFamily.locus (linearSliceFamily F ℓ)) ℓ hℓ
  · intro f hf
    rw [linearSliceFamily_mem]
    intro V hV
    have hfV := (chart_projective_family_mem F f).1 hf V hV
    exact Ideal.le_radical (Ideal.mem_sup_left hfV)
  · rw [linearSliceFamily_mem]
    intro V hV
    exact Ideal.le_radical (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
  · intro d f hf
    rw [linearSliceFamily_mem, chart_projective_family_mem]
    apply forall_congr'
    intro V
    apply forall_congr'
    intro hV
    exact homogeneous_mem_linearSlice_iff V (hF V hV) ℓ f hℓ (hℓF V hV) hf

theorem linearSlice_injective {n : ℕ} (V W : ProjectiveVariety n)
    (hV : V.IsIrreducible) (hW : W.IsIrreducible) (ℓ : Poly n)
    (hℓ : ℓ.IsHomogeneous 1) (hℓV : ℓ ∉ V.ideal) (hℓW : ℓ ∉ W.ideal)
    (h : projectiveLinearSlice V ℓ = projectiveLinearSlice W ℓ) : V = W := by
  apply ProjectiveVariety.ext
  ext f
  rw [MvPolynomial.mem_iff_homogeneousComponent_mem V.isHomogeneous,
    MvPolynomial.mem_iff_homogeneousComponent_mem W.isHomogeneous]
  apply forall_congr'
  intro d
  rw [← homogeneous_mem_linearSlice_iff V hV ℓ _ hℓ hℓV
      (MvPolynomial.homogeneousComponent_isHomogeneous d f), h,
    homogeneous_mem_linearSlice_iff W hW ℓ _ hℓ hℓW
      (MvPolynomial.homogeneousComponent_isHomogeneous d f)]

theorem linearSliceFamily_degree {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ∀ V ∈ F, V.IsIrreducible) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hℓF : ∀ V ∈ F, ℓ ∉ V.ideal) :
    AffineFamily.degree (linearSliceFamily F ℓ) = ProjectiveFamily.degree F := by
  unfold AffineFamily.degree linearSliceFamily ProjectiveFamily.degree
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro V hV
    exact linearSlice_degree V (hF V hV) ℓ hℓ (hℓF V hV)
  · intro V hV W hW h
    exact linearSlice_injective V W (hF V hV) (hF W hW) ℓ hℓ
      (hℓF V hV) (hℓF W hW) h

theorem linearSliceFamily_pure {n : ℕ} (F : ProjectiveFamily.Family n) (k : ℕ)
    (hF : ProjectiveFamily.IsPure F k) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hℓF : ∀ V ∈ F, ℓ ∉ V.ideal) :
    AffineFamily.IsPure (linearSliceFamily F ℓ) k := by
  intro A hA
  obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hA
  exact ⟨linearSlice_irreducible V (hF V hV).1 ℓ hℓ (hℓF V hV),
    (linearSlice_dimension V (hF V hV).1 ℓ hℓ (hℓF V hV)).trans (hF V hV).2⟩

theorem linearSliceFamily_defined {n : ℕ} (F : ProjectiveFamily.Family n) (L : ℕ)
    (hF : ProjectiveFamily.ComponentsDefinedInDegree F L) (hL : 1 ≤ L)
    (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1) (hℓF : ∀ V ∈ F, ℓ ∉ V.ideal) :
    AffineFamily.ComponentsDefinedInDegree (linearSliceFamily F ℓ) L := by
  obtain ⟨E, hE, hcomp⟩ := hF
  refine ⟨E ∪ {ℓ-1}, ?_, ?_⟩
  · intro f hf
    rcases hf with hf | hf
    · obtain ⟨d, hdL, hd⟩ := hE f hf
      exact hd.totalDegree_le.trans hdL
    · obtain rfl := hf
      exact (MvPolynomial.totalDegree_sub _ _).trans
        (max_le (hℓ.totalDegree_le.trans hL) (by simpa using Nat.zero_le L))
  · intro A hA
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hA
    apply linearSlice_component V E _ (hcomp V hV) ℓ hℓ (hℓF V hV)
    intro f hf
    obtain ⟨d, _, hd⟩ := hE f hf
    exact ⟨d, hd⟩

theorem linearSliceFamily_lists {n : ℕ} (F : ProjectiveFamily.Family n) (L : ℕ)
    (hF : FromProjectiveLists F L) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hℓF : ∀ V ∈ F, ℓ ∉ V.ideal) : FromAffineLists (linearSliceFamily F ℓ) L := by
  obtain ⟨r, lists, bounds, hdefined, hunion, hsum⟩ := hF
  refine ⟨r, (fun i => linearSliceFamily (lists i) ℓ), bounds, ?_, ?_, hsum⟩
  · intro i
    refine ⟨(hdefined i).1, linearSliceFamily_defined (lists i) (bounds i)
      (hdefined i).2 (hdefined i).1 ℓ hℓ ?_⟩
    intro V hV
    exact hℓF V ((hunion V).2 ⟨i, hV⟩)
  · intro A
    constructor
    · intro hA
      obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨i, hi⟩ := (hunion V).1 hV
      exact ⟨i, Finset.mem_image.mpr ⟨V, hi, rfl⟩⟩
    · rintro ⟨i, hi⟩
      obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_image.mpr ⟨V, (hunion V).2 ⟨i, hV⟩, rfl⟩

end
end DistinctDistances.TrackA
