import DistinctDistances.TrackA.CommonRadialSourceOpenSupport
import DistinctDistances.TrackA.DepthAlgebra
import DistinctDistances.TrackE.CommonRadialDimension
import DistinctDistances.TrackE.CommonRadialImages
import DistinctDistances.Foundations.GenericFiber

/-! Finite original radial fibers and literal moving roots,
`sc:retained-products.family`, sparse-cones.tex:177–182. -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section

theorem common_radial_fiber_subset_moving_roots {d : ℕ}
    (F : AffineFamily.Family d) (V : AffineVariety d) (hV : V ∈ F)
    (p y : Point d) (hpy : y ≠ p) :
    radialFiber p V (radialProjection p y hpy) ⊆ TrackD.movingRoots F p y := by
  intro z hz
  obtain ⟨hzV, hzx, heq⟩ := hz
  have hproj : Projectivization.mk ℂ (z - p) (sub_ne_zero.mpr hzx) =
      Projectivization.mk ℂ (y - p) (sub_ne_zero.mpr hpy) := heq
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ (z - p) (y - p)
    (sub_ne_zero.mpr hzx) (sub_ne_zero.mpr hpy)).mp hproj
  exact ⟨⟨V, hV, hzV⟩, hzx, c, hc.symm⟩

/-- Pairwise disjoint complete fibers are charged to distinct original moving roots. -/
theorem common_radial_fiber_sum_le_moving_roots {d : ℕ}
    (F G : AffineFamily.Family d) (hGF : G ⊆ F)
    (p y : Point d) (hpy : y ≠ p) (r : AffineVariety d → ℕ)
    (hfinite : ∀ V ∈ G, (radialFiber p V (radialProjection p y hpy)).Finite)
    (hcount : ∀ V ∈ G, (radialFiber p V (radialProjection p y hpy)).ncard = r V)
    (hdisjoint : ∀ V ∈ G, ∀ W ∈ G, V ≠ W →
      Disjoint (radialFiber p V (radialProjection p y hpy))
        (radialFiber p W (radialProjection p y hpy)))
    (hroots : (TrackD.movingRoots F p y).Finite) :
    (∑ V ∈ G, r V) ≤ (TrackD.movingRoots F p y).ncard := by
  classical
  have hsub_each : ∀ V ∈ G,
      radialFiber p V (radialProjection p y hpy) ⊆ TrackD.movingRoots F p y :=
    fun V hV => common_radial_fiber_subset_moving_roots F V (hGF hV) p y hpy
  have hUsub : (⋃ V ∈ (↑G : Set (AffineVariety d)),
      radialFiber p V (radialProjection p y hpy)) ⊆ TrackD.movingRoots F p y := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨V, hVG, hzV⟩ := hz
    have hV : V ∈ G := Finset.mem_coe.mp hVG
    exact hsub_each V hV hzV
  let s : AffineVariety d → Finset (Point d) := fun V =>
    if h : V ∈ G then (hfinite V h).toFinset else ∅
  have hs_coe : ∀ V (hV : V ∈ G),
      ((s V : Finset (Point d)) : Set (Point d)) =
        radialFiber p V (radialProjection p y hpy) := by
    intro V hV
    have hVs : s V = (hfinite V hV).toFinset := dite_eq_left hV
    rw [hVs]
    exact Set.Finite.coe_toFinset (hfinite V hV)
  have hs_card : ∀ V (hV : V ∈ G), (s V).card = r V := by
    intro V hV
    have hVs : s V = (hfinite V hV).toFinset := dite_eq_left hV
    have h1 : (s V).card = (radialFiber p V (radialProjection p y hpy)).ncard := by
      rw [hVs, ← Set.ncard_eq_toFinset_card _ (hfinite V hV)]
    rw [h1, hcount V hV]
  have hs_disj : (↑G : Set (AffineVariety d)).PairwiseDisjoint s := by
    intro V hVG W hWG hne
    have hV : V ∈ G := Finset.mem_coe.mp hVG
    have hW : W ∈ G := Finset.mem_coe.mp hWG
    have hset : Disjoint (radialFiber p V (radialProjection p y hpy))
        (radialFiber p W (radialProjection p y hpy)) :=
      hdisjoint V hV W hW hne
    rw [← hs_coe V hV, ← hs_coe W hW] at hset
    exact Finset.disjoint_coe.mp hset
  have hcard : (G.biUnion s).card = ∑ V ∈ G, r V := by
    rw [Finset.card_biUnion hs_disj]
    apply Finset.sum_congr rfl
    intro V hV
    exact hs_card V hV
  have hcoe : ((G.biUnion s : Finset (Point d)) : Set (Point d)) =
      ⋃ V ∈ (↑G : Set (AffineVariety d)),
        radialFiber p V (radialProjection p y hpy) := by
    rw [Finset.coe_biUnion]
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨V, hVG, hzV⟩
      have hV : V ∈ G := Finset.mem_coe.mp hVG
      refine ⟨V, hVG, ?_⟩
      rw [hs_coe V hV] at hzV
      exact hzV
    · rintro ⟨V, hVG, hzV⟩
      have hV : V ∈ G := Finset.mem_coe.mp hVG
      refine ⟨V, hVG, ?_⟩
      rw [hs_coe V hV]
      exact hzV
  have hncard_eq : (⋃ V ∈ (↑G : Set (AffineVariety d)),
      radialFiber p V (radialProjection p y hpy)).ncard = ∑ V ∈ G, r V := by
    rw [← hcoe, Set.ncard_coe_finset, hcard]
  rw [← hncard_eq]
  exact Set.ncard_le_ncard hUsub hroots

theorem common_moving_roots_mono {d : ℕ} (F L : AffineFamily.Family d)
    (hFL : F ⊆ L) (p y : Point d) :
    TrackD.movingRoots F p y ⊆ TrackD.movingRoots L p y := by
  intro z hz
  obtain ⟨⟨Z, hZF, hzZ⟩, hne, c, hc⟩ := hz
  exact ⟨⟨Z, hFL hZF, hzZ⟩, hne, c, hc⟩

/-- Equal complete-image groups lie in the original complete radial-image groups. -/
theorem common_complete_image_degree_sum_le_depth {d : ℕ} (i₀ : Fin d)
    (X : AffineVariety d) (F : AffineFamily.Family d) (p : Point d)
    (Y : AffineVariety d)
    (hequal : ∀ V ∈ F, commonProductImage i₀ X V = commonProductImage i₀ X Y →
      radialImage p V = radialImage p Y) :
    (∑ V ∈ F.filter (fun V => commonProductImage i₀ X V = commonProductImage i₀ X Y),
      TrackA.radialMapDegree p V) ≤ TrackA.groupDepth p F Y := by
  unfold TrackA.groupDepth
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro V hV
    simp only [Finset.mem_filter] at hV ⊢
    obtain ⟨hVF, hVP⟩ := hV
    exact ⟨hVF, hequal V hVF hVP⟩
  · intro V _ _
    exact Nat.zero_le _

end
end DistinctDistances.SparseCones
