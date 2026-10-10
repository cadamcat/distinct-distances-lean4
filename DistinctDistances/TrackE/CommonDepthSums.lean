import DistinctDistances.TrackE.CommonDepthInputs

/-! Exact map-degree sums from the original moving-root bound,
`sc:retained-products.family`, sparse-cones.tex:177–182. -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section

theorem common_radial_group_depth_of_moving_roots {d k : ℕ}
    (F : AffineFamily.Family d) (hk : 1 ≤ k) (hF : AffineFamily.IsPure F k)
    (p : Point d) (himages : ∀ V ∈ F, (radialImage p V).dimension = k)
    (Y : AffineVariety d) (hY : Y ∈ F) (R : ℝ)
    (hroots : TrackD.ForGeneralPoint Y (fun y =>
      (TrackD.movingRoots F p y).Finite ∧
        ((TrackD.movingRoots F p y).ncard : ℝ) ≤ R)) :
    (TrackA.groupDepth p F Y : ℝ) ≤ R := by
  have hYirr := (hF Y hY).1
  have hgeneric (V : AffineVariety d) (hV : V ∈ F) :
      GenericallyFiniteRadialDegree p V (TrackA.radialMapDegree p V) :=
    TrackA.dep_radial_degree_exists V (hF V hV).1 k hk (hF V hV).2 p (himages V hV)
  obtain ⟨Q, e, hhom, hnot, hopen⟩ := TrackA.radial_group_fiber_open F hk hF Y hY p
    (himages Y hY) (TrackA.radialMapDegree p) (fun V hV _ => hgeneric V hV)
  obtain ⟨a, ha, hap⟩ := TrackA.radial_center_coordinate_separator Y hYirr hk (hF Y hY).2 p
  have hQpull := TrackA.radialDirectionPullback_not_mem Y p Q hhom hnot
  have hprod : a * TrackA.radialDirectionPullback p Q ∉ Y.ideal := by
    intro hmem
    exact (hYirr.mem_or_mem hmem).elim ha hQpull
  have havoid : TrackD.ForGeneralPoint Y (fun y => ∃ hpy : y ≠ p,
      MvPolynomial.eval (radialProjection p y hpy).rep Q ≠ 0) := by
    refine ⟨a * TrackA.radialDirectionPullback p Q, ?_, ?_⟩
    · exact GenericFiber.exists_point_of_not_mem Y _ hprod
    · intro y hy hval
      have hparts : MvPolynomial.eval y a ≠ 0 ∧
          MvPolynomial.eval y (TrackA.radialDirectionPullback p Q) ≠ 0 := by
        simpa only [map_mul, mul_ne_zero_iff] using hval
      have hpy : y ≠ p := by
        intro he
        exact hparts.1 (he ▸ hap)
      exact ⟨hpy, TrackA.radialDirectionPullback_nonzero p y hpy Q hhom hparts.2⟩
  obtain ⟨y, hy, hh⟩ := (hroots.and hYirr havoid).exists
  rcases hh with ⟨hroot, hpy, hQ⟩
  let z := radialProjection p y hpy
  have hz : z ∈ (radialImage p Y).points :=
    ProjectiveVariety.subset_closure _ ⟨y, hy, hpy, rfl⟩
  have hfibers := hopen z hQ
  let G := F.filter (fun V => radialImage p V = radialImage p Y)
  have hcount (V : AffineVariety d) (hV : V ∈ G) :
      (radialFiber p V z).Finite ∧
        (radialFiber p V z).ncard = TrackA.radialMapDegree p V := by
    obtain ⟨hVF, heq⟩ := Finset.mem_filter.mp hV
    exact hfibers.1 V hVF heq hz
  have hdisjoint (V : AffineVariety d) (hV : V ∈ G)
      (W : AffineVariety d) (hW : W ∈ G) (hne : V ≠ W) :
      Disjoint (radialFiber p V z) (radialFiber p W z) := by
    obtain ⟨hVF, heq⟩ := Finset.mem_filter.mp hV
    exact hfibers.2 V hVF heq W (Finset.mem_filter.mp hW).1 hne
  have hsum := common_radial_fiber_sum_le_moving_roots F G (Finset.filter_subset _ _)
    p y hpy (TrackA.radialMapDegree p)
    (fun V hV => (hcount V hV).1) (fun V hV => (hcount V hV).2) hdisjoint hroot.1
  have hn : TrackA.groupDepth p F Y ≤ (TrackD.movingRoots F p y).ncard := by
    simpa only [TrackA.groupDepth, G] using hsum
  have hnR : (TrackA.groupDepth p F Y : ℝ) ≤
      ((TrackD.movingRoots F p y).ncard : ℝ) := by
    exact_mod_cast hn
  exact hnR.trans hroot.2

/-- One source open counts every radial group of the original fixed target list. -/
theorem common_general_radial_group_depth {d k : ℕ}
    (X : AffineVariety d) (hX : X.IsIrreducible)
    (F : AffineFamily.Family d) (hk : 1 ≤ k) (hF : AffineFamily.IsPure F k) (R : ℝ)
    (himages : TrackD.ForGeneralPoint X (fun x =>
      ∀ V ∈ F, (radialImage x V).dimension = k))
    (hroots : ∀ Y ∈ F, TrackD.ForGeneralPair X Y (fun x y =>
      (TrackD.movingRoots F x y).Finite ∧
        ((TrackD.movingRoots F x y).ncard : ℝ) ≤ R)) :
    TrackD.ForGeneralPoint X (fun x =>
      ∀ Y ∈ F, (TrackA.groupDepth x F Y : ℝ) ≤ R) := by
  have hsource : TrackD.ForGeneralPoint X (fun x => ∀ Y ∈ F,
      TrackD.ForGeneralPoint Y (fun y => (TrackD.movingRoots F x y).Finite ∧
        ((TrackD.movingRoots F x y).ncard : ℝ) ≤ R)) := by
    apply TrackD.ForGeneralPoint.finset_all hX (X.points_nonempty_of_isIrreducible hX) F
      (fun Y x => TrackD.ForGeneralPoint Y (fun y =>
        (TrackD.movingRoots F x y).Finite ∧ ((TrackD.movingRoots F x y).ncard : ℝ) ≤ R))
    intro Y hY
    exact (hroots Y hY).swap.fiber_right
  apply (himages.and hX hsource).mono
  intro x hx hh Y hY
  exact common_radial_group_depth_of_moving_roots F hk hF x hh.1 Y hY R (hh.2 Y hY)

end
end DistinctDistances.SparseCones
