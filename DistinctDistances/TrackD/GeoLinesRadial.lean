import DistinctDistances.TrackD.GeoLinesReal

/-! Linear constraints on radial images and noncollapse of an exterior line. -/

namespace DistinctDistances.TrackD.GeoLines
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

 def linearPoly (L : Point d →ₗ[ℂ] ℂ) : Poly d :=
  ∑ j : Fin d, MvPolynomial.C (L (Pi.single j 1)) * MvPolynomial.X j

 theorem eval_linearPoly (L : Point d →ₗ[ℂ] ℂ) (x : Point d) :
    MvPolynomial.aeval x (linearPoly L) = L x := by
  unfold linearPoly
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  conv_rhs => rw [GeoCommon.pi_decomp x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [map_smul, mul_comm]

 theorem radial_reps_in_flat (p : Point d) (Y : AffineVariety d)
    (W : Submodule ℂ (Point d))
    (hY : Y.points ⊆ (AffineSubspace.mk' p W : Set (Point d))) :
    ∀ z ∈ (radialImage p Y).points, z.submodule ≤ W := by
  intro z hz
  rw [Projectivization.submodule_eq]
  apply Submodule.span_le.mpr
  apply Set.singleton_subset_iff.mpr
  by_contra hnot
  obtain ⟨L, hLz, hLW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hvan : ∀ w ∈ W, L w = 0 := by
    intro w hw
    have hm : L w ∈ W.map L := Submodule.mem_map.mpr ⟨w, hw, rfl⟩
    rwa [hLW, Submodule.mem_bot] at hm
  have hf : linearPoly L ∈ (radialImage p Y).ideal := by
    change linearPoly L ∈ ProjectiveVariety.vanishingIdeal
      {q | ∃ x ∈ Y.points, ∃ hx : x ≠ p, radialProjection p x hx = q}
    rintro v ⟨hv, x, hx, hxp, he⟩
    have hxW : x-p ∈ W := by
      simpa only [vsub_eq_sub] using (AffineSubspace.mem_mk'.mp (hY hx))
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ (x-p) v (sub_ne_zero.mpr hxp) hv).mp he
    have hc0 : c ≠ 0 := by
      intro he0
      rw [he0, zero_smul] at hc
      exact (sub_ne_zero.mpr hxp) hc.symm
    have hvW := W.smul_mem c⁻¹ hxW
    rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at hvW
    rw [eval_linearPoly]
    exact hvan v hvW
  exact hLz (by rw [← eval_linearPoly]; exact hz z.rep z.rep_nonzero z.mk_rep _ hf)

 theorem radial_dimension_ne_zero_off (p : Point d) (Y : AffineVariety d)
    (hY : IsCurve Y) (hp : p ∉ Y.points) : (radialImage p Y).dimension ≠ 0 := by
  intro hd0
  let R := radialImage p Y
  change R.dimension = 0 at hd0
  have hR : R.IsIrreducible := radialImage_irreducible p Y hY.1
    (GeoRadial.curve_point_off p Y hY)
  obtain ⟨z, hz⟩ := GeoRadial.radial_nonempty p Y hY
  obtain ⟨j, hj⟩ := GeoRadial.exists_coord z.rep z.rep_nonzero
  have hdimR : R.affineCone.dimension = 1 := by
    simpa only [hd0, zero_add] using R.dimension_cone ⟨z, hz⟩
  have hline0 : (Bridges.complexLine 0 z.rep).dimension = 1 :=
    Bridges.complexLine_dimension 0 z.rep j hj
  have hLC : Bridges.complexLine 0 z.rep = R.affineCone :=
    GeoRadial.curve_eq_of_subset _ _ hR hline0 hdimR (GeoRadial.cone_contains_line R z hz)
  have hsub : Y.points ⊆ (Bridges.complexLine p z.rep).points := by
    intro x hx
    rw [Bridges.complexLine_points p z.rep j hj]
    have hxp : x ≠ p := fun he => hp (he ▸ hx)
    have hxR : x-p ∈ R.affineCone.points :=
      (ProjectiveVariety.mem_points_mk_iff R (x-p) (sub_ne_zero.mpr hxp)).mp
        (GeoRadial.radial_mem p Y x hx hxp)
    rw [← hLC, Bridges.complexLine_points 0 z.rep j hj] at hxR
    obtain ⟨t, ht⟩ := hxR
    simp only [zero_add] at ht
    refine ⟨t, ?_⟩
    calc
      x = (x-p)+p := by abel
      _ = p+t • z.rep := by rw [ht]; abel
  have he := GeoRadial.curve_eq_of_subset Y (Bridges.complexLine p z.rep)
    (Bridges.complexLine_irreducible _ _) hY.2
    (Bridges.complexLine_dimension p z.rep j hj) hsub
  apply hp
  rw [he, Bridges.complexLine_points p z.rep j hj]
  exact ⟨0, by simp⟩

 theorem radial_member_off (p : Pt d) (Y : AffineVariety d) (hY : IsCurve Y)
    (hp : toC p ∉ Y.points) (C : ProjectiveFamily.Family d)
    (hC : IsDirectionalFamily C) (hproj : ProjectsInto C p Y) :
    radialImage (toC p) Y ∈ C ∧ (radialImage (toC p) Y).dimension = 1 := by
  let R := radialImage (toC p) Y
  change R ∈ C ∧ R.dimension = 1
  have hR : R.IsIrreducible := radialImage_irreducible _ _ hY.1
    (GeoRadial.curve_point_off _ Y hY)
  have hRne := GeoRadial.radial_nonempty (toC p) Y hY
  obtain ⟨V, hVC, hRV⟩ := GeoRadial.contained_member R hR C hproj
  have hV := hC V hVC
  have hle := GeoRadial.projective_dimension_mono R V hR hV.1 hRne hRV
  have hne := radial_dimension_ne_zero_off (toC p) Y hY hp
  change R.dimension ≠ 0 at hne
  have hdimR : R.dimension = 1 := by rw [hV.2.1] at hle; omega
  have he := GeoRadial.projective_curve_eq_of_subset R V hV.1 hRne hdimR hV.2.1 hRV
  exact ⟨by rwa [he], hdimR⟩

end
end DistinctDistances.TrackD.GeoLines
