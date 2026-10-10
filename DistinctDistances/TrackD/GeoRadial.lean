import DistinctDistances.TrackD.GeoCommon
import DistinctDistances.Bridges.DegreeOneCurve

/-! Projective containment and linear-span facts for terminal curve grouping. -/

namespace DistinctDistances.TrackD.GeoRadial

open scoped BigOperators Classical
noncomputable section

variable {d : ℕ}

theorem projective_ideal_le (V W : ProjectiveVariety d)
    (hVW : V.points ⊆ W.points) : W.ideal ≤ V.ideal := by
  intro f hf
  rw [← V.vanishingIdeal_points]
  apply MvPolynomial.mem_vanishingIdeal_iff.mpr
  rintro v ⟨hv, hp⟩
  exact (hVW hp) v hv rfl f hf

theorem contained_member (V : ProjectiveVariety d) (hV : V.IsIrreducible)
    (C : ProjectiveFamily.Family d) (hVC : V.points ⊆ familyPoints C) :
    ∃ W ∈ C, V.points ⊆ W.points := by
  have hI : C.inf (fun W => W.ideal) ≤ V.ideal := by
    intro f hf
    rw [← V.vanishingIdeal_points]
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro v ⟨hv, hp⟩
    obtain ⟨W, hWC, hpW⟩ : ∃ W ∈ C, Projectivization.mk ℂ v hv ∈ W.points := by
      simpa only [familyPoints, Set.mem_iUnion, exists_prop] using hVC hp
    have hle : C.inf (fun W => W.ideal) ≤ W.ideal := Finset.inf_le hWC
    exact hpW v hv rfl f (hle hf)
  obtain ⟨W, hW, hWV⟩ := hV.inf_le'.mp hI
  refine ⟨W, hW, ?_⟩
  intro z hz v hv he f hf
  exact hz v hv he f (hWV hf)

theorem curve_eq_of_subset (V W : AffineVariety d) (hW : W.IsIrreducible)
    (hVdim : V.dimension = 1) (hWdim : W.dimension = 1)
    (hVW : V.points ⊆ W.points) : V = W := by
  letI : W.ideal.IsPrime := hW
  have hI := (AffineVariety.subvariety_iff_points_subset V W).mpr hVW
  have he := OAI.QuarticPowerFree.prime_same_dimension_eq W.ideal V.ideal hI hWdim hVdim
  exact AffineVariety.ext he.symm

theorem projective_curve_eq_of_subset (V W : ProjectiveVariety d)
    (hW : W.IsIrreducible) (hVne : V.points.Nonempty)
    (hVdim : V.dimension = 1) (hWdim : W.dimension = 1)
    (hVW : V.points ⊆ W.points) : V = W := by
  letI : W.ideal.IsPrime := hW
  have hI := projective_ideal_le V W hVW
  have hdW : OAI.QuarticPowerFree.affineDimension W.ideal = 1 + 1 := by
    change W.affineCone.dimension = 1 + 1
    simpa only [hWdim] using W.dimension_cone (hVne.mono hVW)
  have hdV : OAI.QuarticPowerFree.affineDimension V.ideal = 1 + 1 := by
    change V.affineCone.dimension = 1 + 1
    simpa only [hVdim] using V.dimension_cone hVne
  exact ProjectiveVariety.ext
    (OAI.QuarticPowerFree.prime_same_dimension_eq W.ideal V.ideal hI hdW hdV).symm

theorem exists_coord (v : Point d) (hv : v ≠ 0) : ∃ j : Fin d, v j ≠ 0 := by
  by_contra h
  push Not at h
  apply hv
  funext j
  exact h j

theorem zero_mem_cone (V : ProjectiveVariety d) (hVne : V.points.Nonempty) :
    (0 : Point d) ∈ V.affineCone.points := by
  obtain ⟨z, hz⟩ := hVne
  intro f hf
  have hc := MvPolynomial.homogeneousComponent_mem_of_mem V.isHomogeneous hf 0
  have he := hz z.rep z.rep_nonzero z.mk_rep _ hc
  simpa [MvPolynomial.homogeneousComponent_zero, MvPolynomial.aeval_zero,
    MvPolynomial.constantCoeff_eq] using he

theorem cone_contains_line (V : ProjectiveVariety d) (z : ProjectivePoint d)
    (hz : z ∈ V.points) :
    (Bridges.complexLine 0 z.rep).points ⊆ V.affineCone.points := by
  obtain ⟨j, hj⟩ := exists_coord z.rep z.rep_nonzero
  intro x hx
  rw [Bridges.complexLine_points 0 z.rep j hj] at hx
  obtain ⟨t, rfl⟩ := hx
  simp only [zero_add]
  by_cases ht : t = 0
  · simpa [ht] using zero_mem_cone V ⟨z, hz⟩
  · have htv : t • z.rep ≠ 0 := smul_ne_zero ht z.rep_nonzero
    apply (ProjectiveVariety.mem_points_mk_iff V (t • z.rep) htv).mp
    have he : Projectivization.mk ℂ (t • z.rep) htv = z := by
      calc
        _ = Projectivization.mk ℂ z.rep z.rep_nonzero :=
          (Projectivization.mk_eq_mk_iff' ℂ _ _ htv z.rep_nonzero).mpr ⟨t, rfl⟩
        _ = z := z.mk_rep
    rwa [he]

theorem radial_mem (p : Point d) (Y : AffineVariety d) (x : Point d)
    (hx : x ∈ Y.points) (hne : x ≠ p) :
    radialProjection p x hne ∈ (radialImage p Y).points :=
  ProjectiveVariety.subset_closure _ ⟨x, hx, hne, rfl⟩

theorem radial_nonempty (p : Point d) (Y : AffineVariety d) (hY : IsCurve Y) :
    (radialImage p Y).points.Nonempty := by
  obtain ⟨x, hx, hxp⟩ := (Bridges.curve_points_infinite Y hY.1 hY.2).exists_notMem_finset {p}
  have hne : x ≠ p := by simpa using hxp
  exact ⟨radialProjection p x hne, radial_mem p Y x hx hne⟩

theorem radial_subset_flat (p : Point d) (Y : AffineVariety d)
    (W : Submodule ℂ (Point d))
    (hW : ∀ z ∈ (radialImage p Y).points, z.submodule ≤ W) :
    Y.points ⊆ (AffineSubspace.mk' p W : Set (Point d)) := by
  intro x hx
  apply AffineSubspace.mem_mk'.mpr
  rw [vsub_eq_sub]
  by_cases hne : x = p
  · subst x
    simp
  · have hp := hW (radialProjection p x hne) (radial_mem p Y x hx hne)
    rw [radialProjection, Projectivization.submodule_mk] at hp
    exact hp (Submodule.mem_span_singleton_self _)

theorem curve_point_off (p : Point d) (Y : AffineVariety d) (hY : IsCurve Y) :
    ∃ x ∈ Y.points, x ≠ p := by
  obtain ⟨x, hx, hxp⟩ := (Bridges.curve_points_infinite Y hY.1 hY.2).exists_notMem_finset {p}
  exact ⟨x, hx, by simpa using hxp⟩

theorem radial_dimension_ne_zero (p : Point d) (Y : AffineVariety d)
    (hY : IsCurve Y) (hnl : ¬ IsLine Y) : (radialImage p Y).dimension ≠ 0 := by
  intro hd0
  let R := radialImage p Y
  change R.dimension = 0 at hd0
  have hR : R.IsIrreducible := radialImage_irreducible p Y hY.1 (curve_point_off p Y hY)
  have hRne := radial_nonempty p Y hY
  obtain ⟨z, hz⟩ := hRne
  obtain ⟨j, hj⟩ := exists_coord z.rep z.rep_nonzero
  have hdimR : R.affineCone.dimension = 1 := by
    simpa only [hd0, zero_add] using R.dimension_cone ⟨z, hz⟩
  have hline0 : (Bridges.complexLine 0 z.rep).dimension = 1 :=
    Bridges.complexLine_dimension 0 z.rep j hj
  have hLC : Bridges.complexLine 0 z.rep = R.affineCone :=
    curve_eq_of_subset _ _ hR hline0 hdimR (cone_contains_line R z hz)
  have hsub : Y.points ⊆ (Bridges.complexLine p z.rep).points := by
    intro x hx
    rw [Bridges.complexLine_points p z.rep j hj]
    by_cases hxp : x = p
    · exact ⟨0, by simp [hxp]⟩
    · have hxR : x-p ∈ R.affineCone.points :=
        (ProjectiveVariety.mem_points_mk_iff R (x-p) (sub_ne_zero.mpr hxp)).mp
          (radial_mem p Y x hx hxp)
      rw [← hLC, Bridges.complexLine_points 0 z.rep j hj] at hxR
      obtain ⟨t, ht⟩ := hxR
      simp only [zero_add] at ht
      refine ⟨t, ?_⟩
      calc
        x = (x-p)+p := by abel
        _ = p + t • z.rep := by rw [ht]; abel
  have he := curve_eq_of_subset Y (Bridges.complexLine p z.rep)
    (Bridges.complexLine_irreducible _ _) hY.2
    (Bridges.complexLine_dimension p z.rep j hj) hsub
  apply hnl
  refine ⟨p, z.rep, z.rep_nonzero, ?_⟩
  rw [he, Bridges.complexLine_points p z.rep j hj]

theorem projective_dimension_mono (V W : ProjectiveVariety d)
    (hV : V.IsIrreducible) (hW : W.IsIrreducible) (hVne : V.points.Nonempty)
    (hVW : V.points ⊆ W.points) : V.dimension ≤ W.dimension := by
  letI : V.ideal.IsPrime := hV
  letI : W.ideal.IsPrime := hW
  have h := OAI.QuarticPowerFree.affineDimension_antitone W.ideal V.ideal
    (projective_ideal_le V W hVW)
  change V.affineCone.dimension ≤ W.affineCone.dimension at h
  rw [V.dimension_cone hVne, W.dimension_cone (hVne.mono hVW)] at h
  omega

theorem radial_member (p : Pt d) (Y : AffineVariety d) (hY : IsCurve Y)
    (hnl : ¬ IsLine Y) (C : ProjectiveFamily.Family d) (hC : IsDirectionalFamily C)
    (hproj : ProjectsInto C p Y) :
    radialImage (toC p) Y ∈ C ∧ (radialImage (toC p) Y).dimension = 1 := by
  let R := radialImage (toC p) Y
  change R ∈ C ∧ R.dimension = 1
  have hR : R.IsIrreducible :=
    radialImage_irreducible _ _ hY.1 (curve_point_off _ Y hY)
  have hRne := radial_nonempty (toC p) Y hY
  obtain ⟨W, hWC, hRW⟩ := contained_member R hR C hproj
  have hW := hC W hWC
  have hle := projective_dimension_mono R W hR hW.1 hRne hRW
  have hne := radial_dimension_ne_zero (toC p) Y hY hnl
  change R.dimension ≠ 0 at hne
  have hdimR : R.dimension = 1 := by rw [hW.2.1] at hle; omega
  have he := projective_curve_eq_of_subset R W hW.1 hRne hdimR hW.2.1 hRW
  exact ⟨by rwa [he], hdimR⟩

end
end DistinctDistances.TrackD.GeoRadial
