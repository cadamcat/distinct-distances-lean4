import DistinctDistances.TrackD.GeoD4Scale
import DistinctDistances.Bridges.CurveInvariants

/-! Degree and linear equations of projective curves used by the d3 grouping. -/

namespace DistinctDistances.TrackD.GeoD3
open scoped BigOperators Classical
noncomputable section

 theorem radial_degree_unique (p : Point 3) (Y : AffineVariety 3) (hY : IsCurve Y)
    (r s : ℕ) (hr : GenericallyFiniteRadialDegree p Y r)
    (hs : GenericallyFiniteRadialDegree p Y s) : r = s := by
  let R := radialImage p Y
  have hR : R.IsIrreducible := radialImage_irreducible p Y hY.1
    (GeoRadial.curve_point_off p Y hY)
  obtain ⟨_, g, D, hg, hnotg, hfibg⟩ := hr
  obtain ⟨_, f, E, hf, hnotf, hfibf⟩ := hs
  have hprod : g*f ∉ R.ideal := by
    intro h
    exact (hR.mem_or_mem h).elim hnotg hnotf
  obtain ⟨z, hz, hzf⟩ := GeoRadial.homogeneous_witness R (g*f) (D+E) (hg.mul hf) hprod
  rw [map_mul] at hzf
  have hgz := (mul_ne_zero_iff.mp hzf).1
  have hfz := (mul_ne_zero_iff.mp hzf).2
  exact (hfibg z hz hgz).2.symm.trans (hfibf z hz hfz).2

 theorem projective_curve_degree_nat {d : ℕ} (R : ProjectiveVariety d)
    (hR : R.IsIrreducible) (hdim : R.dimension = 1) :
    ∃ a : ℕ, R.degree = (a : ℚ) := by
  have hdegree : R.degree = R.hilbertPolynomial.coeff 1 := by
    simp only [ProjectiveVariety.degree, OAI.PiExponentJets.W22.actualMultiplicity,
      hdim, Nat.factorial_one, Nat.cast_one, mul_one]
  rw [hdegree]
  obtain ⟨N, hN⟩ := R.hilbert_eventually
  apply Bridges.linearPolynomial_slope_nat R.hilbertPolynomial hdim.le
    (by rw [← hdegree, ← R.degree_cone]; exact (R.affineCone.one_le_degree hR.ne_top).trans' (by norm_num)) (N+1)
  intro t ht
  exact ⟨R.hilbert t, (hN t (by omega)).symm⟩

 theorem degree_ge_two_or_one {d : ℕ} (R : ProjectiveVariety d)
    (hR : R.IsIrreducible) (hdim : R.dimension = 1) :
    2 ≤ R.degree ∨ R.degree = 1 := by
  obtain ⟨a, ha⟩ := projective_curve_degree_nat R hR hdim
  have hone := R.affineCone.one_le_degree hR.ne_top
  rw [R.degree_cone, ha] at hone
  have ha1 : 1 ≤ a := by exact_mod_cast hone
  by_cases ha2 : 2 ≤ a
  · left; rw [ha]; exact_mod_cast ha2
  · right
    have haeq : a = 1 := by omega
    simpa only [haeq, Nat.cast_one] using ha

 def linearForm (c : Point 3) : Poly 3 := ∑ j : Fin 3, MvPolynomial.C (c j) * MvPolynomial.X j

 def linearEval (c : Point 3) : Point 3 →ₗ[ℂ] ℂ :=
   ∑ j : Fin 3, c j • LinearMap.proj j

 theorem eval_linearForm (c x : Point 3) : MvPolynomial.aeval x (linearForm c) = linearEval c x := by
   simp [linearForm, linearEval, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

 theorem degree_one_plane (R : ProjectiveVariety 3) (hR : R.IsIrreducible)
    (hdim : R.dimension = 1) (hdeg : R.degree = 1) :
    ∃ W : Submodule ℂ (Point 3), Module.finrank ℂ W ≤ 2 ∧
      ∀ z ∈ R.points, z.submodule ≤ W := by
  let L : Point 3 →ₗ[ℂ] Poly 3 :=
    ∑ j : Fin 3, (LinearMap.mulRight ℂ (MvPolynomial.X j)).comp
      ((Algebra.linearMap ℂ (Poly 3)).comp (LinearMap.proj j))
  have hL (c : Point 3) : L c = linearForm c := by
    simp [L, linearForm, LinearMap.sum_apply, LinearMap.comp_apply]
  let q := (Ideal.Quotient.mkₐ ℂ R.ideal).toLinearMap.comp L
  have hqle : LinearMap.range q ≤ R.restrictionSpace 1 := by
    rintro y ⟨c, rfl⟩
    refine ⟨linearForm c, ?_, ?_⟩
    · change (linearForm c).IsHomogeneous 1
      apply MvPolynomial.IsHomogeneous.sum
      intro j hj
      exact (MvPolynomial.isHomogeneous_C (Fin 3) (c j)).mul (MvPolynomial.isHomogeneous_X ℂ j)
    · exact congrArg (Ideal.Quotient.mk R.ideal) (hL c)
  have hupper : R.hilbert 1 ≤ 2 := by
    have hpure : ProjectiveFamily.IsPure {R} 1 := by
      intro V hV; simpa only [Finset.mem_singleton.mp hV] using And.intro hR hdim
    have hlocus : ProjectiveFamily.locus {R} = R := by
      apply ProjectiveVariety.ext
      have hset : (⋃ V ∈ ({R} : ProjectiveFamily.Family 3), V.points) = R.points := by
        ext z; simp
      change ProjectiveVariety.vanishingIdeal (⋃ V ∈ ({R} : ProjectiveFamily.Family 3), V.points) = R.ideal
      rw [hset]
      exact R.vanishingIdeal_points
    have h := TrackA.poly_hilbert_projective_upper {R} 1 hpure 1
    exact_mod_cast (by simpa [ProjectiveFamily.hilbert, hlocus,
      ProjectiveFamily.degree, hdeg] using h : (R.hilbert 1 : ℚ) ≤ 2)
  have hrank : Module.finrank ℂ (LinearMap.range q) ≤ 2 :=
    (Submodule.finrank_mono hqle).trans hupper
  have hkpos : 0 < Module.finrank ℂ (LinearMap.ker q) := by
    have he := q.finrank_range_add_finrank_ker
    have h3 : Module.finrank ℂ (Point 3) = 3 := GeoCommon.finrank_point 3
    rw [h3] at he
    omega
  obtain ⟨c, hc⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hkpos
  have hc0 : (c : Point 3) ≠ 0 := fun h => hc (Subtype.ext h)
  have hcI : linearForm c ∈ R.ideal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := c.property
    change q c = 0 at h
    change Ideal.Quotient.mk R.ideal (L c) = 0 at h
    rwa [hL] at h
  have hlin : linearEval c ≠ 0 := by
    intro hzero
    apply hc0
    funext j
    have he := congrArg (fun f : Point 3 →ₗ[ℂ] ℂ => f (Pi.single j 1)) hzero
    simpa [linearEval, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Pi.single_apply] using he
  let W := LinearMap.ker (linearEval c)
  have hWne : W ≠ ⊤ := by
    intro htop
    apply hlin
    exact LinearMap.ker_eq_top.mp htop
  have hWrank : Module.finrank ℂ W ≤ 2 := by
    have hlt := Submodule.finrank_lt hWne
    rw [GeoCommon.finrank_point 3] at hlt
    omega
  refine ⟨W, hWrank, ?_⟩
  intro z hz
  rw [Projectivization.submodule_eq]
  apply Submodule.span_le.mpr
  apply Set.singleton_subset_iff.mpr
  change linearEval c z.rep = 0
  rw [← eval_linearForm]
  exact hz z.rep z.rep_nonzero z.mk_rep _ hcI

 theorem degree_one_center_in_span (p : Pt 3) (Y : AffineVariety 3)
    (hY : IsCurve Y) (hnl : ¬ IsLine Y)
    (himage : (radialImage (toC p) Y).dimension = 1)
    (hdeg : (radialImage (toC p) Y).degree = 1) :
    Module.finrank ℂ (complexSpan Y).direction = 2 ∧ toC p ∈ complexSpan Y := by
  let R := radialImage (toC p) Y
  obtain ⟨W, hW, hrep⟩ := degree_one_plane R
    (radialImage_irreducible _ _ hY.1 (GeoRadial.curve_point_off _ Y hY)) himage hdeg
  let G := AffineSubspace.mk' (toC p) W
  have hYG : Y.points ⊆ G := GeoRadial.radial_subset_flat (toC p) Y W hrep
  have hSG : complexSpan Y ≤ G := affineSpan_le.mpr hYG
  have hdir : (complexSpan Y).direction ≤ G.direction := AffineSubspace.direction_le hSG
  have hle : Module.finrank ℂ (complexSpan Y).direction ≤ Module.finrank ℂ W := by
    have h : Module.finrank ℂ (complexSpan Y).direction ≤ Module.finrank ℂ G.direction :=
      Submodule.finrank_mono hdir
    dsimp only [G] at h
    rw [AffineSubspace.direction_mk'] at h
    exact h
  have hge := GeoRadial.nonlinear_span_ge_two Y hY hnl
  have hS2 : Module.finrank ℂ (complexSpan Y).direction = 2 := by omega
  have hGdim : Module.finrank ℂ G.direction = 2 := by
    dsimp only [G]
    rw [AffineSubspace.direction_mk']
    have hW2 : Module.finrank ℂ W = 2 := by omega
    exact hW2
  have hdirs : (complexSpan Y).direction = G.direction :=
    Submodule.eq_of_le_of_finrank_eq hdir (hS2.trans hGdim.symm)
  have hSne := (Bridges.curve_points_infinite Y hY.1 hY.2).nonempty.mono (subset_affineSpan ℂ _)
  have heq := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdirs hSne hSG
  refine ⟨hS2, ?_⟩
  rw [heq]
  exact AffineSubspace.self_mem_mk' _ _

end
end DistinctDistances.TrackD.GeoD3
