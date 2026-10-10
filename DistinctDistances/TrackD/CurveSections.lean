import DistinctDistances.TrackA.Intersections
import DistinctDistances.TrackD.SecantsSpan

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

variable {d : ℕ}

/-- The finite component family has the same reduced locus as its carrier. -/
theorem component_family_locus (V : AffineVariety d) :
    AffineFamily.locus (Finset.univ.image (fun W : V.Component => W.variety)) = V := by
  apply (AffineVariety.points_eq_iff _ _).mp
  rw [AffineFamily.points_locus, AffineVariety.points_components V]
  ext x
  simp

/-- A proper polynomial section of an irreducible curve is finite, with the
degree budget of `FA.bezout`; only frozen track-A interfaces enter this wrapper. -/
theorem proper_curve_section (Y : AffineVariety d) (hY : IsCurve Y)
    (f : Poly d) (hf : f ∉ Y.ideal) :
    (Y.cut f).points.Finite ∧
      ((Y.cut f).points.ncard : ℚ) ≤ (f.totalDegree : ℚ) * Y.degree := by
  let V := Y.cut f
  have hcomponent (W : V.Component) : W.variety.IsComponentOf
      (Y.ideal ⊔ Ideal.span {f}) := by
    change W.val ∈ (Y.ideal ⊔ Ideal.span {f}).minimalPrimes
    simpa only [AffineVariety.IsComponentOf, V, AffineVariety.cut,
      AffineVariety.ofIdeal, Ideal.radical_minimalPrimes] using W.property
  have hpure : V.IsPure 0 := by
    intro W
    exact TrackA.fa_bezout_proper_dimension Y W.variety hY.1 f hf
      (hcomponent W) 0 hY.2
  obtain ⟨hfin, hcard⟩ := TrackA.fa_bezout_zero_dimensional V hpure
  let F : AffineFamily.Family d := Finset.univ.image (fun W : V.Component => W.variety)
  have hF : AffineFamily.IsPure F 0 := by
    intro W hW
    obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hW
    exact ⟨A.irreducible, hpure A⟩
  have hFc : ∀ W ∈ F, W.IsComponentOf (Y.ideal ⊔ Ideal.span {f}) := by
    intro W hW
    obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hW
    exact hcomponent A
  have hdegree : V.degree = AffineFamily.degree F := by
    have heq : AffineFamily.locus F = V := component_family_locus V
    rw [← heq]
    exact AffineFamily.degree_locus F 0 hF
  refine ⟨hfin, ?_⟩
  rw [hcard, hdegree]
  exact TrackA.fa_bezout_proper_degree Y hY.1 f hf F hFc 0 hY.2

theorem covectorPoly_degree_le_one (f : Point d →ₗ[ℂ] ℂ) (y : Point d) :
    (covectorPoly f y).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_sub_C_le _ _).trans
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

/-- An affine line in the plane is the zero set of one affine linear equation. -/
theorem planar_line_equation (L : AffineSubspace ℂ (Point 2))
    (hL : Module.finrank ℂ L.direction = 1) :
    ∃ f : Poly 2, f.totalDegree ≤ 1 ∧
      ∀ x : Point 2, MvPolynomial.eval x f = 0 ↔ x ∈ L := by
  have hne : (L : Set (Point 2)).Nonempty := by
    apply L.nonempty_iff_ne_bot.mpr
    intro h
    rw [h, AffineSubspace.direction_bot, finrank_bot] at hL
    norm_num at hL
  obtain ⟨y, hy⟩ := hne
  have htop : L.direction ≠ ⊤ := by
    intro h
    rw [h, finrank_top] at hL
    norm_num [Point] at hL
  have hex : ∃ w : Point 2, w ∉ L.direction := by
    by_contra h
    push Not at h
    apply htop
    exact top_unique (fun w _ => h w)
  obtain ⟨w, hw⟩ := hex
  obtain ⟨lam, hlam, hmap⟩ := L.direction.exists_dual_map_eq_bot_of_notMem hw inferInstance
  have hzero : ∀ u ∈ L.direction, lam u = 0 := by
    intro u hu
    have hm : lam u ∈ L.direction.map lam := Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    simpa only [hmap, Submodule.mem_bot] using hm
  have hlam0 : lam ≠ 0 := by
    intro h
    simpa [h] using hlam
  have hdimker : Module.finrank ℂ (LinearMap.ker lam) = 1 := by
    have h : Module.finrank ℂ (LinearMap.ker lam) + 1 = 2 := by
      simpa [Point] using Module.Dual.finrank_ker_add_one_of_ne_zero hlam0
    omega
  have hker : L.direction = LinearMap.ker lam :=
    Submodule.eq_of_le_of_finrank_eq (fun u hu => hzero u hu) (hL.trans hdimker.symm)
  refine ⟨covectorPoly lam y, covectorPoly_degree_le_one lam y, ?_⟩
  intro x
  rw [eval_covectorPoly]
  change x - y ∈ LinearMap.ker lam ↔ x ∈ L
  rw [← hker]
  exact AffineSubspace.vsub_right_mem_direction_iff_mem hy x

/-- `secants.tex:351–367`: the constant in the planar curve–line bound is one. -/
theorem planar_curve_line_intersection (Y : AffineVariety 2) (hY : IsCurve Y)
    (L : AffineSubspace ℂ (Point 2)) (hL : Module.finrank ℂ L.direction = 1)
    (hproper : ¬ Y.points ⊆ L) :
    (Y.points ∩ (L : Set (Point 2))).Finite ∧
      ((Y.points ∩ (L : Set (Point 2))).ncard : ℝ) ≤ (Y.degree : ℝ) := by
  obtain ⟨f, hdegree, hline⟩ := planar_line_equation L hL
  have hf : f ∉ Y.ideal := by
    intro hf
    apply hproper
    intro x hx
    exact (hline x).mp ((mem_ideal_iff_eval_zero Y f).mp hf x hx)
  have heq : (Y.cut f).points = Y.points ∩ (L : Set (Point 2)) := by
    ext x
    rw [AffineVariety.cut, AffineVariety.points_ofIdeal]
    constructor
    · intro hx
      refine ⟨fun g hg => hx g (Ideal.mem_sup_left hg), (hline x).mp ?_⟩
      exact hx f (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton f)))
    · rintro ⟨hx, hxL⟩ g hg
      have hI : Y.ideal ⊔ Ideal.span {f} ≤
          MvPolynomial.vanishingIdeal ℂ {x} := by
        apply sup_le
        · intro a ha z hz
          have hz' : z = x := Set.mem_singleton_iff.mp hz
          subst z
          exact hx a ha
        · apply Ideal.span_le.mpr
          intro a ha z hz
          have ha' : a = f := Set.mem_singleton_iff.mp ha
          subst a
          have hz' : z = x := Set.mem_singleton_iff.mp hz
          subst z
          exact (hline x).mpr hxL
      exact hI hg x (Set.mem_singleton x)
  obtain ⟨hfin, hcard⟩ := proper_curve_section Y hY f hf
  rw [heq] at hfin hcard
  refine ⟨hfin, ?_⟩
  have hnonneg : 0 ≤ Y.degree := (Y.one_le_degree hY.1.ne_top).trans' (by norm_num)
  have hbound : ((Y.points ∩ (L : Set (Point 2))).ncard : ℚ) ≤ Y.degree := by
    apply hcard.trans
    have hdegQ : (f.totalDegree : ℚ) ≤ 1 := by exact_mod_cast hdegree
    simpa using mul_le_mul_of_nonneg_right hdegQ hnonneg
  exact_mod_cast hbound

end
end DistinctDistances.TrackD
