import DistinctDistances.TrackD.TripleProjectionData
import DistinctDistances.TrackD.TripleNonlinearity
import DistinctDistances.TrackD.GeoD3Degree
import DistinctDistances.TrackB.UniformCompletion
import DistinctDistances.Bridges.AmbientHilbert
import DistinctDistances.TrackD.RationalContainment
import DistinctDistances.TrackD.Secants
import DistinctDistances.TrackD.GeoSliceArrangement
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import DistinctDistances.TrackA.ProjectiveChartRankSupport

/-! Generic projection geometry for the two m-d-geo declarations. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

/-- A projective plane curve with a nonzero linear equation has degree at
most one. The affine cone is a component of the linear cut of affine space. -/
theorem projective_plane_curve_degree_le_one_of_linear_equation
    (C : ProjectiveVariety 3) (hC : C.IsIrreducible)
    (hdim : C.dimension = 1) (hne : C.points.Nonempty)
    (f : Poly 3) (hf : f ≠ 0) (hdeg : f.totalDegree ≤ 1) (hmem : f ∈ C.ideal) :
    C.degree ≤ 1 := by
  letI : C.ideal.IsPrime := hC
  let V : AffineVariety 3 := AffineVariety.whole
  have hVI : V.ideal = ⊥ := by
    exact Ideal.radical_bot_of_isReduced
  have hV : V.IsIrreducible := by
    change V.ideal.IsPrime
    rw [hVI]
    infer_instance
  have hVdim : V.dimension = 2 + 1 := Bridges.affine_whole_dimension 3
  have hnot : f ∉ V.ideal := by simpa only [hVI, Ideal.mem_bot] using hf
  have hle : V.ideal ⊔ Ideal.span {f} ≤ C.ideal := by
    rw [hVI, bot_sup_eq]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  obtain ⟨J, hJ, hJC⟩ := Ideal.exists_minimalPrimes_le hle
  let W : AffineVariety 3 := ⟨J, hJ.isPrime.isRadical⟩
  have hWdim : W.dimension = 2 :=
    TrackA.fa_bezout_proper_dimension V W hV f hnot hJ 2 hVdim
  have hcone : C.affineCone.dimension = 2 := by
    rw [C.dimension_cone hne, hdim]
  letI : J.IsPrime := hJ.isPrime
  have heq : J = C.ideal :=
    OAI.QuarticPowerFree.prime_same_dimension_eq J C.ideal hJC hWdim hcone
  have hcomp : C.affineCone.IsComponentOf (V.ideal ⊔ Ideal.span {f}) := by
    change C.ideal ∈ _
    rwa [← heq]
  have hbound := TrackA.fa_bezout_proper_degree V hV f hnot {C.affineCone}
    (by intro Z hZ; simpa only [Finset.mem_singleton.mp hZ] using hcomp) 2 hVdim
  have hbound' : C.degree ≤ (f.totalDegree : ℚ) := by
    simpa only [AffineFamily.degree, Finset.sum_singleton, C.degree_cone,
      V, TrackB.whole_degree, mul_one] using hbound
  exact hbound'.trans (by exact_mod_cast hdeg)

theorem covectorPoly_zero_totalDegree_le {d : ℕ} (lam : Point d →ₗ[ℂ] ℂ) :
    (covectorPoly lam 0).totalDegree ≤ 1 := by
  simp only [covectorPoly, map_zero, MvPolynomial.C_0, sub_zero]
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro j hj
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp

/-- A curve lying in a plane projects to a line from any centre in that
plane (`secants.tex:450–457`). -/
theorem radial_curve_degree_le_one_of_plane
    (p : Point 3) (Y : AffineVariety 3) (hY : IsCurve Y)
    (F : AffineSubspace ℂ (Point 3)) (hF : Module.finrank ℂ F.direction ≤ 2)
    (hYF : Y.points ⊆ F) (hpF : p ∈ F)
    (hdim : (radialImage p Y).dimension = 1) : (radialImage p Y).degree ≤ 1 := by
  have hproper : F.direction ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, GeoCommon.finrank_point] at hF
    omega
  obtain ⟨a, _, ha⟩ := SetLike.exists_of_lt
    (lt_top_iff_ne_top.mpr hproper)
  obtain ⟨lam, hlam, hmap⟩ := F.direction.exists_dual_map_eq_bot_of_notMem ha inferInstance
  have hzero : ∀ u ∈ F.direction, lam u = 0 := by
    intro u hu
    have h : lam u ∈ F.direction.map lam := Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    simpa only [hmap, Submodule.mem_bot] using h
  let f := covectorPoly lam 0
  have hf : f ≠ 0 := by
    intro h
    apply hlam
    have he : MvPolynomial.eval a f = 0 := by rw [h]; simp
    simpa only [f, eval_covectorPoly, sub_zero] using he
  have hmem : f ∈ (radialImage p Y).ideal := by
    rintro u ⟨hu, x, hx, hxp, hxproj⟩
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ u (x-p) hu
      (sub_ne_zero.mpr hxp)).mp hxproj.symm
    change MvPolynomial.aeval u f = 0
    change MvPolynomial.eval u (covectorPoly lam 0) = 0
    rw [eval_covectorPoly, sub_zero, ← hc, map_smul]
    rw [hzero (x-p) (AffineSubspace.vsub_mem_direction (hYF hx) hpF)]
    simp
  exact projective_plane_curve_degree_le_one_of_linear_equation (radialImage p Y)
    (radialImage_irreducible p Y hY.1 (GeoRadial.curve_point_off p Y hY))
    hdim (GeoRadial.radial_nonempty p Y hY) f hf
    (covectorPoly_zero_totalDegree_le lam) hmem

/-- Projection from outside a containing flat has generic degree one. -/
theorem radialMapDegree_eq_one_of_exterior_flat {d : ℕ}
    (p : Point d) (Y : AffineVariety d) (hY : IsCurve Y)
    (F : AffineSubspace ℂ (Point d)) (hYF : Y.points ⊆ F) (hpF : p ∉ F)
    (hdim : (radialImage p Y).dimension = 1) : radialMapDegree p Y = 1 := by
  have hA := TrackA.dep_radial_degree_exists Y hY.1 1 (by norm_num) hY.2 p hdim
  have hex : ∃ r, GenericallyFiniteRadialDegree p Y r := ⟨_, hA⟩
  have hD : GenericallyFiniteRadialDegree p Y (radialMapDegree p Y) := by
    unfold radialMapDegree
    rw [dif_pos hex]
    exact Nat.find_spec hex
  obtain ⟨hr, g, D, hg, hnot, hfib⟩ := hD
  obtain ⟨z, hz, hgz⟩ := GeoRadial.homogeneous_witness (radialImage p Y) g D hg hnot
  obtain ⟨hfinite, hcard⟩ := hfib z hz hgz
  have hle : (radialFiber p Y z).ncard ≤ 1 :=
    (Set.ncard_le_one hfinite).mpr (GeoRadial.radial_fiber_subsingleton F p Y hYF hpF z)
  omega

/-- A valid triple's nonlinear common image excludes a centre lying in
any containing plane of any member. -/
theorem curveTripleValid_center_not_mem_plane
    (p : Point 3) (Y₁ Y₂ Y₃ Y : AffineVariety 3)
    (hv : CurveTripleValid p Y₁ Y₂ Y₃) (hY : IsCurve Y)
    (hmem : Y ∈ ({Y₁, Y₂, Y₃} : Finset _))
    (F : AffineSubspace ℂ (Point 3)) (hF : Module.finrank ℂ F.direction ≤ 2)
    (hYF : Y.points ⊆ F) : p ∉ F := by
  have hEq : radialImage p Y = radialImage p Y₁ := by
    have hm : Y = Y₁ ∨ Y = Y₂ ∨ Y = Y₃ := by simpa using hmem
    rcases hm with rfl | rfl | rfl
    · rfl
    · exact hv.1.symm
    · exact hv.2.1.symm
  intro hpF
  have h := radial_curve_degree_le_one_of_plane p Y hY F hF hYF hpF
    (by rw [hEq]; exact hv.2.2.1)
  rw [hEq] at h
  have hge := hv.2.2.2.1
  linarith

/-- A repeated first index in a valid triple cannot be planar: outside
its plane the map degree is one, while validity requires at least two. -/
theorem curveTripleValid_repeated_source_not_planar
    (p : Point 3) (X Z : AffineVariety 3) (hX : IsCurve X)
    (hv : CurveTripleValid p X X Z)
    (F : AffineSubspace ℂ (Point 3)) (hF : Module.finrank ℂ F.direction ≤ 2) :
    ¬ X.points ⊆ F := by
  intro hXF
  have hpF := curveTripleValid_center_not_mem_plane p X X Z X hv hX (by simp) F hF hXF
  have hdeg := radialMapDegree_eq_one_of_exterior_flat p X hX F hXF hpF hv.2.2.1
  have hcount := hv.2.2.2.2.2 X (by simp)
  simp only [ite_true, eq_self] at hcount
  rw [hdeg] at hcount
  split_ifs at hcount <;> omega

theorem covectorPoly_zero_homogeneous {d : ℕ} (lam : Point d →ₗ[ℂ] ℂ) :
    (covectorPoly lam 0).IsHomogeneous 1 := by
  simp only [covectorPoly, map_zero, MvPolynomial.C_0, sub_zero]
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  exact (MvPolynomial.isHomogeneous_C (Fin d) (lam (Pi.single j 1))).mul
    (MvPolynomial.isHomogeneous_X ℂ j)

def radialRecoveryForms {d : ℕ} (p : Point d) (lam : Point d →ₗ[ℂ] ℂ) : Fin d → Poly d :=
  fun j => MvPolynomial.C (p j) * covectorPoly lam 0 + MvPolynomial.X j

theorem radialRecoveryNumerator_homogeneous {d : ℕ}
    (p : Point d) (lam : Point d →ₗ[ℂ] ℂ) (q : Poly d) :
    (rationalNumerator (radialRecoveryForms p lam) (covectorPoly lam 0) q).IsHomogeneous
      q.totalDegree := by
  have hforms : ∀ j : Option (Fin d),
      (j.elim (covectorPoly lam 0) (radialRecoveryForms p lam)).IsHomogeneous 1 := by
    intro j
    cases j with
    | none => exact covectorPoly_zero_homogeneous lam
    | some j =>
      exact ((MvPolynomial.isHomogeneous_C (Fin d) (p j)).mul
        (covectorPoly_zero_homogeneous lam)).add (MvPolynomial.isHomogeneous_X ℂ j)
  simpa only [rationalNumerator, one_mul] using
    (OAI.PiExponentJets.W22.homogenize_isHomogeneous q).aeval _ hforms

theorem radialRecoveryNumerator_eval {d : ℕ}
    (p x : Point d) (lam : Point d →ₗ[ℂ] ℂ) (h : lam (x-p) = 1) (q : Poly d) :
    MvPolynomial.eval (x-p)
      (rationalNumerator (radialRecoveryForms p lam) (covectorPoly lam 0) q) =
        MvPolynomial.eval x q := by
  have hden : MvPolynomial.eval (x-p) (covectorPoly lam 0) = 1 := by
    simpa using h
  rw [rationalNumerator_eval _ _ _ _ (by rw [hden]; exact one_ne_zero), hden, one_pow, one_mul]
  have hpoint : rationalPoint (radialRecoveryForms p lam) (covectorPoly lam 0) (x-p) = x := by
    ext j
    simp [rationalPoint, radialRecoveryForms, hden]
  rw [hpoint]

/-- A covector normalizes every direction from an exterior centre to a
containing flat; polynomial equations can then be recovered from directions. -/
theorem exterior_flat_normalizing_covector {d : ℕ}
    (F : AffineSubspace ℂ (Point d)) (hF : (F : Set (Point d)).Nonempty)
    (p : Point d) (hp : p ∉ F) :
    ∃ lam : Point d →ₗ[ℂ] ℂ, ∀ x ∈ F, lam (x-p) = 1 := by
  obtain ⟨a, ha⟩ := hF
  have hap : a-p ∉ F.direction := by
    intro h
    have hpa : p-a ∈ F.direction := by simpa only [neg_sub] using F.direction.neg_mem h
    exact hp ((AffineSubspace.vsub_right_mem_direction_iff_mem ha p).mp hpa)
  obtain ⟨lam, hlam, hmap⟩ := F.direction.exists_dual_map_eq_bot_of_notMem hap inferInstance
  refine ⟨(lam (a-p))⁻¹ • lam, ?_⟩
  intro x hx
  have hxa : lam (x-a) = 0 := by
    have h : lam (x-a) ∈ F.direction.map lam := Submodule.mem_map.mpr
      ⟨x-a, AffineSubspace.vsub_mem_direction hx ha, rfl⟩
    simpa only [hmap, Submodule.mem_bot] using h
  change (lam (a-p))⁻¹ * lam (x-p) = 1
  rw [show x-p = (x-a)+(a-p) by abel, map_add, hxa, zero_add, inv_mul_cancel₀ hlam]

theorem radialRecoveryNumerator_mem_image {d : ℕ}
    (p : Point d) (Y : AffineVariety d) (lam : Point d →ₗ[ℂ] ℂ)
    (hnorm : ∀ x ∈ Y.points, lam (x-p) = 1) (q : Poly d) (hq : q ∈ Y.ideal) :
    rationalNumerator (radialRecoveryForms p lam) (covectorPoly lam 0) q ∈
      (radialImage p Y).ideal := by
  rintro u ⟨hu, x, hx, hxp, hxproj⟩
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ u (x-p) hu
    (sub_ne_zero.mpr hxp)).mp hxproj.symm
  change MvPolynomial.aeval u _ = 0
  rw [MvPolynomial.aeval_eq_eval, ← hc,
    Bridges.homogeneous_eval_smul _ (radialRecoveryNumerator_homogeneous p lam q),
    radialRecoveryNumerator_eval p x lam (hnorm x hx) q]
  have heval : MvPolynomial.eval x q = 0 := hx q hq
  rw [heval, mul_zero]

/-- On one flat, radial projection from outside the flat determines the
entire reduced carrier, including its Zariski closure. -/
theorem radialImage_injective_on_exterior_flat {d : ℕ}
    (p : Point d) (X Y : AffineVariety d) (F : AffineSubspace ℂ (Point d))
    (hF : (F : Set (Point d)).Nonempty) (hp : p ∉ F)
    (hXF : X.points ⊆ F) (hYF : Y.points ⊆ F)
    (hEq : radialImage p X = radialImage p Y) : X = Y := by
  obtain ⟨lam, hlam⟩ := exterior_flat_normalizing_covector F hF p hp
  have hsub (A B : AffineVariety d) (hAF : A.points ⊆ F) (hBF : B.points ⊆ F)
      (hAB : radialImage p A = radialImage p B) : A.points ⊆ B.points := by
    intro x hx q hq
    have hxp : x ≠ p := by intro he; exact hp (he ▸ hAF hx)
    have hnum := radialRecoveryNumerator_mem_image p B lam
      (fun x hx => hlam x (hBF hx)) q hq
    have hdir : radialProjection p x hxp ∈ (radialImage p B).points := by
      rw [← hAB]
      exact GeoRadial.radial_mem p A x hx hxp
    have hz := hdir (x-p) (sub_ne_zero.mpr hxp) rfl _ hnum
    change MvPolynomial.aeval (x-p) _ = 0 at hz
    rw [MvPolynomial.aeval_eq_eval, radialRecoveryNumerator_eval p x lam (hlam x (hAF hx)) q] at hz
    exact hz
  apply AffineVariety.ext
  exact le_antisymm
    ((AffineVariety.subvariety_iff_points_subset Y X).mpr (hsub Y X hYF hXF hEq.symm))
    ((AffineVariety.subvariety_iff_points_subset X Y).mpr (hsub X Y hXF hYF hEq))

/-- Distinct members of a valid triple cannot lie in a common plane.
At an interior centre their common image is linear; at an exterior
centre equality of images would identify the two original curves. -/
theorem curveTripleValid_distinct_not_common_plane
    (p : Point 3) (Y₁ Y₂ Y₃ X Y : AffineVariety 3)
    (hv : CurveTripleValid p Y₁ Y₂ Y₃) (hX : IsCurve X) (hY : IsCurve Y)
    (hXm : X ∈ ({Y₁, Y₂, Y₃} : Finset _)) (hYm : Y ∈ ({Y₁, Y₂, Y₃} : Finset _))
    (hne : X ≠ Y) (F : AffineSubspace ℂ (Point 3))
    (hF : Module.finrank ℂ F.direction ≤ 2) : ¬ (X.points ⊆ F ∧ Y.points ⊆ F) := by
  rintro ⟨hXF, hYF⟩
  have hpF := curveTripleValid_center_not_mem_plane p Y₁ Y₂ Y₃ X hv hX hXm F hF hXF
  have hFne : (F : Set (Point 3)).Nonempty :=
    (X.points_nonempty_of_isIrreducible hX.1).mono hXF
  have hEq (Z : AffineVariety 3) (hZm : Z ∈ ({Y₁, Y₂, Y₃} : Finset _)) :
      radialImage p Z = radialImage p Y₁ := by
    have hm : Z = Y₁ ∨ Z = Y₂ ∨ Z = Y₃ := by simpa using hZm
    rcases hm with rfl | rfl | rfl
    · rfl
    · exact hv.1.symm
    · exact hv.2.1.symm
  exact hne (radialImage_injective_on_exterior_flat p X Y F hFne hpF hXF hYF
    ((hEq X hXm).trans (hEq Y hYm).symm))

theorem curveTripleValid_source_target_not_common_plane
    (p : Point 3) (Y₁ Y₂ Y₃ Y : AffineVariety 3)
    (hv : CurveTripleValid p Y₁ Y₂ Y₃) (hY₁ : IsCurve Y₁) (hY : IsCurve Y)
    (hYm : Y ∈ ({Y₂, Y₃} : Finset _))
    (F : AffineSubspace ℂ (Point 3)) (hF : Module.finrank ℂ F.direction ≤ 2) :
    ¬ (Y₁.points ⊆ F ∧ Y.points ⊆ F) := by
  have hm : Y = Y₂ ∨ Y = Y₃ := by simpa using hYm
  have hYall : Y ∈ ({Y₁, Y₂, Y₃} : Finset _) := by
    rcases hm with rfl | rfl <;> simp
  by_cases hEq : Y₁ = Y
  · rintro ⟨h₁F, hYF⟩
    have hpF := curveTripleValid_center_not_mem_plane p Y₁ Y₂ Y₃ Y₁ hv hY₁
      (by simp) F hF h₁F
    have hdeg := radialMapDegree_eq_one_of_exterior_flat p Y₁ hY₁ F h₁F hpF hv.2.2.1
    have hcount := hv.2.2.2.2.2 Y₁ (by simp)
    rw [hdeg] at hcount
    rcases hm with rfl | rfl
    · simp only [hEq, eq_self, ite_true] at hcount
      split_ifs at hcount <;> omega
    · simp only [hEq, eq_self, ite_true] at hcount
      split_ifs at hcount <;> omega
  · exact curveTripleValid_distinct_not_common_plane p Y₁ Y₂ Y₃ Y₁ Y hv hY₁ hY
      (by simp) hYall hEq F hF

/-- The secant lemma rules out a *generic* further root for either target
once one valid original centre is available. The constructible-locus
step that turns this into a generic absence statement is separate. -/
theorem curveTripleValid_not_generic_further_root
    (p : Point 3) (Y₁ Y₂ Y₃ Y Z : AffineVariety 3)
    (hv : CurveTripleValid p Y₁ Y₂ Y₃)
    (hY₁ : IsCurve Y₁) (hY : IsCurve Y) (hZ : IsCurve Z)
    (hnl₁ : ¬ IsLine Y₁) (hnlY : ¬ IsLine Y)
    (hYm : Y ∈ ({Y₂, Y₃} : Finset _)) :
    ¬ ForGeneralPair Y₁ Y (fun v y =>
      ∃ z ∈ Z, z ≠ v ∧ z ≠ y ∧ ∃ c : ℂ, z-v = c • (y-v)) := by
  intro hroot
  have htrans := nonlinear_curves_generic_nontangency Y₁ Y hY₁ hY hnl₁ hnlY
  obtain ⟨_, hcommon⟩ := geo_secants_further_root Y₁ Y Z 1 1
    hY₁.1 hY.1 hZ.1 hY₁.2 hY.2 hZ.2 (by norm_num) (by norm_num) htrans hroot
  obtain ⟨F, hF, h₁F, hYF⟩ := hcommon rfl
  exact curveTripleValid_source_target_not_common_plane p Y₁ Y₂ Y₃ Y hv hY₁ hY hYm
    F hF ⟨h₁F, hYF⟩

namespace FiniteFlatSlice

open GeoSlice

variable {d : ℕ}

/-- An intersection with a flat not containing `F` has smaller dimension
than the positive-dimensional flat `F`. -/
theorem intersection_rank_lt_of_not_le (F G : AffineSubspace ℝ (Pt d))
    (r : ℕ) (hr : 0 < r) (hF : Module.finrank ℝ F.direction = r)
    (hFG : ¬ F ≤ G) : Module.finrank ℝ (F ⊓ G).direction < r := by
  by_cases hne : ((F ⊓ G : AffineSubspace ℝ (Pt d)) : Set (Pt d)).Nonempty
  · have hle : (F ⊓ G).direction ≤ F.direction := AffineSubspace.direction_le inf_le_left
    have hdim := Submodule.finrank_mono hle
    rw [hF] at hdim
    by_contra! hn
    have he : Module.finrank ℝ (F ⊓ G).direction = r := le_antisymm hdim hn
    have hdir := Submodule.eq_of_le_of_finrank_eq hle (he.trans hF.symm)
    have heq := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir hne inf_le_left
    exact hFG (heq ▸ inf_le_right)
  · have hs : ((F ⊓ G : AffineSubspace ℝ (Pt d)) : Set (Pt d)).Subsingleton := by
      rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact Set.subsingleton_empty
    rw [AffineSubspace.direction_eq_bot_iff.mpr hs, finrank_bot]
    exact hr

/-- One generic hyperplane cuts every positive-dimensional flat of a
finite arrangement and avoids every zero-dimensional flat. -/
theorem exists_one_slice (hd : 0 < d) (A : Finset (AffineSubspace ℝ (Pt d))) :
    ∃ K : AffineSubspace ℝ (Pt d), ∀ F ∈ A,
      (((F ⊓ K : AffineSubspace ℝ (Pt d)) : Set (Pt d)).Nonempty ↔
        (F : Set (Pt d)).Nonempty ∧ 0 < Module.finrank ℝ F.direction) ∧
      Module.finrank ℝ (F ⊓ K).direction = Module.finrank ℝ F.direction - 1 := by
  let D := insert (⊤ : Submodule ℝ (Pt d)) (A.image AffineSubspace.direction)
  obtain ⟨φ, hφ⟩ := finite_functional D
  have htop : (⊤ : Submodule ℝ (Pt d)) ≠ ⊥ := by
    intro he
    have hdim := congrArg (fun W : Submodule ℝ (Pt d) => Module.finrank ℝ W) he
    simp only [finrank_top, finrank_bot, Pt, finrank_euclideanSpace, Fintype.card_fin] at hdim
    omega
  have hφne : φ ≠ 0 := by
    obtain ⟨v, _, hv⟩ := hφ ⊤ (Finset.mem_insert_self _ _) htop
    intro he
    exact hv (by rw [he]; rfl)
  obtain ⟨u, hu⟩ := LinearMap.surjective hφne (1 : ℝ)
  let Z := A.filter (fun F : AffineSubspace ℝ (Pt d) => Module.finrank ℝ F.direction = 0 ∧
    (F : Set (Pt d)).Nonempty)
  obtain ⟨t, ht⟩ := (Z.image (fun F => φ (point F))).exists_notMem
  refine ⟨level φ t u, ?_⟩
  intro F hF
  by_cases hr : 0 < Module.finrank ℝ F.direction
  · have hdir : F.direction ≠ ⊥ := by
      intro he
      rw [he, finrank_bot] at hr
      omega
    have hw : ∃ v ∈ F.direction, φ v ≠ 0 :=
      hφ F.direction (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hF)) hdir
    have hne := slice_nonempty φ t u hu F (affine_nonempty F hdir) hw
    refine ⟨⟨fun _ => ⟨affine_nonempty F hdir, hr⟩, fun _ => hne⟩, ?_⟩
    rw [slice_direction φ t u F hne]
    have hdim := inf_ker_rank φ F.direction hw
    omega
  · have hz : Module.finrank ℝ F.direction = 0 := by omega
    have hsub : (F : Set (Pt d)).Subsingleton :=
      AffineSubspace.direction_eq_bot_iff.mp (Submodule.finrank_eq_zero.mp hz)
    have hn : ¬ ((F ⊓ level φ t u : AffineSubspace ℝ (Pt d)) : Set (Pt d)).Nonempty := by
      rintro ⟨x, hx⟩
      have hFne : (F : Set (Pt d)).Nonempty := ⟨x, hx.1⟩
      have hp : point F = x := hsub (point_mem F hFne) hx.1
      apply ht
      exact Finset.mem_image.mpr ⟨F, Finset.mem_filter.mpr ⟨hF, hz, hFne⟩,
        by rw [hp]; exact (level_mem φ t u hu x).mp hx.2⟩
    refine ⟨by simp only [hn, false_iff]; intro h; exact hr h.2, ?_⟩
    have hs : ((F ⊓ level φ t u : AffineSubspace ℝ (Pt d)) : Set (Pt d)).Subsingleton :=
      fun _ hx _ hy => hsub hx.1 hy.1
    rw [AffineSubspace.direction_eq_bot_iff.mpr hs, finrank_bot, hz]

/-- A common slice realizes the expected dimensions of every member of
a finite real affine arrangement. -/
theorem exists_slice (hd : 0 < d) (A : Finset (AffineSubspace ℝ (Pt d))) (n : ℕ) :
    ∃ K : AffineSubspace ℝ (Pt d), ∀ F ∈ A,
      (((F ⊓ K : AffineSubspace ℝ (Pt d)) : Set (Pt d)).Nonempty ↔
        (F : Set (Pt d)).Nonempty ∧ n ≤ Module.finrank ℝ F.direction) ∧
      Module.finrank ℝ (F ⊓ K).direction = Module.finrank ℝ F.direction - n := by
  induction n with
  | zero =>
      refine ⟨⊤, ?_⟩
      intro F hF
      have he : F ⊓ (⊤ : AffineSubspace ℝ (Pt d)) = F := inf_top_eq F
      rw [he]
      simp
  | succ n ih =>
      obtain ⟨K, hK⟩ := ih
      obtain ⟨J, hJ⟩ := exists_one_slice hd (A.image (fun F => F ⊓ K))
      refine ⟨K ⊓ J, ?_⟩
      intro F hF
      have hprev := hK F hF
      have hnext := hJ (F ⊓ K) (Finset.mem_image_of_mem _ hF)
      rw [inf_assoc] at hnext
      refine ⟨?_, ?_⟩
      · rw [hnext.1, hprev.1, hprev.2]
        constructor
        · rintro ⟨⟨hne, hdim⟩, hpos⟩
          exact ⟨hne, by omega⟩
        · rintro ⟨hne, hdim⟩
          exact ⟨⟨hne, by omega⟩, by omega⟩
      · rw [hnext.2, hprev.2]
        omega

/-- A finite arrangement enlarged by every pairwise intersection. -/
def intersectionArrangement (A : Finset (AffineSubspace ℝ (Pt d))) :
    Finset (AffineSubspace ℝ (Pt d)) :=
  A ∪ (A ×ˢ A).image (fun FG => FG.1 ⊓ FG.2)

theorem mem_intersectionArrangement (A : Finset (AffineSubspace ℝ (Pt d)))
    (F : AffineSubspace ℝ (Pt d)) (hF : F ∈ A) : F ∈ intersectionArrangement A :=
  Finset.mem_union_left _ hF

theorem inf_mem_intersectionArrangement (A : Finset (AffineSubspace ℝ (Pt d)))
    (F G : AffineSubspace ℝ (Pt d)) (hF : F ∈ A) (hG : G ∈ A) :
    F ⊓ G ∈ intersectionArrangement A :=
  Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨(F, G), Finset.mem_product.mpr ⟨hF, hG⟩, rfl⟩)

/-- Slicing a finite family of `k`-flats and `(k+1)`-flats preserves
distinctness and reflects every containment as a point-line incidence. -/
theorem exists_point_line_representation (hd : 0 < d) (k : ℕ) (hk : 0 < k)
    (L H : Finset (AffineSubspace ℝ (Pt d)))
    (hL : ∀ F ∈ L, Module.finrank ℝ F.direction = k)
    (hH : ∀ G ∈ H, Module.finrank ℝ G.direction = k + 1) :
    ∃ (a : AffineSubspace ℝ (Pt d) → Pt d)
      (b : AffineSubspace ℝ (Pt d) → AffineSubspace ℝ (Pt d)),
      Set.InjOn a (L : Set (AffineSubspace ℝ (Pt d))) ∧
      Set.InjOn b (H : Set (AffineSubspace ℝ (Pt d))) ∧
      (∀ G ∈ H, IsRealLine (b G)) ∧
      ∀ F ∈ L, ∀ G ∈ H, a F ∈ b G ↔ F ≤ G := by
  let A := L ∪ H
  obtain ⟨K, hK⟩ := exists_slice hd (intersectionArrangement A) k
  have hLA : ∀ F ∈ L, F ∈ A := fun F hF => Finset.mem_union_left _ hF
  have hHA : ∀ G ∈ H, G ∈ A := fun G hG => Finset.mem_union_right _ hG
  have hLslice : ∀ F ∈ L, ((F ⊓ K : AffineSubspace ℝ (Pt d)) : Set (Pt d)).Nonempty := by
    intro F hF
    apply (hK F (mem_intersectionArrangement A F (hLA F hF))).1.mpr
    exact ⟨affine_nonempty F (direction_ne_bot_of_rank F k hk (hL F hF)),
      by rw [hL F hF]⟩
  have hHslice : ∀ G ∈ H, IsRealLine (G ⊓ K) := by
    intro G hG
    have hr := (hK G (mem_intersectionArrangement A G (hHA G hG))).2
    change Module.finrank ℝ (G ⊓ K).direction = 1
    rw [hr, hH G hG]
    omega
  let a : AffineSubspace ℝ (Pt d) → Pt d := fun F => point (F ⊓ K)
  let b : AffineSubspace ℝ (Pt d) → AffineSubspace ℝ (Pt d) := fun G => G ⊓ K
  have ha_mem : ∀ F ∈ L, a F ∈ F ∧ a F ∈ K := by
    intro F hF
    exact point_mem (F ⊓ K) (hLslice F hF)
  refine ⟨a, b, ?_, ?_, hHslice, ?_⟩
  · intro F hF G hG he
    by_contra hFG
    have hsmall := intersection_rank_lt F G k hk (hL F hF) (hL G hG) hFG
    have hpF := ha_mem F hF
    have hpG := ha_mem G hG
    have hsurvive : (((F ⊓ G) ⊓ K : AffineSubspace ℝ (Pt d)) : Set (Pt d)).Nonempty :=
      ⟨a F, ⟨⟨hpF.1, he.symm ▸ hpG.1⟩, hpF.2⟩⟩
    have hdim := ((hK (F ⊓ G)
      (inf_mem_intersectionArrangement A F G (hLA F hF) (hLA G hG))).1.mp hsurvive).2
    omega
  · intro F hF G hG he
    change F ⊓ K = G ⊓ K at he
    by_contra hFG
    have hsmall := intersection_rank_lt F G (k+1) (by omega) (hH F hF) (hH G hG) hFG
    have hcut := (hK (F ⊓ G)
      (inf_mem_intersectionArrangement A F G (hHA F hF) (hHA G hG))).2
    have hle : F ⊓ K ≤ (F ⊓ G) ⊓ K :=
      le_inf (le_inf inf_le_left (by rw [he]; exact inf_le_left)) inf_le_right
    have hdim := Submodule.finrank_mono (AffineSubspace.direction_le hle)
    have hline : Module.finrank ℝ (F ⊓ K).direction = 1 := hHslice F hF
    rw [hline, hcut] at hdim
    omega
  · intro F hF G hG
    constructor
    · intro hp
      by_contra hFG
      have hsmall := intersection_rank_lt_of_not_le F G k hk (hL F hF) hFG
      have hpF := ha_mem F hF
      have hsurvive : (((F ⊓ G) ⊓ K : AffineSubspace ℝ (Pt d)) : Set (Pt d)).Nonempty :=
        ⟨a F, ⟨⟨hpF.1, hp.1⟩, hpF.2⟩⟩
      have hdim := ((hK (F ⊓ G)
        (inf_mem_intersectionArrangement A F G (hLA F hF) (hHA G hG))).1.mp hsurvive).2
      omega
    · intro hFG
      exact ⟨hFG (ha_mem F hF).1, (ha_mem F hF).2⟩

/-- Transport a finite weight function to its image, adding weights when
the map is not injective. -/
def imageWeight {α β : Type*} (A : Finset α) (a : α → β) (ω : α → ℝ) (q : β) : ℝ :=
  ∑ F ∈ A.filter (fun F => a F = q), ω F

theorem imageWeight_apply {α β : Type*} (A : Finset α) (a : α → β) (ω : α → ℝ)
    (ha : Set.InjOn a (A : Set α)) (F : α) (hF : F ∈ A) :
    imageWeight A a ω (a F) = ω F := by
  have hf : A.filter (fun G => a G = a F) = {F} := by
    ext G
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hG, he⟩
      exact ha hG hF he
    · rintro rfl
      exact ⟨hF, rfl⟩
  simp only [imageWeight, hf, Finset.sum_singleton]

theorem filter_image_incidence (L : Finset (AffineSubspace ℝ (Pt d)))
    (a : AffineSubspace ℝ (Pt d) → Pt d)
    (G B : AffineSubspace ℝ (Pt d))
    (hinc : ∀ F ∈ L, a F ∈ B ↔ F ≤ G) :
    (L.image a).filter (fun q => q ∈ B) = (L.filter (fun F => F ≤ G)).image a := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨F, hF, rfl⟩, hp⟩
    exact ⟨F, ⟨hF, (hinc F hF).mp hp⟩, rfl⟩
  · rintro ⟨F, ⟨hF, hFG⟩, rfl⟩
    exact ⟨⟨F, hF, rfl⟩, (hinc F hF).mpr hFG⟩

theorem occ_image (L : Finset (AffineSubspace ℝ (Pt d)))
    (a : AffineSubspace ℝ (Pt d) → Pt d)
    (ha : Set.InjOn a (L : Set (AffineSubspace ℝ (Pt d))))
    (G B : AffineSubspace ℝ (Pt d))
    (hinc : ∀ F ∈ L, a F ∈ B ↔ F ≤ G) :
    occ (L.image a) B = (L.filter (fun F => F ≤ G)).card := by
  rw [occ, filter_image_incidence L a G B hinc]
  exact Finset.card_image_of_injOn fun F hF G hG he =>
    ha (Finset.mem_filter.mp hF).1 (Finset.mem_filter.mp hG).1 he

theorem sum_imageWeight_incidence (L : Finset (AffineSubspace ℝ (Pt d)))
    (a : AffineSubspace ℝ (Pt d) → Pt d) (ω : AffineSubspace ℝ (Pt d) → ℝ)
    (ha : Set.InjOn a (L : Set (AffineSubspace ℝ (Pt d))))
    (G B : AffineSubspace ℝ (Pt d))
    (hinc : ∀ F ∈ L, a F ∈ B ↔ F ≤ G) :
    ∑ q ∈ (L.image a).filter (fun q => q ∈ B), imageWeight L a ω q =
      ∑ F ∈ L.filter (fun F => F ≤ G), ω F := by
  rw [filter_image_incidence L a G B hinc, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro F hF
    exact imageWeight_apply L a ω ha F (Finset.mem_filter.mp hF).1
  · intro F hF G hG he
    exact ha (Finset.mem_filter.mp hF).1 (Finset.mem_filter.mp hG).1 he

/-- A positive lower weight cutoff turns a flat-mass bound into an
occupancy bound. -/
theorem occupancy_le_mass_div (L : Finset (AffineSubspace ℝ (Pt d)))
    (ω : AffineSubspace ℝ (Pt d) → ℝ) (a M : ℝ) (ha : 0 < a)
    (hlower : ∀ F ∈ L, a ≤ ω F) (G : AffineSubspace ℝ (Pt d))
    (hmass : (∑ F ∈ L.filter (fun F => F ≤ G), ω F) ≤ M) :
    ((L.filter (fun F => F ≤ G)).card : ℝ) ≤ M / a := by
  apply (le_div_iff₀ ha).mpr
  calc
    _ = ∑ F ∈ L.filter (fun F => F ≤ G), a := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ F ∈ L.filter (fun F => F ≤ G), ω F := by
      apply Finset.sum_le_sum
      intro F hF
      exact hlower F (Finset.mem_filter.mp hF).1
    _ ≤ M := hmass

/-- Removing light members of a finite family costs at most the number
of members times the cutoff. -/
theorem sum_light_weights_le_card_mul {α : Type*} (A : Finset α) (ω : α → ℝ)
    (a : ℝ) (ha : 0 ≤ a) :
    (∑ F ∈ A.filter (fun F => ω F < a), ω F) ≤ (A.card : ℝ) * a := by
  calc
    _ ≤ ∑ F ∈ A.filter (fun F => ω F < a), a :=
      Finset.sum_le_sum fun F hF => (Finset.mem_filter.mp hF).2.le
    _ = ((A.filter (fun F => ω F < a)).card : ℝ) * a := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (A.card : ℝ) * a := by
      apply mul_le_mul_of_nonneg_right _ ha
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ A)

/-- Assign each ordered pair to one containing flat. Its product weight
is one term of the squared total weight in that flat. -/
theorem weighted_pairs_le_squared_flat_mass
    (L H : Finset (AffineSubspace ℝ (Pt d)))
    (ω : AffineSubspace ℝ (Pt d) → ℝ)
    (R : Finset (AffineSubspace ℝ (Pt d) × AffineSubspace ℝ (Pt d)))
    (join : AffineSubspace ℝ (Pt d) × AffineSubspace ℝ (Pt d) →
      AffineSubspace ℝ (Pt d))
    (hω : ∀ F ∈ L, 0 ≤ ω F) (hR : R ⊆ L ×ˢ L)
    (hjoin : ∀ FG ∈ R, join FG ∈ H ∧ FG.1 ≤ join FG ∧ FG.2 ≤ join FG) :
    (∑ FG ∈ R, ω FG.1 * ω FG.2) ≤
      ∑ G ∈ H, (∑ F ∈ L.filter (fun F => F ≤ G), ω F) ^ 2 := by
  let fiber := fun G => R.filter (fun FG => join FG = G)
  have hfilter : R.filter (fun FG => join FG ∈ H) = R := by
    ext FG
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.1, fun h => ⟨h, (hjoin FG h).1⟩⟩
  have hsum : (∑ G ∈ H, ∑ FG ∈ fiber G, ω FG.1 * ω FG.2) =
      ∑ FG ∈ R, ω FG.1 * ω FG.2 := by
    dsimp only [fiber]
    rw [Finset.sum_fiberwise_eq_sum_filter R H join (fun FG => ω FG.1 * ω FG.2), hfilter]
  rw [← hsum]
  apply Finset.sum_le_sum
  intro G hG
  let inside := L.filter (fun F => F ≤ G)
  have hsub : fiber G ⊆ inside ×ˢ inside := by
    intro FG hFG
    obtain ⟨hFR, he⟩ := Finset.mem_filter.mp hFG
    have hFL := Finset.mem_product.mp (hR hFR)
    have hj := hjoin FG hFR
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hFL.1, he ▸ hj.2.1⟩,
      Finset.mem_filter.mpr ⟨hFL.2, he ▸ hj.2.2⟩⟩
  calc
    (∑ FG ∈ fiber G, ω FG.1 * ω FG.2) ≤
        ∑ FG ∈ inside ×ˢ inside, ω FG.1 * ω FG.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro FG hFG _
      have hm := Finset.mem_product.mp hFG
      exact mul_nonneg (hω FG.1 (Finset.mem_filter.mp hm.1).1)
        (hω FG.2 (Finset.mem_filter.mp hm.2).1)
    _ = (∑ F ∈ inside, ω F) ^ 2 := by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, pow_two]

end FiniteFlatSlice


namespace RealFlatGeometry

variable {d : ℕ}

/-- Real and imaginary coordinate maps on the complex affine model. -/
def realPart : Point d →ₗ[ℝ] Pt d where
  toFun z := (WithLp.toLp 2 fun i => (z i).re)
  map_add' z u := by ext i; simp
  map_smul' c z := by ext i; simp

def imagPart : Point d →ₗ[ℝ] Pt d where
  toFun z := (WithLp.toLp 2 fun i => (z i).im)
  map_add' z u := by ext i; simp
  map_smul' c z := by ext i; simp

@[simp] theorem realPart_toC (x : Pt d) : realPart (toC x) = x := by
  ext i
  simp [realPart, toC]

@[simp] theorem imagPart_toC (x : Pt d) : imagPart (toC x) = 0 := by
  ext i
  simp [imagPart, toC]

@[simp] theorem toC_sub (x y : Pt d) : toC (x-y) = toC x-toC y := by
  ext i
  simp [toC]

@[simp] theorem toC_add (x y : Pt d) : toC (x+y) = toC x+toC y := by
  ext i
  simp [toC]

@[simp] theorem toC_zero : toC (0 : Pt d) = 0 := by
  ext i
  simp [toC]

@[simp] theorem realPart_smul (c : ℂ) (v : Point d) :
    realPart (c • v) = c.re • realPart v - c.im • imagPart v := by
  ext i
  simp [realPart, imagPart, Complex.mul_re]

@[simp] theorem imagPart_smul (c : ℂ) (v : Point d) :
    imagPart (c • v) = c.re • imagPart v + c.im • realPart v := by
  ext i
  simp [realPart, imagPart, Complex.mul_im]

/-- Both parts of a vector in the complex span of a real subspace remain
in that real subspace. -/
theorem parts_mem_of_mem_span (V : Submodule ℝ (Pt d)) (v : Point d)
    (hv : v ∈ Submodule.span ℂ (toC '' (V : Set (Pt d)))) :
    realPart v ∈ V ∧ imagPart v ∈ V := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨x, hx, rfl⟩ := hv
      exact ⟨by simpa using hx, by simp⟩
  | zero => simp
  | add v u hv hu ihv ihu =>
      exact ⟨by simpa using V.add_mem ihv.1 ihu.1,
        by simpa using V.add_mem ihv.2 ihu.2⟩
  | smul c v hv ih =>
      exact ⟨by simpa using V.sub_mem (V.smul_mem c.re ih.1) (V.smul_mem c.im ih.2),
        by simpa using V.add_mem (V.smul_mem c.re ih.2) (V.smul_mem c.im ih.1)⟩

/-- Complex affine span of the real flat. -/
def complexify (F : AffineSubspace ℝ (Pt d)) : AffineSubspace ℂ (Point d) :=
  affineSpan ℂ (toC '' (F : Set (Pt d)))

theorem complexify_direction (F : AffineSubspace ℝ (Pt d)) (a : Pt d) (ha : a ∈ F) :
    (complexify F).direction = Submodule.span ℂ (toC '' (F.direction : Set (Pt d))) := by
  rw [complexify, direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℂ
    (Set.mem_image_of_mem toC ha)]
  congr 1
  ext v
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x-a, ?_, ?_⟩
    · change x-a ∈ F.direction
      exact AffineSubspace.vsub_mem_direction hx ha
    · simp only [vsub_eq_sub, toC_sub]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨toC (x+a), Set.mem_image_of_mem toC
      (AffineSubspace.vadd_mem_of_mem_direction hx ha), ?_⟩
    simp only [vsub_eq_sub, toC_add, add_sub_cancel_right]

/-- Complexifying a real flat introduces no new real points. -/
theorem real_locus_complexify (F : AffineSubspace ℝ (Pt d))
    (hne : (F : Set (Pt d)).Nonempty) (x : Pt d) :
    toC x ∈ complexify F ↔ x ∈ F := by
  obtain ⟨a, ha⟩ := hne
  have hCa : toC a ∈ complexify F := subset_affineSpan ℂ _ (Set.mem_image_of_mem toC ha)
  constructor
  · intro hx
    have hv := AffineSubspace.vsub_mem_direction hx hCa
    rw [complexify_direction F a ha] at hv
    have hm := (parts_mem_of_mem_span F.direction _ hv).1
    have hr : realPart (toC x -ᵥ toC a) = x-a := by
      simp only [vsub_eq_sub, map_sub, realPart_toC]
    rw [hr] at hm
    exact (AffineSubspace.vsub_right_mem_direction_iff_mem ha x).mp hm
  · intro hx
    exact subset_affineSpan ℂ _ (Set.mem_image_of_mem toC hx)

theorem vanishing_on_affineSpan (G : AffineSubspace ℝ (Pt d))
    (x₀ : Pt d) (hx₀ : x₀ ∈ G) (f : Poly d)
    (hvan : ∀ x ∈ G, MvPolynomial.eval (toC x) f = 0)
    (z : Point d) (hz : z ∈ affineSpan ℂ (toC '' (G : Set (Pt d)))) :
    MvPolynomial.eval z f = 0 := by
  classical
  let T : Set (Point d) := toC '' (G : Set (Pt d))
  let S : Set (Point d) := (fun y : Point d => y -ᵥ toC x₀) '' T
  let r : ℕ := Module.finrank ℂ (Submodule.span ℂ S)
  obtain ⟨v, hvS, hvspan, _⟩ :
      ∃ v : Fin r → Point d, (∀ i, v i ∈ S) ∧
        Submodule.span ℂ (Set.range v) = Submodule.span ℂ S ∧ LinearIndependent ℂ v := by
    simpa [r] using Submodule.exists_fun_fin_finrank_span_eq ℂ S
  have hx₀T : toC x₀ ∈ T := Set.mem_image_of_mem toC hx₀
  have hdir : (affineSpan ℂ T).direction = Submodule.span ℂ (Set.range v) := by
    rw [direction_affineSpan,
      vectorSpan_eq_span_vsub_set_right ℂ hx₀T]
    exact hvspan.symm
  have hvWitness : ∀ i, ∃ x : Pt d, x ∈ G ∧ toC x -ᵥ toC x₀ = v i := by
    intro i
    rcases hvS i with ⟨y, hy, hyv⟩
    rcases hy with ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    simpa [hxy] using hyv
  choose x hxG hvx using hvWitness
  have hvxC (i : Fin r) : v i = toC (x i -ᵥ x₀) := by
    rw [← hvx i]
    ext j
    simp [toC]
  let param : Fin d → MvPolynomial (Fin r) ℂ := fun j =>
    MvPolynomial.C (toC x₀ j) +
      ∑ i, MvPolynomial.C (v i j) * MvPolynomial.X i
  let q : MvPolynomial (Fin r) ℂ := MvPolynomial.aeval param f
  have hEval (u : Fin r → ℂ) :
      MvPolynomial.eval u q =
        MvPolynomial.eval (fun j => toC x₀ j + ∑ i, u i * v i j) f := by
    have hcomp : (MvPolynomial.aeval u).comp (MvPolynomial.aeval param) =
        MvPolynomial.aeval (fun j => toC x₀ j + ∑ i, u i * v i j) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [param, mul_comm]
    simpa [q] using congrArg (fun φ : Poly d →ₐ[ℂ] ℂ => φ f) hcomp
  have hrealPoint (u : Fin r → ℝ) :
      (fun j => toC x₀ j + ∑ i, (u i : ℂ) * v i j) =
        toC ((∑ i, u i • (x i -ᵥ x₀)) +ᵥ x₀) := by
    funext j
    simp [toC, hvxC, Finset.sum_apply, Complex.ofReal_sum, Complex.ofReal_mul]
    <;> ring
  have hpointG (u : Fin r → ℝ) :
      (∑ i, u i • (x i -ᵥ x₀)) +ᵥ x₀ ∈ G := by
    apply AffineSubspace.vadd_mem_of_mem_direction
    · exact Submodule.sum_mem _ fun i hi =>
        G.direction.smul_mem _ (AffineSubspace.vsub_mem_direction (hxG i) hx₀)
    · exact hx₀
  have hqzero : q = 0 := by
    apply MvPolynomial.funext_set
      (s := fun _ : Fin r => Set.range (fun t : ℝ => (t : ℂ)))
      (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
    intro u hu
    have hucoord : ∀ i, u i ∈ Set.range (fun t : ℝ => (t : ℂ)) := by
      intro i
      exact (Set.mem_pi.mp hu) i (Set.mem_univ i)
    choose t ht using hucoord
    have huEq : u = fun i => (t i : ℂ) := by
      funext i
      exact (ht i).symm
    rw [huEq, hEval, hrealPoint]
    exact hvan _ (hpointG t)
  have hzdir : z -ᵥ toC x₀ ∈ Submodule.span ℂ (Set.range v) := by
    rw [← hdir]
    exact AffineSubspace.vsub_mem_direction hz (subset_affineSpan ℂ T hx₀T)
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hzdir
  have hqu : MvPolynomial.eval u q = 0 := by rw [hqzero]; simp
  rw [hEval] at hqu
  have hzEq : z = fun j => toC x₀ j + ∑ i, u i * v i j := by
    calc
      z = (z -ᵥ toC x₀) +ᵥ toC x₀ := by simp
      _ = (∑ i, u i • v i) +ᵥ toC x₀ := by rw [hu]
      _ = _ := by
        ext j
        simp [Finset.sum_apply, smul_eq_mul]
        ring
  rw [hzEq]
  exact hqu


/-- A complex affine flat is Zariski closed, as witnessed by its linear
separating equations. -/
theorem closure_subset_complex_flat (T : Set (Point d))
    (F : AffineSubspace ℂ (Point d)) (hF : (F : Set (Point d)).Nonempty)
    (hT : T ⊆ F) : (AffineVariety.closure T).points ⊆ F := by
  obtain ⟨a, ha⟩ := hF
  intro z hz
  by_contra hn
  have hv : z-a ∉ F.direction := by
    intro hv
    exact hn ((AffineSubspace.vsub_right_mem_direction_iff_mem ha z).mp hv)
  obtain ⟨L, hL, hker⟩ := Submodule.exists_le_ker_of_notMem hv
  have hf : covectorPoly L a ∈ (AffineVariety.closure T).ideal := by
    intro x hx
    change MvPolynomial.eval x (covectorPoly L a) = 0
    rw [eval_covectorPoly]
    exact LinearMap.mem_ker.mp (hker
      (AffineSubspace.vsub_mem_direction (hT hx) ha))
  have hzero := hz (covectorPoly L a) hf
  change MvPolynomial.eval z (covectorPoly L a) = 0 at hzero
  rw [eval_covectorPoly] at hzero
  exact hL hzero

/-- The Zariski closure in the definition of IsRealFlat is exactly the
complex affine span of its witness. -/
theorem closure_image_points (F : AffineSubspace ℝ (Pt d))
    (hne : (F : Set (Pt d)).Nonempty) :
    (AffineVariety.closure (toC '' (F : Set (Pt d)))).points =
      (complexify F : Set (Point d)) := by
  obtain ⟨a, ha⟩ := hne
  apply Set.Subset.antisymm
  · apply closure_subset_complex_flat
    · exact ⟨toC a, subset_affineSpan ℂ _ (Set.mem_image_of_mem toC ha)⟩
    · exact subset_affineSpan ℂ _
  · intro z hz f hf
    apply vanishing_on_affineSpan F a ha f _ z hz
    intro x hx
    exact hf (toC x) (Set.mem_image_of_mem toC hx)

/-- Every direction of a complex affine flat lies in its tangent space:
restricting an ideal polynomial to any line in the flat gives zero. -/
theorem flat_direction_le_tangent (X : AffineVariety d)
    (F : AffineSubspace ℂ (Point d)) (hF : X.points = (F : Set (Point d)))
    (x : Point d) (hx : x ∈ X) : F.direction ≤ X.tangentSpace x := by
  intro v hv
  simp only [AffineVariety.tangentSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  intro f
  let A : ℂ →ₗ[ℂ] Point d := (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight v
  let path : ℂ → Point d := fun t => A t + x
  have hxF : x ∈ F := by change x ∈ X.points at hx; rwa [hF] at hx
  have hpath : HasFDerivAt path A.toContinuousLinearMap 0 := by
    exact A.toContinuousLinearMap.hasFDerivAt.add_const x
  have hzero : (fun t : ℂ => MvPolynomial.eval (path t) f.val) = fun _ => 0 := by
    funext t
    apply (mem_ideal_iff_eval_zero X f.val).mp f.property
    change path t ∈ X.points
    rw [hF]
    exact AffineSubspace.vadd_mem_of_mem_direction (F.direction.smul_mem t hv) hxF
  have hderiv := (polynomial_eval_hasFDerivAt f.val (path 0)).comp 0 hpath
  have hconst : HasFDerivAt (𝕜 := ℂ) (fun t : ℂ => MvPolynomial.eval (path t) f.val) 0 0 := by
    rw [hzero]
    exact hasFDerivAt_const 0 0
  have he := hderiv.unique hconst
  have he1 := congrArg (fun D : ℂ →L[ℂ] ℂ => D 1) he
  simpa [path, A, LinearMap.toContinuousLinearMap] using he1

/-- The shared algebraic dimension of a complex affine flat is its
linear direction dimension. -/
theorem flat_dimension_eq_finrank (X : AffineVariety d) (hX : X.IsIrreducible)
    (F : AffineSubspace ℂ (Point d)) (hF : X.points = (F : Set (Point d))) :
    X.dimension = Module.finrank ℂ F.direction := by
  obtain ⟨x, hx, hdim⟩ := (request_general_tangent_finrank X hX).exists
  have hxF : x ∈ F := by change x ∈ X.points at hx; rwa [hF] at hx
  have hlow := Submodule.finrank_mono (flat_direction_le_tangent X F hF x hx)
  rw [hdim] at hlow
  have hsub : X.points ⊆ ↑(AffineSubspace.mk' x F.direction) := by
    rw [AffineSubspace.mk'_eq hxF, hF]
  have hupp := GeoCommon.dim_le_of_mem_flat X X.dimension hX rfl x F.direction
    hsub (Module.finrank ℂ F.direction) rfl
  exact le_antisymm hupp hlow

/-- Complexifying a real subspace preserves its dimension. A complex
basis chosen from its real vectors is also a real basis. -/
theorem span_complexification_finrank (V : Submodule ℝ (Pt d)) :
    Module.finrank ℂ (Submodule.span ℂ (toC '' (V : Set (Pt d)))) =
      Module.finrank ℝ V := by
  let r := Module.finrank ℂ (Submodule.span ℂ (toC '' (V : Set (Pt d))))
  obtain ⟨v, hv, hspan, hli⟩ :
      ∃ v : Fin r → Point d, (∀ i, v i ∈ toC '' (V : Set (Pt d))) ∧
        Submodule.span ℂ (Set.range v) = Submodule.span ℂ (toC '' (V : Set (Pt d))) ∧
        LinearIndependent ℂ v := by
    simpa only [r] using Submodule.exists_fun_fin_finrank_span_eq ℂ (toC '' (V : Set (Pt d)))
  choose u hu hvu using hv
  have hsumRe : ∀ c : Fin r → ℂ,
      realPart (∑ i, c i • v i) = ∑ i, (c i).re • u i := by
    intro c
    simp only [map_sum, realPart_smul, ← hvu, realPart_toC, imagPart_toC, smul_zero,
      sub_zero]
  have hrealSpan : Submodule.span ℝ (Set.range u) = V := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hu i
    · intro x hx
      have hCx : toC x ∈ Submodule.span ℂ (Set.range v) := by
        rw [hspan]
        exact Submodule.subset_span (Set.mem_image_of_mem toC hx)
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hCx
      have he := congrArg realPart hc
      rw [hsumRe, realPart_toC] at he
      rw [← he]
      exact Submodule.sum_mem _ fun i _ =>
        (Submodule.span ℝ (Set.range u)).smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hliR : LinearIndependent ℝ u := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have hCc : (∑ j, (c j : ℂ) • v j) = 0 := by
      rw [← toC_zero]
      have hmap : toC (∑ j, c j • u j) = ∑ j, (c j : ℂ) • v j := by
        ext j
        simp [toC, ← hvu, Finset.sum_apply, Complex.ofReal_sum, Complex.ofReal_mul]
      rw [← hmap, hc]
    have hi := (Fintype.linearIndependent_iff.mp hli) (fun j => (c j : ℂ)) hCc i
    exact Complex.ofReal_injective hi
  have hdim := finrank_span_eq_card hliR
  rw [hrealSpan, Fintype.card_fin] at hdim
  exact hdim.symm

theorem complexify_finrank (F : AffineSubspace ℝ (Pt d))
    (hne : (F : Set (Pt d)).Nonempty) :
    Module.finrank ℂ (complexify F).direction = Module.finrank ℝ F.direction := by
  obtain ⟨a, ha⟩ := hne
  rw [complexify_direction F a ha]
  exact span_complexification_finrank F.direction

def realPreimage (F : AffineSubspace ℂ (Point d)) : AffineSubspace ℝ (Pt d) :=
  { carrier := {x | toC x ∈ F}
    smul_vsub_vadd_mem' := by
      rintro c p₁ p₂ p₃ hp₁ hp₂ hp₃
      change toC p₁ ∈ F at hp₁
      change toC p₂ ∈ F at hp₂
      change toC p₃ ∈ F at hp₃
      change toC (c • (p₁-p₂)+p₃) ∈ F
      have he : toC (c • (p₁-p₂)+p₃) =
          (c : ℂ) • (toC p₁-toC p₂)+toC p₃ := by
        ext i
        simp [toC]
      rw [he]
      exact F.smul_vsub_vadd_mem' (c : ℂ) hp₁ hp₂ hp₃ }

@[simp] theorem realPreimage_mem (F : AffineSubspace ℂ (Point d)) (x : Pt d) :
    x ∈ realPreimage F ↔ toC x ∈ F := Iff.rfl

theorem complexify_le_iff (F : AffineSubspace ℝ (Pt d))
    (G : AffineSubspace ℂ (Point d)) : complexify F ≤ G ↔ F ≤ realPreimage G := by
  rw [complexify, affineSpan_le]
  constructor
  · intro h x hx
    exact h (Set.mem_image_of_mem toC hx)
  · intro h z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact h hx

theorem complexify_mono (F G : AffineSubspace ℝ (Pt d)) (h : F ≤ G) :
    complexify F ≤ complexify G := by
  apply affineSpan_mono ℂ
  exact Set.image_mono h

theorem complexify_sup (F G : AffineSubspace ℝ (Pt d)) :
    complexify (F ⊔ G) = complexify F ⊔ complexify G := by
  apply le_antisymm
  · apply (complexify_le_iff _ _).mpr
    apply sup_le
    · apply (complexify_le_iff _ _).mp
      exact le_sup_left
    · apply (complexify_le_iff _ _).mp
      exact le_sup_right
  · exact sup_le (complexify_mono F _ le_sup_left) (complexify_mono G _ le_sup_right)

theorem complexify_injective (F G : AffineSubspace ℝ (Pt d))
    (hF : (F : Set (Pt d)).Nonempty) (hG : (G : Set (Pt d)).Nonempty)
    (he : complexify F = complexify G) : F = G := by
  ext x
  rw [← real_locus_complexify F hF x, ← real_locus_complexify G hG x, he]

/-- The witness from IsRealFlat, chosen once for each carrier. -/
def realCarrier (Z : AffineVariety d) : AffineSubspace ℝ (Pt d) :=
  if h : IsRealFlat Z then h.choose else ⊥

theorem realCarrier_spec (Z : AffineVariety d) (hZ : IsRealFlat Z) :
    (realCarrier Z : Set (Pt d)).Nonempty ∧
    Z.points = (AffineVariety.closure (toC '' (realCarrier Z : Set (Pt d)))).points := by
  unfold realCarrier
  rw [dif_pos hZ]
  exact hZ.choose_spec

theorem realCarrier_complexify (Z : AffineVariety d) (hZ : IsRealFlat Z) :
    Z.points = (complexify (realCarrier Z) : Set (Point d)) := by
  have h := realCarrier_spec Z hZ
  rw [h.2, closure_image_points _ h.1]

theorem realCarrier_mem (Z : AffineVariety d) (hZ : IsRealFlat Z) (x : Pt d) :
    toC x ∈ Z.points ↔ x ∈ realCarrier Z := by
  rw [realCarrier_complexify Z hZ]
  exact real_locus_complexify _ (realCarrier_spec Z hZ).1 x

theorem realCarrier_finrank (Z : AffineVariety d) (hZ : Z.IsIrreducible)
    (hrZ : IsRealFlat Z) : Module.finrank ℝ (realCarrier Z).direction = Z.dimension := by
  have hdim := flat_dimension_eq_finrank Z hZ _ (realCarrier_complexify Z hrZ)
  rw [complexify_finrank _ (realCarrier_spec Z hrZ).1] at hdim
  exact hdim.symm

theorem realCarrier_injective (Y Z : AffineVariety d) (hY : IsRealFlat Y)
    (hZ : IsRealFlat Z) (he : realCarrier Y = realCarrier Z) : Y = Z := by
  apply (AffineVariety.points_eq_iff Y Z).mp
  rw [(realCarrier_spec Y hY).2, (realCarrier_spec Z hZ).2, he]

theorem isFlat_of_isRealFlat (Z : AffineVariety d) (hZ : IsRealFlat Z) : IsFlat Z :=
  ⟨complexify (realCarrier Z), realCarrier_complexify Z hZ⟩

theorem complexSpan_realCarrier (Z : AffineVariety d) (hZ : IsRealFlat Z) :
    complexSpan Z = complexify (realCarrier Z) := by
  rw [complexSpan, realCarrier_complexify Z hZ]
  exact AffineSubspace.affineSpan_coe _

theorem complexify_le_complexify_iff (F G : AffineSubspace ℝ (Pt d))
    (hG : (G : Set (Pt d)).Nonempty) : complexify F ≤ complexify G ↔ F ≤ G := by
  rw [complexify_le_iff]
  constructor
  · intro h x hx
    exact (real_locus_complexify G hG x).mp (h hx)
  · intro h x hx
    exact (real_locus_complexify G hG x).mpr (h hx)

theorem realCarrier_containment_iff (Y Z : AffineVariety d)
    (hY : IsRealFlat Y) (hZ : IsRealFlat Z) :
    Y.points ⊆ Z.points ↔ realCarrier Y ≤ realCarrier Z := by
  rw [realCarrier_complexify Y hY, realCarrier_complexify Z hZ]
  exact complexify_le_complexify_iff _ _ (realCarrier_spec Z hZ).1

/-- Containment and equality of dimensions identify nonempty flats. -/
theorem eq_of_le_of_finrank_eq (F G : AffineSubspace ℝ (Pt d))
    (hF : (F : Set (Pt d)).Nonempty) (hle : F ≤ G)
    (hdim : Module.finrank ℝ F.direction = Module.finrank ℝ G.direction) : F = G := by
  exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) hdim) hF hle

/-- Unequal real `k`-flats inside a common complex flat of dimension at
most `k+1` have a real `(k+1)`-flat as their join. -/
theorem join_finrank_of_complex_bound (F G : AffineSubspace ℝ (Pt d)) (k : ℕ)
    (hF : (F : Set (Pt d)).Nonempty) (hG : (G : Set (Pt d)).Nonempty)
    (hFk : Module.finrank ℝ F.direction = k) (hGk : Module.finrank ℝ G.direction = k)
    (hne : F ≠ G) (H : AffineSubspace ℂ (Point d))
    (hH : Module.finrank ℂ H.direction ≤ k + 1)
    (hFH : complexify F ≤ H) (hGH : complexify G ≤ H) :
    Module.finrank ℝ (F ⊔ G).direction = k + 1 := by
  have hjoinne : ((F ⊔ G : AffineSubspace ℝ (Pt d)) : Set (Pt d)).Nonempty := by
    obtain ⟨x, hx⟩ := hF
    exact ⟨x, (show F ≤ F ⊔ G from le_sup_left) hx⟩
  have hjoinH : complexify (F ⊔ G) ≤ H := by
    rw [complexify_sup]
    exact sup_le hFH hGH
  have hupp := Submodule.finrank_mono (AffineSubspace.direction_le hjoinH)
  rw [complexify_finrank _ hjoinne] at hupp
  have hhigh : Module.finrank ℝ (F ⊔ G).direction ≤ k+1 := hupp.trans hH
  have hlow : k ≤ Module.finrank ℝ (F ⊔ G).direction := by
    rw [← hFk]
    exact Submodule.finrank_mono (AffineSubspace.direction_le le_sup_left)
  by_contra hn
  have hjoinrank : Module.finrank ℝ (F ⊔ G).direction = k := by omega
  have hFjoin : F = F ⊔ G := eq_of_le_of_finrank_eq F _ hF le_sup_left
    (hFk.trans hjoinrank.symm)
  have hGF : G ≤ F := by rw [hFjoin]; exact le_sup_right
  have he : G = F := eq_of_le_of_finrank_eq G F hG hGF (hGk.trans hFk.symm)
  exact hne he.symm

/-- The real carrier join realizes every equal-dimensional common-flat
exception occurring after geometric pruning. -/
theorem realCarrier_join_finrank (Y Z : AffineVariety d) (k : ℕ)
    (hY : Y.IsIrreducible) (hZ : Z.IsIrreducible) (hrY : IsRealFlat Y)
    (hrZ : IsRealFlat Z) (hYk : Y.dimension = k) (hZk : Z.dimension = k)
    (hne : Y ≠ Z) (H : AffineSubspace ℂ (Point d))
    (hH : Module.finrank ℂ H.direction ≤ k+1) (hYH : Y.points ⊆ H) (hZH : Z.points ⊆ H) :
    Module.finrank ℝ (realCarrier Y ⊔ realCarrier Z).direction = k+1 := by
  apply join_finrank_of_complex_bound _ _ k (realCarrier_spec Y hrY).1
    (realCarrier_spec Z hrZ).1
    ((realCarrier_finrank Y hY hrY).trans hYk)
    ((realCarrier_finrank Z hZ hrZ).trans hZk)
    (fun he => hne (realCarrier_injective Y Z hrY hrZ he)) H hH
  · rwa [realCarrier_complexify Y hrY] at hYH
  · rwa [realCarrier_complexify Z hrZ] at hZH

/-- A common `(k+1)`-flat is uniquely the complexification of the real
join of two distinct real `k`-flat carriers. -/
theorem complexify_realCarrier_join_eq (Y Z : AffineVariety d) (k : ℕ)
    (hY : Y.IsIrreducible) (hZ : Z.IsIrreducible) (hrY : IsRealFlat Y)
    (hrZ : IsRealFlat Z) (hYk : Y.dimension = k) (hZk : Z.dimension = k)
    (hne : Y ≠ Z) (H : AffineSubspace ℂ (Point d))
    (hH : Module.finrank ℂ H.direction ≤ k+1) (hYH : Y.points ⊆ H) (hZH : Z.points ⊆ H) :
    complexify (realCarrier Y ⊔ realCarrier Z) = H := by
  have hjoinRank := realCarrier_join_finrank Y Z k hY hZ hrY hrZ hYk hZk hne H hH hYH hZH
  have hjoinNe : ((realCarrier Y ⊔ realCarrier Z : AffineSubspace ℝ (Pt d)) :
      Set (Pt d)).Nonempty := by
    obtain ⟨x, hx⟩ := (realCarrier_spec Y hrY).1
    exact ⟨x, (show realCarrier Y ≤ realCarrier Y ⊔ realCarrier Z from le_sup_left) hx⟩
  have hle : complexify (realCarrier Y ⊔ realCarrier Z) ≤ H := by
    rw [complexify_sup]
    exact sup_le (by rwa [realCarrier_complexify Y hrY] at hYH)
      (by rwa [realCarrier_complexify Z hrZ] at hZH)
  have hdim : Module.finrank ℂ (complexify (realCarrier Y ⊔ realCarrier Z)).direction =
      k+1 := (complexify_finrank _ hjoinNe).trans hjoinRank
  have hdirle := AffineSubspace.direction_le hle
  have hdimle := Submodule.finrank_mono hdirle
  have hsame : Module.finrank ℂ (complexify (realCarrier Y ⊔ realCarrier Z)).direction =
      Module.finrank ℂ H.direction := by omega
  have hCne : ((complexify (realCarrier Y ⊔ realCarrier Z)) : Set (Point d)).Nonempty := by
    obtain ⟨x, hx⟩ := hjoinNe
    exact ⟨toC x, subset_affineSpan ℂ _ (Set.mem_image_of_mem toC hx)⟩
  exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of_le_of_finrank_eq hdirle hsame) hCne hle

theorem complexify_ne_top_of_finrank_lt (F : AffineSubspace ℝ (Pt d))
    (hF : (F : Set (Pt d)).Nonempty) (hdim : Module.finrank ℝ F.direction < d) :
    complexify F ≠ ⊤ := by
  intro he
  have hrank := complexify_finrank F hF
  rw [he, AffineSubspace.direction_top, finrank_top, GeoCommon.finrank_point] at hrank
  omega

/-- A generically transverse source flat cannot equal its target. -/
theorem genericallyTransverse_flat_ne {d : ℕ} (X Y : AffineVariety d)
    (hflat : IsFlat X) (htrans : GenericallyTransverse X Y) : X ≠ Y := by
  intro he
  subst Y
  obtain ⟨F, hF⟩ := hflat
  obtain ⟨x, hx, y, hy, hxy⟩ := htrans.exists
  have hxF : x ∈ F := by change x ∈ X.points at hx; rwa [hF] at hx
  have hyF : y ∈ F := by change y ∈ X.points at hy; rwa [hF] at hy
  exact hxy.1 (flat_direction_le_tangent X F hF x hx
    (AffineSubspace.vsub_mem_direction hyF hxF))

end RealFlatGeometry

namespace CarrierWeights

/-- Sum the weights attached to each of two finite families. -/
def combined {α : Type*} (I J : Finset α) (a b : α → ℝ) (x : α) : ℝ :=
  (if x ∈ I then a x else 0) + (if x ∈ J then b x else 0)

theorem combined_nonneg {α : Type*} (I J : Finset α) (a b : α → ℝ)
    (ha : ∀ x ∈ I, 0 ≤ a x) (hb : ∀ x ∈ J, 0 ≤ b x) (x : α) :
    0 ≤ combined I J a b x := by
  unfold combined
  by_cases hi : x ∈ I <;> by_cases hj : x ∈ J <;> simp only [hi, hj, if_true, if_false]
  · exact add_nonneg (ha x hi) (hb x hj)
  · simpa using ha x hi
  · simpa using hb x hj
  · norm_num

theorem le_combined_left {α : Type*} (I J : Finset α) (a b : α → ℝ)
    (hb : ∀ x ∈ J, 0 ≤ b x) (x : α) (hx : x ∈ I) :
    a x ≤ combined I J a b x := by
  unfold combined
  rw [if_pos hx]
  by_cases hj : x ∈ J
  · rw [if_pos hj]
    linarith [hb x hj]
  · simp [hj]

theorem le_combined_right {α : Type*} (I J : Finset α) (a b : α → ℝ)
    (ha : ∀ x ∈ I, 0 ≤ a x) (x : α) (hx : x ∈ J) :
    b x ≤ combined I J a b x := by
  unfold combined
  rw [if_pos hx]
  by_cases hi : x ∈ I
  · rw [if_pos hi]
    linarith [ha x hi]
  · simp [hi]

theorem combined_le {α : Type*} (I J : Finset α) (a b : α → ℝ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : ∀ x ∈ I, a x ≤ A) (hb : ∀ x ∈ J, b x ≤ B)
    (x : α) : combined I J a b x ≤ A+B := by
  unfold combined
  by_cases hi : x ∈ I <;> by_cases hj : x ∈ J <;> simp only [hi, hj, if_true, if_false]
  · exact add_le_add (ha x hi) (hb x hj)
  · linarith [ha x hi]
  · linarith [hb x hj]
  · linarith

/-- Filtering the union preserves the sum of both families' weights,
including members that occur in both families. -/
theorem sum_combined_filter {α : Type*} (I J : Finset α) (a b : α → ℝ) (P : α → Prop) :
    (∑ x ∈ (I ∪ J).filter P, combined I J a b x) =
      (∑ x ∈ I.filter P, a x) + (∑ x ∈ J.filter P, b x) := by
  simp only [combined, Finset.sum_add_distrib]
  have hI : ((I ∪ J).filter P).filter (fun x => x ∈ I) = I.filter P := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  have hJ : ((I ∪ J).filter P).filter (fun x => x ∈ J) = J.filter P := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  rw [← Finset.sum_filter, ← Finset.sum_filter, hI, hJ]

theorem filter_image {α β : Type*} (A : Finset α) (f : α → β) (P : β → Prop) :
    (A.image f).filter P = (A.filter (fun x => P (f x))).image f := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hp⟩
    exact ⟨x, ⟨hx, hp⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hp⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, hp⟩

/-- Exact transport of a filtered weighted sum through an injective
finite image. -/
theorem sum_imageWeight_filter {α β : Type*} (A : Finset α) (f : α → β) (a : α → ℝ)
    (hf : Set.InjOn f (A : Set α)) (P : β → Prop) :
    (∑ y ∈ (A.image f).filter P, FiniteFlatSlice.imageWeight A f a y) =
      ∑ x ∈ A.filter (fun x => P (f x)), a x := by
  rw [filter_image, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    exact FiniteFlatSlice.imageWeight_apply A f a hf x (Finset.mem_filter.mp hx).1
  · intro x hx y hy he
    exact hf (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 he

theorem card_image_filter {α β : Type*} (A : Finset α) (f : α → β)
    (hf : Set.InjOn f (A : Set α)) (P : β → Prop) :
    ((A.image f).filter P).card = (A.filter (fun x => P (f x))).card := by
  rw [filter_image]
  exact Finset.card_image_of_injOn fun x hx y hy he =>
    hf (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 he

end CarrierWeights

set_option maxHeartbeats 1000000 in
/-- The label-image equality from the secants comparison, retaining a chart
witness on the further target for closed-containment arguments. -/
theorem further_root_label_images {d : ℕ} (X Y Y' : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible) (hY' : Y'.IsIrreducible)
    (hdim : Y'.dimension = Y.dimension) (hlpos : 0 < Y.dimension)
    (htr : GenericallyTransverse X Y)
    (hroot : ForGeneralPair X Y (fun x y =>
      ∃ z ∈ Y', z ≠ x ∧ z ≠ y ∧ ∃ c : ℂ, z - x = c • (y - x))) :
    ∃ i : Fin d,
      rationalImage (productVariety X Y) (secantChartNumerator i) (secantChartDenominator i) =
        rationalImage (productVariety X Y') (secantChartNumerator i) (secantChartDenominator i) ∧
      ∃ x ∈ X, ∃ z ∈ Y', (z-x) i ≠ 0 := by
  obtain ⟨x₀, hx₀, y₀, hy₀, htrans₀⟩ := htr.exists
  have hu₀ : y₀ - x₀ ≠ 0 := by
    intro h
    apply htrans₀.1
    rw [h]
    exact Submodule.zero_mem _
  have hex : ∃ i : Fin d, (y₀ - x₀) i ≠ 0 := by
    by_contra h
    push Not at h
    apply hu₀
    funext i
    exact h i
  obtain ⟨i, hi₀⟩ := hex
  let f := secantChartNumerator i
  let g := secantChartDenominator i
  let S := productVariety X Y
  let S' := productVariety X Y'
  let W := rationalImage S f g
  let W' := rationalImage S' f g
  have hS : S.IsIrreducible := productVariety_irreducible X Y hX hY
  have hS' : S'.IsIrreducible := productVariety_irreducible X Y' hX hY'
  have hchart : ForGeneralPair X Y (fun x y => (y - x) i ≠ 0) := by
    refine ⟨MvPolynomial.rename finSumFinEquiv.symm g, ⟨x₀, hx₀, y₀, hy₀, ?_⟩, ?_⟩
    · simpa only [eval_product_rename, g, eval_secantChartDenominator] using hi₀
    · intro x hx y hy hn
      simpa only [eval_product_rename, g, eval_secantChartDenominator] using hn
  have hg : g ∉ S.ideal := by
    intro hg
    have hp : productPoint x₀ y₀ ∈ S := AffineVariety.subset_closure _ ⟨x₀, hx₀, y₀, hy₀, rfl⟩
    have hzero := hp g hg
    change MvPolynomial.eval (productPoint x₀ y₀) g = 0 at hzero
    exact hi₀ (by simpa only [g, eval_secantChartDenominator] using hzero)
  have hrootchart := hroot.and hX hY hchart
  have hg' : g ∉ S'.ideal := by
    obtain ⟨x, hx, y, hy, ⟨z, hz, hzx, hzy, c, hline⟩, hi⟩ := hrootchart.exists
    have hc := (further_root_scalar_ne x y z c hzx hzy hline).1
    have hzgi := further_root_chart_ne_zero i x y z c hc hi hline
    intro hg'
    have hp : productPoint x z ∈ S' := AffineVariety.subset_closure _ ⟨x, hx, z, hz, rfl⟩
    have hzero := hp g hg'
    change MvPolynomial.eval (productPoint x z) g = 0 at hzero
    exact hzgi (by simpa only [g, eval_secantChartDenominator] using hzero)
  obtain ⟨hW, hgenW⟩ := request_rational_image_generic_tangent S hS f g hg
  obtain ⟨hW', hgenW'⟩ := request_rational_image_generic_tangent S' hS' f g hg'
  have hsubsetPair : ForGeneralPair X Y (fun x y =>
      MvPolynomial.eval (productPoint x y) g ≠ 0 ∧ rationalPoint f g (productPoint x y) ∈ W') := by
    apply hrootchart.mono
    intro x hx y hy hh
    rcases hh with ⟨⟨z, hz, hzx, hzy, c, hline⟩, hi⟩
    have hc := (further_root_scalar_ne x y z c hzx hzy hline).1
    have hzgi := further_root_chart_ne_zero i x y z c hc hi hline
    refine ⟨by simpa only [g, eval_secantChartDenominator] using hi, ?_⟩
    have heq := further_root_labels_eq i x y z c hc hi hline
    change rationalPoint (secantChartNumerator i) (secantChartDenominator i) (productPoint x y) ∈ W'
    rw [heq]
    exact rationalPoint_mem_image S' f g (productPoint x z)
      (AffineVariety.subset_closure _ ⟨x, hx, z, hz, rfl⟩)
      (by simpa only [g, eval_secantChartDenominator] using hzgi)
  have hsubsetSource : ForGeneralPoint S (fun p => MvPolynomial.eval p g ≠ 0 ∧ rationalPoint f g p ∈ W') := by
    simpa only [productPoint_left_right] using hsubsetPair.on_product
  have hsub : W.Subvariety W' := request_rational_image_generic_subset S hS f g W' hsubsetSource
  have hdx := (general_tangent_finrank X hX).on_left ⟨y₀, hy₀⟩
  have hdy := (general_tangent_finrank Y hY).on_right ⟨x₀, hx₀⟩
  have hrankPair : ForGeneralPair X Y (fun x y => Module.finrank ℂ
      ((S.tangentSpace (productPoint x y)).map (rationalDifferential f g (productPoint x y))) = S.dimension) := by
    apply (((htr.and hX hY hchart).and hX hY hdx).and hX hY hdy).mono
    intro x hx y hy hh
    rcases hh with ⟨⟨⟨htrans, hi⟩, hdx⟩, hdy⟩
    have hr := rational_secant_tangent_finrank X Y i x y hx hy hi htrans.2
    simpa only [S, f, g, product_dimension X Y hX hY, hdx, hdy] using hr
  have hrankSource : ForGeneralPoint S (fun p => Module.finrank ℂ
      ((S.tangentSpace p).map (rationalDifferential f g p)) = S.dimension) := by
    apply hrankPair.on_product.mono
    intro p hp hh
    have heq := productPoint_left_right p
    rw [heq] at hh
    exact hh
  have hdimW : W.dimension = S.dimension :=
    rational_image_dimension_eq_of_generic_rank S hS f g hgenW hrankSource
  have hdimW' : W'.dimension ≤ S'.dimension :=
    rational_image_dimension_le_of_generic_rank S' hS' f g hgenW'
  have hsourceEq : S'.dimension = S.dimension := by
    simp only [S, S', product_dimension X Y hX hY, product_dimension X Y' hX hY', hdim]
  have hdimEq : W.dimension = W'.dimension := by
    have hlo := irreducible_dimension_mono W W' hW hW' hsub
    rw [hsourceEq, ← hdimW] at hdimW'
    exact Nat.le_antisymm hlo hdimW'
  have hpos : 0 < W'.dimension := by
    rw [← hdimEq, hdimW]
    have hsdim := product_dimension X Y hX hY
    change 0 < (productVariety X Y).dimension
    rw [hsdim]
    omega
  have hWW' : W = W' := irreducible_subvariety_eq_of_pos_dimension_eq W W' hW hW' hsub hpos hdimEq
  obtain ⟨x, hx, y, hy, ⟨z, hz, hzx, hzy, c, hline⟩, hi⟩ := hrootchart.exists
  exact ⟨i, hWW', x, hx, z, hz,
    further_root_chart_ne_zero i x y z c
      (further_root_scalar_ne x y z c hzx hzy hline).1 hi hline⟩

/-- A linear equation in the direction half of the label coordinates. -/
def secantDirectionPoly {d : ℕ} (lam : Point d →ₗ[ℂ] ℂ) : Poly (d+d) :=
  MvPolynomial.rename (fun j => finSumFinEquiv (Sum.inr j)) (covectorPoly lam 0)

@[simp] theorem eval_secantDirectionPoly {d : ℕ} (lam : Point d →ₗ[ℂ] ℂ) (x u : Point d) :
    MvPolynomial.eval (productPoint x u) (secantDirectionPoly lam) = lam u := by
  rw [secantDirectionPoly, MvPolynomial.eval_rename]
  have hcoords : productPoint x u ∘ (fun j => finSumFinEquiv (Sum.inr j)) = u := by
    funext j
    exact productPoint_inr x u j
  rw [hcoords, eval_covectorPoly, sub_zero]

/-- If both original carriers lie in a flat, every generic further-root
target of the same positive dimension lies there too. -/
theorem generic_further_root_target_in_flat {d : ℕ} (X Y Z : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible) (hZ : Z.IsIrreducible)
    (hdim : Z.dimension = Y.dimension) (hlpos : 0 < Y.dimension)
    (htr : GenericallyTransverse X Y)
    (hroot : ForGeneralPair X Y (fun x y =>
      ∃ z ∈ Z, z ≠ x ∧ z ≠ y ∧ ∃ c : ℂ, z - x = c • (y - x)))
    (F : AffineSubspace ℂ (Point d)) (hXF : X.points ⊆ F) (hYF : Y.points ⊆ F) :
    Z.points ⊆ F := by
  obtain ⟨i, heq, x₀, hx₀, z₀, hz₀, hi₀⟩ :=
    further_root_label_images X Y Z hX hY hZ hdim hlpos htr hroot
  intro z hz
  by_contra hzF
  have hu : z-x₀ ∉ F.direction := by
    intro hu
    have hm := AffineSubspace.vadd_mem_of_mem_direction hu (hXF hx₀)
    apply hzF
    change z ∈ F
    simpa only [vadd_eq_add, vsub_eq_sub, sub_add_cancel] using hm
  obtain ⟨lam, hlam, hmap⟩ := F.direction.exists_dual_map_eq_bot_of_notMem hu inferInstance
  have hzero : ∀ u ∈ F.direction, lam u = 0 := by
    intro u hu
    have hm : lam u ∈ F.direction.map lam := Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    simpa only [hmap, Submodule.mem_bot] using hm
  have hq : secantDirectionPoly lam ∈
      (rationalImage (productVariety X Y) (secantChartNumerator i) (secantChartDenominator i)).ideal := by
    rintro p ⟨a, ha, hg, rfl⟩
    obtain ⟨hx, hy⟩ : productLeft a ∈ X ∧ productRight a ∈ Y := by
      change a ∈ (productVariety X Y).points at ha
      rw [productVariety_points] at ha
      exact ha
    have haeq := productPoint_left_right a
    rw [← haeq] at hg ⊢
    have hi : (productRight a - productLeft a) i ≠ 0 := by
      simpa only [eval_secantChartDenominator] using hg
    change MvPolynomial.eval _ _ = 0
    rw [rational_secant_label i _ _ hi, eval_secantDirectionPoly]
    rw [dirChart, map_smul]
    have hdir : productRight a - productLeft a ∈ F.direction :=
      AffineSubspace.vsub_mem_direction (hYF hy) (hXF hx)
    rw [hzero _ hdir]
    simp
  rw [heq] at hq
  let g : Poly d := MvPolynomial.X i - MvPolynomial.C (x₀ i)
  have heval (u : Point d) : MvPolynomial.eval u g = (u-x₀) i := by
    simp only [g, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, Pi.sub_apply]
  have hgen : ForGeneralPoint Z (fun u => MvPolynomial.eval u (covectorPoly lam x₀) = 0) := by
    refine ⟨g, ⟨z₀, hz₀, by simpa only [heval] using hi₀⟩, ?_⟩
    intro u hu hgu
    have hi : (u-x₀) i ≠ 0 := by simpa only [heval] using hgu
    have hp := rationalPoint_mem_image (productVariety X Z) (secantChartNumerator i)
      (secantChartDenominator i) (productPoint x₀ u)
      (AffineVariety.subset_closure _ ⟨x₀, hx₀, u, hu, rfl⟩)
      (by simpa only [eval_secantChartDenominator] using hi)
    have hv := (mem_ideal_iff_eval_zero _ _).mp hq _ hp
    rw [rational_secant_label i x₀ u hi, eval_secantDirectionPoly, dirChart, map_smul,
      smul_eq_mul] at hv
    have hlu : lam (u-x₀) = 0 := (mul_eq_zero.mp hv).resolve_left (inv_ne_zero hi)
    rw [eval_covectorPoly]
    exact hlu
  have hzlam := ForGeneralPoint.eval_zero hZ (covectorPoly lam x₀) hgen z hz
  rw [eval_covectorPoly] at hzlam
  exact hlam hzlam

/-- Transversality to a flat target excludes containment of the source in
that flat, so a general source point avoids the target. -/
theorem genericallyTransverse_avoid_flat {d : ℕ} (X Z : AffineVariety d)
    (hflat : IsFlat Z) (htr : GenericallyTransverse X Z) :
    ForGeneralPoint X (fun x => x ∉ Z.points) := by
  obtain ⟨F, hF⟩ := hflat
  have hnot : ¬ X.points ⊆ F := by
    intro hXF
    obtain ⟨x, hx, z, hz, htrans⟩ := htr.exists
    have hzF : z ∈ F := by
      change z ∈ Z.points at hz
      rw [hF] at hz
      exact hz
    exact htrans.2 (RealFlatGeometry.flat_direction_le_tangent Z F hF z
      (by change z ∈ Z.points; rwa [hF])
      (AffineSubspace.vsub_mem_direction hzF (hXF hx)))
  apply (ForGeneralPoint.avoid_flat F hnot).mono
  intro x hx hn hxZ
  apply hn
  change x ∈ (F : Set (Point d))
  rwa [← hF]

/-- A line through a point outside a containing flat meets the target in
at most one point. This is the literal root set, with the centre removed. -/
theorem flat_secant_roots_subsingleton {d : ℕ} (Z : AffineVariety d)
    (hflat : IsFlat Z) (x y : Point d) (hx : x ∉ Z.points) :
    {z : Point d | z ∈ Z ∧ z ≠ x ∧ ∃ c : ℂ, z-x = c • (y-x)}.Subsingleton := by
  obtain ⟨F, hF⟩ := hflat
  have hxF : x ∉ F := by
    intro hxF
    apply hx
    rwa [hF]
  by_cases hyx : y = x
  · rintro z ⟨hz, hzx, c, hc⟩
    rw [hyx, sub_self, smul_zero] at hc
    exact (hzx (sub_eq_zero.mp hc)).elim
  · have hfib := GeoRadial.radial_fiber_subsingleton F x Z
      (by rw [hF]) hxF (radialProjection x y hyx)
    have hsub : {z : Point d | z ∈ Z ∧ z ≠ x ∧ ∃ c : ℂ, z-x = c • (y-x)} ⊆
        radialFiber x Z (radialProjection x y hyx) := by
      rintro z ⟨hz, hzx, c, hc⟩
      refine ⟨hz, hzx, ?_⟩
      exact (Projectivization.mk_eq_mk_iff' ℂ (z-x) (y-x)
        (sub_ne_zero.mpr hzx) (sub_ne_zero.mpr hyx)).mpr ⟨c, hc.symm⟩
    exact fun z hz u hu => hfib (hsub hz) (hsub hu)

namespace ConstructibleSecants

/-- The maximal evaluation ideal of an actual complex point. -/
def evalPrime {σ : Type*} (x : σ → ℂ) : PrimeSpectrum (MvPolynomial σ ℂ) :=
  ⟨MvPolynomial.vanishingIdeal ℂ {x}, inferInstance⟩

@[simp] theorem mem_evalPrime {σ : Type*} (x : σ → ℂ) (f : MvPolynomial σ ℂ) :
    f ∈ (evalPrime x).asIdeal ↔ MvPolynomial.eval x f = 0 := by
  exact MvPolynomial.mem_vanishingIdeal_singleton_iff x f

theorem evalPrime_maximal {σ : Type*} (x : σ → ℂ) : (evalPrime x).asIdeal.IsMaximal := by
  dsimp [evalPrime]
  infer_instance

@[simp] theorem evalPrime_comap_inl {σ τ : Type*} (x : σ ⊕ τ → ℂ) :
    PrimeSpectrum.comap (MvPolynomial.rename (R := ℂ) (Sum.inl : σ → σ ⊕ τ)).toRingHom
      (evalPrime x) = evalPrime (x ∘ Sum.inl) := by
  apply PrimeSpectrum.ext
  ext f
  change MvPolynomial.rename Sum.inl f ∈ (evalPrime x).asIdeal ↔
    f ∈ (evalPrime (x ∘ Sum.inl)).asIdeal
  simp only [mem_evalPrime, MvPolynomial.eval_rename]

/-- A prime lift over a complex evaluation ideal gives an actual complex
point after enlargement to a maximal ideal. All constraints are closed. -/
theorem projection_closed_point {σ τ : Type*} [Finite σ] [Finite τ]
    (I : Ideal (MvPolynomial (σ ⊕ τ) ℂ)) (x : σ → ℂ) :
    evalPrime x ∈ PrimeSpectrum.comap
      (MvPolynomial.rename (R := ℂ) (Sum.inl : σ → σ ⊕ τ)).toRingHom ''
        PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (σ ⊕ τ) ℂ)) ↔
      ∃ v : τ → ℂ, Sum.elim x v ∈ MvPolynomial.zeroLocus ℂ I := by
  let rho : MvPolynomial σ ℂ →+* MvPolynomial (σ ⊕ τ) ℂ :=
    (MvPolynomial.rename Sum.inl).toRingHom
  constructor
  · rintro ⟨q, hqI, hqx⟩
    have hI : I ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus q _).mp hqI
    obtain ⟨M, hM, hqM⟩ := q.asIdeal.exists_le_maximal q.isPrime.ne_top
    have hxq : (evalPrime x).asIdeal = q.asIdeal.comap rho := by
      exact (congrArg PrimeSpectrum.asIdeal hqx).symm
    have hxM : (evalPrime x).asIdeal = M.comap rho :=
      (evalPrime_maximal x).eq_of_le (hM.isPrime.comap rho).ne_top
        (by rw [hxq]; exact Ideal.comap_mono hqM)
    obtain ⟨w, hw⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
    have hleft : ∀ j : σ, w (Sum.inl j) = x j := by
      intro j
      let f : MvPolynomial σ ℂ := MvPolynomial.X j - MvPolynomial.C (x j)
      have hf : f ∈ (evalPrime x).asIdeal := by
        rw [mem_evalPrime]
        simp [f]
      have hrf : rho f ∈ M := by
        exact (show f ∈ M.comap rho from hxM ▸ hf)
      rw [hw] at hrf
      have hzero := (MvPolynomial.mem_vanishingIdeal_singleton_iff w (rho f)).mp hrf
      apply sub_eq_zero.mp
      simpa [rho, f] using hzero
    let v : τ → ℂ := fun j => w (Sum.inr j)
    have heq : w = Sum.elim x v := by
      funext j
      cases j with
      | inl j => exact hleft j
      | inr j => rfl
    refine ⟨v, ?_⟩
    intro f hf
    have hfM : f ∈ M := hqM (hI hf)
    rw [hw] at hfM
    have hz := (MvPolynomial.mem_vanishingIdeal_singleton_iff w f).mp hfM
    rw [heq] at hz
    exact hz
  · rintro ⟨v, hv⟩
    refine ⟨evalPrime (Sum.elim x v), ?_, ?_⟩
    · apply (PrimeSpectrum.mem_zeroLocus _ _).mpr
      intro f hf
      exact (mem_evalPrime _ f).mpr (hv f hf)
    · simpa only [evalPrime_comap_inl, Function.comp_def, Sum.elim_inl]

/-- Polynomial coordinate projections are finitely presented over their
Noetherian polynomial base. -/
theorem rename_inl_finitePresentation {σ τ : Type*} [Finite σ] [Finite τ] :
    (MvPolynomial.rename (R := ℂ) (Sum.inl : σ → σ ⊕ τ)).toRingHom.FinitePresentation := by
  let R := MvPolynomial σ ℂ
  let A := MvPolynomial (σ ⊕ τ) ℂ
  let rho : R →+* A := (MvPolynomial.rename Sum.inl).toRingHom
  letI : Algebra R A := rho.toAlgebra
  letI : IsScalarTower ℂ R A := IsScalarTower.of_algebraMap_eq (by
    intro c
    change MvPolynomial.C c = rho (MvPolynomial.C c)
    exact (MvPolynomial.rename_C (R := ℂ) (Sum.inl : σ → σ ⊕ τ) c).symm)
  letI : Algebra.FiniteType R A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ R A
  change @Algebra.FinitePresentation R A _ _ rho.toAlgebra
  exact (Algebra.FinitePresentation.of_finiteType (R := R) (A := A)).mp inferInstance

theorem projection_constructible {σ τ : Type*} [Finite σ] [Finite τ]
    (I : Ideal (MvPolynomial (σ ⊕ τ) ℂ)) :
    Topology.IsConstructible (PrimeSpectrum.comap
      (MvPolynomial.rename (R := ℂ) (Sum.inl : σ → σ ⊕ τ)).toRingHom ''
        PrimeSpectrum.zeroLocus (I : Set (MvPolynomial (σ ⊕ τ) ℂ))) := by
  apply PrimeSpectrum.isConstructible_comap_image rename_inl_finitePresentation
  have hfg : I.FG := (inferInstance : IsNoetherianRing (MvPolynomial (σ ⊕ τ) ℂ)).noetherian I
  have hc := (PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg hfg).isConstructible
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  simpa only [compl_compl] using hc.compl

/-- On an irreducible carrier each fixed polynomial either vanishes
everywhere or is nonzero on a nonempty principal open. -/
theorem general_polynomial_test {n : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (f : Poly n) :
    ForGeneralPoint V (fun x => (MvPolynomial.eval x f = 0 ↔ f ∈ V.ideal)) := by
  classical
  by_cases hf : f ∈ V.ideal
  · obtain ⟨x, hx⟩ := V.points_nonempty_of_isIrreducible hV
    refine ⟨1, ⟨x, hx, by simp⟩, ?_⟩
    intro y hy hn
    have hz := (mem_ideal_iff_eval_zero V f).mp hf y hy
    simp only [hf, hz]
  · have hex : ∃ x ∈ V, MvPolynomial.eval x f ≠ 0 := by
      by_contra he
      push Not at he
      exact hf ((mem_ideal_iff_eval_zero V f).mpr he)
    exact ⟨f, hex, fun _ _ hn => by simp only [hn, hf]⟩

def basicVerdict {n : ℕ} (V : AffineVariety n)
    (C : PrimeSpectrum.BasicConstructibleSetData (Poly n)) : Prop :=
  (∀ i, C.g i ∈ V.ideal) ∧ C.f ∉ V.ideal

theorem general_basic_piece {n : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (C : PrimeSpectrum.BasicConstructibleSetData (Poly n)) :
    ForGeneralPoint V (fun x => (evalPrime x ∈ C.toSet ↔ basicVerdict V C)) := by
  have hg := ForGeneralPoint.finset_all hV (V.points_nonempty_of_isIrreducible hV)
    (Finset.univ : Finset (Fin C.n)) (fun i x => (MvPolynomial.eval x (C.g i) = 0 ↔ C.g i ∈ V.ideal))
    (fun i _ => general_polynomial_test V hV (C.g i))
  apply (hg.and hV (general_polynomial_test V hV C.f)).mono
  intro x hx ht
  have hp : evalPrime x ∈ C.toSet ↔
      (∀ i, MvPolynomial.eval x (C.g i) = 0) ∧ MvPolynomial.eval x C.f ≠ 0 := by
    simp only [PrimeSpectrum.BasicConstructibleSetData.toSet, Set.mem_sdiff,
      PrimeSpectrum.mem_zeroLocus, Set.range_subset_iff, Set.singleton_subset_iff,
      SetLike.mem_coe, mem_evalPrime]
  rw [hp]
  constructor
  · rintro ⟨hgx, hfx⟩
    refine ⟨fun i => (ht.1 i (Finset.mem_univ i)).mp (hgx i), ?_⟩
    intro hf
    exact hfx (ht.2.mpr hf)
  · rintro ⟨hgi, hfi⟩
    refine ⟨fun i => (ht.1 i (Finset.mem_univ i)).mpr (hgi i), ?_⟩
    intro hf
    exact hfi (ht.2.mp hf)

theorem general_constructible_data {n : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (T : PrimeSpectrum.ConstructibleSetData (Poly n)) :
    ForGeneralPoint V (fun x => (evalPrime x ∈ T.toSet ↔ ∃ C ∈ T, basicVerdict V C)) := by
  have ht := ForGeneralPoint.finset_all hV (V.points_nonempty_of_isIrreducible hV) T
    (fun C x => (evalPrime x ∈ C.toSet ↔ basicVerdict V C))
    (fun C _ => general_basic_piece V hV C)
  apply ht.mono
  intro x hx h
  simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion]
  constructor
  · rintro ⟨C, hC, hxC⟩
    exact ⟨C, hC, (h C hC).mp hxC⟩
  · rintro ⟨C, hC, hvC⟩
    exact ⟨C, hC, (h C hC).mpr hvC⟩

/-- A finite polynomial constructible description has constant membership
on some nonempty principal open of an irreducible complex carrier. -/
theorem constructible_point_dichotomy {n : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (U : Set (PrimeSpectrum (Poly n))) (hU : Topology.IsConstructible U) :
    ForGeneralPoint V (fun x => evalPrime x ∈ U) ∨
      ForGeneralPoint V (fun x => evalPrime x ∉ U) := by
  classical
  obtain ⟨T, hT⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hU
  have ht := general_constructible_data V hV T
  rw [← hT]
  by_cases hb : ∃ C ∈ T, basicVerdict V C
  · exact Or.inl (ht.mono (fun _ _ h => h.mpr hb))
  · exact Or.inr (ht.mono (fun _ _ h hn => hb (h.mp hn)))

/-- Base coordinates followed by the secant scalar and an inverse variable. -/
abbrev IncidencePoly (d : ℕ) := MvPolynomial (Fin (d+d) ⊕ Fin 2) ℂ

def incidencePoint {d : ℕ} (x y : Point d) (v : Fin 2 → ℂ) :
    Fin (d+d) ⊕ Fin 2 → ℂ := Sum.elim (productPoint x y) v

def sourceForm {d : ℕ} (j : Fin d) : IncidencePoly d :=
  MvPolynomial.X (Sum.inl (finSumFinEquiv (Sum.inl j)))

def targetForm {d : ℕ} (j : Fin d) : IncidencePoly d :=
  MvPolynomial.X (Sum.inl (finSumFinEquiv (Sum.inr j)))

def rootForm {d : ℕ} (j : Fin d) : IncidencePoly d :=
  sourceForm j + MvPolynomial.X (Sum.inr 0) * (targetForm j - sourceForm j)

def inverseEquation {d : ℕ} (i : Fin d) : IncidencePoly d :=
  MvPolynomial.X (Sum.inr 0) * (MvPolynomial.X (Sum.inr 0) - 1) *
    (targetForm i - sourceForm i) * MvPolynomial.X (Sum.inr 1) - 1

def incidenceIdeal {d : ℕ} (Z : AffineVariety d) (i : Fin d) : Ideal (IncidencePoly d) :=
  Ideal.span (Set.range (fun f : Z.ideal => MvPolynomial.aeval rootForm f.val)) ⊔
    Ideal.span {inverseEquation i}

@[simp] theorem eval_rootForm {d : ℕ} (j : Fin d) (x y : Point d) (v : Fin 2 → ℂ) :
    MvPolynomial.eval (incidencePoint x y v) (rootForm j) = (x + v 0 • (y-x)) j := by
  simp only [rootForm, sourceForm, targetForm, map_add, map_mul, map_sub, MvPolynomial.eval_X,
    incidencePoint, Sum.elim_inl, Sum.elim_inr, productPoint_inl, productPoint_inr,
    Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]

@[simp] theorem eval_inverseEquation {d : ℕ} (i : Fin d) (x y : Point d) (v : Fin 2 → ℂ) :
    MvPolynomial.eval (incidencePoint x y v) (inverseEquation i) =
      v 0 * (v 0 - 1) * (y-x) i * v 1 - 1 := by
  simp only [inverseEquation, sourceForm, targetForm, map_mul, map_sub, map_one,
    MvPolynomial.eval_X, incidencePoint, Sum.elim_inl, Sum.elim_inr,
    productPoint_inl, productPoint_inr, Pi.sub_apply]

/-- Literal solutions of the closed incidence equations are exactly target
points on the secant with the chosen denominator invertible. -/
theorem incidence_mem_iff {d : ℕ} (Z : AffineVariety d) (i : Fin d)
    (x y : Point d) (v : Fin 2 → ℂ) :
    incidencePoint x y v ∈ MvPolynomial.zeroLocus ℂ (incidenceIdeal Z i) ↔
      x + v 0 • (y-x) ∈ Z ∧ v 0 * (v 0 - 1) * (y-x) i * v 1 = 1 := by
  have hcoords : (fun j : Fin d => MvPolynomial.eval (incidencePoint x y v) (rootForm j)) =
      x + v 0 • (y-x) := by
    funext j
    exact eval_rootForm j x y v
  constructor
  · intro hp
    constructor
    · intro f hf
      have hgen : MvPolynomial.aeval rootForm f ∈ incidenceIdeal Z i := by
        apply (le_sup_left : Ideal.span
          (Set.range (fun q : Z.ideal => MvPolynomial.aeval rootForm q.val)) ≤ incidenceIdeal Z i)
        exact Ideal.subset_span ⟨⟨f, hf⟩, rfl⟩
      have hzero := hp _ hgen
      change MvPolynomial.aeval (incidencePoint x y v) (MvPolynomial.aeval rootForm f) = 0 at hzero
      rw [MvPolynomial.comp_aeval_apply] at hzero
      change MvPolynomial.eval
        (fun j => MvPolynomial.eval (incidencePoint x y v) (rootForm j)) f = 0 at hzero
      rw [hcoords] at hzero
      exact hzero
    · have hgen : inverseEquation i ∈ incidenceIdeal Z i := by
        apply (le_sup_right : Ideal.span {inverseEquation i} ≤ incidenceIdeal Z i)
        exact Ideal.subset_span (Set.mem_singleton _)
      have hzero := hp _ hgen
      change MvPolynomial.eval (incidencePoint x y v) (inverseEquation i) = 0 at hzero
      rw [eval_inverseEquation] at hzero
      exact sub_eq_zero.mp hzero
  · rintro ⟨hz, hinv⟩
    have hle : incidenceIdeal Z i ≤
        RingHom.ker (MvPolynomial.aeval (incidencePoint x y v)).toRingHom := by
      apply sup_le
      · apply Ideal.span_le.mpr
        rintro f ⟨q, rfl⟩
        change MvPolynomial.aeval (incidencePoint x y v) (MvPolynomial.aeval rootForm q.val) = 0
        rw [MvPolynomial.comp_aeval_apply]
        change MvPolynomial.eval
          (fun j => MvPolynomial.eval (incidencePoint x y v) (rootForm j)) q.val = 0
        rw [hcoords]
        exact hz q.val q.property
      · apply Ideal.span_le.mpr
        intro f hf
        have hf' : f = inverseEquation i := Set.mem_singleton_iff.mp hf
        subst f
        change MvPolynomial.eval (incidencePoint x y v) (inverseEquation i) = 0
        rw [eval_inverseEquation, hinv, sub_self]
    exact fun f hf => hle hf

/-- The inverse equation encodes all inequalities in the further-root
condition; the finite union of nonzero coordinate charts is exact. -/
theorem further_root_iff_incidence {d : ℕ} (Z : AffineVariety d) (x y : Point d) :
    (∃ z ∈ Z, z ≠ x ∧ z ≠ y ∧ ∃ c : ℂ, z-x = c • (y-x)) ↔
      ∃ i : Fin d, ∃ v : Fin 2 → ℂ,
        incidencePoint x y v ∈ MvPolynomial.zeroLocus ℂ (incidenceIdeal Z i) := by
  classical
  constructor
  · rintro ⟨z, hz, hzx, hzy, c, hline⟩
    obtain ⟨hc0, hc1⟩ := further_root_scalar_ne x y z c hzx hzy hline
    have hu : y-x ≠ 0 := by
      intro hu
      rw [hu, smul_zero] at hline
      exact hzx (sub_eq_zero.mp hline)
    obtain ⟨i, hi⟩ : ∃ i : Fin d, (y-x) i ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hu (funext hn)
    let a : ℂ := c * (c-1) * (y-x) i
    have ha : a ≠ 0 := mul_ne_zero (mul_ne_zero hc0 (sub_ne_zero.mpr hc1)) hi
    let v : Fin 2 → ℂ := Fin.cases c (fun _ => a⁻¹)
    have hv0 : v 0 = c := rfl
    have hv1 : v 1 = a⁻¹ := rfl
    refine ⟨i, v, (incidence_mem_iff Z i x y v).mpr ⟨?_, ?_⟩⟩
    · rw [hv0]
      have heq : x + c • (y-x) = z := by rw [← hline]; abel
      rwa [heq]
    · rw [hv0, hv1]
      exact mul_inv_cancel₀ ha
  · rintro ⟨i, v, hp⟩
    obtain ⟨hz, hinv⟩ := (incidence_mem_iff Z i x y v).mp hp
    have hn : v 0 * (v 0 - 1) * (y-x) i * v 1 ≠ 0 := by rw [hinv]; exact one_ne_zero
    simp only [mul_ne_zero_iff] at hn
    obtain ⟨⟨⟨hc0, hc1⟩, hi⟩, ht⟩ := hn
    have hu : y-x ≠ 0 := by intro hu; exact hi (by rw [hu]; rfl)
    let z : Point d := x + v 0 • (y-x)
    have hline : z-x = v 0 • (y-x) := by dsimp [z]; abel
    have hzx : z ≠ x := by
      intro hz
      have he : v 0 • (y-x) = 0 := by rw [← hline, hz, sub_self]
      exact smul_ne_zero hc0 hu he
    have hzy : z ≠ y := by
      intro hz
      have he : v 0 • (y-x) = y-x := by rw [← hline, hz]
      have he0 : (v 0 - 1) • (y-x) = 0 := by rw [sub_smul, one_smul, he, sub_self]
      exact smul_ne_zero hc1 hu he0
    exact ⟨z, hz, hzx, hzy, v 0, hline⟩

def furtherRootLocus {d : ℕ} (Z : AffineVariety d) : Set (PrimeSpectrum (Poly (d+d))) :=
  ⋃ i : Fin d, PrimeSpectrum.comap
    (MvPolynomial.rename (R := ℂ) (Sum.inl : Fin (d+d) → Fin (d+d) ⊕ Fin 2)).toRingHom ''
      PrimeSpectrum.zeroLocus (incidenceIdeal Z i : Set (IncidencePoly d))

theorem furtherRootLocus_constructible {d : ℕ} (Z : AffineVariety d) :
    Topology.IsConstructible (furtherRootLocus Z) :=
  Topology.IsConstructible.iUnion (fun i => projection_constructible (incidenceIdeal Z i))

/-- The spectral constructible locus is the actual further-root existential
condition at every complex pair, rather than merely its closure. -/
theorem mem_furtherRootLocus {d : ℕ} (Z : AffineVariety d) (x y : Point d) :
    evalPrime (productPoint x y) ∈ furtherRootLocus Z ↔
      ∃ z ∈ Z, z ≠ x ∧ z ≠ y ∧ ∃ c : ℂ, z-x = c • (y-x) := by
  rw [further_root_iff_incidence]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    obtain ⟨v, hv⟩ := (projection_closed_point (incidenceIdeal Z i) (productPoint x y)).mp hi
    exact ⟨i, v, hv⟩
  · rintro ⟨i, v, hv⟩
    apply Set.mem_iUnion.mpr
    exact ⟨i, (projection_closed_point (incidenceIdeal Z i) (productPoint x y)).mpr ⟨v, hv⟩⟩

theorem general_product_to_pair {d : ℕ} (X Y : AffineVariety d)
    (Q : Point d → Point d → Prop)
    (h : ForGeneralPoint (productVariety X Y) (fun p => Q (productLeft p) (productRight p))) :
    ForGeneralPair X Y Q := by
  obtain ⟨g, ⟨p, hp, hg⟩, hQ⟩ := h
  have hpXY : productLeft p ∈ X ∧ productRight p ∈ Y := by
    change p ∈ (productVariety X Y).points at hp
    rwa [productVariety_points] at hp
  have hleft (x y : Point d) : productLeft (productPoint x y) = x :=
    congrArg Prod.fst (productLinearEquiv.left_inv (x,y))
  have hright (x y : Point d) : productRight (productPoint x y) = y :=
    congrArg Prod.snd (productLinearEquiv.left_inv (x,y))
  refine ⟨MvPolynomial.rename finSumFinEquiv.symm g,
    ⟨productLeft p, hpXY.1, productRight p, hpXY.2, ?_⟩, ?_⟩
  · simpa only [eval_product_rename, productPoint_left_right] using hg
  · intro x hx y hy hn
    have hp : productPoint x y ∈ productVariety X Y :=
      AffineVariety.subset_closure _ ⟨x, hx, y, hy, rfl⟩
    have hh := hQ (productPoint x y) hp (by simpa only [eval_product_rename] using hn)
    simpa only [hleft, hright] using hh

/-- Chevalley and the closed-point bridge give the exact generic
further-root alternative needed by secants, for arbitrary fixed targets. -/
theorem generic_further_root_dichotomy {d : ℕ} (X Y Z : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible) :
    ForGeneralPair X Y (fun x y => ∃ z ∈ Z, z ≠ x ∧ z ≠ y ∧ ∃ c : ℂ, z-x = c • (y-x)) ∨
    ForGeneralPair X Y (fun x y => ¬ ∃ z ∈ Z, z ≠ x ∧ z ≠ y ∧ ∃ c : ℂ, z-x = c • (y-x)) := by
  obtain hp | hn := constructible_point_dichotomy (productVariety X Y)
    (productVariety_irreducible X Y hX hY) (furtherRootLocus Z)
    (furtherRootLocus_constructible Z)
  · left
    apply general_product_to_pair X Y
    apply hp.mono
    intro p hp h
    exact (mem_furtherRootLocus Z (productLeft p) (productRight p)).mp
      (by simpa only [productPoint_left_right] using h)
  · right
    apply general_product_to_pair X Y
    apply hn.mono
    intro p hp h hroot
    apply h
    simpa only [productPoint_left_right] using
      (mem_furtherRootLocus Z (productLeft p) (productRight p)).mpr hroot

end ConstructibleSecants

namespace TripleGeneric

variable {d : ℕ}

/-- At a valid centre, the secant obstruction and constructibility give
absence on a principal open of source-target pairs. -/
theorem further_root_absent
    (p : Point 3) (Y₁ Y₂ Y₃ Y Z : AffineVariety 3)
    (hv : CurveTripleValid p Y₁ Y₂ Y₃)
    (hY₁ : IsCurve Y₁) (hY : IsCurve Y) (hZ : IsCurve Z)
    (hnl₁ : ¬ IsLine Y₁) (hnlY : ¬ IsLine Y)
    (hYm : Y ∈ ({Y₂, Y₃} : Finset _)) :
    ForGeneralPair Y₁ Y (fun v y =>
      ¬ ∃ z ∈ Z, z ≠ v ∧ z ≠ y ∧ ∃ c : ℂ, z-v = c • (y-v)) := by
  obtain h | h := ConstructibleSecants.generic_further_root_dichotomy Y₁ Y Z hY₁.1 hY.1
  · exact (curveTripleValid_not_generic_further_root p Y₁ Y₂ Y₃ Y Z hv
      hY₁ hY hZ hnl₁ hnlY hYm h).elim
  · exact h

theorem general_point_ne (p : Point d) (Y : AffineVariety d) (hY : IsCurve Y) :
    ForGeneralPoint Y (fun y => y ≠ p) := by
  obtain ⟨y, hy, hyp⟩ := GeoRadial.curve_point_off p Y hY
  obtain ⟨i, hi⟩ := GeoRadial.exists_coord (y-p) (sub_ne_zero.mpr hyp)
  refine ⟨MvPolynomial.X i - MvPolynomial.C (p i), ⟨y, hy, ?_⟩, ?_⟩
  · simpa using hi
  · intro x hx hn he
    subst x
    simpa using hn

/-- Distinct irreducible curves have a principal open disjoint from one another. -/
theorem general_avoid_curve (X Y : AffineVariety d) (hX : IsCurve X) (hY : IsCurve Y)
    (hne : X ≠ Y) : ForGeneralPoint X (fun x => x ∉ Y.points) := by
  have hnot : ¬ X.points ⊆ Y.points := by
    intro hsub
    exact hne (GeoRadial.curve_eq_of_subset X Y hY.1 hX.2 hY.2 hsub)
  obtain ⟨x, hx, hxy⟩ := Set.not_subset.mp hnot
  have hex : ∃ f ∈ Y.ideal, MvPolynomial.eval x f ≠ 0 := by
    by_contra! h
    exact hxy h
  obtain ⟨f, hf, hfx⟩ := hex
  exact ⟨f, ⟨x, hx, hfx⟩, fun y hy hn hyY => hn (hyY f hf)⟩

def radialPullback (p : Point d) (g : Poly d) : Poly d :=
  MvPolynomial.aeval (fun j => MvPolynomial.X j - MvPolynomial.C (p j)) g

@[simp] theorem eval_radialPullback (p x : Point d) (g : Poly d) :
    MvPolynomial.eval x (radialPullback p g) = MvPolynomial.eval (x-p) g := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [radialPullback]
  | add f g hf hg => simp_all [radialPullback]
  | mul_X f i hf => simp_all [radialPullback]

/-- A homogeneous open of the radial image pulls back to a nonempty
principal open of the actual affine source. -/
theorem radial_nonzero_open (p : Point d) (Y : AffineVariety d) (hY : IsCurve Y)
    (g : Poly d) (D : ℕ) (hg : g.IsHomogeneous D) (hnot : g ∉ (radialImage p Y).ideal) :
    ForGeneralPoint Y (fun y => ∃ hy : y ≠ p,
      MvPolynomial.aeval (radialProjection p y hy).rep g ≠ 0) := by
  have hex : ∃ y ∈ Y, MvPolynomial.eval (y-p) g ≠ 0 := by
    by_contra! h
    apply hnot
    rintro u ⟨hu, y, hy, hyp, heq⟩
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ u (y-p) hu
      (sub_ne_zero.mpr hyp)).mp heq.symm
    change MvPolynomial.eval u g = 0
    rw [← hc, Bridges.homogeneous_eval_smul g hg, h y hy, mul_zero]
  have hopen : ForGeneralPoint Y (fun y => MvPolynomial.eval (y-p) g ≠ 0) := by
    refine ⟨radialPullback p g, ?_, ?_⟩
    · simpa only [eval_radialPullback] using hex
    · intro y hy hn
      simpa only [eval_radialPullback] using hn
  apply (hopen.and hY.1 (general_point_ne p Y hY)).mono
  intro y hy h
  refine ⟨h.2, ?_⟩
  change MvPolynomial.eval (Projectivization.mk ℂ (y-p) (sub_ne_zero.mpr h.2)).rep g ≠ 0
  exact fun hz => h.1 ((Bridges.homogeneous_eval_zero_mk_iff g hg _ _).mp hz)

/-- A further-root-free direction has exactly its specified source point
in its literal fibre. -/
theorem radial_fiber_singleton (v : Point d) (Y : AffineVariety d)
    (y : Point d) (hy : y ∈ Y.points) (hyv : y ≠ v)
    (hroot : ¬ ∃ z ∈ Y, z ≠ v ∧ z ≠ y ∧ ∃ c : ℂ, z-v = c • (y-v)) :
    radialFiber v Y (radialProjection v y hyv) = {y} := by
  ext z
  constructor
  · rintro ⟨hz, hzv, hproj⟩
    apply Set.mem_singleton_iff.mpr
    by_contra hzy
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ (z-v) (y-v)
      (sub_ne_zero.mpr hzv) (sub_ne_zero.mpr hyv)).mp hproj
    exact hroot ⟨z, hz, hzv, hzy, c, hc.symm⟩
  · rintro rfl
    exact ⟨hy, hyv, rfl⟩

theorem general_radial_fiber_singleton (v : Point d) (Y : AffineVariety d) (hY : IsCurve Y)
    (hroot : ForGeneralPoint Y (fun y =>
      ¬ ∃ z ∈ Y, z ≠ v ∧ z ≠ y ∧ ∃ c : ℂ, z-v = c • (y-v))) :
    ForGeneralPoint Y (fun y => ∃ hy : y ≠ v,
      radialFiber v Y (radialProjection v y hy) = {y}) := by
  apply (hroot.and hY.1 (general_point_ne v Y hY)).mono
  intro y hy h
  exact ⟨h.2, radial_fiber_singleton v Y y hy h.2 h.1⟩

/-- The generic degree is one once a principal open of literal fibres is
singleton; the dimension hypothesis supplies existence of that degree. -/
theorem radialMapDegree_eq_one (v : Point d) (Y : AffineVariety d) (hY : IsCurve Y)
    (hdim : (radialImage v Y).dimension = 1)
    (hroot : ForGeneralPoint Y (fun y =>
      ¬ ∃ z ∈ Y, z ≠ v ∧ z ≠ y ∧ ∃ c : ℂ, z-v = c • (y-v))) :
    radialMapDegree v Y = 1 := by
  have hex : ∃ r, GenericallyFiniteRadialDegree v Y r :=
    ⟨_, TrackA.dep_radial_degree_exists Y hY.1 1 (by norm_num) hY.2 v hdim⟩
  have hdeg : GenericallyFiniteRadialDegree v Y (radialMapDegree v Y) := by
    simpa only [radialMapDegree, dif_pos hex] using Nat.find_spec hex
  obtain ⟨hr, g, D, hg, hnot, hfib⟩ := hdeg
  obtain ⟨y, hy, ⟨hyv, hsingle⟩, hyv', hnonzero⟩ :=
    ((general_radial_fiber_singleton v Y hY hroot).and hY.1
      (radial_nonzero_open v Y hY g D hg hnot)).exists
  have hcard := (hfib (radialProjection v y hyv)
    (GeoRadial.radial_mem v Y y hy hyv) hnonzero).2
  simpa only [hsingle, Set.ncard_singleton] using hcard.symm

/-- Cross-target absence forces distinct plane images. An equal image's
generic fibre supplies an actual point of the other target. -/
theorem radial_images_ne (v : Point d) (Y Z : AffineVariety d)
    (hY : IsCurve Y) (hZ : IsCurve Z) (hne : Y ≠ Z)
    (hdim : (radialImage v Z).dimension = 1)
    (hroot : ForGeneralPoint Y (fun y =>
      ¬ ∃ z ∈ Z, z ≠ v ∧ z ≠ y ∧ ∃ c : ℂ, z-v = c • (y-v))) :
    radialImage v Y ≠ radialImage v Z := by
  intro heq
  obtain ⟨hr, g, D, hg, hnot, hfib⟩ :=
    TrackA.dep_radial_degree_exists Z hZ.1 1 (by norm_num) hZ.2 v hdim
  rw [← heq] at hnot
  obtain ⟨y, hy, ⟨hrooty, hyv, hnonzero⟩, hyZ⟩ :=
    ((hroot.and hY.1 (radial_nonzero_open v Y hY g D hg hnot)).and hY.1
      (general_avoid_curve Y Z hY hZ hne)).exists
  have hdir : radialProjection v y hyv ∈ (radialImage v Z).points := by
    rw [← heq]
    exact GeoRadial.radial_mem v Y y hy hyv
  obtain ⟨hfinite, hcard⟩ := hfib _ hdir hnonzero
  have hncard : 0 < (radialFiber v Z (radialProjection v y hyv)).ncard := by
    rw [hcard]
    exact hr
  obtain ⟨z, hz, hzv, hproj⟩ := Set.nonempty_of_ncard_ne_zero (ne_of_gt hncard)
  have hzy : z ≠ y := by rintro rfl; exact hyZ hz
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ (z-v) (y-v)
    (sub_ne_zero.mpr hzv) (sub_ne_zero.mpr hyv)).mp hproj
  exact hrooty ⟨z, hz, hzv, hzy, c, hc.symm⟩

def coneForms (p : Point 3) : Fin 3 → Poly (3+3) := fun i =>
  MvPolynomial.X (finSumFinEquiv (Sum.inr (0 : Fin 3))) *
    (MvPolynomial.X (finSumFinEquiv (Sum.inl i)) - MvPolynomial.C (p i))

theorem coneForms_point (p y u : Point 3) :
    rationalPoint (coneForms p) 1 (productPoint y u) = u 0 • (y-p) := by
  ext i
  simp [rationalPoint, coneForms, productPoint, pairPt]

/-- The radial image cone is the polynomial image of the curve times a
scalar line. This matches the literal images before taking either closure. -/
theorem radial_cone_eq_image (p : Point 3) (Y : AffineVariety 3) (hY : IsCurve Y) :
    (radialImage p Y).affineCone = rationalImage
      (productVariety Y (Bridges.complexLine 0 (Pi.single (0 : Fin 3) 1))) (coneForms p) 1 := by
  let u : Point 3 := Pi.single (0 : Fin 3) 1
  have hu : u 0 ≠ 0 := by simp [u]
  let L := Bridges.complexLine 0 u
  let S := productVariety Y L
  have hline : L.points = {z | ∃ c : ℂ, z = c • u} := by
    simpa only [zero_add] using Bridges.complexLine_points (0 : Point 3) u 0 hu
  have hmem (c : ℂ) : c • u ∈ L := by
    change c • u ∈ L.points
    rw [hline]
    exact ⟨c, rfl⟩
  apply AffineVariety.ext
  apply le_antisymm
  · intro q hq
    rintro z ⟨w, hw, hg, rfl⟩
    have hparts : productLeft w ∈ Y ∧ productRight w ∈ L := by
      change w ∈ S.points at hw
      simpa only [S, productVariety_points, Set.mem_setOf_eq] using hw
    rw [← productPoint_left_right w, coneForms_point]
    let c := productRight w 0
    let y := productLeft w
    have hzero : (0 : Point 3) ∈ (radialImage p Y).affineCone.points :=
      GeoRadial.zero_mem_cone _ (GeoRadial.radial_nonempty p Y hY)
    by_cases hc : c = 0
    · simpa only [c, hc, zero_smul] using hzero q hq
    by_cases hyp : y = p
    · simpa only [y, hyp, sub_self, smul_zero] using hzero q hq
    have hz : c • (y-p) ∈ (radialImage p Y).affineCone.points := by
      apply (ProjectiveVariety.mem_points_mk_iff _ _ (smul_ne_zero hc (sub_ne_zero.mpr hyp))).mp
      have heq : Projectivization.mk ℂ (c • (y-p)) (smul_ne_zero hc (sub_ne_zero.mpr hyp)) =
          radialProjection p y hyp :=
        (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨c, rfl⟩
      rw [heq]
      exact GeoRadial.radial_mem p Y y hparts.1 hyp
    exact hz q hq
  · intro q hq
    rintro z ⟨hz, y, hy, hyp, heq⟩
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ z (y-p) hz
      (sub_ne_zero.mpr hyp)).mp heq.symm
    have hw : productPoint y (c • u) ∈ S :=
      AffineVariety.subset_closure _ ⟨y, hy, c • u, hmem c, rfl⟩
    have he : rationalPoint (coneForms p) 1 (productPoint y (c • u)) = z := by
      rw [coneForms_point]
      simpa [u] using hc
    exact hq z ⟨productPoint y (c • u), hw, by simp, he⟩

theorem radial_curve_image_dimension (p : Point 3) (Y : AffineVariety 3)
    (hY : IsCurve Y) (hnl : ¬ IsLine Y) : (radialImage p Y).dimension = 1 := by
  let u : Point 3 := Pi.single (0 : Fin 3) 1
  let L := Bridges.complexLine 0 u
  let S := productVariety Y L
  have hL : L.IsIrreducible := Bridges.complexLine_irreducible _ _
  have hS := productVariety_irreducible Y L hY.1 hL
  have hnot : (1 : Poly (3+3)) ∉ S.ideal := by
    intro h
    exact hS.ne_top (S.ideal.eq_top_of_isUnit_mem h isUnit_one)
  have hdim := rational_image_dimension_le_of_generic_rank S hS (coneForms p) 1
    (request_rational_image_generic_tangent S hS (coneForms p) 1 hnot).2
  have hLdim : L.dimension = 1 := Bridges.complexLine_dimension 0 u 0 (by simp [u])
  rw [product_dimension Y L hY.1 hL, hY.2, hLdim] at hdim
  rw [← radial_cone_eq_image p Y hY,
    (radialImage p Y).dimension_cone (GeoRadial.radial_nonempty p Y hY)] at hdim
  have hn := GeoRadial.radial_dimension_ne_zero p Y hY hnl
  omega

theorem radial_curve_image_degree_le (p : Point 3) (Y : AffineVariety 3)
    (hY : IsCurve Y) (hnl : ¬ IsLine Y) : (radialImage p Y).degree ≤ Y.degree := by
  have hdim := radial_curve_image_dimension p Y hY hnl
  have hdeg := TrackA.dep_radial_degree_exists Y hY.1 1 (by norm_num) hY.2 p hdim
  have heq := TrackA.poly_projection_radial Y hY.1 1 (by norm_num) hY.2 p hdim _ hdeg
  have hmult : 0 ≤ Y.multiplicity p := by
    by_cases hp : p ∈ Y
    · exact (Y.multiplicity_pos p hp).le
    · rw [Y.multiplicity_eq_zero_off p hp]
  have hpos := (projective_irreducible_degree_pos (radialImage p Y)
    (radialImage_irreducible p Y hY.1 (GeoRadial.curve_point_off p Y hY))).le
  have hr : (1 : ℚ) ≤ TrackA.radialMapDegree p Y := by exact_mod_cast hdeg.1
  nlinarith

theorem generic_fiber_on_equal_image (p : Point d) (X Y : AffineVariety d)
    (hX : IsCurve X) (heq : radialImage p X = radialImage p Y) (r : ℕ)
    (hdeg : GenericallyFiniteRadialDegree p Y r) :
    ForGeneralPoint X (fun v => ∃ hv : v ≠ p,
      (radialFiber p Y (radialProjection p v hv)).Finite ∧
      (radialFiber p Y (radialProjection p v hv)).ncard = r) := by
  obtain ⟨hr, g, D, hg, hnot, hfib⟩ := hdeg
  rw [← heq] at hnot
  apply (radial_nonzero_open p X hX g D hg hnot).mono
  intro v hv h
  obtain ⟨hvp, hn⟩ := h
  have hdir : radialProjection p v hvp ∈ (radialImage p Y).points := by
    rw [← heq]
    exact GeoRadial.radial_mem p X v hv hvp
  exact ⟨hvp, hfib _ hdir hn⟩

/-- Removing the source viewpoint subtracts exactly one point precisely
when the source and target carriers coincide. -/
theorem generic_residual_fiber_on_equal_image (p : Point d) (X Y : AffineVariety d)
    (hX : IsCurve X) (hY : IsCurve Y) (heq : radialImage p X = radialImage p Y) (r : ℕ)
    (hdeg : GenericallyFiniteRadialDegree p Y r) :
    ForGeneralPoint X (fun v => ∃ hv : v ≠ p,
      (radialFiber p Y (radialProjection p v hv)).Finite ∧
      (radialFiber p Y (radialProjection p v hv)).ncard = r ∧
      (radialFiber p Y (radialProjection p v hv) \ {v}).ncard =
        r - (if X = Y then 1 else 0)) := by
  have hgen := generic_fiber_on_equal_image p X Y hX heq r hdeg
  by_cases hsame : X = Y
  · apply hgen.mono
    intro v hv h
    obtain ⟨hvp, hfinite, hcard⟩ := h
    have hmem : v ∈ radialFiber p Y (radialProjection p v hvp) :=
      ⟨hsame ▸ hv, hvp, rfl⟩
    exact ⟨hvp, hfinite, hcard, by rw [Set.ncard_sdiff_singleton_of_mem hmem, hcard, if_pos hsame]⟩
  · apply (hgen.and hX.1 (general_avoid_curve X Y hX hY hsame)).mono
    intro v hv h
    obtain ⟨⟨hvp, hfinite, hcard⟩, hvY⟩ := h
    have hd : radialFiber p Y (radialProjection p v hvp) \ {v} =
        radialFiber p Y (radialProjection p v hvp) := by
      ext y
      simp only [Set.mem_sdiff, Set.mem_singleton_iff, and_iff_left_iff_imp]
      intro hy he
      subst y
      exact hvY hy.1
    exact ⟨hvp, hfinite, hcard, by rw [hd, hcard, if_neg hsame, Nat.sub_zero]⟩

/-- Original-centre fibres through a general nonlinear source viewpoint
avoid every exceptional point of any prescribed generic target condition. -/
theorem general_radial_fiber_all (p : Point d) (X Y : AffineVariety d)
    (hX : IsCurve X) (hnlX : ¬ IsLine X) (hY : IsCurve Y)
    (Q : Point d → Prop) (hQ : ForGeneralPoint Y Q) :
    ForGeneralPoint X (fun v => ∀ hv : v ≠ p,
      ∀ y ∈ radialFiber p Y (radialProjection p v hv), Q y) := by
  obtain ⟨g, hg, hgeneral⟩ := hQ
  have hnot : g ∉ Y.ideal := by
    intro h
    obtain ⟨y, hy, hny⟩ := hg
    exact hny (hy g h)
  have hbad : {y : Point d | y ∈ Y ∧ ¬ Q y}.Finite := by
    apply (proper_curve_section Y hY g hnot).1.subset
    intro y hy
    have heval : MvPolynomial.eval y g = 0 := by
      by_contra hn
      exact hy.2 (hgeneral y hy.1 hn)
    rw [AffineVariety.cut, AffineVariety.points_ofIdeal]
    have hI : Y.ideal ⊔ Ideal.span {g} ≤ MvPolynomial.vanishingIdeal ℂ {y} := by
      apply sup_le
      · intro f hf z hz
        rcases Set.mem_singleton_iff.mp hz with rfl
        exact hy.1 f hf
      · apply Ideal.span_le.mpr
        intro f hf z hz
        have hf' : f = g := Set.mem_singleton_iff.mp hf
        subst f
        rcases Set.mem_singleton_iff.mp hz with rfl
        exact heval
    exact fun f hf => hI hf y (Set.mem_singleton y)
  let A := hbad.toFinset.filter (fun y => y ≠ p)
  let F (a : Point d) : AffineSubspace ℂ (Point d) :=
    AffineSubspace.mk' p (ℂ ∙ (a-p))
  have hF (a : Point d) (ha : a ≠ p) : Module.finrank ℂ (F a).direction = 1 := by
    rw [AffineSubspace.direction_mk']
    exact finrank_span_singleton (sub_ne_zero.mpr ha)
  have hgen := ForGeneralPoint.finset_all hX.1 (X.points_nonempty_of_isIrreducible hX.1)
    A (fun a v => v ∉ F a) (by
      intro a ha
      apply ForGeneralPoint.avoid_flat
      exact nonlinear_curve_not_contained_in_line X hX hnlX (F a)
        (hF a (Finset.mem_filter.mp ha).2))
  apply hgen.mono
  intro v hv havoid hvp y hy
  by_contra hyQ
  have ha : y ∈ A := Finset.mem_filter.mpr
    ⟨hbad.mem_toFinset.mpr ⟨hy.1, hyQ⟩, hy.2.choose⟩
  obtain ⟨hyp, heq⟩ := hy.2
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ (v-p) (y-p)
    (sub_ne_zero.mpr hvp) (sub_ne_zero.mpr hyp)).mp heq.symm
  apply havoid y ha
  apply AffineSubspace.mem_mk'.mpr
  change v-p ∈ ℂ ∙ (y-p)
  rw [← hc]
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)

theorem general_smooth_point (Y : AffineVariety d) (hY : IsCurve Y) :
    ForGeneralPoint Y (fun y => Y.IsSmoothAt y) := by
  apply (general_tangent_finrank Y hY.1).mono
  intro y hy hdim
  exact ⟨hy, hdim.trans (Y.localDimension_eq_dimension y hY.1 hy).symm⟩

/-- The finite list of original-centre fibres can all be chosen in the
smooth locus of the target, by avoiding finitely many joining lines. -/
theorem general_original_fibers_smooth
    (X Y : AffineVariety d) (hX : IsCurve X) (hnlX : ¬ IsLine X) (hY : IsCurve Y)
    (Pc : Finset (Point d)) :
    ForGeneralPoint X (fun v => ∀ p ∈ Pc, ∀ hv : v ≠ p,
      ∀ y ∈ radialFiber p Y (radialProjection p v hv), Y.IsSmoothAt y) := by
  apply ForGeneralPoint.finset_all hX.1 (X.points_nonempty_of_isIrreducible hX.1) Pc
  intro p hp
  exact general_radial_fiber_all p X Y hX hnlX hY _ (general_smooth_point Y hY)

/-- One valid centre makes both target projections generically birational
and makes distinct targets have distinct image curves. -/
theorem general_projection_viewpoints
    (p : Point 3) (Y₁ Y₂ Y₃ : AffineVariety 3)
    (hv : CurveTripleValid p Y₁ Y₂ Y₃)
    (hY₁ : IsCurve Y₁) (hY₂ : IsCurve Y₂) (hY₃ : IsCurve Y₃)
    (hnl₁ : ¬ IsLine Y₁) (hnl₂ : ¬ IsLine Y₂) (hnl₃ : ¬ IsLine Y₃) :
    ForGeneralPoint Y₁ (fun v =>
      radialMapDegree v Y₂ = 1 ∧ radialMapDegree v Y₃ = 1 ∧
      (Y₂ ≠ Y₃ → radialImage v Y₂ ≠ radialImage v Y₃) ∧
      ForGeneralPoint Y₂ (fun y => ∃ hy : y ≠ v,
        radialFiber v Y₂ (radialProjection v y hy) = {y}) ∧
      ForGeneralPoint Y₃ (fun y => ∃ hy : y ≠ v,
        radialFiber v Y₃ (radialProjection v y hy) = {y})) := by
  have h₂ := (further_root_absent p Y₁ Y₂ Y₃ Y₂ Y₂ hv hY₁ hY₂ hY₂
    hnl₁ hnl₂ (by simp)).swap.fiber_right
  have h₃ := (further_root_absent p Y₁ Y₂ Y₃ Y₃ Y₃ hv hY₁ hY₃ hY₃
    hnl₁ hnl₃ (by simp)).swap.fiber_right
  have h₂₃ := (further_root_absent p Y₁ Y₂ Y₃ Y₂ Y₃ hv hY₁ hY₂ hY₃
    hnl₁ hnl₂ (by simp)).swap.fiber_right
  apply ((h₂.and hY₁.1 h₃).and hY₁.1 h₂₃).mono
  intro v hvY h
  refine ⟨radialMapDegree_eq_one v Y₂ hY₂ (radial_curve_image_dimension v Y₂ hY₂ hnl₂) h.1.1,
    radialMapDegree_eq_one v Y₃ hY₃ (radial_curve_image_dimension v Y₃ hY₃ hnl₃) h.1.2,
    ?_, general_radial_fiber_singleton v Y₂ hY₂ h.1.1,
    general_radial_fiber_singleton v Y₃ hY₃ h.1.2⟩
  intro hne
  exact radial_images_ne v Y₂ Y₃ hY₂ hY₃ hne
    (radial_curve_image_dimension v Y₃ hY₃ hnl₃) h.2

/-- Simultaneous residual fibre counts for the complete finite list of
valid centres; the generic degree is still the degree from each original centre. -/
theorem general_valid_residual_fibers
    (Y₁ Y₂ Y₃ Y : AffineVariety 3) (hY₁ : IsCurve Y₁) (hY : IsCurve Y)
    (hYm : Y ∈ ({Y₂, Y₃} : Finset _))
    (Pc : Finset (Point 3)) (hvalid : ∀ p ∈ Pc, CurveTripleValid p Y₁ Y₂ Y₃) :
    ForGeneralPoint Y₁ (fun v => ∀ p ∈ Pc, ∃ hv : v ≠ p,
      (radialFiber p Y (radialProjection p v hv)).Finite ∧
      (radialFiber p Y (radialProjection p v hv)).ncard = radialMapDegree p Y ∧
      (radialFiber p Y (radialProjection p v hv) \ {v}).ncard =
        radialMapDegree p Y - (if Y₁ = Y then 1 else 0)) := by
  apply ForGeneralPoint.finset_all hY₁.1 (Y₁.points_nonempty_of_isIrreducible hY₁.1) Pc
  intro p hp
  have hv := hvalid p hp
  have hYall : Y ∈ ({Y₁, Y₂, Y₃} : Finset _) := by
    have hm : Y = Y₂ ∨ Y = Y₃ := by simpa using hYm
    rcases hm with rfl | rfl <;> simp
  have heq : radialImage p Y₁ = radialImage p Y := by
    have hm : Y = Y₂ ∨ Y = Y₃ := by simpa using hYm
    rcases hm with rfl | rfl
    · exact hv.1
    · exact hv.2.1
  exact generic_residual_fiber_on_equal_image p Y₁ Y hY₁ hY heq _
    (radialMapDegree_pos_has_degree p Y (curveTripleValid_mapDegree_pos p Y₁ Y₂ Y₃ Y hv hYall))

/-- Any surviving point on the original-centre fibre proves that the
projected centre lies on the target image from the new viewpoint. -/
theorem projected_center_mem_of_residual (p v : Point d) (Y : AffineVariety d)
    (hvp : v ≠ p)
    (hres : 0 < (radialFiber p Y (radialProjection p v hvp) \ {v}).ncard) :
    radialProjection v p hvp.symm ∈ (radialImage v Y).points := by
  obtain ⟨y, hy, hyv⟩ := Set.nonempty_of_ncard_ne_zero (ne_of_gt hres)
  have hyv' : y ≠ v := fun h => hyv (Set.mem_singleton_iff.mpr h)
  obtain ⟨hyp, heq⟩ := hy.2
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ (y-p) (v-p)
    (sub_ne_zero.mpr hyp) (sub_ne_zero.mpr hvp)).mp heq
  have hline : (1-c) • (p-v) = y-v := by
    ext i
    have hi := congrFun hc i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hi ⊢
    linear_combination hi
  have hproj : radialProjection v y hyv' = radialProjection v p hvp.symm :=
    (Projectivization.mk_eq_mk_iff' ℂ (y-v) (p-v)
      (sub_ne_zero.mpr hyv') (sub_ne_zero.mpr hvp.symm)).mpr ⟨1-c, hline⟩
  rw [← hproj]
  exact GeoRadial.radial_mem v Y y hy.1 hyv'

theorem valid_residual_count_pos (p : Point 3) (Y₁ Y₂ Y₃ Y : AffineVariety 3)
    (hv : CurveTripleValid p Y₁ Y₂ Y₃) (hYm : Y ∈ ({Y₂, Y₃} : Finset _)) :
    0 < radialMapDegree p Y - (if Y₁ = Y then 1 else 0) := by
  have hr := curveTripleValid_target_removal_bound p Y₁ Y₂ Y₃ Y hv hYm
  have hYall : Y ∈ ({Y₁, Y₂, Y₃} : Finset _) := by
    have hm : Y = Y₂ ∨ Y = Y₃ := by simpa using hYm
    rcases hm with rfl | rfl <;> simp
  have ht := curveTripleValid_mapDegree_pos p Y₁ Y₂ Y₃ Y hv hYall
  split_ifs at hr ⊢ <;> omega

/-- Both target images contain all projected valid centres for a general
source viewpoint, using the actual nonempty residual fibres. -/
theorem general_valid_projected_centers
    (Y₁ Y₂ Y₃ Y : AffineVariety 3) (hY₁ : IsCurve Y₁) (hY : IsCurve Y)
    (hYm : Y ∈ ({Y₂, Y₃} : Finset _))
    (Pc : Finset (Point 3)) (hvalid : ∀ p ∈ Pc, CurveTripleValid p Y₁ Y₂ Y₃) :
    ForGeneralPoint Y₁ (fun v => ∀ p ∈ Pc, ∃ hp : p ≠ v,
      radialProjection v p hp ∈ (radialImage v Y).points) := by
  apply (general_valid_residual_fibers Y₁ Y₂ Y₃ Y hY₁ hY hYm Pc hvalid).mono
  intro v hv h p hp
  obtain ⟨hvp, hfinite, hcard, hres⟩ := h p hp
  refine ⟨hvp.symm, projected_center_mem_of_residual p v Y hvp ?_⟩
  rw [hres]
  exact valid_residual_count_pos p Y₁ Y₂ Y₃ Y (hvalid p hp) hYm

/-- All fields of the paper's projection data are now constructed from
one valid centre, apart from the two explicit generic multiplicity bounds. -/
theorem projection_data_of_generic_multiplicity
    (p₀ : Point 3) (Y₁ Y₂ Y₃ : AffineVariety 3)
    (hv₀ : CurveTripleValid p₀ Y₁ Y₂ Y₃)
    (hY₁ : IsCurve Y₁) (hY₂ : IsCurve Y₂) (hY₃ : IsCurve Y₃)
    (hnl₁ : ¬ IsLine Y₁) (hnl₂ : ¬ IsLine Y₂) (hnl₃ : ¬ IsLine Y₃)
    (Pc : Finset (Point 3)) (hvalid : ∀ p ∈ Pc, CurveTripleValid p Y₁ Y₂ Y₃)
    (hm₂ : ForGeneralPoint Y₁ (fun v => ∀ p ∈ Pc, ∀ hp : p ≠ v,
      ((radialMapDegree p Y₂ - (if Y₁ = Y₂ then 1 else 0) : ℕ) : ℚ) ≤
        (radialImage v Y₂).multiplicity (radialProjection v p hp)))
    (hm₃ : ForGeneralPoint Y₁ (fun v => ∀ p ∈ Pc, ∀ hp : p ≠ v,
      ((radialMapDegree p Y₃ - (if Y₁ = Y₃ then 1 else 0) : ℕ) : ℚ) ≤
        (radialImage v Y₃).multiplicity (radialProjection v p hp))) :
    Nonempty (TripleProjectionData Y₁ Y₂ Y₃ Pc) := by
  have hproj := general_projection_viewpoints p₀ Y₁ Y₂ Y₃ hv₀
    hY₁ hY₂ hY₃ hnl₁ hnl₂ hnl₃
  have hsep := nonlinear_curve_general_viewpoint_centers_separated Y₁ hY₁ hnl₁ Pc
  have hpoints₂ := general_valid_projected_centers Y₁ Y₂ Y₃ Y₂ hY₁ hY₂ (by simp) Pc hvalid
  have hpoints₃ := general_valid_projected_centers Y₁ Y₂ Y₃ Y₃ hY₁ hY₃ (by simp) Pc hvalid
  obtain ⟨v, hv, hprojection, hseparation, hpoints, hm⟩ :=
    (hproj.and hY₁.1 (hsep.and hY₁.1
      ((hpoints₂.and hY₁.1 hpoints₃).and hY₁.1 (hm₂.and hY₁.1 hm₃)))).exists
  let u : Point 3 := Pi.single (0 : Fin 3) 1
  have hu : u ≠ 0 := by
    intro h
    have hi := congrFun h (0 : Fin 3)
    simpa [u] using hi
  let z : Point 3 → ProjectivePoint 3 := fun p =>
    if hp : p ≠ v then radialProjection v p hp else Projectivization.mk ℂ u hu
  have hz (p : Point 3) (hp : p ∈ Pc) :
      z p = radialProjection v p (hseparation.1 p hp).symm := by
    simp only [z, dif_pos (hseparation.1 p hp).symm]
  refine ⟨{
    viewpoint := v
    viewpoint_mem := hv
    z := z
    radial := fun p hp => ⟨(hseparation.1 p hp).symm, hz p hp⟩
    injective := ?_
    image₂_curve := ⟨radialImage_irreducible v Y₂ hY₂.1 (GeoRadial.curve_point_off v Y₂ hY₂),
      radial_curve_image_dimension v Y₂ hY₂ hnl₂⟩
    image₃_curve := ⟨radialImage_irreducible v Y₃ hY₃.1 (GeoRadial.curve_point_off v Y₃ hY₃),
      radial_curve_image_dimension v Y₃ hY₃ hnl₃⟩
    image₂_degree := radial_curve_image_degree_le v Y₂ hY₂ hnl₂
    image₃_degree := radial_curve_image_degree_le v Y₃ hY₃ hnl₃
    distinct := hprojection.2.2.1
    points := ?_
    branches₂ := ?_
    branches₃ := ?_ }⟩
  · intro p hp q hq heq
    by_contra hpq
    apply hseparation.2 p hp q hq hpq (hseparation.1 p hp).symm (hseparation.1 q hq).symm
    simpa only [hz p hp, hz q hq] using heq
  · intro p hp
    rw [hz p hp]
    exact ⟨(hpoints.1 p hp).choose_spec, (hpoints.2 p hp).choose_spec⟩
  · intro p hp
    rw [hz p hp]
    exact hm.1 p hp _
  · intro p hp
    rw [hz p hp]
    exact hm.2 p hp _

/-- Every surviving original-centre preimage maps to the projected centre
from the new viewpoint. -/
theorem residual_fiber_subset (p v : Point d) (Y : AffineVariety d) (hvp : v ≠ p) :
    radialFiber p Y (radialProjection p v hvp) \ {v} ⊆
      radialFiber v Y (radialProjection v p hvp.symm) := by
  intro y hy
  have hyv : y ≠ v := fun h => hy.2 (Set.mem_singleton_iff.mpr h)
  obtain ⟨hyp, heq⟩ := hy.1.2
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ (y-p) (v-p)
    (sub_ne_zero.mpr hyp) (sub_ne_zero.mpr hvp)).mp heq
  have hline : (1-c) • (p-v) = y-v := by
    ext i
    have hi := congrFun hc i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hi ⊢
    linear_combination hi
  exact ⟨hy.1.1, hyv, (Projectivization.mk_eq_mk_iff' ℂ (y-v) (p-v)
    (sub_ne_zero.mpr hyv) (sub_ne_zero.mpr hvp.symm)).mpr ⟨1-c, hline⟩⟩

/-- The precise local geometric input still needed for the triple bound.
Smooth distinct preimages of a birational radial map give distinct branches
of the plane image. This is a proposition, not an asserted theorem. -/
def SmoothRadialFiberMultiplicityBound : Prop :=
  ∀ (Y : AffineVariety 3), IsCurve Y → ∀ v : Point 3,
    (radialImage v Y).dimension = 1 → GenericallyFiniteRadialDegree v Y 1 →
    ∀ (z : ProjectivePoint 3) (S : Finset (Point 3)),
      (∀ y ∈ S, y ∈ radialFiber v Y z ∧ Y.IsSmoothAt y) →
        (S.card : ℚ) ≤ (radialImage v Y).multiplicity z

/-- Exact transport from the local branch-count input to the two generic
residual multiplicity bounds in the paper's projection data. -/
theorem general_valid_residual_multiplicity
    (hbound : SmoothRadialFiberMultiplicityBound)
    (p₀ : Point 3) (Y₁ Y₂ Y₃ Y : AffineVariety 3)
    (hv₀ : CurveTripleValid p₀ Y₁ Y₂ Y₃)
    (hY₁ : IsCurve Y₁) (hY : IsCurve Y)
    (hnl₁ : ¬ IsLine Y₁) (hnlY : ¬ IsLine Y)
    (hYm : Y ∈ ({Y₂, Y₃} : Finset _))
    (Pc : Finset (Point 3)) (hvalid : ∀ p ∈ Pc, CurveTripleValid p Y₁ Y₂ Y₃) :
    ForGeneralPoint Y₁ (fun v => ∀ p ∈ Pc, ∀ hp : p ≠ v,
      ((radialMapDegree p Y - (if Y₁ = Y then 1 else 0) : ℕ) : ℚ) ≤
        (radialImage v Y).multiplicity (radialProjection v p hp)) := by
  have habsent := (further_root_absent p₀ Y₁ Y₂ Y₃ Y Y hv₀ hY₁ hY hY hnl₁ hnlY hYm).swap.fiber_right
  have hbir : ForGeneralPoint Y₁ (fun v => radialMapDegree v Y = 1) := by
    apply habsent.mono
    intro v hv h
    exact radialMapDegree_eq_one v Y hY (radial_curve_image_dimension v Y hY hnlY) h
  have hres := general_valid_residual_fibers Y₁ Y₂ Y₃ Y hY₁ hY hYm Pc hvalid
  have hsm := general_original_fibers_smooth Y₁ Y hY₁ hnl₁ hY Pc
  apply ((hbir.and hY₁.1 hres).and hY₁.1 hsm).mono
  intro v hv h p hp hpv
  obtain ⟨hvp, hfinite, hcard, hrescard⟩ := h.1.2 p hp
  let R := radialFiber p Y (radialProjection p v hvp) \ {v}
  have hR : R.Finite := hfinite.sdiff
  let S : Finset (Point 3) := hR.toFinset
  have hGFD : GenericallyFiniteRadialDegree v Y 1 := by
    have ht : 0 < radialMapDegree v Y := by rw [h.1.1]; norm_num
    simpa only [h.1.1] using radialMapDegree_pos_has_degree v Y ht
  have hS : ∀ y ∈ S, y ∈ radialFiber v Y (radialProjection v p hpv) ∧ Y.IsSmoothAt y := by
    intro y hy
    have hyR : y ∈ R := hR.mem_toFinset.mp hy
    exact ⟨residual_fiber_subset p v Y hvp hyR, h.2 p hp hvp y hyR.1⟩
  have hmult := hbound Y hY v (radial_curve_image_dimension v Y hY hnlY) hGFD
    (radialProjection v p hpv) S hS
  have hScard : S.card = radialMapDegree p Y - (if Y₁ = Y then 1 else 0) := by
    rw [Set.ncard_eq_toFinset_card R hR] at hrescard
    exact hrescard
  rwa [hScard] at hmult

/-- The complete frozen quantifier order and conclusion, with just the
explicit local branch-count proposition as an additional input. -/
theorem terminal_triple_of_fiber_multiplicity
    (hbound : SmoothRadialFiberMultiplicityBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y₁ Y₂ Y₃ : AffineVariety 3),
      IsCurve Y₁ → IsCurve Y₂ → IsCurve Y₃ → ¬ IsLine Y₁ → ¬ IsLine Y₂ → ¬ IsLine Y₃ →
      ∀ Pc : Finset (Point 3), (∀ p ∈ Pc, CurveTripleValid p Y₁ Y₂ Y₃) →
        ∑ p ∈ Pc, (((radialImage p Y₁).degree : ℝ))⁻¹ ^ 2 ≤ C := by
  refine ⟨48, by norm_num, ?_⟩
  intro Y₁ Y₂ Y₃ hY₁ hY₂ hY₃ hnl₁ hnl₂ hnl₃ Pc hvalid
  by_cases hPc : Pc.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hPc
    have hv₀ := hvalid p₀ hp₀
    have hm₂ := general_valid_residual_multiplicity hbound p₀ Y₁ Y₂ Y₃ Y₂ hv₀
      hY₁ hY₂ hnl₁ hnl₂ (by simp) Pc hvalid
    have hm₃ := general_valid_residual_multiplicity hbound p₀ Y₁ Y₂ Y₃ Y₃ hv₀
      hY₁ hY₃ hnl₁ hnl₃ (by simp) Pc hvalid
    obtain ⟨data⟩ := projection_data_of_generic_multiplicity p₀ Y₁ Y₂ Y₃ hv₀
      hY₁ hY₂ hY₃ hnl₁ hnl₂ hnl₃ Pc hvalid hm₂ hm₃
    exact terminal_triple_bound_of_projection_data Y₁ Y₂ Y₃ hY₂ hY₃ Pc hvalid data
  · have he : Pc = ∅ := Finset.not_nonempty_iff_eq_empty.mp hPc
    simp only [he, Finset.sum_empty]
    norm_num

end TripleGeneric

namespace TripleSections

variable {d : ℕ}

def pointCarrier (x : Point d) : AffineVariety d :=
  ⟨pointIdeal x, (pointIdeal_isMaximal x).isPrime.isRadical⟩

theorem pointCarrier_irreducible (x : Point d) : (pointCarrier x).IsIrreducible :=
  (pointIdeal_isMaximal x).isPrime

theorem pointCarrier_degree (x : Point d) : (pointCarrier x).degree = 1 :=
  TrackA.affine_point_degree_one x

theorem pointCarrier_injective : Function.Injective (pointCarrier (d := d)) := by
  intro x y heq
  have hI : pointIdeal x = pointIdeal y := congrArg AffineVariety.ideal heq
  ext j
  have hf : MvPolynomial.X j - MvPolynomial.C (x j) ∈ pointIdeal x := by
    rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  rw [hI, pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hf
  simpa using (sub_eq_zero.mp (by simpa using hf : y j - x j = 0)).symm

theorem point_minimal_of_curve_cut (Y : AffineVariety d) (hY : IsCurve Y)
    (f : Poly d) (hf : f ∉ Y.ideal) (x : Point d) (hx : x ∈ Y.points)
    (hfx : MvPolynomial.eval x f = 0) :
    pointIdeal x ∈ (Y.ideal ⊔ Ideal.span {f}).minimalPrimes := by
  have hfp : f ∈ pointIdeal x := by
    rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact hfx
  have hle : Y.ideal ⊔ Ideal.span {f} ≤ pointIdeal x := by
    apply sup_le
    · intro q hq
      rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      exact hx q hq
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfp)
  obtain ⟨P, hP, hPx⟩ := Ideal.exists_minimalPrimes_le hle
  let Z : AffineVariety d := ⟨P, hP.isPrime.isRadical⟩
  have hdim : Z.dimension = 0 :=
    TrackA.fa_bezout_proper_dimension Y Z hY.1 f hf hP 0 hY.2
  letI : P.IsPrime := hP.isPrime
  have hmax : P.IsMaximal := OAI.QuarticPowerFree.zeroDim_isMaximal P hdim
  have heq : P = pointIdeal x := hmax.eq_of_le (pointIdeal_isMaximal x).ne_top hPx
  exact heq ▸ hP

/-- One proper curve section bounds the sum of actual local lengths at
any finite list of distinct selected points. -/
theorem curve_section_point_length_budget (Y : AffineVariety d) (hY : IsCurve Y)
    (f : Poly d) (hf : f ∉ Y.ideal) (S : Finset (Point d))
    (hS : ∀ x ∈ S, x ∈ Y.points ∧ MvPolynomial.eval x f = 0) :
    ∃ L : Point d → ℕ,
      (∀ x ∈ S, localLengthAt (Y.ideal ⊔ Ideal.span {f}) x = (L x : ℕ∞)) ∧
      (∑ x ∈ S, (L x : ℚ)) ≤ (f.totalDegree : ℚ) * Y.degree := by
  let F : AffineFamily.Family d := S.image pointCarrier
  have hF : ∀ W ∈ F, W.IsComponentOf (Y.ideal ⊔ Ideal.span {f}) := by
    intro W hW
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hW
    exact point_minimal_of_curve_cut Y hY f hf x (hS x hx).1 (hS x hx).2
  obtain ⟨m, hm, hbudget⟩ := TrackA.fa_bezout_weighted_cut Y hY.1 0 hY.2 f hf F hF
  refine ⟨fun x => m (pointCarrier x), ?_, ?_⟩
  · intro x hx
    exact hm (pointCarrier x) (Finset.mem_image_of_mem _ hx) (pointCarrier_irreducible x)
  · have hsum : (∑ W ∈ F, (m W : ℚ) * W.degree) =
        ∑ x ∈ S, (m (pointCarrier x) : ℚ) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro x hx
        rw [pointCarrier_degree, mul_one]
      · intro x hx y hy heq
        exact pointCarrier_injective heq
    rwa [hsum] at hbudget

theorem localClass_square_mem (Y : AffineVariety d) (x : Point d) (f : Poly d)
    (hf : MvPolynomial.eval x f = 0) :
    TrackA.localClass Y x (f^2) ∈ TrackA.carrierMaximalIdeal Y x ^ 2 := by
  letI : CommRing (TrackA.CarrierLocalRing Y x) :=
    { __ := (inferInstance : Ring (TrackA.CarrierLocalRing Y x))
      mul_comm := fun a b => mul_comm a b }
  have hfp : f ∈ pointIdeal x := by
    rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact hf
  have hclass : TrackA.localClass Y x f ∈ TrackA.carrierMaximalIdeal Y x :=
    Ideal.mem_map_of_mem _ hfp
  simpa only [TrackA.localClass, map_pow] using Ideal.pow_mem_pow hclass 2

/-- Squaring a linear section lets the existing double-order length
comparison count full source multiplicities at all selected points. -/
theorem curve_linear_section_multiplicity_sum_le (Y : AffineVariety d) (hY : IsCurve Y)
    (f : Poly d) (hf : f ∉ Y.ideal) (hdeg : f.totalDegree ≤ 1)
    (S : Finset (Point d)) (hS : ∀ x ∈ S, x ∈ Y.points ∧ MvPolynomial.eval x f = 0) :
    (∑ x ∈ S, Y.multiplicity x) ≤ Y.degree := by
  have hg : f^2 ∉ Y.ideal := by
    intro h
    have hh : f*f ∈ Y.ideal := by simpa only [pow_two] using h
    exact (hY.1.mem_or_mem hh).elim hf hf
  have hSg : ∀ x ∈ S, x ∈ Y.points ∧ MvPolynomial.eval x (f^2) = 0 := by
    intro x hx
    exact ⟨(hS x hx).1, by rw [map_pow, (hS x hx).2]; simp⟩
  obtain ⟨L, hL, hbudget⟩ := curve_section_point_length_budget Y hY (f^2) hg S hSg
  have hpoint : ∀ x ∈ S, 2 * Y.multiplicity x ≤ (L x : ℚ) := by
    intro x hx
    obtain ⟨l, hl, hbound⟩ := TrackA.poly_curve_double_order_length Y hY.1 hY.2 x
      (hS x hx).1 (f^2) hg (localClass_square_mem Y x f (hS x hx).2)
    have heq : l = L x := WithTop.coe_inj.mp (hl.symm.trans (hL x hx))
    simpa only [heq] using hbound
  have hsum : 2 * (∑ x ∈ S, Y.multiplicity x) ≤ ∑ x ∈ S, (L x : ℚ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpoint
  have hpowdeg : (f^2).totalDegree ≤ 2 := by
    rw [pow_two]
    exact (MvPolynomial.totalDegree_mul f f).trans (by omega)
  have hpowdegQ : ((f^2).totalDegree : ℚ) ≤ 2 := by exact_mod_cast hpowdeg
  have hY0 : 0 ≤ Y.degree := (Y.one_le_degree hY.1.ne_top).trans' (by norm_num)
  have htotal : (∑ x ∈ S, (L x : ℚ)) ≤ 2 * Y.degree :=
    hbudget.trans (mul_le_mul_of_nonneg_right hpowdegQ hY0)
  linarith

theorem one_le_multiplicity_of_mem (Y : AffineVariety d) (x : Point d) (hx : x ∈ Y.points) :
    1 ≤ Y.multiplicity x := by
  obtain ⟨a, ha⟩ := TrackA.multiplicity_eq_nat Y x hx
  have hpos : 0 < a := by exact_mod_cast (ha ▸ Y.multiplicity_pos x hx)
  rw [ha]
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hpos))

/-- The centre's full multiplicity can be removed from the linear-section
budget using the degree-one radial formula. -/
theorem curve_linear_section_card_off_center_le (v : Point d) (Y : AffineVariety d)
    (hY : IsCurve Y) (hdim : (radialImage v Y).dimension = 1)
    (hbir : GenericallyFiniteRadialDegree v Y 1)
    (f : Poly d) (hf : f ∉ Y.ideal) (hdeg : f.totalDegree ≤ 1)
    (hfv : MvPolynomial.eval v f = 0) (S : Finset (Point d))
    (hS : ∀ x ∈ S, x ∈ Y.points ∧ x ≠ v ∧ MvPolynomial.eval x f = 0) :
    (S.card : ℚ) ≤ (radialImage v Y).degree := by
  have hformula := TrackA.poly_projection_radial Y hY.1 1 (by norm_num) hY.2 v hdim 1 hbir
  norm_num only [Nat.cast_one, one_mul] at hformula
  have hcard : (S.card : ℚ) ≤ ∑ x ∈ S, Y.multiplicity x := by
    calc
      (S.card : ℚ) = ∑ x ∈ S, (1 : ℚ) := by simp
      _ ≤ ∑ x ∈ S, Y.multiplicity x :=
        Finset.sum_le_sum (fun x hx => one_le_multiplicity_of_mem Y x (hS x hx).1)
  by_cases hv : v ∈ Y.points
  · have hnot : v ∉ S := by intro h; exact (hS v h).2.1 rfl
    have hselected : ∀ x ∈ insert v S, x ∈ Y.points ∧ MvPolynomial.eval x f = 0 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨hv, hfv⟩
      · exact ⟨(hS x hx).1, (hS x hx).2.2⟩
    have hbudget := curve_linear_section_multiplicity_sum_le Y hY f hf hdeg (insert v S) hselected
    rw [Finset.sum_insert hnot] at hbudget
    linarith
  · have hbudget := curve_linear_section_multiplicity_sum_le Y hY f hf hdeg S
      (fun x hx => ⟨(hS x hx).1, (hS x hx).2.2⟩)
    rw [Y.multiplicity_eq_zero_off v hv, sub_zero] at hformula
    linarith

end TripleSections

namespace TriplePencil

variable {n : ℕ}

def chartDeletion (i : Fin (n+1)) : AffineProjection (n+1) n :=
  ⟨{ toFun := fun x j => x (i.succAbove j)
     map_add' := fun x y => rfl
     map_smul' := fun c x => rfl }, 0⟩

@[simp] theorem chartDeletion_apply (i : Fin (n+1)) (x : Point (n+1)) :
    (chartDeletion i).apply x = fun j => x (i.succAbove j) := by
  simp [chartDeletion, AffineProjection.apply]

theorem chartDeletion_pullback (i : Fin (n+1)) :
    (chartDeletion i).pullback = MvPolynomial.rename i.succAbove := by
  ext j : 1
  apply MvPolynomial.funext
  intro x
  rw [← MvPolynomial.aeval_eq_eval, AffineProjection.eval_pullback]
  simp [chartDeletion_apply]

theorem slice_coordinate (C : ProjectiveVariety (n+1)) (i : Fin (n+1))
    (x : Point (n+1)) (hx : x ∈ (TrackA.projectiveLinearSlice C (MvPolynomial.X i)).points) :
    x i = 1 := by
  simpa using ((TrackA.linearSlice_points C (MvPolynomial.X i) x).mp hx).2

theorem insert_chart_mem (C : ProjectiveVariety (n+1)) (i : Fin (n+1))
    (y : Point n) :
    Fin.insertNth i 1 y ∈ (TrackA.projectiveLinearSlice C (MvPolynomial.X i)).points ↔
      y ∈ (C.affineChart i).points := by
  constructor
  · intro h
    have hc := (TrackA.linearSlice_points C (MvPolynomial.X i) _).mp h
    simpa using TrackA.chart_points_from_cone C i (Fin.insertNth i 1 y) hc.1 (by simp)
  · intro h
    apply (TrackA.linearSlice_points C (MvPolynomial.X i) _).mpr
    refine ⟨?_, by simp⟩
    intro f hf
    have hm : chartPullback i f ∈ (C.affineChart i).ideal :=
      Ideal.le_radical (Ideal.mem_map_of_mem (chartPullback i).toRingHom hf)
    have hz := h (chartPullback i f) hm
    simpa only [MvPolynomial.aeval_eq_eval, TrackA.chartPullback_eval] using hz

theorem chartDeletion_image (C : ProjectiveVariety (n+1)) (i : Fin (n+1)) :
    (chartDeletion i).image (TrackA.projectiveLinearSlice C (MvPolynomial.X i)) = C.affineChart i := by
  apply AffineVariety.ext
  ext f
  rw [← AffineVariety.vanishingIdeal_points (C.affineChart i)]
  change (chartDeletion i).pullback f ∈ (TrackA.projectiveLinearSlice C (MvPolynomial.X i)).ideal ↔ _
  rw [← AffineVariety.vanishingIdeal_points, MvPolynomial.mem_vanishingIdeal_iff,
    MvPolynomial.mem_vanishingIdeal_iff]
  constructor
  · intro h y hy
    have hpoint := (insert_chart_mem C i y).mpr hy
    simpa [AffineProjection.eval_pullback, chartDeletion_apply]
      using h _ hpoint
  · intro h x hx
    have hxi := slice_coordinate C i x hx
    have he : Fin.insertNth i 1 (fun j => x (i.succAbove j)) = x := by
      funext j
      rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩ <;> simp [hxi]
    have hchart : (fun j => x (i.succAbove j)) ∈ (C.affineChart i).points :=
      (insert_chart_mem C i _).mp (he.symm ▸ hx)
    simpa only [AffineProjection.eval_pullback, chartDeletion_apply] using h _ hchart

theorem chartDeletion_fiber (C : ProjectiveVariety (n+1)) (i : Fin (n+1))
    (x : Point (n+1)) (hx : x ∈ (TrackA.projectiveLinearSlice C (MvPolynomial.X i)).points) :
    (chartDeletion i).fiber (TrackA.projectiveLinearSlice C (MvPolynomial.X i))
      ((chartDeletion i).apply x) = {x} := by
  ext y
  constructor
  · rintro ⟨hy, he⟩
    apply Set.mem_singleton_iff.mpr
    funext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩
    · exact (slice_coordinate C _ y hy).trans (slice_coordinate C _ x hx).symm
    · simpa only [chartDeletion_apply] using congrFun he a
  · rintro rfl
    exact ⟨hx, rfl⟩

theorem chartDeletion_generic_degree (C : ProjectiveVariety (n+1)) (hC : C.IsIrreducible)
    (i : Fin (n+1)) (hi : MvPolynomial.X i ∉ C.ideal) :
    (chartDeletion i).GenericallyFiniteOfDegree (TrackA.projectiveLinearSlice C (MvPolynomial.X i)) 1 := by
  have hA := TrackA.linearSlice_irreducible C hC (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X ℂ i) hi
  refine ⟨by norm_num, 1, ((chartDeletion i).image_irreducible _ hA).one_notMem, ?_⟩
  intro y hy hn
  rw [chartDeletion_image] at hy
  have hx := (insert_chart_mem C i y).mpr hy
  have he : (chartDeletion i).apply (Fin.insertNth i 1 y) = y := by
    ext j
    simp
  have hf := chartDeletion_fiber C i _ hx
  rw [he] at hf
  rw [hf]
  exact ⟨Set.finite_singleton _, by simp⟩

theorem chartDeletion_quotient_surjective (C : ProjectiveVariety (n+1)) (i : Fin (n+1)) :
    Function.Surjective ((Ideal.Quotient.mk (TrackA.projectiveLinearSlice C (MvPolynomial.X i)).ideal).comp
      (chartDeletion i).pullback.toRingHom) := by
  intro q
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨chartPullback i f, ?_⟩
  change Ideal.Quotient.mk _ ((chartDeletion i).pullback (chartPullback i f)) = _
  apply Ideal.Quotient.eq.mpr
  rw [← AffineVariety.vanishingIdeal_points]
  intro x hx
  change MvPolynomial.eval x ((chartDeletion i).pullback (chartPullback i f) - f) = 0
  have hxi := slice_coordinate C i x hx
  have he : Fin.insertNth i 1 ((chartDeletion i).apply x) = x := by
    funext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩ <;> simp [hxi]
  rw [map_sub, ← MvPolynomial.aeval_eq_eval, AffineProjection.eval_pullback,
    MvPolynomial.aeval_eq_eval, TrackA.chartPullback_eval, he]
  simp only [MvPolynomial.aeval_eq_eval, sub_self]

theorem chartDeletion_finite (C : ProjectiveVariety (n+1)) (i : Fin (n+1)) :
    TrackA.FiniteAffineProjection (chartDeletion i) (TrackA.projectiveLinearSlice C (MvPolynomial.X i)) :=
  RingHom.Finite.of_surjective _ (chartDeletion_quotient_surjective C i)

def normalizedRepresentative (q : ProjectivePoint (n+1)) (i : Fin (n+1)) : Point (n+1) :=
  (q.rep i)⁻¹ • q.rep

theorem normalizedRepresentative_mem (C : ProjectiveVariety (n+1)) (q : ProjectivePoint (n+1))
    (hq : q ∈ C.points) (i : Fin (n+1)) (hi : q.rep i ≠ 0) :
    normalizedRepresentative q i ∈ (TrackA.projectiveLinearSlice C (MvPolynomial.X i)).points := by
  apply (TrackA.linearSlice_points C (MvPolynomial.X i) _).mpr
  refine ⟨TrackA.cone_smul_mem C q.rep (hq q.rep q.rep_nonzero (Projectivization.mk_rep q)) _, ?_⟩
  simp [normalizedRepresentative, hi]

theorem normalizedRepresentative_projection (q : ProjectivePoint (n+1)) (i : Fin (n+1)) :
    (chartDeletion i).apply (normalizedRepresentative q i) = chartCoordinates i q := by
  ext j
  simp [normalizedRepresentative, chartCoordinates, div_eq_mul_inv, mul_comm]

theorem normalizedRepresentative_multiplicity_le (C : ProjectiveVariety (n+1))
    (hC : C.IsIrreducible) (q : ProjectivePoint (n+1)) (hq : q ∈ C.points)
    (i : Fin (n+1)) (hi : q.rep i ≠ 0) :
    (TrackA.projectiveLinearSlice C (MvPolynomial.X i)).multiplicity (normalizedRepresentative q i) ≤
      C.multiplicity q := by
  let Z := TrackA.projectiveLinearSlice C (MvPolynomial.X i)
  let a := normalizedRepresentative q i
  let y := chartCoordinates i q
  have hai : a i = 1 := by simp [a, normalizedRepresentative, hi]
  have hya : (fun j => a (i.succAbove j)) = y := by
    have h := normalizedRepresentative_projection q i
    rw [chartDeletion_apply] at h
    exact h
  have hinsert : Fin.insertNth i 1 y = a := by
    rw [← hya]
    funext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨b, rfl⟩ <;> simp [hai]
  have hZpoint (x : Point (n+1)) (hx : x ∈ Z.points) :
      Fin.insertNth i 1 (fun j => x (i.succAbove j)) = x := by
    have hxi := slice_coordinate C i x hx
    funext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨b, rfl⟩ <;> simp [hxi]
  have hφa (f : Poly (n+1)) :
      MvPolynomial.eval y (chartPullback i f) = MvPolynomial.eval a f := by
    rw [TrackA.chartPullback_eval, hinsert]
  have hψy (g : Poly n) :
      MvPolynomial.eval a (MvPolynomial.rename i.succAbove g) = MvPolynomial.eval y g := by
    rw [MvPolynomial.eval_rename, ← hya]
    rfl
  have hφZ : ∀ f ∈ Z.ideal, chartPullback i f ∈ (C.affineChart i).ideal := by
    intro f hf
    rw [← AffineVariety.vanishingIdeal_points, MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    have hxZ := (insert_chart_mem C i x).mpr hx
    change MvPolynomial.eval x (chartPullback i f) = 0
    rw [TrackA.chartPullback_eval]
    exact hxZ f hf
  have hψW : ∀ g ∈ (C.affineChart i).ideal, MvPolynomial.rename i.succAbove g ∈ Z.ideal := by
    intro g hg
    rw [← AffineVariety.vanishingIdeal_points Z, MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    change MvPolynomial.eval x (MvPolynomial.rename i.succAbove g) = 0
    rw [MvPolynomial.eval_rename]
    have hxW : (fun j => x (i.succAbove j)) ∈ (C.affineChart i).points :=
      (insert_chart_mem C i _).mp ((hZpoint x hx).symm ▸ hx)
    exact hxW g hg
  have hret : ∀ f, MvPolynomial.rename i.succAbove (chartPullback i f) - f ∈ Z.ideal := by
    intro f
    rw [← AffineVariety.vanishingIdeal_points Z, MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    change MvPolynomial.eval x (MvPolynomial.rename i.succAbove (chartPullback i f) - f) = 0
    rw [map_sub, MvPolynomial.eval_rename]
    change MvPolynomial.eval (fun j => x (i.succAbove j)) (chartPullback i f) -
      MvPolynomial.eval x f = 0
    rw [TrackA.chartPullback_eval, hZpoint x hx, sub_self]
  have heq : Z.multiplicity a = (C.affineChart i).multiplicity y :=
    TrackA.multiplicity_eq_of_localHilbert_eq Z a (C.affineChart i) y (fun t =>
      TrackA.localHilbert_eq_of_retraction Z (C.affineChart i) (chartPullback i)
        (MvPolynomial.rename i.succAbove) (TrackA.chartPullback_rename i) a y
        hφa hψy hφZ hψW hret t)
  rw [heq, ← C.multiplicity_chart q i hi]

end TriplePencil

namespace TriplePencil

/-- A literal affine line has degree one in the shared Hilbert model. -/
theorem curve_degree_eq_one_of_isLine {d : ℕ} (A : AffineVariety d)
    (hA : IsCurve A) (hline : IsLine A) : A.degree = 1 := by
  obtain ⟨b, u, hu, hpoints⟩ := hline
  obtain ⟨j, hj⟩ := GeoRadial.exists_coord u hu
  have he : A = Bridges.complexLine b u :=
    GeoRadial.curve_eq_of_subset A _ (Bridges.complexLine_irreducible b u) hA.2
      (Bridges.complexLine_dimension b u j hj) (by
        rw [Bridges.complexLine_points b u j hj, hpoints])
  rw [he, Bridges.complexLine_degree b u j hj]

theorem slice_isCurve (C : ProjectiveVariety 3) (hC : C.IsIrreducible)
    (hdim : C.dimension = 1) (i : Fin 3) (hi : MvPolynomial.X i ∉ C.ideal) :
    IsCurve (TrackA.projectiveLinearSlice C (MvPolynomial.X i)) := by
  exact ⟨TrackA.linearSlice_irreducible C hC _ (MvPolynomial.isHomogeneous_X ℂ i) hi,
    (TrackA.linearSlice_dimension C hC _ (MvPolynomial.isHomogeneous_X ℂ i) hi).trans hdim⟩

theorem slice_not_line (C : ProjectiveVariety 3) (hC : C.IsIrreducible)
    (hdim : C.dimension = 1) (hdeg : 1 < C.degree)
    (i : Fin 3) (hi : MvPolynomial.X i ∉ C.ideal) :
    ¬ IsLine (TrackA.projectiveLinearSlice C (MvPolynomial.X i)) := by
  intro hline
  have hd := curve_degree_eq_one_of_isLine _ (slice_isCurve C hC hdim i hi) hline
  rw [TrackA.linearSlice_degree C hC _ (MvPolynomial.isHomogeneous_X ℂ i) hi] at hd
  exact (ne_of_gt hdeg) hd

/-- A nonlinear curve in the plane X_i=1 has a degree-one radial image
from a point of that plane. -/
theorem slice_radial_degree_one (C : ProjectiveVariety 3) (hC : C.IsIrreducible)
    (hdim : C.dimension = 1) (hdeg : 1 < C.degree) (i : Fin 3)
    (hi : MvPolynomial.X i ∉ C.ideal) (a : Point 3)
    (ha : a ∈ (TrackA.projectiveLinearSlice C (MvPolynomial.X i)).points) :
    (radialImage a (TrackA.projectiveLinearSlice C (MvPolynomial.X i))).dimension = 1 ∧
    (radialImage a (TrackA.projectiveLinearSlice C (MvPolynomial.X i))).degree = 1 := by
  let A := TrackA.projectiveLinearSlice C (MvPolynomial.X i)
  have hA : IsCurve A := slice_isCurve C hC hdim i hi
  have hnl : ¬ IsLine A := slice_not_line C hC hdim hdeg i hi
  have hRdim := TripleGeneric.radial_curve_image_dimension a A hA hnl
  have hR := radialImage_irreducible a A hA.1 (GeoRadial.curve_point_off a A hA)
  have hRne := GeoRadial.radial_nonempty a A hA
  have hmem : MvPolynomial.X i ∈ (radialImage a A).ideal := by
    rintro u ⟨hu, x, hx, hxa, heq⟩
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ u (x-a) hu
      (sub_ne_zero.mpr hxa)).mp heq.symm
    simp only [MvPolynomial.aeval_X]
    rw [← hc]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      slice_coordinate C i x hx, slice_coordinate C i a ha, sub_self, mul_zero]
  have hupper := projective_plane_curve_degree_le_one_of_linear_equation _ hR hRdim hRne
    (MvPolynomial.X i) (MvPolynomial.X_ne_zero i) (by simp) hmem
  have hlower : 1 ≤ (radialImage a A).degree := by
    simpa only [ProjectiveVariety.degree_cone] using
      (radialImage a A).affineCone.one_le_degree hR.ne_top
  exact ⟨hRdim, le_antisymm hupper hlower⟩

/-- Choose one finite line-pencil fibre in a normalized slice, with all
its points avoiding an arbitrary prescribed homogeneous exceptional locus. -/
theorem exists_good_slice_pencil (C : ProjectiveVariety 3) (hC : C.IsIrreducible)
    (hdim : C.dimension = 1) (hdeg : 1 < C.degree) (i : Fin 3)
    (hi : MvPolynomial.X i ∉ C.ideal) (a : Point 3)
    (ha : a ∈ (TrackA.projectiveLinearSlice C (MvPolynomial.X i)).points)
    (g : Poly 3) (D : ℕ) (hg : g.IsHomogeneous D) (hnot : g ∉ C.ideal) :
    ∃ (r : ℕ) (c : Point 3), c ∈ (TrackA.projectiveLinearSlice C (MvPolynomial.X i)).points ∧
      ∃ hc : c ≠ a,
        (radialFiber a (TrackA.projectiveLinearSlice C (MvPolynomial.X i))
          (radialProjection a c hc)).Finite ∧
        (radialFiber a (TrackA.projectiveLinearSlice C (MvPolynomial.X i))
          (radialProjection a c hc)).ncard = r ∧
        (r : ℚ) = C.degree - (TrackA.projectiveLinearSlice C (MvPolynomial.X i)).multiplicity a ∧
        ∀ x ∈ radialFiber a (TrackA.projectiveLinearSlice C (MvPolynomial.X i))
          (radialProjection a c hc), MvPolynomial.eval x g ≠ 0 := by
  let A := TrackA.projectiveLinearSlice C (MvPolynomial.X i)
  have hA : IsCurve A := slice_isCurve C hC hdim i hi
  have hnl : ¬ IsLine A := slice_not_line C hC hdim hdeg i hi
  obtain ⟨hRdim, hRdeg⟩ := slice_radial_degree_one C hC hdim hdeg i hi a ha
  let r := TrackA.radialMapDegree a A
  have hr : GenericallyFiniteRadialDegree a A r :=
    TrackA.dep_radial_degree_exists A hA.1 1 (by norm_num) hA.2 a hRdim
  have hformula := TrackA.poly_projection_radial A hA.1 1 (by norm_num) hA.2 a hRdim r hr
  rw [hRdeg, mul_one, TrackA.linearSlice_degree C hC _ (MvPolynomial.isHomogeneous_X ℂ i) hi]
    at hformula
  have hgA : g ∉ A.ideal := by
    exact fun h => hnot ((TrackA.homogeneous_mem_linearSlice_iff C hC _ g
      (MvPolynomial.isHomogeneous_X ℂ i) hi hg).mp h)
  have hopen : ForGeneralPoint A (fun x => MvPolynomial.eval x g ≠ 0) := by
    refine ⟨g, ?_, fun x hx hn => hn⟩
    by_contra! h
    exact hgA ((mem_ideal_iff_eval_zero A g).mpr h)
  have hall := TripleGeneric.general_radial_fiber_all a A A hA hnl hA _ hopen
  have hfinite := TripleGeneric.generic_fiber_on_equal_image a A A hA rfl r hr
  obtain ⟨c, hcA, ⟨hca, hf, hcard⟩, hgood⟩ := (hfinite.and hA.1 hall).exists
  exact ⟨r, c, hcA, hca, hf, hcard, hformula, hgood hca⟩

end TriplePencil

namespace TriplePencil

variable {d : ℕ}

theorem mk_eq_iff_on_unit_coordinate (i : Fin d) (x y : Point d)
    (hxi : x i = 1) (hyi : y i = 1) (hx : x ≠ 0) (hy : y ≠ 0) :
    Projectivization.mk ℂ x hx = Projectivization.mk ℂ y hy ↔ x = y := by
  constructor
  · intro he
    obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ x y hx hy).mp he
    have ht1 : t = 1 := by
      have hi := congrFun ht i
      simpa only [Pi.smul_apply, smul_eq_mul, hxi, hyi, mul_one] using hi
    simpa only [ht1, one_smul] using ht.symm
  · rintro rfl
    rfl

theorem normalizedRepresentative_nonzero {n : ℕ} (q : ProjectivePoint (n+1))
    (i : Fin (n+1)) (hi : q.rep i ≠ 0) : normalizedRepresentative q i ≠ 0 := by
  intro he
  have hh := congrFun he i
  have he1 : normalizedRepresentative q i i = 1 := by simp [normalizedRepresentative, hi]
  rw [he1] at hh
  exact one_ne_zero hh

theorem normalizedRepresentative_mk {n : ℕ} (q : ProjectivePoint (n+1))
    (i : Fin (n+1)) (hi : q.rep i ≠ 0) :
    Projectivization.mk ℂ (normalizedRepresentative q i) (normalizedRepresentative_nonzero q i hi) = q := by
  have he : Projectivization.mk ℂ (normalizedRepresentative q i)
      (normalizedRepresentative_nonzero q i hi) = Projectivization.mk ℂ q.rep q.rep_nonzero :=
    (Projectivization.mk_eq_mk_iff' ℂ _ _
      (normalizedRepresentative_nonzero q i hi) q.rep_nonzero).mpr ⟨(q.rep i)⁻¹, rfl⟩
  exact he.trans (Projectivization.mk_rep q)

/-- A covector vanishing on a radial direction gives a literal affine
linear equation at every point of its fibre. -/
theorem covector_zero_of_radial_fiber (v : Point d) (Y : AffineVariety d)
    (z : ProjectivePoint d) (lam : Point d →ₗ[ℂ] ℂ) (hz : lam z.rep = 0)
    (y : Point d) (hy : y ∈ radialFiber v Y z) :
    MvPolynomial.eval y (covectorPoly lam v) = 0 := by
  obtain ⟨hym, hyv, he⟩ := hy
  have he' : Projectivization.mk ℂ (y-v) (sub_ne_zero.mpr hyv) =
      Projectivization.mk ℂ z.rep z.rep_nonzero := he.trans (Projectivization.mk_rep z).symm
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _
    (sub_ne_zero.mpr hyv) z.rep_nonzero).mp he'
  rw [eval_covectorPoly, ← ht, map_smul, hz, smul_zero]

/-- Every point on one affine pencil ray lies in the linear span of its
centre and one selected point. -/
theorem covector_zero_of_pencil_fiber (a c : Point d) (A : AffineVariety d)
    (hc : c ≠ a) (lam : Point d →ₗ[ℂ] ℂ)
    (ha : lam a = 0) (hcz : lam c = 0) (x : Point d)
    (hx : x ∈ radialFiber a A (radialProjection a c hc)) : lam x = 0 := by
  obtain ⟨hxm, hxa, he⟩ := hx
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ (x-a) (c-a)
    (sub_ne_zero.mpr hxa) (sub_ne_zero.mpr hc)).mp he
  have heval := congrArg lam ht
  simp only [map_smul, map_sub, ha, hcz, sub_zero, sub_self, smul_zero] at heval
  exact heval.symm

end TriplePencil

namespace TriplePencil

variable {d : ℕ}

theorem projective_multiplicity_nonneg {n : ℕ} (C : ProjectiveVariety (n+1))
    (z : ProjectivePoint (n+1)) : 0 ≤ C.multiplicity z := by
  rw [C.multiplicity_chart z (chartIndex z) (chartIndex_nonzero z)]
  by_cases hz : chartCoordinates (chartIndex z) z ∈ (C.affineChart (chartIndex z)).points
  · exact ((C.affineChart (chartIndex z)).multiplicity_pos _ hz).le
  · rw [(C.affineChart (chartIndex z)).multiplicity_eq_zero_off _ hz]

theorem one_le_projective_multiplicity_of_mem {n : ℕ} (C : ProjectiveVariety (n+1))
    (z : ProjectivePoint (n+1)) (hz : z ∈ C.points) : 1 ≤ C.multiplicity z := by
  rw [C.multiplicity_chart z (chartIndex z) (chartIndex_nonzero z)]
  exact TripleSections.one_le_multiplicity_of_mem _ _
    ((C.chart_mem_iff z (chartIndex z) (chartIndex_nonzero z)).mpr hz)

/-- A dimension-one birational radial image admits a proper affine linear
section through any prescribed radial ray. -/
theorem exists_proper_ray_section (v : Point d) (Y : AffineVariety d)
    (hY : IsCurve Y) (hdim : (radialImage v Y).dimension = 1)
    (hbir : GenericallyFiniteRadialDegree v Y 1) (z : ProjectivePoint d) :
    ∃ lam : Point d →ₗ[ℂ] ℂ, lam z.rep = 0 ∧ covectorPoly lam v ∉ Y.ideal := by
  obtain ⟨j, hj⟩ := GeoRadial.exists_coord z.rep z.rep_nonzero
  have houtside : ∃ y ∈ Y.points, y-v ∉ (ℂ ∙ z.rep : Submodule ℂ (Point d)) := by
    by_contra! h
    have hsub : Y.points ⊆ (Bridges.complexLine v z.rep).points := by
      intro y hy
      rw [Bridges.complexLine_points v z.rep j hj]
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (h y hy)
      refine ⟨t, ?_⟩
      calc
        y = v+(y-v) := by abel
        _ = v+t • z.rep := by rw [ht]
    have he := GeoRadial.curve_eq_of_subset Y (Bridges.complexLine v z.rep)
      (Bridges.complexLine_irreducible _ _) hY.2
      (Bridges.complexLine_dimension v z.rep j hj) hsub
    have hdeg : Y.degree = 1 := by rw [he, Bridges.complexLine_degree v z.rep j hj]
    have hvm : v ∈ Y.points := by
      rw [he, Bridges.complexLine_points v z.rep j hj]
      exact ⟨0, by simp⟩
    have hm := TripleSections.one_le_multiplicity_of_mem Y v hvm
    have hR := radialImage_irreducible v Y hY.1 (GeoRadial.curve_point_off v Y hY)
    have hRdeg : 1 ≤ (radialImage v Y).degree := by
      simpa only [ProjectiveVariety.degree_cone] using
        (radialImage v Y).affineCone.one_le_degree hR.ne_top
    have hf := TrackA.poly_projection_radial Y hY.1 1 (by norm_num) hY.2 v hdim 1 hbir
    norm_num only [Nat.cast_one, one_mul, hdeg] at hf
    linarith
  obtain ⟨y, hy, hout⟩ := houtside
  obtain ⟨lam, hne, hmap⟩ := (ℂ ∙ z.rep : Submodule ℂ (Point d)).exists_dual_map_eq_bot_of_notMem
    hout inferInstance
  have hz : lam z.rep = 0 := by
    have hmem : lam z.rep ∈ (ℂ ∙ z.rep : Submodule ℂ (Point d)).map lam :=
      Submodule.mem_map.mpr ⟨z.rep, Submodule.mem_span_singleton_self _, rfl⟩
    simpa only [hmap, Submodule.mem_bot] using hmem
  refine ⟨lam, hz, ?_⟩
  intro hf
  have hh := hy (covectorPoly lam v) hf
  exact hne (by simpa only [MvPolynomial.aeval_eq_eval, eval_covectorPoly] using hh)

/-- Degree-one images already give the full fibre multiplicity inequality. -/
theorem radial_fiber_card_le_multiplicity_of_degree_one (v : Point 3) (Y : AffineVariety 3)
    (hY : IsCurve Y) (hdim : (radialImage v Y).dimension = 1)
    (hbir : GenericallyFiniteRadialDegree v Y 1) (hdeg : (radialImage v Y).degree = 1)
    (z : ProjectivePoint 3) (S : Finset (Point 3))
    (hS : ∀ y ∈ S, y ∈ radialFiber v Y z) :
    (S.card : ℚ) ≤ (radialImage v Y).multiplicity z := by
  by_cases hne : S.Nonempty
  · obtain ⟨lam, hlam, hf⟩ := exists_proper_ray_section v Y hY hdim hbir z
    have hb := TripleSections.curve_linear_section_card_off_center_le v Y hY hdim hbir
      (covectorPoly lam v) hf (covectorPoly_degree_le_one lam v)
      (by simp [eval_covectorPoly]) S (by
        intro y hy
        exact ⟨(hS y hy).1, (hS y hy).2.1,
          covector_zero_of_radial_fiber v Y z lam hlam y (hS y hy)⟩)
    rw [hdeg] at hb
    obtain ⟨y, hy⟩ := hne
    have hzm : z ∈ (radialImage v Y).points :=
      (hS y hy).2.2 ▸ GeoRadial.radial_mem v Y y (hS y hy).1 (hS y hy).2.1
    exact hb.trans (one_le_projective_multiplicity_of_mem _ _ hzm)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simpa only [Finset.card_empty, Nat.cast_zero] using projective_multiplicity_nonneg (radialImage v Y) z

end TriplePencil

namespace TriplePencil

/-- A two-vector pencil has a nonzero annihilator. If the radial image
has degree greater than one, its affine equation is a proper source section. -/
theorem exists_proper_pencil_covector (v : Point 3) (Y : AffineVariety 3)
    (hY : IsCurve Y) (hdim : (radialImage v Y).dimension = 1)
    (hdeg : 1 < (radialImage v Y).degree) (a c : Point 3) :
    ∃ lam : Point 3 →ₗ[ℂ] ℂ, lam a = 0 ∧ lam c = 0 ∧ covectorPoly lam v ∉ Y.ideal := by
  let W : Submodule ℂ (Point 3) := Submodule.span ℂ (({a,c} : Finset (Point 3)) : Set (Point 3))
  have hWdim : Module.finrank ℂ W ≤ 2 := by
    have h := finrank_span_finset_le_card (R := ℂ) ({a,c} : Finset (Point 3))
    exact h.trans ((Finset.card_insert_le a {c}).trans (by simp))
  have hW : W ≠ ⊤ := by
    intro h
    rw [h, finrank_top, GeoCommon.finrank_point] at hWdim
    omega
  obtain ⟨u, _, hu⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hW)
  obtain ⟨lam, hlam, hmap⟩ := W.exists_dual_map_eq_bot_of_notMem hu inferInstance
  have hzero : ∀ x ∈ W, lam x = 0 := by
    intro x hx
    have hmem : lam x ∈ W.map lam := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    simpa only [hmap, Submodule.mem_bot] using hmem
  have ha : lam a = 0 := hzero a (Submodule.subset_span (by simp))
  have hc : lam c = 0 := hzero c (Submodule.subset_span (by simp))
  refine ⟨lam, ha, hc, ?_⟩
  intro hf
  let F : AffineSubspace ℂ (Point 3) := AffineSubspace.mk' v (LinearMap.ker lam)
  have hproper : LinearMap.ker lam ≠ ⊤ := by
    intro h
    have hu0 : u ∈ LinearMap.ker lam := by rw [h]; trivial
    exact hlam hu0
  have hkerdim : Module.finrank ℂ (LinearMap.ker lam) ≤ 2 := by
    have hlt := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hproper)
    rw [finrank_top, GeoCommon.finrank_point] at hlt
    omega
  have hYF : Y.points ⊆ F := by
    intro x hx
    apply AffineSubspace.mem_mk'.mpr
    change lam (x-v) = 0
    have hh := hx (covectorPoly lam v) hf
    simpa only [MvPolynomial.aeval_eq_eval, eval_covectorPoly] using hh
  have hpF : v ∈ F := by apply AffineSubspace.mem_mk'.mpr; simp
  have hbound := radial_curve_degree_le_one_of_plane v Y hY F
    (by
      change Module.finrank ℂ (AffineSubspace.mk' v (LinearMap.ker lam)).direction ≤ 2
      rw [AffineSubspace.direction_mk']
      exact hkerdim) hYF hpF hdim
  exact (not_le_of_gt hdeg) hbound

end TriplePencil

namespace TriplePencil

variable {d : ℕ}

/-- Lift a finite list of distinct radial directions, retaining its literal
cardinality and its disjointness from one specified original fibre. -/
theorem lift_finite_radial_directions (v : Point d) (Y : AffineVariety d)
    (R : Finset (Point d)) (dirs : Point d → ProjectivePoint d)
    (hinj : Set.InjOn dirs (R : Set (Point d)))
    (hex : ∀ x ∈ R, (radialFiber v Y (dirs x)).Nonempty)
    (q : ProjectivePoint d) (hneq : ∀ x ∈ R, dirs x ≠ q)
    (S : Finset (Point d)) (hS : ∀ y ∈ S, y ∈ radialFiber v Y q)
    (lam : Point d →ₗ[ℂ] ℂ) (hzero : ∀ x ∈ R, lam (dirs x).rep = 0) :
    ∃ T : Finset (Point d), T.card = R.card ∧ Disjoint S T ∧
      ∀ y ∈ T, y ∈ Y.points ∧ y ≠ v ∧ MvPolynomial.eval y (covectorPoly lam v) = 0 := by
  have he : ∀ x : {x // x ∈ R}, ∃ y, y ∈ radialFiber v Y (dirs x.val) := by
    intro x
    exact hex x.val x.property
  choose lift hlift using he
  have hliftinj : Function.Injective lift := by
    intro x y hxy
    apply Subtype.ext
    apply hinj x.property y.property
    have hx := (hlift x).2.2
    have hy := (hlift y).2.2
    have heproj : radialProjection v (lift x) (hlift x).2.1 =
        radialProjection v (lift y) (hlift y).2.1 := by
      apply (Projectivization.mk_eq_mk_iff' ℂ (lift x-v) (lift y-v)
        (sub_ne_zero.mpr (hlift x).2.1) (sub_ne_zero.mpr (hlift y).2.1)).mpr
      exact ⟨1, by simp only [one_smul, hxy]⟩
    exact hx.symm.trans (heproj.trans hy)
  let T := Finset.univ.image lift
  refine ⟨T, ?_, ?_, ?_⟩
  · simp only [T, Finset.card_image_of_injective _ hliftinj, Finset.card_univ, Fintype.card_coe]
  · apply Finset.disjoint_left.mpr
    intro y hyS hyT
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyT
    have heq : dirs x.val = q := (hlift x).2.2.symm.trans (hS _ hyS).2.2
    exact hneq x.val x.property heq
  · intro y hyT
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyT
    exact ⟨(hlift x).1, (hlift x).2.1,
      covector_zero_of_radial_fiber v Y (dirs x.val) lam (hzero x.val x.property) _ (hlift x)⟩

/-- The generic-degree open supplies a literal lift of every direction on
which its homogeneous witness does not vanish. -/
theorem radial_lift_of_generic_open (v : Point d) (Y : AffineVariety d)
    (g : Poly d) (D : ℕ) (hg : g.IsHomogeneous D)
    (hfib : ∀ z ∈ (radialImage v Y).points, MvPolynomial.aeval z.rep g ≠ 0 →
      (radialFiber v Y z).Finite ∧ (radialFiber v Y z).ncard = 1)
    (x : Point d) (hx : x ≠ 0) (hcone : x ∈ (radialImage v Y).affineCone.points)
    (hgood : MvPolynomial.eval x g ≠ 0) :
    (radialFiber v Y (Projectivization.mk ℂ x hx)).Nonempty := by
  have hmem := (ProjectiveVariety.mem_points_mk_iff (radialImage v Y) x hx).mpr hcone
  have hn : MvPolynomial.aeval (Projectivization.mk ℂ x hx).rep g ≠ 0 := by
    simpa only [MvPolynomial.aeval_eq_eval] using
      (fun h => hgood ((Bridges.homogeneous_eval_zero_mk_iff g hg x hx).mp h))
  have hc := (hfib _ hmem hn).2
  exact Set.nonempty_of_ncard_ne_zero (by rw [hc]; norm_num)

end TriplePencil

namespace TriplePencil

/-- A finite fibre of a degree-one radial map is bounded by the full
multiplicity of its plane image at that direction. -/
theorem radial_birational_fiber_card_le_multiplicity (v : Point 3) (Y : AffineVariety 3)
    (hY : IsCurve Y) (hdim : (radialImage v Y).dimension = 1)
    (hbir : GenericallyFiniteRadialDegree v Y 1) (q : ProjectivePoint 3)
    (S : Finset (Point 3)) (hS : ∀ y ∈ S, y ∈ radialFiber v Y q) :
    (S.card : ℚ) ≤ (radialImage v Y).multiplicity q := by
  by_cases hSne : S.Nonempty
  · let C := radialImage v Y
    have hC : C.IsIrreducible := radialImage_irreducible v Y hY.1
      (GeoRadial.curve_point_off v Y hY)
    obtain ⟨y, hy⟩ := hSne
    have hq : q ∈ C.points :=
      (hS y hy).2.2 ▸ GeoRadial.radial_mem v Y y (hS y hy).1 (hS y hy).2.1
    have hCdeg : 1 ≤ C.degree := by
      simpa only [ProjectiveVariety.degree_cone] using C.affineCone.one_le_degree hC.ne_top
    by_cases hlarge : 1 < C.degree
    · obtain ⟨i, hi⟩ := exists_nonzero_coordinate q
      let a := normalizedRepresentative q i
      let A := TrackA.projectiveLinearSlice C (MvPolynomial.X i)
      have ha : a ∈ A.points := normalizedRepresentative_mem C q hq i hi
      have hXi : MvPolynomial.X i ∉ C.ideal := by
        intro hh
        have hz := hq q.rep q.rep_nonzero (Projectivization.mk_rep q) (MvPolynomial.X i) hh
        exact hi (by simpa using hz)
      obtain ⟨hr, g, D, hg, hnot, hfib⟩ := hbir
      obtain ⟨r, c, hcA, hca, hf, hcard, hformula, hgood⟩ :=
        exists_good_slice_pencil C hC hdim hlarge i hXi a ha g D hg hnot
      let R := hf.toFinset
      have hR : ∀ x ∈ R, x ∈ radialFiber a A (radialProjection a c hca) := by
        intro x hx
        exact hf.mem_toFinset.mp hx
      have hRcard : R.card = r := by
        rw [Set.ncard_eq_toFinset_card _ hf] at hcard
        exact hcard
      have hxi : ∀ x ∈ R, x i = 1 := fun x hx => slice_coordinate C i x (hR x hx).1
      have hx0 : ∀ x ∈ R, x ≠ 0 := by
        intro x hx hz
        have hh := congrFun hz i
        rw [hxi x hx] at hh
        exact one_ne_zero hh
      let dirs : Point 3 → ProjectivePoint 3 := fun x =>
        if h : x ≠ 0 then Projectivization.mk ℂ x h else q
      have hdirections : ∀ (x : Point 3) (hx : x ∈ R), dirs x = Projectivization.mk ℂ x (hx0 x hx) := by
        intro x hx
        simp only [dirs, dif_pos (hx0 x hx)]
      obtain ⟨lam, hla, hlc, hproper⟩ := exists_proper_pencil_covector v Y hY hdim hlarge a c
      have hqzero : lam q.rep = 0 := by
        have hh : (q.rep i)⁻¹ * lam q.rep = 0 := by
          simpa only [a, normalizedRepresentative, map_smul, smul_eq_mul] using hla
        exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero hi)
      have hinj : Set.InjOn dirs (R : Set (Point 3)) := by
        intro x hx x' hx' he
        rw [hdirections x hx, hdirections x' hx'] at he
        exact (mk_eq_iff_on_unit_coordinate i x x' (hxi x hx) (hxi x' hx')
          (hx0 x hx) (hx0 x' hx')).mp he
      have hex : ∀ x ∈ R, (radialFiber v Y (dirs x)).Nonempty := by
        intro x hx
        rw [hdirections x hx]
        exact radial_lift_of_generic_open v Y g D hg hfib x (hx0 x hx)
          ((TrackA.linearSlice_points C (MvPolynomial.X i) x).mp (hR x hx).1).1
          (hgood x (hR x hx))
      have hneq : ∀ x ∈ R, dirs x ≠ q := by
        intro x hx he
        rw [hdirections x hx] at he
        have ha0 := normalizedRepresentative_nonzero q i hi
        have he' := he.trans (normalizedRepresentative_mk q i hi).symm
        have hai : a i = 1 := slice_coordinate C i a ha
        have hxa := (mk_eq_iff_on_unit_coordinate i x a (hxi x hx) hai (hx0 x hx) ha0).mp he'
        exact (hR x hx).2.1 hxa
      have hzero : ∀ x ∈ R, lam (dirs x).rep = 0 := by
        intro x hx
        have hlx := covector_zero_of_pencil_fiber a c A hca lam hla hlc x (hR x hx)
        have heval : MvPolynomial.eval x (covectorPoly lam 0) = 0 := by
          rw [eval_covectorPoly, sub_zero, hlx]
        have hrep := (Bridges.homogeneous_eval_zero_mk_iff (covectorPoly lam 0)
          (covectorPoly_zero_homogeneous lam) x (hx0 x hx)).mpr heval
        rw [hdirections x hx]
        simpa only [eval_covectorPoly, sub_zero] using hrep
      obtain ⟨T, hTcard, hdisj, hT⟩ := lift_finite_radial_directions v Y R dirs hinj hex q hneq S hS lam hzero
      have hbudget := TripleSections.curve_linear_section_card_off_center_le v Y hY hdim
        (by exact ⟨hr, g, D, hg, hnot, hfib⟩) (covectorPoly lam v) hproper
        (covectorPoly_degree_le_one lam v) (by simp [eval_covectorPoly]) (S ∪ T) (by
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact ⟨(hS x hx).1, (hS x hx).2.1,
              covector_zero_of_radial_fiber v Y q lam hqzero x (hS x hx)⟩
          · exact hT x hx)
      rw [Finset.card_union_of_disjoint hdisj, Nat.cast_add, hTcard, hRcard] at hbudget
      have hSm : (S.card : ℚ) ≤ A.multiplicity a := by linarith
      exact hSm.trans (normalizedRepresentative_multiplicity_le C hC q hq i hi)
    · have he : C.degree = 1 := le_antisymm (not_lt.mp hlarge) hCdeg
      exact radial_fiber_card_le_multiplicity_of_degree_one v Y hY hdim hbir he q S hS
  · rw [Finset.not_nonempty_iff_eq_empty.mp hSne]
    simpa only [Finset.card_empty, Nat.cast_zero] using projective_multiplicity_nonneg (radialImage v Y) q

theorem smooth_radial_fiber_multiplicity_bound : TripleGeneric.SmoothRadialFiberMultiplicityBound := by
  intro Y hY v hdim hbir q S hS
  exact radial_birational_fiber_card_le_multiplicity v Y hY hdim hbir q S (fun y hy => (hS y hy).1)

end TriplePencil

end
end DistinctDistances.TrackD
