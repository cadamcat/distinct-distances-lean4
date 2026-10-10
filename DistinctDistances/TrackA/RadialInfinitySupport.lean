import DistinctDistances.TrackA.RadialProjectionSupport

namespace DistinctDistances.TrackA
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical BigOperators

def radialInfinityCut {n : ℕ} (X : AffineVariety n) : AffineVariety (n+1) :=
  (projectiveClosure X).affineCone.cut (MvPolynomial.X 0)

def radialInfinityAffineImage {n : ℕ} (X : AffineVariety n) (p : Point n) : AffineVariety n :=
  (⟨radialLinearProjection p, 0⟩ : AffineProjection (n+1) n).image (radialInfinityCut X)

def radialInfinityImage {n : ℕ} (X : AffineVariety n) (p : Point n) : ProjectiveVariety n :=
  ProjectiveVariety.closure {z | ∃ v : Point (n+1),
    v ∈ (projectiveClosure X).affineCone.points ∧ v 0 = 0 ∧
    ∃ hφ : radialLinearProjection p v ≠ 0,
      Projectivization.mk ℂ (radialLinearProjection p v) hφ = z}

theorem radialInfinityCut_mem {n : ℕ} (X : AffineVariety n) (v : Point (n+1))
    (hv : v ∈ (projectiveClosure X).affineCone.points) (hv0 : v 0 = 0) :
    v ∈ (radialInfinityCut X).points := by
  rw [radialInfinityCut, AffineVariety.cut, AffineVariety.points_ofIdeal]
  have hI : (projectiveClosure X).ideal ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom :=
    fun F hF => hv F hF
  have hX : Ideal.span {(MvPolynomial.X 0 : Poly (n+1))} ≤
      RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    apply Ideal.span_le.mpr
    rintro F rfl
    change MvPolynomial.aeval v (MvPolynomial.X 0) = 0
    simpa using hv0
  exact fun F hF => sup_le hI hX hF

/-- All representatives of the actual infinity image lie in the affine image
of the hyperplane cut of the source cone. -/
theorem radialInfinity_ideal_le {n : ℕ} (X : AffineVariety n) (p : Point n) :
    (radialInfinityAffineImage X p).ideal ≤ (radialInfinityImage X p).ideal := by
  intro F hF
  apply MvPolynomial.mem_vanishingIdeal_iff.mpr
  rintro w ⟨hw, v, hv, hv0, hφ, heq⟩
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ w
    (radialLinearProjection p v) hw hφ).mp heq.symm
  have hcv : c • v ∈ (radialInfinityCut X).points :=
    radialInfinityCut_mem X (c • v) (cone_smul_mem _ v hv c)
      (by simp [Pi.smul_apply, hv0])
  have hpull : (⟨radialLinearProjection p, 0⟩ : AffineProjection (n+1) n).pullback F ∈
      (radialInfinityCut X).ideal := hF
  have hz := hcv _ hpull
  rw [AffineProjection.eval_pullback] at hz
  have hvec : (⟨radialLinearProjection p, 0⟩ : AffineProjection (n+1) n).apply (c • v) = w := by
    simpa [AffineProjection.apply, map_smul] using hc
  rwa [hvec] at hz

/-- The infinity image has filtered Hilbert dimension at most dim X.
Its source is one proper hyperplane cut of the cone, and linear pullback
embeds its restriction spaces into those of that cut. -/
theorem radialInfinity_dimension_le {n k : ℕ} (X : AffineVariety n)
    (hX : X.IsIrreducible) (hdim : X.dimension = k) (p : Point n) :
    (radialInfinityAffineImage X p).dimension ≤ k := by
  let V := projectiveClosure X
  let K := V.ideal ⊔ Ideal.span {(MvPolynomial.X 0 : Poly (n+1))}
  let Q := OAI.QuarticPowerFree.coordinateHilbert K
  let A := radialInfinityCut X
  let W := radialInfinityAffineImage X p
  have hne := X.points_nonempty_of_isIrreducible hX
  obtain ⟨x, hx⟩ := hne
  have hVne : V.points.Nonempty := ⟨affineEmbedding x, (affineEmbedding_mem_closure X x).mpr hx⟩
  have hVdim : V.affineCone.dimension = k+1 := by
    rw [V.dimension_cone hVne, projectiveClosure_dimension X ⟨x, hx⟩, hdim]
  have hX0 : (MvPolynomial.X 0 : Poly (n+1)) ∉ V.ideal := by
    intro hmem
    have hz := projectiveClosure_aeval_mem X _ hmem
    have hzero := hx _ hz
    have hbad : (1 : ℂ) = 0 := by simpa using hzero
    exact one_ne_zero hbad
  letI : V.ideal.IsPrime := projectiveClosure_isIrreducible X hX
  have hQdeg : Q.natDegree ≤ k :=
    (OAI.QuarticPowerFree.proper_cut_hilbert_polynomial V.ideal (MvPolynomial.X 0) hX0
      (OAI.QuarticPowerFree.coordinateHilbert V.ideal) Q
      ((OAI.QuarticPowerFree.coordinateHilbert_eventually V.ideal).mono (fun _ h => h.symm))
      ((OAI.QuarticPowerFree.coordinateHilbert_eventually K).mono (fun _ h => h.symm))
      k hVdim.le).1
  have hpb : (⟨radialLinearProjection p, 0⟩ : AffineProjection (n+1) n).pullback =
      linearPullback (radialLinearProjection p) := by
    ext j
    simp [AffineProjection.pullback, linearPullback]
  have hWideal : W.ideal = A.ideal.comap (linearPullback (radialLinearProjection p)).toRingHom := by
    change A.ideal.comap (⟨radialLinearProjection p, 0⟩ : AffineProjection (n+1) n).pullback.toRingHom = _
    rw [hpb]
  have hproj (T : ℕ) : W.hilbert T ≤ A.hilbert T := by
    have h := OAI.QuarticPowerFree.polynomial_projection_hilbert_le A.ideal W.ideal
      (linearCoordinate (radialLinearProjection p)) 1
      (fun j => (linearCoordinate_homogeneous _ j).totalDegree_le) (fun F => by
        rw [Ideal.Quotient.eq_zero_iff_mem, hWideal, Ideal.mem_comap]
        rfl) T
    change W.hilbert T ≤ A.hilbert (1*T) at h
    simpa only [Nat.one_mul] using h
  have hcut (T : ℕ) : A.hilbert T ≤ Module.finrank ℂ
      ((OAI.QuarticPowerFree.totalSpace T).map (Ideal.Quotient.mkₐ ℂ K).toLinearMap) :=
    OAI.QuarticPowerFree.quotient_hilbert_le K A.ideal Ideal.le_radical T
  have hWQ : ∀ᶠ T : ℕ in Filter.atTop, W.hilbertPolynomial.eval (T : ℚ) ≤ Q.eval (T : ℚ) := by
    filter_upwards [W.hilbert_eventually, OAI.QuarticPowerFree.coordinateHilbert_eventually K]
      with T hW hQ
    rw [← hW, ← hQ]
    exact_mod_cast (hproj T).trans (hcut T)
  have hWnonneg : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ W.hilbertPolynomial.eval (T : ℚ) := by
    filter_upwards [W.hilbert_eventually] with T hT
    rw [← hT]
    positivity
  exact (OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds _ _ hWnonneg hWQ).trans hQdeg

/-- A homogeneous principal open in the radial image excludes every source
point at infinity. Only the dimension-preserving hypothesis is used. -/
theorem radial_no_infinity_polynomial {n k : ℕ} (X : AffineVariety n)
    (hX : X.IsIrreducible) (hdim : X.dimension = k) (p : Point n)
    (himage : (radialImage p X).dimension = k) (hactual : ∃ x ∈ X.points, x ≠ p) :
    ∃ (H : Poly n) (D : ℕ), H.IsHomogeneous D ∧ H ∉ (radialImage p X).ideal ∧
      H ∈ (radialInfinityImage X p).ideal := by
  let Y := radialImage p X
  let W := radialInfinityAffineImage X p
  let Z := radialInfinityImage X p
  obtain ⟨x, hx, hxne⟩ := hactual
  have hYne : Y.points.Nonempty :=
    ⟨radialProjection p x hxne, ProjectiveVariety.subset_closure _ ⟨x, hx, hxne, rfl⟩⟩
  have hYdim : Y.affineCone.dimension = k+1 := by rw [Y.dimension_cone hYne, himage]
  have hWdim := radialInfinity_dimension_le X hX hdim p
  change W.dimension ≤ k at hWdim
  have hnot : ¬ Z.ideal ≤ Y.ideal := by
    intro hZY
    have hWY : W.ideal ≤ Y.ideal := (radialInfinity_ideal_le X p).trans hZY
    have hle : ∀ᶠ T : ℕ in Filter.atTop,
        Y.affineCone.hilbertPolynomial.eval (T : ℚ) ≤ W.hilbertPolynomial.eval (T : ℚ) := by
      filter_upwards [Y.affineCone.hilbert_eventually, W.hilbert_eventually] with T hY hW
      rw [← hY, ← hW]
      exact_mod_cast OAI.QuarticPowerFree.quotient_hilbert_le W.ideal Y.ideal hWY T
    have hnonneg : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ Y.affineCone.hilbertPolynomial.eval (T : ℚ) := by
      filter_upwards [Y.affineCone.hilbert_eventually] with T hT
      rw [← hT]
      positivity
    have hdimle := OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds _ _ hnonneg hle
    change Y.affineCone.dimension ≤ W.dimension at hdimle
    omega
  change ¬ ∀ G, G ∈ Z.ideal → G ∈ Y.ideal at hnot
  push Not at hnot
  obtain ⟨G, hGZ, hGY⟩ := hnot
  have hex : ∃ d, MvPolynomial.homogeneousComponent d G ∉ Y.ideal := by
    by_contra h
    push Not at h
    apply hGY
    rw [← MvPolynomial.sum_homogeneousComponent G]
    exact Y.ideal.sum_mem (fun d hd => h d)
  obtain ⟨d, hd⟩ := hex
  exact ⟨MvPolynomial.homogeneousComponent d G, d,
    MvPolynomial.homogeneousComponent_isHomogeneous d G, hd,
    MvPolynomial.homogeneousComponent_mem_of_mem Z.isHomogeneous hGZ d⟩

end
end DistinctDistances.TrackA
