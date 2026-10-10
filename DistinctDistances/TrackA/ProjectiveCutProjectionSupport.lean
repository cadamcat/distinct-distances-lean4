import DistinctDistances.TrackA.RadialFiberSupport

namespace DistinctDistances.TrackA
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical BigOperators

def projectiveCutImage {a b : ℕ} (V : ProjectiveVariety a) (f : Poly a)
    (φ : LinearProjection a b) : ProjectiveVariety b :=
  ProjectiveVariety.closure {z | ∃ v ∈ V.affineCone.points,
    MvPolynomial.eval v f = 0 ∧ ∃ hv : φ v ≠ 0, Projectivization.mk ℂ (φ v) hv = z}

theorem cone_cut_mem {a : ℕ} (V : ProjectiveVariety a) (f : Poly a) (v : Point a)
    (hv : v ∈ V.affineCone.points) (hf : MvPolynomial.eval v f = 0) :
    v ∈ (V.affineCone.cut f).points := by
  rw [AffineVariety.cut, AffineVariety.points_ofIdeal]
  have hI : V.ideal ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := fun g hg => hv g hg
  have hfI : Ideal.span {f} ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    apply Ideal.span_le.mpr
    rintro g rfl
    simpa [MvPolynomial.aeval_eq_eval] using hf
  exact fun g hg => sup_le hI hfI hg

theorem cone_cut_projection_dimension {a b k : ℕ} (V : ProjectiveVariety a)
    (hV : V.IsIrreducible) (hdim : V.affineCone.dimension = k+1)
    (f : Poly a) (hf : f ∉ V.ideal) (φ : LinearProjection a b) :
    ((⟨φ, 0⟩ : AffineProjection a b).image (V.affineCone.cut f)).dimension ≤ k := by
  let K := V.ideal ⊔ Ideal.span {f}
  let Q := OAI.QuarticPowerFree.coordinateHilbert K
  let A := V.affineCone.cut f
  let W := (⟨φ, 0⟩ : AffineProjection a b).image A
  letI : V.ideal.IsPrime := hV
  have hQdeg : Q.natDegree ≤ k :=
    (OAI.QuarticPowerFree.proper_cut_hilbert_polynomial V.ideal f hf
      (OAI.QuarticPowerFree.coordinateHilbert V.ideal) Q
      ((OAI.QuarticPowerFree.coordinateHilbert_eventually V.ideal).mono (fun _ h => h.symm))
      ((OAI.QuarticPowerFree.coordinateHilbert_eventually K).mono (fun _ h => h.symm))
      k hdim.le).1
  have hpb : (⟨φ, 0⟩ : AffineProjection a b).pullback = linearPullback φ := by
    ext j
    simp [AffineProjection.pullback, linearPullback]
  have hWideal : W.ideal = A.ideal.comap (linearPullback φ).toRingHom := by
    change A.ideal.comap (⟨φ, 0⟩ : AffineProjection a b).pullback.toRingHom = _
    rw [hpb]
  have hproj (T : ℕ) : W.hilbert T ≤ A.hilbert T := by
    have h := OAI.QuarticPowerFree.polynomial_projection_hilbert_le A.ideal W.ideal
      (linearCoordinate φ) 1
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
  have hnonneg : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ W.hilbertPolynomial.eval (T : ℚ) := by
    filter_upwards [W.hilbert_eventually] with T hT
    rw [← hT]
    positivity
  exact (OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds _ _ hnonneg hWQ).trans hQdeg

theorem cone_cut_image_ideal_le {a b e : ℕ} (V : ProjectiveVariety a) (f : Poly a)
    (hf : f.IsHomogeneous e) (φ : LinearProjection a b) :
    ((⟨φ, 0⟩ : AffineProjection a b).image (V.affineCone.cut f)).ideal ≤
      (projectiveCutImage V f φ).ideal := by
  intro F hF
  apply MvPolynomial.mem_vanishingIdeal_iff.mpr
  rintro w ⟨hw, v, hv, hvf, hφ, heq⟩
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ w (φ v) hw hφ).mp heq.symm
  have hcv : c • v ∈ (V.affineCone.cut f).points := by
    apply cone_cut_mem V f _ (cone_smul_mem V v hv c)
    rw [Bridges.homogeneous_eval_smul f hf, hvf, mul_zero]
  have hpull : (⟨φ, 0⟩ : AffineProjection a b).pullback F ∈ (V.affineCone.cut f).ideal := hF
  have hz := hcv _ hpull
  rw [AffineProjection.eval_pullback] at hz
  have hvec : (⟨φ, 0⟩ : AffineProjection a b).apply (c • v) = w := by
    simpa [AffineProjection.apply, map_smul] using hc
  rwa [hvec] at hz

theorem cone_cut_image_separator {a b k e : ℕ} (V : ProjectiveVariety a)
    (hV : V.IsIrreducible) (hdim : V.affineCone.dimension = k+1)
    (f : Poly a) (hfhom : f.IsHomogeneous e) (hf : f ∉ V.ideal)
    (φ : LinearProjection a b) (Y : ProjectiveVariety b)
    (hYne : Y.points.Nonempty) (hYdim : Y.dimension = k) :
    ∃ (H : Poly b) (E : ℕ), H.IsHomogeneous E ∧ H ∉ Y.ideal ∧
      H ∈ (projectiveCutImage V f φ).ideal := by
  let W := (⟨φ, 0⟩ : AffineProjection a b).image (V.affineCone.cut f)
  let Z := projectiveCutImage V f φ
  have hWdim := cone_cut_projection_dimension V hV hdim f hf φ
  change W.dimension ≤ k at hWdim
  have hYcone : Y.affineCone.dimension = k+1 := by rw [Y.dimension_cone hYne, hYdim]
  have hnot : ¬ Z.ideal ≤ Y.ideal := by
    intro hZY
    have hWY : W.ideal ≤ Y.ideal := (cone_cut_image_ideal_le V f hfhom φ).trans hZY
    have hle : ∀ᶠ T : ℕ in Filter.atTop,
        Y.affineCone.hilbertPolynomial.eval (T : ℚ) ≤ W.hilbertPolynomial.eval (T : ℚ) := by
      filter_upwards [Y.affineCone.hilbert_eventually, W.hilbert_eventually] with T hY hW
      rw [← hY, ← hW]
      exact_mod_cast OAI.QuarticPowerFree.quotient_hilbert_le W.ideal Y.ideal hWY T
    have hnonneg : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ Y.affineCone.hilbertPolynomial.eval (T : ℚ) := by
      filter_upwards [Y.affineCone.hilbert_eventually] with T hT
      rw [← hT]
      positivity
    have hdl := OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds _ _ hnonneg hle
    change Y.affineCone.dimension ≤ W.dimension at hdl
    omega
  change ¬ ∀ G, G ∈ Z.ideal → G ∈ Y.ideal at hnot
  push Not at hnot
  obtain ⟨G, hGZ, hGY⟩ := hnot
  have hex : ∃ d, MvPolynomial.homogeneousComponent d G ∉ Y.ideal := by
    by_contra hn
    push Not at hn
    apply hGY
    rw [← MvPolynomial.sum_homogeneousComponent G]
    exact Y.ideal.sum_mem (fun d _ => hn d)
  obtain ⟨d, hd⟩ := hex
  exact ⟨MvPolynomial.homogeneousComponent d G, d,
    MvPolynomial.homogeneousComponent_isHomogeneous d G, hd,
    MvPolynomial.homogeneousComponent_mem_of_mem Z.isHomogeneous hGZ d⟩

end
end DistinctDistances.TrackA
