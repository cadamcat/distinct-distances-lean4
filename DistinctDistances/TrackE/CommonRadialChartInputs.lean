import DistinctDistances.TrackE.CommonRadialChartData
import DistinctDistances.TrackE.CommonRadialContainment

/-! Page-sized radial chart identities for sparse-cones.tex:143–155,172–180. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

theorem common_radial_chart_point {d : ℕ} (i₀ : Fin d) (p y : Point d) :
    TrackD.rationalPoint (commonRadialNumerator p) (commonRadialDenominator i₀ p) y =
      TrackD.dirChart (LinearMap.proj i₀) (y - p) := by
  funext j
  simp only [TrackD.rationalPoint, TrackD.dirChart, commonRadialNumerator,
    commonRadialDenominator, LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul,
    map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, Pi.sub_apply]
  rw [div_eq_mul_inv, mul_comm]

theorem common_radial_chart_differential {d : ℕ} (i₀ : Fin d) (p y : Point d) :
    TrackD.rationalDifferential (commonRadialNumerator p) (commonRadialDenominator i₀ p) y =
      TrackD.dirChartDeriv (LinearMap.proj i₀) (y - p) := by
  have hdiff_num : ∀ j : Fin d,
      differential (commonRadialNumerator p j) y = LinearMap.proj j := by
    intro j
    simp only [commonRadialNumerator, TrackD.differential_sub, TrackD.differential_X,
      TrackD.differential_C, sub_zero]
  have hdiff_den :
      differential (commonRadialDenominator i₀ p) y = LinearMap.proj i₀ := by
    simp only [commonRadialDenominator, commonRadialNumerator,
      TrackD.differential_sub, TrackD.differential_X, TrackD.differential_C,
      sub_zero]
  have heval_num : ∀ j : Fin d,
      MvPolynomial.eval y (commonRadialNumerator p j) = (y - p) j := by
    intro j
    simp only [commonRadialNumerator, map_sub, MvPolynomial.eval_X,
      MvPolynomial.eval_C, Pi.sub_apply]
  have heval_den :
      MvPolynomial.eval y (commonRadialDenominator i₀ p) = (y - p) i₀ := by
    simp only [commonRadialDenominator, commonRadialNumerator, map_sub,
      MvPolynomial.eval_X, MvPolynomial.eval_C,
      Pi.sub_apply]
  apply LinearMap.ext
  intro w
  funext j
  simp only [TrackD.rationalDifferential, TrackD.dirChartDeriv, LinearMap.pi_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.proj_apply,
    LinearMap.id_apply, LinearMap.smulRight_apply, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply, hdiff_num, hdiff_den, heval_num, heval_den]
  rw [div_eq_mul_inv]
  ring

/-- Every actual normalized direction is on the shared complete radial slice. -/
theorem common_radial_chart_point_slice {d : ℕ} (Y : AffineVariety d)
    (i₀ : Fin d) (p y : Point d) (hy : y ∈ Y) (hi : (y - p) i₀ ≠ 0) :
    TrackD.dirChart (LinearMap.proj i₀) (y - p) ∈
      TrackA.projectiveLinearSlice (radialImage p Y) (MvPolynomial.X i₀) := by
  have hne : y ≠ p := fun he => hi (by simp [he])
  have hw_eq : TrackD.dirChart (LinearMap.proj i₀) (y - p) =
      ((y - p) i₀)⁻¹ • (y - p) := by
    simp only [TrackD.dirChart, LinearMap.proj_apply]
  have hw_i0 : (TrackD.dirChart (LinearMap.proj i₀) (y - p)) i₀ = 1 := by
    rw [hw_eq, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hi]
  have hw_ne : TrackD.dirChart (LinearMap.proj i₀) (y - p) ≠ 0 := by
    intro hz
    have h := congrFun hz i₀
    rw [hw_i0] at h
    exact one_ne_zero h
  have hmk : Projectivization.mk ℂ (TrackD.dirChart (LinearMap.proj i₀) (y - p)) hw_ne =
      radialProjection p y hne := by
    unfold radialProjection
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ hw_ne (sub_ne_zero.mpr hne)).mpr
    exact ⟨((y - p) i₀)⁻¹, hw_eq⟩
  have hTmem : radialProjection p y hne ∈ (radialImage p Y).points := by
    apply ProjectiveVariety.subset_closure
    exact ⟨y, hy, hne, rfl⟩
  have hmem : Projectivization.mk ℂ (TrackD.dirChart (LinearMap.proj i₀) (y - p)) hw_ne ∈
      (radialImage p Y).points := hmk ▸ hTmem
  have hcone : TrackD.dirChart (LinearMap.proj i₀) (y - p) ∈
      (radialImage p Y).affineCone.points :=
    (ProjectiveVariety.mem_points_mk_iff _ _ hw_ne).mp hmem
  apply (TrackA.linearSlice_points _ _ _).mpr
  refine ⟨hcone, ?_⟩
  simpa only [MvPolynomial.eval_X] using hw_i0

/-- The literal chart coordinate is proper on the complete radial image. -/
theorem common_radial_chart_coordinate_not_mem {d : ℕ} (Y : AffineVariety d)
    (i₀ : Fin d) (p : Point d) (hchart : ∃ y ∈ Y, (y - p) i₀ ≠ 0) :
    MvPolynomial.X i₀ ∉ (radialImage p Y).ideal := by
  intro hmem
  obtain ⟨y, hy, hi⟩ := hchart
  have hs := common_radial_chart_point_slice Y i₀ p y hy hi
  obtain ⟨hcone, h1⟩ := (TrackA.linearSlice_points _ _ _).mp hs
  have hz : MvPolynomial.eval (TrackD.dirChart (LinearMap.proj i₀) (y - p))
      (MvPolynomial.X i₀) = 0 :=
    (TrackD.mem_ideal_iff_eval_zero (radialImage p Y).affineCone _).1 hmem _ hcone
  rw [h1] at hz
  exact one_ne_zero hz

/-- Clearing the fixed homogeneous power keeps all original direction points. -/
theorem common_radial_chart_homogenize_zero {d : ℕ} (i₀ : Fin d)
    (q : Poly d) (v : Point d) (hi : v i₀ ≠ 0)
    (hq : MvPolynomial.eval (TrackD.dirChart (LinearMap.proj i₀) v) q = 0) :
    MvPolynomial.eval v
      (TrackA.chartHomogenize (MvPolynomial.X i₀) q.totalDegree q) = 0 := by
  have hc : ((v i₀)⁻¹ : ℂ) ≠ 0 := inv_ne_zero hi
  have hw_eq : TrackD.dirChart (LinearMap.proj i₀) v = (v i₀)⁻¹ • v := by
    simp only [TrackD.dirChart, LinearMap.proj_apply]
  have hℓ1 : MvPolynomial.eval (TrackD.dirChart (LinearMap.proj i₀) v)
      (MvPolynomial.X i₀) = 1 := by
    simp only [TrackD.dirChart, LinearMap.proj_apply, MvPolynomial.eval_X,
      Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hi]
  have hℓhom : (MvPolynomial.X i₀ : Poly d).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X ℂ i₀
  have hhom : (TrackA.chartHomogenize (MvPolynomial.X i₀) q.totalDegree q).IsHomogeneous
      q.totalDegree :=
    TrackA.chartHomogenize_homogeneous _ _ hℓhom
  have heq : MvPolynomial.eval (TrackD.dirChart (LinearMap.proj i₀) v)
      (TrackA.chartHomogenize (MvPolynomial.X i₀) q.totalDegree q) =
      MvPolynomial.eval (TrackD.dirChart (LinearMap.proj i₀) v) q :=
    TrackA.chartHomogenize_eval _ _ le_rfl _ hℓ1
  have hzero : MvPolynomial.eval (TrackD.dirChart (LinearMap.proj i₀) v)
      (TrackA.chartHomogenize (MvPolynomial.X i₀) q.totalDegree q) = 0 :=
    heq.trans hq
  rw [hw_eq, Bridges.homogeneous_eval_smul _ hhom] at hzero
  rcases mul_eq_zero.mp hzero with hpow | heval
  · exact (pow_ne_zero _ hc) hpow |>.elim
  · exact heval

/-- A homogeneous radial equation on a target open holds on the complete image. -/
theorem common_radial_homogeneous_equation {d : ℕ} (Y : AffineVariety d)
    (hY : Y.IsIrreducible) (p : Point d) (a : Poly d) (D : ℕ)
    (ha : a.IsHomogeneous D)
    (hgen : TrackD.ForGeneralPoint Y (fun y => MvPolynomial.eval (y - p) a = 0)) :
    a ∈ (radialImage p Y).ideal := by
  have heval : ∀ y : Point d,
      MvPolynomial.eval y
        (MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (p i)) a) =
        MvPolynomial.eval (y - p) a := by
    intro y
    have hfun : (fun i => MvPolynomial.eval y
        (MvPolynomial.X i - MvPolynomial.C (p i))) = y - p := by
      funext i
      simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, Pi.sub_apply]
    rw [TrackD.eval_polynomial_substitution, hfun]
  have hgen_b : TrackD.ForGeneralPoint Y (fun y =>
      MvPolynomial.eval y
        (MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (p i)) a) = 0) := by
    apply hgen.mono
    intro y hy h
    rw [heval]
    exact h
  have hall : ∀ y ∈ Y,
      MvPolynomial.eval y
        (MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (p i)) a) = 0 :=
    TrackD.ForGeneralPoint.eval_zero hY _ hgen_b
  have hall_sub : ∀ y ∈ Y, MvPolynomial.eval (y - p) a = 0 := by
    intro y hy
    rw [← heval]
    exact hall y hy
  change a ∈ MvPolynomial.vanishingIdeal ℂ (ProjectiveVariety.nonzeroRepresentatives
    {z | ∃ x ∈ Y.points, ∃ hx : x ≠ p, radialProjection p x hx = z})
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  rintro v ⟨hv, y, hy, hne, hproj⟩
  have hsub : y - p ≠ 0 := sub_ne_zero.mpr hne
  have hmk : Projectivization.mk ℂ v hv = Projectivization.mk ℂ (y - p) hsub := by
    have hrw : radialProjection p y hne = Projectivization.mk ℂ (y - p) hsub := rfl
    rw [hrw] at hproj
    exact hproj.symm
  obtain ⟨c, hc⟩ :=
    (Projectivization.mk_eq_mk_iff' ℂ v (y - p) hv hsub).mp hmk
  rw [MvPolynomial.aeval_eq_eval, ← hc, Bridges.homogeneous_eval_smul _ ha,
    hall_sub y hy, mul_zero]

/-- Transversality makes the original chart differential injective on target tangents. -/
theorem common_radial_chart_tangent_finrank {d : ℕ} (Y : AffineVariety d)
    (i₀ : Fin d) (p y : Point d) (hi : (y - p) i₀ ≠ 0)
    (htrans : y - p ∉ Y.tangentSpace y) :
    Module.finrank ℂ ((Y.tangentSpace y).map
      (TrackD.rationalDifferential (commonRadialNumerator p)
        (commonRadialDenominator i₀ p) y)) =
      Module.finrank ℂ (Y.tangentSpace y) := by
  rw [common_radial_chart_differential]
  have hlam : ((LinearMap.proj i₀ : Point d →ₗ[ℂ] ℂ)) (y - p) ≠ 0 := by
    simpa only [LinearMap.proj_apply] using hi
  have hinj : Function.Injective
      ((TrackD.dirChartDeriv (LinearMap.proj i₀) (y - p)).domRestrict
        (Y.tangentSpace y)) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨v, hv⟩ hz
    change TrackD.dirChartDeriv (LinearMap.proj i₀) (y - p) v = 0 at hz
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (TrackD.dirChartDeriv_kernel_mem_line _ _ _ hlam hz)
    have ha0 : a = 0 := by
      by_contra hn
      apply htrans
      have hu := (Y.tangentSpace y).smul_mem a⁻¹ hv
      simpa only [← ha, smul_smul, inv_mul_cancel₀ hn, one_smul] using hu
    have hv0 : v = 0 := by
      rw [← ha, ha0, zero_smul]
    exact Subtype.ext hv0
  rw [← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj hinj

end
end DistinctDistances.SparseCones
