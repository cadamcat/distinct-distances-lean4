import DistinctDistances.TrackB.ParameterImageSupport

namespace DistinctDistances.TrackB
noncomputable section

theorem aeval_smul_of_isHomogeneous {n D : ℕ} {f : Poly n} (hf : f.IsHomogeneous D) (c : ℂ)
    (x : Point n) : MvPolynomial.aeval (c • x) f = c ^ D * MvPolynomial.aeval x f := by
  have h := GenericFiber.aeval_scale_of_isWeightedHomogeneous (R := ℂ) (w := 1) hf x c
  have hfun : (fun s => c ^ (1 : Fin n → ℕ) s * x s) = c • x := by
    funext s
    simp
  rw [hfun] at h
  exact h

theorem differential_sum {n : ℕ} {ι : Type*} (s : Finset ι) (F : ι → Poly n) (x v : Point n) :
    differential (∑ i ∈ s, F i) x v = ∑ i ∈ s, differential (F i) x v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      simp [differential]
  | @insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has, differential_add, ih]

theorem differential_homogeneous_smul {n : ℕ} (F : Poly n) (d : ℕ) (hhom : F.IsHomogeneous d)
    (x v : Point n) (c : ℂ) (hc : c ≠ 0) (hdiff : differential F (c • x) v = 0) :
    differential F x v = 0 := by
  let P := lineRestriction x v F
  let Q := lineRestriction (c • x) (c • v) F
  have hPQ : Q = Polynomial.C (c ^ d) * P := by
    have hsub : Q - Polynomial.C (c ^ d) * P = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      have hall : {t : ℂ | Polynomial.IsRoot (Q - Polynomial.C (c ^ d) * P) t} = Set.univ := by
        apply Set.eq_univ_of_forall
        intro t
        change Polynomial.eval t (Q - Polynomial.C (c ^ d) * P) = 0
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
        rw [eval_lineRestriction, eval_lineRestriction]
        have hsmul : c • x + t • (c • v) = c • (x + t • v) := by
          calc
            c • x + t • (c • v) = c • x + (t * c) • v := by rw [smul_smul]
            _ = c • x + (c * t) • v := by rw [mul_comm t c]
            _ = c • x + c • (t • v) := by rw [smul_smul]
            _ = c • (x + t • v) := (smul_add c x (t • v)).symm
        rw [hsmul, aeval_smul_of_isHomogeneous hhom]
        ring
      rw [hall]
      exact Set.infinite_univ
    exact sub_eq_zero.mp hsub
  have hQcoeff : Q.coeff 1 = (Polynomial.C (c ^ d) * P).coeff 1 := by rw [hPQ]
  rw [Polynomial.coeff_C_mul, coeff_one_lineRestriction, coeff_one_lineRestriction] at hQcoeff
  have hQlin : differential F (c • x) (c • v) = c * differential F (c • x) v := by
    simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul, Pi.smul_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hQlin, hdiff, mul_zero] at hQcoeff
  have hpow : c ^ d ≠ 0 := pow_ne_zero d hc
  exact (mul_eq_zero.mp hQcoeff.symm).resolve_left hpow

/-- kernels of differentials of a homogeneous ideal are unchanged
when their base point is multiplied by a nonzero scalar. -/
theorem projective_cone_tangent_scaling {n : ℕ} (Y : ProjectiveVariety n)
    (x : Point n) (c : ℂ) (hc : c ≠ 0) :
    Y.affineCone.tangentSpace (c • x) = Y.affineCone.tangentSpace x := by
  have hle : ∀ (y : Point n) (a : ℂ) (ha : a ≠ 0),
      Y.affineCone.tangentSpace (a • y) ≤ Y.affineCone.tangentSpace y := by
    intro y a ha v hv
    simp only [AffineVariety.tangentSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hv ⊢
    intro f
    have hfsum : differential f.val y v =
        ∑ d ∈ Finset.range (f.val.totalDegree + 1),
          differential (MvPolynomial.homogeneousComponent d f.val) y v := by
      conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent f.val]
      exact differential_sum _ _ y v
    rw [hfsum]
    apply Finset.sum_eq_zero
    intro d hd
    have hFmem : MvPolynomial.homogeneousComponent d f.val ∈ Y.ideal :=
      MvPolynomial.homogeneousComponent_mem_of_mem Y.isHomogeneous f.property d
    have hdiff_zero := hv ⟨MvPolynomial.homogeneousComponent d f.val, hFmem⟩
    exact differential_homogeneous_smul (MvPolynomial.homogeneousComponent d f.val) d
      (MvPolynomial.homogeneousComponent_isHomogeneous d f.val) y v a ha hdiff_zero
  apply le_antisymm (hle x c hc)
  have hinv : c⁻¹ ≠ 0 := inv_ne_zero hc
  have hle_inv := hle (c • x) c⁻¹ hinv
  rw [inv_smul_smul₀ hc] at hle_inv
  exact hle_inv

/-- a positive-degree homogeneous principal open excludes the origin;
representative scaling transfers the null tangent statement to cone points. -/
theorem projective_null_tangent_open {e D : ℕ} (Y : ProjectiveVariety (e + e))
    (g : Poly (e + e)) (hD : 0 < D) (hhom : g.IsHomogeneous D)
    (hnull : ∀ p ∈ Y.points, MvPolynomial.aeval p.rep g ≠ 0 →
      ∀ v ∈ Y.affineCone.tangentSpace p.rep, parameterValue v = 0) :
    ∀ x ∈ Y.affineCone.points, MvPolynomial.aeval x g ≠ 0 →
      ∀ v ∈ Y.affineCone.tangentSpace x, parameterValue v = 0 := by
  intro x hxcone hxg v hv
  have hxne : x ≠ 0 := by
    rintro rfl
    have hzero : MvPolynomial.aeval (0 : Point (e + e)) g = 0 := by
      have hsmul := aeval_smul_of_isHomogeneous hhom (0 : ℂ) (0 : Point (e + e))
      simp only [zero_smul, zero_pow hD.ne', zero_mul] at hsmul
      exact hsmul
    exact hxg hzero
  let p : ProjectivePoint (e + e) := Projectivization.mk ℂ x hxne
  have hpY : p ∈ Y.points := (Y.mem_points_mk_iff x hxne).mpr hxcone
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hxne
  have hrep : p.rep = (u : ℂ) • x := by simpa only [Units.smul_def] using hu.symm
  have hu0 : (u : ℂ) ≠ 0 := Units.ne_zero u
  have hgrep : MvPolynomial.aeval p.rep g ≠ 0 := by
    rw [hrep, aeval_smul_of_isHomogeneous hhom]
    exact mul_ne_zero (pow_ne_zero D hu0) hxg
  have hnullp := hnull p hpY hgrep
  have hscale := projective_cone_tangent_scaling Y x (u : ℂ) hu0
  rw [← hrep] at hscale
  rw [← hscale] at hv
  exact hnullp v hv

/-- projectivizing a nonzero linear space preserves its affine
vanishing ideal. The nonzero hypothesis excludes the empty projective space. -/
theorem linearProjectivePlane_cone_ideal {n : ℕ} (L : Submodule ℂ (Point n))
    (hL : ∃ x ∈ L, x ≠ 0) :
    (linearProjectivePlane L).ideal = MvPolynomial.vanishingIdeal ℂ (L : Set (Point n)) := by
  classical
  let T : Set (ProjectivePoint n) := {p | ∃ x ∈ L, ∃ hx : x ≠ 0, Projectivization.mk ℂ x hx = p}
  have hTnonempty : T.Nonempty := by
    obtain ⟨x, hxL, hx0⟩ := hL
    exact ⟨Projectivization.mk ℂ x hx0, ⟨x, hxL, hx0, rfl⟩⟩
  change (ProjectiveVariety.closure T).ideal = MvPolynomial.vanishingIdeal ℂ (L : Set (Point n))
  apply le_antisymm
  · intro f hf
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]
      have h0cone := zero_mem_projective_cone T hTnonempty
      exact h0cone f hf
    · have hrep : x ∈ ProjectiveVariety.nonzeroRepresentatives T := by
        refine ⟨hx0, ?_⟩
        exact ⟨x, hx, hx0, rfl⟩
      exact (MvPolynomial.mem_vanishingIdeal_iff.mp hf) x hrep
  · intro f hf
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro v ⟨hv0, ⟨x, hxL, hx0, hmk⟩⟩
    obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff ℂ v x hv0 hx0).mp hmk.symm
    have hvL : v ∈ L := by
      rw [← hu]
      change (u : ℂ) • x ∈ L
      exact Submodule.smul_mem L (u : ℂ) hxL
    exact (MvPolynomial.mem_vanishingIdeal_iff.mp hf) v hvL

end
end DistinctDistances.TrackB
