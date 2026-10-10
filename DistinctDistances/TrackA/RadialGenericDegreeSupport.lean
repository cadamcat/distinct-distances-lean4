import DistinctDistances.TrackA.RadialLiteralFiberSupport

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- Scaling polynomial of the original target denominator, without translation. -/
def coneScalingPolynomial {n : ℕ} (v : Point n) (H : Poly n) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (H.totalDegree+1),
    Polynomial.monomial j (MvPolynomial.eval v (MvPolynomial.homogeneousComponent j H))

theorem coneScalingPolynomial_eval {n : ℕ} (v : Point n) (H : Poly n) (t : ℂ) :
    (coneScalingPolynomial v H).eval t = MvPolynomial.eval (t • v) H := by
  unfold coneScalingPolynomial
  conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent H]
  simp only [map_sum, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Bridges.homogeneous_eval_smul _ (MvPolynomial.homogeneousComponent_isHomogeneous j H)]
  ring

theorem coneScalingPolynomial_coeff {n : ℕ} (v : Point n) (H : Poly n) (j : ℕ)
    (hj : j ≤ H.totalDegree) :
    (coneScalingPolynomial v H).coeff j =
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent j H) := by
  simp [coneScalingPolynomial, Polynomial.coeff_monomial, hj]

/-- A proper target denominator has a proper homogeneous component; on
its open every direction has a nonzero representative avoiding the denominator. -/
theorem homogeneous_cone_denominator_open {n : ℕ} (W : ProjectiveVariety n)
    (H : Poly n) (hH : H ∉ W.ideal) :
    ∃ (G : Poly n) (D : ℕ), G.IsHomogeneous D ∧ G ∉ W.ideal ∧
      ∀ v : Point n, MvPolynomial.eval v G ≠ 0 →
        ∃ t : ℂ, t ≠ 0 ∧ MvPolynomial.eval (t • v) H ≠ 0 := by
  obtain ⟨j, hj, hnot⟩ : ∃ j ≤ H.totalDegree,
      MvPolynomial.homogeneousComponent j H ∉ W.ideal := by
    by_contra h
    push_neg at h
    apply hH
    rw [← MvPolynomial.sum_homogeneousComponent H]
    apply Ideal.sum_mem
    intro j hj
    exact h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  refine ⟨MvPolynomial.homogeneousComponent j H, j,
    MvPolynomial.homogeneousComponent_isHomogeneous _ _, hnot, ?_⟩
  intro v hv
  have hQ : coneScalingPolynomial v H ≠ 0 := by
    intro he
    have hc := coneScalingPolynomial_coeff v H j hj
    rw [he, Polynomial.coeff_zero] at hc
    exact hv hc.symm
  have hprod : coneScalingPolynomial v H * Polynomial.X ≠ 0 :=
    mul_ne_zero hQ Polynomial.X_ne_zero
  obtain ⟨t, ht⟩ : ∃ t : ℂ, (coneScalingPolynomial v H * Polynomial.X).eval t ≠ 0 := by
    by_contra h
    push_neg at h
    exact hprod (Polynomial.zero_of_eval_zero _ h)
  rw [Polynomial.eval_mul, Polynomial.eval_X] at ht
  refine ⟨t, (mul_ne_zero_iff.mp ht).2, ?_⟩
  rw [← coneScalingPolynomial_eval]
  exact (mul_ne_zero_iff.mp ht).1

/-- The actual positive-dimensional radial cone argument gives a genuine
homogeneous principal open with positive constant literal radial degree. -/
theorem radial_generic_degree_exists {n l : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hl : 1 ≤ l) (hd : V.dimension = l) (p : Point n)
    (himage : (radialImage p V).dimension = l) :
    ∃ r : ℕ, GenericallyFiniteRadialDegree p V r := by
  have hactual := radial_actual_of_positive_dimension V hV hl hd p
  obtain ⟨H, hH, r, hr, hcount⟩ := radial_generic_cone_fiber_count V hV hd p hactual himage
  obtain ⟨G, D, hGhom, hG, hopen⟩ := homogeneous_cone_denominator_open (radialImage p V) H hH
  refine ⟨r, hr, G, D, hGhom, hG, ?_⟩
  intro z hz hzeval
  obtain ⟨t, ht, hval⟩ := hopen z.rep (by simpa only [MvPolynomial.aeval_eq_eval] using hzeval)
  have hv0 : t • z.rep ≠ 0 := smul_ne_zero ht z.rep_nonzero
  have hzcone : z.rep ∈ (radialImage p V).affineCone.points := by
    apply (ProjectiveVariety.mem_points_mk_iff _ z.rep z.rep_nonzero).mp
    simpa only [Projectivization.mk_rep] using hz
  have hv := cone_smul_mem (radialImage p V) z.rep hzcone t
  have heq : Projectivization.mk ℂ (t • z.rep) hv0 = z := by
    exact ((Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨t, rfl⟩).trans
      (Projectivization.mk_rep z)
  have h := hcount (t • z.rep) hv0 hv (by simpa only [MvPolynomial.aeval_eq_eval] using hval)
  rwa [heq] at h

end
end DistinctDistances.TrackA
