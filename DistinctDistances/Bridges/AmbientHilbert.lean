import DistinctDistances.Bridges.DegreeOneCurve

/-! Ambient-dimension endpoint checks used before projecting an affine curve. -/

namespace DistinctDistances.Bridges
open scoped Classical
noncomputable section

 theorem affine_dimension_le {n : ℕ} (Y : AffineVariety n) : Y.dimension ≤ n :=
  (OAI.QuarticPowerFree.coordinate_hilbert_eventually_polynomial Y.ideal).choose_spec.1

 theorem hilbert_le_totalSpace {n : ℕ} (Y : AffineVariety n) (D : ℕ) :
    Y.hilbert D ≤ (D+n).choose n := by
  let H := OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) D
  letI := OAI.QuarticPowerFree.totalSpace_finite (n := n) (K := ℂ) D
  change Module.finrank ℂ (H.map (Ideal.Quotient.mkₐ ℂ Y.ideal).toLinearMap) ≤ _
  exact (Submodule.finrank_map_le _ _).trans_eq (OAI.QuarticPowerFree.totalSpace_finrank D)

 theorem affine_whole_dimension (n : ℕ) : (AffineVariety.whole : AffineVariety n).dimension = n := by
  have hp : (AffineVariety.whole : AffineVariety n).hilbertPolynomial =
      Polynomial.preHilbertPoly ℚ n 0 := by
    apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
    filter_upwards [(AffineVariety.whole : AffineVariety n).hilbert_eventually] with D hD
    rw [← hD, Polynomial.preHilbertPoly_eq_choose_add_sub ℚ n (Nat.zero_le (D+n))]
    simp only [Nat.sub_zero]
    congr 1
    let H := OAI.QuarticPowerFree.totalSpace (σ := Fin n) (K := ℂ) D
    letI := OAI.QuarticPowerFree.totalSpace_finite (n := n) (K := ℂ) D
    let q : H →ₗ[ℂ] (Poly n ⧸ (⊥ : Ideal (Poly n))) :=
      (Ideal.Quotient.mkₐ ℂ ⊥).toLinearMap.comp H.subtype
    have hker : LinearMap.ker q = ⊥ := by
      ext f
      change Ideal.Quotient.mk ⊥ f.val = 0 ↔ f = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      simp
    have hrange : LinearMap.range q = H.map (Ideal.Quotient.mkₐ ℂ ⊥).toLinearMap := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have h := q.finrank_range_add_finrank_ker
    rw [hker, finrank_bot, add_zero, hrange] at h
    have hi : (AffineVariety.whole : AffineVariety n).ideal = ⊥ :=
      Ideal.radical_bot_of_isReduced
    change Module.finrank ℂ ((OAI.QuarticPowerFree.totalSpace D).map
      (Ideal.Quotient.mkₐ ℂ (AffineVariety.whole : AffineVariety n).ideal).toLinearMap) = _
    rw [hi]
    exact h.trans (OAI.QuarticPowerFree.totalSpace_finrank D)
  change (AffineVariety.whole : AffineVariety n).hilbertPolynomial.natDegree = n
  rw [hp, Polynomial.natDegree_preHilbertPoly]

 theorem curve_ideal_ne_bot {n : ℕ} (Y : AffineVariety n)
    (hdim : Y.dimension = 1) (hn : 2 ≤ n) : Y.ideal ≠ ⊥ := by
  intro hi
  have he : Y = AffineVariety.whole := by
    apply AffineVariety.ext
    simpa [AffineVariety.whole, AffineVariety.ofIdeal, Ideal.radical_bot_of_isReduced] using hi
  rw [he, affine_whole_dimension] at hdim
  omega

 theorem curve_line_of_ambient_le_one {n : ℕ} (Y : AffineVariety n)
    (hY : Y.IsIrreducible) (hdim : Y.dimension = 1) (hn : n ≤ 1) : TrackD.IsLine Y := by
  have hn1 : n = 1 := by have h := affine_dimension_le Y; omega
  have hle : Y.degree ≤ 1 := by
    have heval : ∀ᶠ D : ℕ in Filter.atTop,
        Y.hilbertPolynomial.eval (D : ℚ) ≤ (Polynomial.X+1 : Polynomial ℚ).eval (D : ℚ) := by
      filter_upwards [Y.hilbert_eventually] with D hD
      rw [← hD]
      have h := hilbert_le_totalSpace Y D
      simp only [hn1, Nat.choose_one_right] at h
      simpa using (show (Y.hilbert D : ℚ) ≤ (D+1 : ℕ) by exact_mod_cast h)
    have h := OAI.QuarticPowerFree.coeff_le_of_eventually_nat_eval_le
      Y.hilbertPolynomial (Polynomial.X+1) 1 hdim.le (by simp) heval
    change ((Y.dimension).factorial : ℚ) * Y.hilbertPolynomial.coeff Y.dimension ≤ 1
    simpa [hdim, Polynomial.coeff_one] using h
  exact degree_one_curve_line Y hY hdim (le_antisymm hle (Y.one_le_degree hY.ne_top))

end
end DistinctDistances.Bridges
