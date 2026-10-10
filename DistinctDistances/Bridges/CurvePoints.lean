import DistinctDistances.Bridges.CurveInvariants
import DistinctDistances.TrackE.Basic

/-! Evaluation on the complex points of a reduced curve detects its filtered quotient. -/

namespace DistinctDistances.Bridges
noncomputable section

 theorem restrictionRank_points_eq_hilbert {n : ℕ} (Y : AffineVariety n) (D : ℕ) :
    restrictionRank Y.points D = Y.hilbert D := by
  let H := MvPolynomial.restrictTotalDegree (Fin n) ℂ D
  let q : H →ₗ[ℂ] (Poly n ⧸ Y.ideal) :=
    (Ideal.Quotient.mkₐ ℂ Y.ideal).toLinearMap.comp H.subtype
  have hrange : LinearMap.range q = Y.restrictionSpace D := by
    ext y
    change (∃ f : H, q f = y) ↔ ∃ f,
      f ∈ OAI.QuarticPowerFree.totalSpace D ∧
        (Ideal.Quotient.mkₐ ℂ Y.ideal).toLinearMap f = y
    constructor
    · rintro ⟨f,hf⟩
      exact ⟨f.val, OAI.QuarticPowerFree.mem_totalSpace.mpr
        ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp f.property), hf⟩
    · rintro ⟨f,hf,he⟩
      exact ⟨⟨f, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
        (OAI.QuarticPowerFree.mem_totalSpace.mp hf)⟩, he⟩
  have hker : LinearMap.ker (restrictionMap Y.points D) = LinearMap.ker q := by
    ext f
    change (restrictionMap Y.points D f = 0) ↔ Ideal.Quotient.mk Y.ideal f.val = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Y.vanishingIdeal_points]
    constructor
    · intro h x hx
      exact congrFun h ⟨x,hx⟩
    · intro h
      funext x
      exact h x.val x.property
  have he := (restrictionMap Y.points D).finrank_range_add_finrank_ker
  have hq := q.finrank_range_add_finrank_ker
  rw [← hker] at hq
  change Module.finrank ℂ (LinearMap.range (restrictionMap Y.points D)) =
    Module.finrank ℂ (Y.restrictionSpace D)
  rw [← hrange]
  exact Nat.add_right_cancel (he.trans hq.symm)

 theorem hilbert_le_ncard_of_finite {n : ℕ} (Y : AffineVariety n)
    (hfin : Y.points.Finite) (D : ℕ) : Y.hilbert D ≤ Y.points.ncard := by
  letI := hfin.fintype
  rw [← restrictionRank_points_eq_hilbert]
  change Module.finrank ℂ (LinearMap.range (restrictionMap Y.points D)) ≤ _
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one, Set.fintypeCard_eq_ncard] using
    (Submodule.finrank_le (LinearMap.range (restrictionMap Y.points D)))

 theorem curve_points_infinite {n : ℕ} (Y : AffineVariety n)
    (hY : Y.IsIrreducible) (hdim : Y.dimension = 1) : Y.points.Infinite := by
  intro hfin
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp Y.hilbert_eventually
  obtain ⟨t,ht⟩ := exists_nat_gt ((Y.points.ncard : ℚ) - Y.hilbertPolynomial.coeff 0)
  let D := N+t
  have hb : (Y.hilbert D : ℚ) ≤ Y.points.ncard := by
    exact_mod_cast hilbert_le_ncard_of_finite Y hfin D
  have he : Y.hilbertPolynomial = Polynomial.C (Y.hilbertPolynomial.coeff 1) *
      Polynomial.X + Polynomial.C (Y.hilbertPolynomial.coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hdim.le
  have hdeg : 1 ≤ Y.hilbertPolynomial.coeff 1 := by
    have h := Y.one_le_degree hY.ne_top
    change 1 ≤ ((Y.dimension).factorial : ℚ) *
      Y.hilbertPolynomial.coeff Y.dimension at h
    simpa [hdim] using h
  rw [hN D (by omega), he] at hb
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at hb
  have htD : (t : ℚ) ≤ (D : ℚ) := by dsimp [D]; exact_mod_cast Nat.le_add_left t N
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg _
  nlinarith

end
end DistinctDistances.Bridges
