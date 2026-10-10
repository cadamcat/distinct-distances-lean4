import DistinctDistances.Foundations.Local
import DistinctDistances.TrackE.MReqAux

namespace DistinctDistances.LocalMultiplicityAux
noncomputable section
open scoped Classical

/-- The ambient point-power quotient has the monomials of degree at most `t`
as a basis, including in dimension zero. -/
theorem whole_localHilbert {n : ℕ} (p : Point n) (t : ℕ) :
    (AffineVariety.whole (n := n)).localHilbert p t = ((t+n).choose n : ℕ∞) := by
  have hwhole : (AffineVariety.whole (n := n)).ideal = ⊥ :=
    Ideal.radical_bot_of_isReduced
  unfold AffineVariety.localHilbert localLengthAt localizedIdeal
  rw [hwhole, bot_sup_eq, Ideal.map_pow,
    IsLocalization.AtPrime.map_eq_maximalIdeal, TrackA.point_power_length]

/-- The cumulative affine-space Hilbert polynomial is the binomial polynomial. -/
theorem whole_localHilbertPolynomial {n : ℕ} (p : Point n) :
    (AffineVariety.whole (n := n)).localHilbertPolynomial p =
      Polynomial.preHilbertPoly ℚ n 0 := by
  apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
  filter_upwards [TrackA.localHilbertPolynomial_eventually AffineVariety.whole p] with t ht
  rw [ht, whole_localHilbert, ENat.toNat_natCast,
    Polynomial.preHilbertPoly_eq_choose_add_sub ℚ n (Nat.zero_le _), Nat.sub_zero]

/-- The factorial-normalized leading coefficient of affine space is one. -/
theorem whole_multiplicity_one {n : ℕ} (p : Point n) :
    (AffineVariety.whole (n := n)).multiplicity p = 1 := by
  simp only [AffineVariety.multiplicity, AffineVariety.localDimension,
    whole_localHilbertPolynomial, Polynomial.natDegree_preHilbertPoly,
    Polynomial.coeff_preHilbertPoly_self]
  exact mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n)

/-- Smoothness supplies a full-rank Jacobian minor. Its original localized
ideal has the free affine-space Hilbert function, so its multiplicity is one. -/
theorem smooth_multiplicity_one {n : ℕ} (X : AffineVariety n)
    (hX : X.IsIrreducible) (p : Point n) (hp : X.IsSmoothAt p) :
    X.multiplicity p = 1 := by
  obtain ⟨g, hg, hker⟩ := TrackD.tangent_square_equations X p
  let M : Matrix (Fin n) (Fin n) ℂ :=
    fun i j => MvPolynomial.eval p (MvPolynomial.pderiv j (g i))
  have hkerM : LinearMap.ker M.mulVecLin = X.tangentSpace p := hker
  have hfin : Module.finrank ℂ (X.tangentSpace p) = X.dimension :=
    hp.2.trans (X.localDimension_eq_dimension p hX hp.1)
  have hkle : X.dimension ≤ n := TrackD.dimension_le_ambient X hX
  have hrank : M.rank = n - X.dimension := by
    have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [hkerM, hfin] at h
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    change Module.finrank ℂ (LinearMap.range M.mulVecLin) = _
    omega
  obtain ⟨rows, cols, hdet⟩ := MReqAux.exists_nonsingular_submatrix_of_rank
    M (n - X.dimension) hrank
  let f : Fin (n - X.dimension) → Poly n := fun i => g (rows i)
  have hf : ∀ i, f i ∈ X.ideal := fun i => hg (rows i)
  have hzero : ∀ i, MvPolynomial.eval p (f i) = 0 := by
    intro i
    simpa only [MvPolynomial.aeval_eq_eval] using hp.1 (f i) (hf i)
  have hdet' : Matrix.det (fun i j => MvPolynomial.eval p
      (MvPolynomial.pderiv (cols j) (f i))) ≠ 0 := hdet
  let W := TrackA.jacobianContractedVariety p f cols hzero hdet'
  have hlocal : localizedIdeal X.ideal p = localizedIdeal W.ideal p := by
    calc
      localizedIdeal X.ideal p = localizedIdeal (Ideal.span (Set.range f)) p :=
        TrackA.request_irreducible_local_jacobian_ideal X.dimension hkle X hX rfl
          p hp.1 f cols hf hdet'
      _ = localizedIdeal W.ideal p := (TrackA.jacobianContractedIdeal_localized p f).symm
  calc
    X.multiplicity p = W.multiplicity p :=
      TrackA.multiplicity_eq_of_localHilbert_eq X p W p
        (TrackA.localHilbert_eq_of_localizedIdeal_eq X W p hlocal)
    _ = (AffineVariety.whole (n := X.dimension)).multiplicity (0 : Point X.dimension) :=
      TrackA.multiplicity_eq_of_localHilbert_eq W p AffineVariety.whole 0
        (TrackA.jacobianContractedVariety_localHilbert hkle p f cols hzero hdet')
    _ = 1 := whole_multiplicity_one _

end
end DistinctDistances.LocalMultiplicityAux
