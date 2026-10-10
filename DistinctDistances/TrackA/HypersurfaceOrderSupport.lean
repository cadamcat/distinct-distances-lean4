import DistinctDistances.TrackA.HypersurfaceLocalizationSupport
import DistinctDistances.TrackA.HypersurfacePolynomialSupport
import DistinctDistances.TrackA.Definitions

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical
open Filter

theorem hypersurface_multiplicity_eq_order {n : ℕ} (V : AffineVariety n) (f : Poly n)
    (hf : f ≠ 0) (hV : V.ideal = Ideal.span {f}) (p : Point n) (s : ℕ)
    (hs : ((OAI.PiExponent.WeightedBezout.translationEquiv p f : Poly n) :
      MvPowerSeries (Fin n) ℂ).order = (s : ℕ∞)) :
    V.multiplicity p = (s : ℚ) := by
  obtain ⟨N, hN⟩ := (V.localHilbert_eventually_polynomial p).choose_spec.2
  change ∀ t ≥ N, ∃ a : ℕ, V.localHilbert p t = (a : ℕ∞) ∧
    (V.localHilbertPolynomial p).eval (t : ℚ) = (a : ℚ) at hN
  by_cases hs0 : s = 0
  · subst s
    have heq : V.localHilbertPolynomial p = 0 := by
      apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
      apply eventually_atTop.mpr
      refine ⟨N, ?_⟩
      intro t ht
      obtain ⟨a, ha, hPa⟩ := hN t ht
      have hzero := hypersurface_local_jet_length V f hV p 0 hs t (Nat.zero_le _)
      have ha0 : a = 0 := by
        rw [hzero] at ha
        have hh : (a : ℕ∞) = (0 : ℕ∞) := by
          simpa only [Nat.sub_zero, Nat.sub_self, Nat.cast_zero] using ha.symm
        exact WithTop.coe_inj.mp hh
      rw [hPa, ha0]
      simp
    simp [AffineVariety.multiplicity, AffineVariety.localDimension, heq]
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    let g := OAI.PiExponent.WeightedBezout.translationEquiv p f
    have hg : g ≠ 0 := by
      intro h
      apply hf
      exact (OAI.PiExponent.WeightedBezout.translationEquiv p).injective (by simpa [g] using h)
    have hg' : (g : MvPowerSeries (Fin 0) ℂ) ≠ 0 := by
      intro h
      apply hg
      apply MvPolynomial.coe_injective (Fin 0) ℂ
      simpa only [MvPolynomial.coe_zero] using h
    obtain ⟨d, _, hd⟩ := MvPowerSeries.exists_coeff_ne_zero_and_order
      (MvPowerSeries.ne_zero_iff_order_finite.mp hg')
    have hd0 : d = 0 := Subsingleton.elim _ _
    have hzero : (d.degree : ℕ∞) = 0 := by rw [hd0]; simp
    have hh : (0 : ℕ∞) = s := hzero.symm.trans (hd.trans hs)
    exact hs0 (by exact_mod_cast hh.symm)
  let P := hypersurfaceJetPolynomial n s
  have heq : V.localHilbertPolynomial p = P := by
    apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
    apply eventually_atTop.mpr
    refine ⟨max N s, ?_⟩
    intro t ht
    obtain ⟨a, ha, hPa⟩ := hN t (le_trans (le_max_left _ _) ht)
    have hst : s ≤ t := le_trans (le_max_right _ _) ht
    have hj := hypersurface_local_jet_length V f hV p s hs t hst
    have haeq : a = (t+n).choose n - (t-s+n).choose n := WithTop.coe_inj.mp (ha.symm.trans hj)
    rw [hPa, haeq, hypersurfaceJetPolynomial_eval n s t hn hst]
  have hcoeff : P.coeff (n-1) = (s : ℚ) * ((n-1).factorial : ℚ)⁻¹ :=
    hypersurfaceJetPolynomial_coeff n s
  have hcoeff_ne : P.coeff (n-1) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (by exact_mod_cast hs0) (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (n-1)))
  have hdegree : P.natDegree = n-1 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (hypersurfaceJetPolynomial_degree_le n s) hcoeff_ne
  have hdim : V.localDimension p = n-1 := by
    unfold AffineVariety.localDimension
    rw [heq, hdegree]
  unfold AffineVariety.multiplicity
  rw [hdim, heq, hcoeff]
  field_simp

theorem hypersurface_order_core {n : ℕ} (V : AffineVariety n) (f : Poly n)
    (hf : f ≠ 0) (hV : V.ideal = Ideal.span {f}) (p : Point n) (r : ℕ) :
    OrderAtLeast f p r ↔ (r : ℚ) ≤ V.multiplicity p := by
  let e := OAI.PiExponent.WeightedBezout.translationEquiv p
  let g := e f
  have hg : g ≠ 0 := by
    intro h
    apply hf
    exact e.injective (by simpa [g] using h)
  have hg' : (g : MvPowerSeries (Fin n) ℂ) ≠ 0 := by
    intro h
    apply hg
    apply MvPolynomial.coe_injective (Fin n) ℂ
    simpa only [MvPolynomial.coe_zero] using h
  let s := (g : MvPowerSeries (Fin n) ℂ).order.toNat
  have hs : (g : MvPowerSeries (Fin n) ℂ).order = (s : ℕ∞) :=
    (MvPowerSeries.ne_zero_iff_order_finite.mp hg').symm
  have hmult := hypersurface_multiplicity_eq_order V f hf hV p s hs
  have hp : (pointIdealOver p).map e.toRingHom = MvPolynomial.idealOfVars (Fin n) ℂ :=
    (separator_translation_pointIdeal p).trans (pointIdeal_origin_eq_vars n)
  have hpow : (pointIdealOver p^r).map e.toRingHom = MvPolynomial.idealOfVars (Fin n) ℂ ^ r := by
    rw [Ideal.map_pow e.toRingHom (pointIdealOver p) r, hp]
  change f ∈ pointIdealOver p^r ↔ _
  rw [← Ideal.apply_mem_of_equiv_iff (f := e.toRingEquiv)]
  change e f ∈ (pointIdealOver p^r).map e.toRingHom ↔ _
  rw [hpow, mem_vars_power_iff_series_order]
  change (r : ℕ∞) ≤ (g : MvPowerSeries (Fin n) ℂ).order ↔ _
  rw [hs, hmult]
  norm_cast

end
end DistinctDistances.TrackA
