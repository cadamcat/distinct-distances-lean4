import DistinctDistances.TrackA.LocalGermSupport
import DistinctDistances.TrackA.RegularityJetSupport
import DistinctDistances.TrackA.LocalPolynomialComparisonSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

theorem differential_mul_apply {n : ℕ} (f g : Poly n) (x v : Point n) :
    differential (f*g) x v = MvPolynomial.eval x f * differential g x v +
      MvPolynomial.eval x g * differential f x v := by
  have hd (p : Poly n) : differential p x v = fieldDirectionalDerivative x v p := by
    simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, fieldDirectionalDerivative_apply, MvPolynomial.aeval_eq_eval,
      smul_eq_mul, mul_comm]
  rw [hd, fieldDirectionalDerivative_mul, ← hd, ← hd]

/-- Clearing a nonvanishing denominator transports the derivative
constraints of the actual localized ideals. -/
theorem tangentSpace_le_of_localizedIdeal_le {n : ℕ} (V W : AffineVariety n)
    (x : Point n) (hxV : x ∈ V.points)
    (h : localizedIdeal V.ideal x ≤ localizedIdeal W.ideal x) :
    W.tangentSpace x ≤ V.tangentSpace x := by
  intro v hv
  change v ∈ ⨅ f : W.ideal, LinearMap.ker (differential f.val x) at hv
  rw [Submodule.mem_iInf] at hv
  change v ∈ ⨅ f : V.ideal, LinearMap.ker (differential f.val x)
  rw [Submodule.mem_iInf]
  intro f
  rw [LinearMap.mem_ker]
  obtain ⟨g, hg, hgf⟩ := localizedIdeal_membership_denominator W.ideal x f.val
    (h (Ideal.mem_map_of_mem _ f.property))
  have hfzero : MvPolynomial.eval x f.val = 0 := by
    simpa only [MvPolynomial.aeval_eq_eval] using hxV f.val f.property
  have hzero : differential (g*f.val) x v = 0 := LinearMap.mem_ker.mp (hv ⟨g*f.val, hgf⟩)
  rw [differential_mul_apply, hfzero, zero_mul, add_zero] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left hg

theorem tangentSpace_eq_of_localizedIdeal_eq {n : ℕ} (V W : AffineVariety n)
    (x : Point n) (hxV : x ∈ V.points) (hxW : x ∈ W.points)
    (h : localizedIdeal V.ideal x = localizedIdeal W.ideal x) :
    V.tangentSpace x = W.tangentSpace x :=
  le_antisymm (tangentSpace_le_of_localizedIdeal_le W V x hxW h.symm.le)
    (tangentSpace_le_of_localizedIdeal_le V W x hxV h.le)

/-- The original point-power quotients agree when the carrier ideals
agree in the actual ambient localization. -/
theorem localHilbert_eq_of_localizedIdeal_eq {n : ℕ} (V W : AffineVariety n)
    (x : Point n) (h : localizedIdeal V.ideal x = localizedIdeal W.ideal x) (t : ℕ) :
    V.localHilbert x t = W.localHilbert x t := by
  change V.ideal.map (algebraMap (Poly n) (PointLocalRing x)) =
    W.ideal.map (algebraMap (Poly n) (PointLocalRing x)) at h
  have hsum : localizedIdeal (V.ideal ⊔ pointIdeal x^(t+1)) x =
      localizedIdeal (W.ideal ⊔ pointIdeal x^(t+1)) x := by
    unfold localizedIdeal
    rw [Ideal.map_sup, Ideal.map_sup, h]
  exact congrArg (fun I : Ideal (PointLocalRing x) =>
    Module.length (PointLocalRing x) (PointLocalRing x ⧸ I)) hsum

theorem localDimension_eq_of_localizedIdeal_eq {n : ℕ} (V W : AffineVariety n)
    (x : Point n) (h : localizedIdeal V.ideal x = localizedIdeal W.ideal x) :
    V.localDimension x = W.localDimension x := by
  have hP := localHilbertPolynomial_eq_of_eventually V x W x
    (Filter.Eventually.of_forall (localHilbert_eq_of_localizedIdeal_eq V W x h))
  exact congrArg Polynomial.natDegree hP

end
end DistinctDistances.TrackA
