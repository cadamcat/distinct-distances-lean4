import DistinctDistances.TrackA.LocalHilbertGrowthSupport

namespace DistinctDistances.TrackA
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical
open IsLocalRing

theorem carrierLocalRing_noetherian {n : ℕ} (V : AffineVariety n) (p : Point n) :
    IsNoetherianRing (CarrierLocalRing V p) := by
  infer_instance

/-- The original carrier point ideal is maximal at an original carrier point. -/
theorem carrierMaximalIdeal_isMaximal {n : ℕ} (V : AffineVariety n)
    (p : Point n) (hp : p ∈ V.points) : (carrierMaximalIdeal V p).IsMaximal := by
  have hVP : V.ideal ≤ pointIdeal p := by
    intro f hf
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff p f).mpr (hp f hf)
  have hpoint : (pointIdeal p).map (algebraMap (Poly n) (PointLocalRing p)) =
      maximalIdeal (PointLocalRing p) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal (pointIdeal p) (PointLocalRing p)
  have hlocal : localizedIdeal V.ideal p ≤ maximalIdeal (PointLocalRing p) := by
    have h := Ideal.map_mono (f := algebraMap (Poly n) (PointLocalRing p)) hVP
    rwa [hpoint] at h
  unfold carrierMaximalIdeal
  rw [← Ideal.map_map, hpoint]
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le
    (Ideal.Quotient.mk_surjective (I := localizedIdeal V.ideal p))
  simpa using hlocal

/-- Outside the original carrier, every original local Hilbert value is zero. -/
theorem localHilbert_zero_off {n : ℕ} (V : AffineVariety n)
    (p : Point n) (hp : p ∉ V.points) (t : ℕ) : V.localHilbert p t = 0 := by
  have hnot : ¬ ∀ f ∈ V.ideal, MvPolynomial.aeval p f = 0 := hp
  push Not at hnot
  obtain ⟨f, hf, hfp⟩ := hnot
  have hfnot : f ∉ pointIdeal p := by
    intro h
    exact hfp ((MvPolynomial.mem_vanishingIdeal_singleton_iff p f).mp h)
  have htop : localizedIdeal (V.ideal ⊔ pointIdeal p^(t+1)) p = ⊤ := by
    exact Ideal.eq_top_of_isUnit_mem _
      (Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hf))
      ((IsLocalization.AtPrime.isUnit_to_map_iff (PointLocalRing p) (pointIdeal p) f).mpr hfnot)
  unfold AffineVariety.localHilbert localLengthAt
  rw [htop]
  simp

/-- The actual original carrier-power colengths have exact finite natural
values and the same ambient point-jet bound. -/
theorem carrier_power_length_finite {n : ℕ} (V : AffineVariety n) (p : Point n)
    (t : ℕ) : ∃ a : ℕ,
      Module.length (CarrierLocalRing V p)
        (CarrierLocalRing V p ⧸ carrierMaximalIdeal V p^(t+1)) = (a : ℕ∞) ∧
      a ≤ (t+n).choose n := by
  obtain ⟨a, ha, hbound⟩ := localHilbert_finite_value V p t
  rw [curve_localHilbert_carrier] at ha
  exact ⟨a, ha, hbound⟩

end
end DistinctDistances.TrackA
