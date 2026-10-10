import DistinctDistances.TrackA.HypersurfaceJetsSupport
import DistinctDistances.TrackA.CurveLengthSupport

namespace DistinctDistances.TrackA
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical
open IsLocalRing

/-- Translate the original point-power quotient in any original dimension. -/
def pointPowerQuotientEquiv {n : ℕ} (p : Point n) (t : ℕ) :
    (Poly n ⧸ pointIdeal p ^ t) ≃ₐ[ℂ]
      (Poly n ⧸ MvPolynomial.idealOfVars (Fin n) ℂ ^ t) := by
  let e := OAI.PiExponent.WeightedBezout.translationEquiv p
  have hp : (pointIdeal p).map e.toRingHom = MvPolynomial.idealOfVars (Fin n) ℂ := by
    have h := separator_translation_pointIdeal p
    change (pointIdeal p).map e.toRingHom = pointIdeal (0 : Point n) at h
    exact h.trans (pointIdeal_origin_eq_vars n)
  have hpow : (pointIdeal p^t).map e.toRingHom =
      MvPolynomial.idealOfVars (Fin n) ℂ ^ t := by
    rw [Ideal.map_pow e.toRingHom (pointIdeal p) t, hp]
  exact Ideal.quotientEquivAlg _ _ e hpow.symm

theorem point_power_length {n : ℕ} (p : Point n) (t : ℕ) :
    Module.length (PointLocalRing p)
      (PointLocalRing p ⧸ maximalIdeal (PointLocalRing p)^(t+1)) =
        ((t+n).choose n : ℕ∞) := by
  let e := (IsLocalization.AtPrime.equivQuotMaximalIdealPow
    (pointIdeal p) (PointLocalRing p) (t+1)).restrictScalars ℂ
  let e₀ := pointPowerQuotientEquiv p (t+1)
  letI : Module.Finite ℂ (Poly n ⧸ pointIdeal p^(t+1)) :=
    e₀.toLinearEquiv.symm.finiteDimensional
  letI : Module.Finite ℂ (PointLocalRing p ⧸ maximalIdeal (PointLocalRing p)^(t+1)) :=
    e.toLinearEquiv.finiteDimensional
  rw [point_local_length_eq_complex_length p, Module.length_eq_finrank,
    ← e.toLinearEquiv.finrank_eq, e₀.toLinearEquiv.finrank_eq, point_jet_quotient_finrank]

/-- Original localized quotient lengths decrease with the original ideal. -/
theorem localLengthAt_antitone {n : ℕ} (I J : Ideal (Poly n)) (p : Point n)
    (hIJ : I ≤ J) : localLengthAt J p ≤ localLengthAt I p := by
  let R := PointLocalRing p
  let h := Ideal.map_mono (f := algebraMap (Poly n) R) hIJ
  let π := Ideal.Quotient.factorₐ R h
  apply Module.length_le_of_surjective π.toLinearMap
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

theorem localHilbert_le_point_jets {n : ℕ} (V : AffineVariety n) (p : Point n)
    (t : ℕ) : V.localHilbert p t ≤ ((t+n).choose n : ℕ∞) := by
  have h := localLengthAt_antitone (pointIdeal p^(t+1))
    (V.ideal ⊔ pointIdeal p^(t+1)) p le_sup_right
  change V.localHilbert p t ≤ _ at h
  unfold localLengthAt localizedIdeal at h
  rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal, point_power_length] at h
  exact h

/-- Every original local Hilbert value is finite and retains its exact
natural value, including points off the original carrier. -/
theorem localHilbert_finite_value {n : ℕ} (V : AffineVariety n) (p : Point n)
    (t : ℕ) : ∃ a : ℕ, V.localHilbert p t = (a : ℕ∞) ∧ a ≤ (t+n).choose n := by
  have h := localHilbert_le_point_jets V p t
  have hne : V.localHilbert p t ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) h
  refine ⟨(V.localHilbert p t).toNat, ?_, ?_⟩
  · exact (ENat.natCast_toNat hne).symm
  · have hc : ((V.localHilbert p t).toNat : ℕ∞) ≤ ((t+n).choose n : ℕ∞) := by
      rwa [ENat.natCast_toNat hne]
    exact_mod_cast hc

end
end DistinctDistances.TrackA
