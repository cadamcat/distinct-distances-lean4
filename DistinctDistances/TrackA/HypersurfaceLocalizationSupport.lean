import DistinctDistances.TrackA.HypersurfaceLengthSupport

namespace DistinctDistances.TrackA
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
open IsLocalRing

def pointTruncationCutEquiv {n : ℕ} (p : Point n) (t : ℕ) (f : Poly n) :
    (Poly n ⧸ pointIdeal p^t ⊔ Ideal.span {f}) ≃ₐ[ℂ]
      (PointLocalRing p ⧸ maximalIdeal (PointLocalRing p)^t ⊔
        Ideal.span {algebraMap (Poly n) (PointLocalRing p) f}) := by
  let I := pointIdeal p^t
  let J := maximalIdeal (PointLocalRing p)^t
  let e : (Poly n ⧸ I) ≃ₐ[ℂ] (PointLocalRing p ⧸ J) :=
    (IsLocalization.AtPrime.equivQuotMaximalIdealPow (pointIdeal p) (PointLocalRing p) t).restrictScalars ℂ
  letI : CommRing (PointLocalRing p ⧸ J) :=
    { __ := (inferInstance : Ring (PointLocalRing p ⧸ J))
      mul_comm := fun a b => mul_comm a b }
  let a := Ideal.Quotient.mk I f
  let b := Ideal.Quotient.mk J (algebraMap (Poly n) (PointLocalRing p) f)
  have hab : e a = b := rfl
  let e₁ : ((Poly n ⧸ I) ⧸ Ideal.span {a}) ≃ₐ[ℂ]
      (Poly n ⧸ I ⊔ Ideal.span {f}) := by
    have hm : (Ideal.span {f}).map (Ideal.Quotient.mkₐ ℂ I) = Ideal.span {a} := by
      change (Ideal.span {f}).map (Ideal.Quotient.mk I) = _
      rw [Ideal.map_span, Set.image_singleton]
    exact (Ideal.quotientEquivAlgOfEq ℂ hm.symm).trans
      (DoubleQuot.quotQuotEquivQuotSupₐ ℂ I (Ideal.span {f}))
  let e₂ : ((PointLocalRing p ⧸ J) ⧸ Ideal.span {b}) ≃ₐ[ℂ]
      (PointLocalRing p ⧸ J ⊔ Ideal.span {algebraMap (Poly n) (PointLocalRing p) f}) := by
    have hm : (Ideal.span {algebraMap (Poly n) (PointLocalRing p) f}).map
        (Ideal.Quotient.mkₐ ℂ J) = Ideal.span {b} := by
      change (Ideal.span {algebraMap (Poly n) (PointLocalRing p) f}).map
        (Ideal.Quotient.mk J) = _
      rw [Ideal.map_span, Set.image_singleton]
    exact (Ideal.quotientEquivAlgOfEq ℂ hm.symm).trans
      (DoubleQuot.quotQuotEquivQuotSupₐ ℂ J
        (Ideal.span {algebraMap (Poly n) (PointLocalRing p) f}))
  let e₃ : ((Poly n ⧸ I) ⧸ Ideal.span {a}) ≃ₐ[ℂ]
      ((PointLocalRing p ⧸ J) ⧸ Ideal.span {b}) :=
    Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {b}) e (by
      change Ideal.span {b} = (Ideal.span {a}).map e.toRingHom
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {b} = Ideal.span {e a}
      rw [hab])
  exact e₁.symm.trans (e₃.trans e₂)

def pointTranslatedCutEquiv {n : ℕ} (p : Point n) (t : ℕ) (f : Poly n) :
    (Poly n ⧸ pointIdeal p^t ⊔ Ideal.span {f}) ≃ₐ[ℂ]
      (Poly n ⧸ MvPolynomial.idealOfVars (Fin n) ℂ ^ t ⊔
        Ideal.span {OAI.PiExponent.WeightedBezout.translationEquiv p f}) := by
  let e := OAI.PiExponent.WeightedBezout.translationEquiv p
  have hp : (pointIdeal p).map e.toRingHom = MvPolynomial.idealOfVars (Fin n) ℂ := by
    have hh := separator_translation_pointIdeal p
    change (pointIdeal p).map e.toRingHom = pointIdeal (0 : Point n) at hh
    exact hh.trans (pointIdeal_origin_eq_vars n)
  exact Ideal.quotientEquivAlg _ _ e (by
    change MvPolynomial.idealOfVars (Fin n) ℂ ^ t ⊔ Ideal.span {e f} =
      (pointIdeal p^t ⊔ Ideal.span {f}).map e.toRingHom
    rw [Ideal.map_sup, Ideal.map_pow e.toRingHom (pointIdeal p) t, hp,
      Ideal.map_span, Set.image_singleton]
    rfl)

theorem hypersurface_local_jet_length {n : ℕ} (V : AffineVariety n) (f : Poly n)
    (hV : V.ideal = Ideal.span {f}) (p : Point n) (s : ℕ)
    (hs : ((OAI.PiExponent.WeightedBezout.translationEquiv p f : Poly n) :
      MvPowerSeries (Fin n) ℂ).order = (s : ℕ∞)) (t : ℕ) (hst : s ≤ t) :
    V.localHilbert p t = ((t+n).choose n - (t-s+n).choose n : ℕ) := by
  let e := pointTruncationCutEquiv p (t+1) f
  let e₀ := pointTranslatedCutEquiv p (t+1) f
  letI : Module.Finite ℂ (Poly n ⧸ pointIdeal p^(t+1) ⊔ Ideal.span {f}) :=
    e₀.toLinearEquiv.symm.finiteDimensional
  letI : Module.Finite ℂ
      (PointLocalRing p ⧸ maximalIdeal (PointLocalRing p)^(t+1) ⊔
        Ideal.span {algebraMap (Poly n) (PointLocalRing p) f}) :=
    e.toLinearEquiv.finiteDimensional
  unfold AffineVariety.localHilbert localLengthAt localizedIdeal
  rw [hV, Ideal.map_sup, Ideal.map_span, Set.image_singleton,
    Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal, sup_comm,
    point_local_length_eq_complex_length p, Module.length_eq_finrank,
    ← e.toLinearEquiv.finrank_eq, e₀.toLinearEquiv.finrank_eq,
    hypersurface_origin_jet_length _ s hs t hst]

end
end DistinctDistances.TrackA
