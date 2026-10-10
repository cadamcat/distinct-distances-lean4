import DistinctDistances.TrackA.FormalJacobianLengthSupport
import DistinctDistances.TrackA.LocalGermSupport

namespace DistinctDistances.TrackA
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical
open IsLocalRing
open OAI.BoundaryOnly.FormalObstruction.FormalCorrection

/-- Actual original maximal-ideal-power quotients of the selected equations
have the lengths of the power series ring on the literal free complement. -/
theorem localizedJacobianSpan_power_length {n q : ℕ} (x : Point n)
    (f : Fin q → Poly n) (cols : Fin q ↪ Fin n)
    (hzero : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hdet : Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (cols j) (f i))) ≠ 0) (r : ℕ) :
    Module.length ℂ (PointLocalRing x ⧸
      localizedIdeal (Ideal.span (Set.range f)) x ⊔ maximalIdeal (PointLocalRing x)^r) =
    Module.length ℂ (MvPowerSeries (↥((Set.range cols)ᶜ : Set (Fin n))) ℂ ⧸
      maximalIdeal (MvPowerSeries (↥((Set.range cols)ᶜ : Set (Fin n))) ℂ)^r) := by
  let α := ↥((Set.range cols)ᶜ : Set (Fin n))
  let e : α ⊕ Fin q ≃ Fin n := jacobianCoordinateEquiv cols
  let F : Fin q → MvPolynomial (α ⊕ Fin q) ℂ := fun i => jacobianCenteredEquiv x e (f i)
  have hF : ∀ i, (F i).coeff 0 = 0 := fun i =>
    (jacobianCenteredEquiv_constant x e (f i)).trans (hzero i)
  have hJ : internalJacobian F = fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (cols j) (f i)) := by
    ext i j
    exact jacobianCenteredEquiv_linear x e (f i) (Sum.inr j)
  have hu : IsUnit (internalJacobian F).det := by
    rw [hJ]
    exact isUnit_iff_ne_zero.mpr hdet
  let E : AffineEtaleChart ℂ (α ⊕ Fin q) := .base
  let J := (Ideal.span (Set.range F)).map (algebraMap (MvPolynomial (α ⊕ Fin q) ℂ) E.LocalRing)
  let c := jacobianCenteredLocalEquiv x e
  have hc : (localizedIdeal (Ideal.span (Set.range f)) x ⊔
      maximalIdeal (PointLocalRing x)^r).map c.toRingHom =
      J ⊔ maximalIdeal E.LocalRing^r := by
    rw [Ideal.map_sup, Ideal.map_pow,
      map_maximalIdeal_of_surjective c.toRingHom c.surjective,
      jacobianCenteredLocalEquiv_span x e f]
  have hlen : Module.length ℂ (PointLocalRing x ⧸
      localizedIdeal (Ideal.span (Set.range f)) x ⊔ maximalIdeal (PointLocalRing x)^r) =
      Module.length ℂ (E.LocalRing ⧸ J ⊔ maximalIdeal E.LocalRing^r) :=
    algEquiv_quotient_field_length c _ _ hc
  have hformal : Module.length ℂ (E.LocalRing ⧸ J ⊔ maximalIdeal E.LocalRing^r) =
      Module.length ℂ (MvPowerSeries α ℂ ⧸ maximalIdeal (MvPowerSeries α ℂ)^r) := by
    refine formalOrigin_system_power_length (α := α) (ι := Fin q) F hF ?_ r
    convert hu using 1
    congr 1
  exact hlen.trans hformal

/-- Identify the literal zero-point localization with the literal base-chart origin. -/
def zeroPointOriginLocalEquiv (k : ℕ) :
    PointLocalRing (0 : Point k) ≃ₐ[ℂ]
      (AffineEtaleChart.base (K := ℂ) (α := Fin k)).LocalRing := by
  let E : AffineEtaleChart ℂ (Fin k) := .base
  have hp : pointIdeal (0 : Point k) = E.point :=
    (pointIdeal_origin_eq_vars k).trans formalOrigin_point_eq_vars.symm
  exact Localization.localAlgEquiv (pointIdeal (0 : Point k)) E.point
    (AlgEquiv.refl : Poly k ≃ₐ[ℂ] MvPolynomial (Fin k) ℂ) (by
      exact hp.trans (by apply Ideal.ext; intro p; rfl))

/-- Free formal power lengths equal the original local Hilbert function of
free affine space. This compares the actual artifacts, without evaluating infinity. -/
theorem formalFree_power_length_eq_whole {α : Type} [Fintype α]
    (k : ℕ) (e : α ≃ Fin k) (t : ℕ) :
    Module.length ℂ (MvPowerSeries α ℂ ⧸ maximalIdeal (MvPowerSeries α ℂ)^(t+1)) =
      (AffineVariety.whole (n := k)).localHilbert (0 : Point k) t := by
  let u := MvPowerSeries.renameEquiv ℂ e
  have hu : (maximalIdeal (MvPowerSeries α ℂ)^(t+1)).map u.toRingHom =
      maximalIdeal (MvPowerSeries (Fin k) ℂ)^(t+1) := by
    rw [Ideal.map_pow, map_maximalIdeal_of_surjective u.toRingHom u.surjective]
  let eu := Ideal.quotientEquivAlg _ _ u hu.symm
  let E : AffineEtaleChart ℂ (Fin k) := .base
  let c := zeroPointOriginLocalEquiv k
  have hc : (maximalIdeal (PointLocalRing (0 : Point k))^(t+1)).map c.toRingHom =
      maximalIdeal E.LocalRing^(t+1) := by
    rw [Ideal.map_pow, map_maximalIdeal_of_surjective c.toRingHom c.surjective]
  let ec := Ideal.quotientEquivAlg _ _ c hc.symm
  have hwhole : (AffineVariety.whole (n := k)).ideal = ⊥ := Ideal.radical_bot_of_isReduced
  have hlocal : (AffineVariety.whole (n := k)).localHilbert (0 : Point k) t =
      Module.length ℂ (PointLocalRing (0 : Point k) ⧸
        maximalIdeal (PointLocalRing (0 : Point k))^(t+1)) := by
    unfold AffineVariety.localHilbert localLengthAt localizedIdeal
    rw [hwhole, bot_sup_eq, Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal,
      point_local_length_eq_complex_length]
  calc
    _ = Module.length ℂ (MvPowerSeries (Fin k) ℂ ⧸
        maximalIdeal (MvPowerSeries (Fin k) ℂ)^(t+1)) := eu.toLinearEquiv.length_eq
    _ = Module.length E.LocalRing (E.LocalRing ⧸ maximalIdeal E.LocalRing^(t+1)) := by
      have h := formalOrigin_quotient_length (maximalIdeal E.LocalRing^(t+1))
      rw [Ideal.map_pow, formalOrigin_localExpansion_maximalIdeal] at h
      exact h.symm
    _ = Module.length ℂ (E.LocalRing ⧸ maximalIdeal E.LocalRing^(t+1)) :=
      formalOrigin_length_eq_complex_length (Fin k) _
    _ = Module.length ℂ (PointLocalRing (0 : Point k) ⧸
        maximalIdeal (PointLocalRing (0 : Point k))^(t+1)) := ec.toLinearEquiv.length_eq.symm
    _ = (AffineVariety.whole (n := k)).localHilbert (0 : Point k) t := hlocal.symm

/-- The actual complement has exactly as many coordinates as the codimension calculation says. -/
theorem jacobianFreeCoordinate_card {n k : ℕ} (hk : k ≤ n) (cols : Fin (n-k) ↪ Fin n) :
    Fintype.card (↥((Set.range cols)ᶜ : Set (Fin n))) = k := by
  have hc := Fintype.card_congr (jacobianCoordinateEquiv cols)
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hc
  omega

end
end DistinctDistances.TrackA
