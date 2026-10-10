import DistinctDistances.TrackA.LocalJacobianIdealSupport
import DistinctDistances.TrackA.SeparatorTranslationSupport

namespace DistinctDistances.TrackA
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
open OAI.BoundaryOnly.FormalObstruction.FormalCorrection

instance jacobianOriginScalarAlgebra (β : Type) :
    Algebra ℂ (AffineEtaleChart.base (K := ℂ) (α := β)).S :=
  inferInstanceAs (Algebra ℂ (MvPolynomial β ℂ))

/-- Translate the original point to zero and reorder the selected coordinates. -/
def jacobianCenteredEquiv {n : ℕ} {α ι : Type} (x : Point n)
    (e : α ⊕ ι ≃ Fin n) : Poly n ≃ₐ[ℂ] MvPolynomial (α ⊕ ι) ℂ :=
  (OAI.PiExponent.WeightedBezout.translationEquiv x).trans
    (MvPolynomial.renameEquiv ℂ e.symm)

/-- The constant term after centering is evaluation at the original point. -/
theorem jacobianCenteredEquiv_constant {n : ℕ} {α ι : Type} (x : Point n)
    (e : α ⊕ ι ≃ Fin n) (p : Poly n) :
    (jacobianCenteredEquiv x e p).coeff 0 = MvPolynomial.eval x p := by
  change MvPolynomial.constantCoeff
    (MvPolynomial.rename e.symm (OAI.PiExponent.WeightedBezout.translationEquiv x p)) = _
  rw [MvPolynomial.constantCoeff_rename, ← MvPolynomial.eval_zero,
    separator_translation_eval, add_zero]

/-- Coordinate partial derivatives commute with the original affine translation. -/
theorem jacobian_translation_pderiv {n : ℕ} (x : Point n) (p : Poly n) (j : Fin n) :
    MvPolynomial.pderiv j (OAI.PiExponent.WeightedBezout.translationEquiv x p) =
      OAI.PiExponent.WeightedBezout.translationEquiv x (MvPolynomial.pderiv j p) := by
  have hX (a : Fin n) : OAI.PiExponent.WeightedBezout.translationEquiv x
      (MvPolynomial.X a) = MvPolynomial.C (x a) + MvPolynomial.X a := by
    simp only [OAI.PiExponent.WeightedBezout.translationEquiv,
      AlgEquiv.ofAlgHom_apply, OAI.PiExponent.WeightedBezout.translation,
      MvPolynomial.aeval_X]
  have hC (a : ℂ) : OAI.PiExponent.WeightedBezout.translationEquiv x
      (MvPolynomial.C a) = MvPolynomial.C a :=
    (OAI.PiExponent.WeightedBezout.translationEquiv x).commutes a
  induction p using MvPolynomial.induction_on with
  | C a => simp only [hC, MvPolynomial.pderiv_C, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p a hp =>
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, hX,
        MvPolynomial.pderiv_C, MvPolynomial.pderiv_X, zero_add,
        Pi.single_apply, apply_ite, map_one, map_zero]

/-- A selected first coefficient after centering is the original evaluated partial derivative. -/
theorem jacobianCenteredEquiv_linear {n : ℕ} {α ι : Type} (x : Point n)
    (e : α ⊕ ι ≃ Fin n) (p : Poly n) (j : α ⊕ ι) :
    (jacobianCenteredEquiv x e p).coeff (Finsupp.single j 1) =
      MvPolynomial.eval x (MvPolynomial.pderiv (e j) p) := by
  have hcoeff : (MvPolynomial.pderiv j (jacobianCenteredEquiv x e p)).coeff 0 =
      (jacobianCenteredEquiv x e p).coeff (Finsupp.single j 1) := by
    simp only [MvPolynomial.coeff_pderiv, zero_add, Finsupp.zero_apply,
      Nat.cast_zero, mul_one]
  rw [← hcoeff]
  have hder : MvPolynomial.pderiv j (jacobianCenteredEquiv x e p) =
      jacobianCenteredEquiv x e (MvPolynomial.pderiv (e j) p) := by
    have hr := MvPolynomial.pderiv_rename e.symm.injective (e j)
      (OAI.PiExponent.WeightedBezout.translationEquiv x p)
    have hr' : MvPolynomial.pderiv j (MvPolynomial.rename e.symm
        (OAI.PiExponent.WeightedBezout.translationEquiv x p)) =
        MvPolynomial.rename e.symm (MvPolynomial.pderiv (e j)
          (OAI.PiExponent.WeightedBezout.translationEquiv x p)) := by
      simpa only [e.symm_apply_apply] using hr
    exact hr'.trans (congrArg (MvPolynomial.rename e.symm)
      (jacobian_translation_pderiv x p (e j)))
  rw [hder, jacobianCenteredEquiv_constant]

/-- The centered polynomial equivalence carries the original point to the literal chart origin. -/
theorem jacobianCenteredEquiv_point {n : ℕ} {α ι : Type}
    (x : Point n) (e : α ⊕ ι ≃ Fin n) :
    pointIdeal x = ((AffineEtaleChart.base (K := ℂ) (α := α ⊕ ι)).point).comap
      (jacobianCenteredEquiv x e).toRingHom := by
  ext p
  change p ∈ pointIdeal x ↔ (jacobianCenteredEquiv x e p).coeff 0 = 0
  rw [jacobianCenteredEquiv_constant]
  simp only [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff,
    MvPolynomial.aeval_eq_eval]

/-- The actual point localization is equivalent to the centered origin localization. -/
def jacobianCenteredLocalEquiv {n : ℕ} {α ι : Type} [Fintype α] [Fintype ι]
    (x : Point n) (e : α ⊕ ι ≃ Fin n) :
    PointLocalRing x ≃ₐ[ℂ] (AffineEtaleChart.base (K := ℂ) (α := α ⊕ ι)).LocalRing :=
  Localization.localAlgEquiv (pointIdeal x)
    (AffineEtaleChart.base (K := ℂ) (α := α ⊕ ι)).point
    (jacobianCenteredEquiv x e) (jacobianCenteredEquiv_point x e)

end
end DistinctDistances.TrackA
