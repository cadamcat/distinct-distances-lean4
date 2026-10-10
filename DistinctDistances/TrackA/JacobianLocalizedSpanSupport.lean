import DistinctDistances.TrackA.JacobianCenterSupport

namespace DistinctDistances.TrackA
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
open OAI.BoundaryOnly.FormalObstruction.FormalCorrection

/-- The local centering map carries the original generated ideal to the actual centered equations. -/
theorem jacobianCenteredLocalEquiv_span {n q : ℕ} {α ι : Type}
    [Fintype α] [Fintype ι] (x : Point n) (e : α ⊕ ι ≃ Fin n)
    (f : Fin q → Poly n) :
    (localizedIdeal (Ideal.span (Set.range f)) x).map
      (jacobianCenteredLocalEquiv x e).toRingHom =
      (Ideal.span (Set.range (fun i => jacobianCenteredEquiv x e (f i)))).map
        (algebraMap (MvPolynomial (α ⊕ ι) ℂ)
          (AffineEtaleChart.base (K := ℂ) (α := α ⊕ ι)).LocalRing) := by
  rw [localizedIdeal, Ideal.map_map, Ideal.map_span, ← Set.range_comp,
    Ideal.map_span, ← Set.range_comp]
  apply congrArg (fun g : Fin q → (AffineEtaleChart.base (K := ℂ) (α := α ⊕ ι)).LocalRing =>
    Ideal.span (Set.range g))
  funext i
  exact Localization.localRingHom_to_map (pointIdeal x)
    (AffineEtaleChart.base (K := ℂ) (α := α ⊕ ι)).point
    (jacobianCenteredEquiv x e).toRingHom (jacobianCenteredEquiv_point x e) (f i)

/-- Free coordinates followed by the selected columns enumerate every original coordinate. -/
def jacobianCoordinateEquiv {n q : ℕ} (cols : Fin q ↪ Fin n) :
    (↥((Set.range cols)ᶜ : Set (Fin n)) ⊕ Fin q) ≃ Fin n :=
  ((Equiv.sumComm _ _).trans
    (Equiv.sumCongr (Equiv.ofInjective cols cols.injective) (Equiv.refl _))).trans
      (Equiv.Set.sumCompl (Set.range cols))

@[simp] theorem jacobianCoordinateEquiv_inr {n q : ℕ} (cols : Fin q ↪ Fin n) (i : Fin q) :
    jacobianCoordinateEquiv cols (Sum.inr i) = cols i := rfl

/-- Independent equation differentials at the original point give a prime
ideal in the original point-local ring. This uses no component dimension hypothesis. -/
theorem localizedJacobianSpan_isPrime {n q : ℕ} (x : Point n)
    (f : Fin q → Poly n) (cols : Fin q ↪ Fin n)
    (hzero : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hdet : Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (cols j) (f i))) ≠ 0) :
    (localizedIdeal (Ideal.span (Set.range f)) x).IsPrime := by
  let α := ↥((Set.range cols)ᶜ : Set (Fin n))
  let e : α ⊕ Fin q ≃ Fin n := jacobianCoordinateEquiv cols
  let F : Fin q → MvPolynomial (α ⊕ Fin q) ℂ :=
    fun i => jacobianCenteredEquiv x e (f i)
  have hF : ∀ i, (F i).coeff 0 = 0 := by
    intro i
    exact (jacobianCenteredEquiv_constant x e (f i)).trans (hzero i)
  have hJ : internalJacobian F = fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (cols j) (f i)) := by
    ext i j
    exact jacobianCenteredEquiv_linear x e (f i) (Sum.inr j)
  have hunit : IsUnit (internalJacobian F).det := by
    rw [hJ]
    exact isUnit_iff_ne_zero.mpr hdet
  let I := localizedIdeal (Ideal.span (Set.range f)) x
  let φ := (jacobianCenteredLocalEquiv x e).toRingHom
  have : (I.map φ).IsPrime := by
    rw [jacobianCenteredLocalEquiv_span x e f]
    apply localCenteredPolynomial_ideal_isPrime F hF
    convert hunit using 1
    congr 1
  have hprime := Ideal.comap_isPrime φ (I.map φ)
  rw [Ideal.comap_map_of_bijective φ (jacobianCenteredLocalEquiv x e).bijective] at hprime
  exact hprime

end
end DistinctDistances.TrackA
