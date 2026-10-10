import DistinctDistances.TrackA.CylinderQuotientSupport

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators

/-- Extract an original source-quotient coefficient from the cylinder quotient. -/
def lineCylinderCoefficient {n : ℕ} (V : AffineVariety n) (i : ℕ) :
    (Poly (n+1) ⧸ (lineCylinder V).ideal) →ₗ[ℂ] (Poly n ⧸ V.ideal) :=
  ((Polynomial.lcoeff (Poly n ⧸ V.ideal) i).restrictScalars ℂ).comp
    (lineCylinderQuotientEquiv V).toLinearMap

theorem lineCylinderCoefficient_mk {n : ℕ} (V : AffineVariety n)
    (f : Poly (n+1)) (i : ℕ) :
    lineCylinderCoefficient V i (Ideal.Quotient.mk (lineCylinder V).ideal f) =
      Ideal.Quotient.mk V.ideal ((MvPolynomial.finSuccEquiv ℂ n f).coeff i) := by
  change (lineCylinderQuotientEquiv V _).coeff i = _
  rw [lineCylinderQuotientEquiv_mk, lineCylinderQuotientMap_coeff]

theorem lineCylinderCoefficient_mem {n : ℕ} (V : AffineVariety n) (D i : ℕ)
    (x : (lineCylinder V).restrictionSpace D) :
    lineCylinderCoefficient V i x.val ∈ V.restrictionSpace D := by
  obtain ⟨f, hf, hfx⟩ := x.property
  rw [← hfx]
  change lineCylinderCoefficient V i (Ideal.Quotient.mk (lineCylinder V).ideal f) ∈ _
  rw [lineCylinderCoefficient_mk]
  refine ⟨(MvPolynomial.finSuccEquiv ℂ n f).coeff i, ?_, rfl⟩
  apply OAI.QuarticPowerFree.mem_totalSpace.mpr
  by_cases hi : (MvPolynomial.finSuccEquiv ℂ n f).coeff i = 0
  · simp [hi]
  · exact (Nat.le_add_right _ _).trans
      ((MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le f i hi).trans
        (OAI.QuarticPowerFree.mem_totalSpace.mp hf))

theorem lineCylinderCoefficient_zero {n : ℕ} (V : AffineVariety n) (D i : ℕ)
    (hi : D < i) (x : (lineCylinder V).restrictionSpace D) :
    lineCylinderCoefficient V i x.val = 0 := by
  obtain ⟨f, hf, hfx⟩ := x.property
  rw [← hfx]
  change lineCylinderCoefficient V i (Ideal.Quotient.mk (lineCylinder V).ideal f) = 0
  rw [lineCylinderCoefficient_mk]
  have hz : (MvPolynomial.finSuccEquiv ℂ n f).coeff i = 0 := by
    by_contra hz
    have h := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le f i hz
    have hD := OAI.QuarticPowerFree.mem_totalSpace.mp hf
    omega
  simp [hz]

/-- The degree-D cylinder restriction embeds in D+1 original degree-D
source restriction spaces, using the actual scalar coefficients. -/
def lineCylinderCoefficientEmbedding {n : ℕ} (V : AffineVariety n) (D : ℕ) :
    (lineCylinder V).restrictionSpace D →ₗ[ℂ] (Fin (D+1) → V.restrictionSpace D) where
  toFun x i := ⟨lineCylinderCoefficient V i x.val, lineCylinderCoefficient_mem V D i x⟩
  map_add' x y := by
    funext i
    apply Subtype.ext
    exact (lineCylinderCoefficient V i).map_add x.val y.val
  map_smul' c x := by
    funext i
    apply Subtype.ext
    exact (lineCylinderCoefficient V i).map_smul c x.val

theorem lineCylinderCoefficientEmbedding_injective {n : ℕ} (V : AffineVariety n)
    (D : ℕ) : Function.Injective (lineCylinderCoefficientEmbedding V D) := by
  intro x y hxy
  apply Subtype.ext
  apply (lineCylinderQuotientEquiv V).injective
  ext i
  by_cases hi : i < D+1
  · exact congrArg Subtype.val (congrFun hxy ⟨i, hi⟩)
  · change lineCylinderCoefficient V i x.val = lineCylinderCoefficient V i y.val
    rw [lineCylinderCoefficient_zero V D i (by omega) x,
      lineCylinderCoefficient_zero V D i (by omega) y]

theorem lineCylinder_hilbert_le {n : ℕ} (V : AffineVariety n) (D : ℕ) :
    (lineCylinder V).hilbert D ≤ (D+1) * V.hilbert D := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (lineCylinderCoefficientEmbedding_injective V D)
  simpa [AffineVariety.hilbert, Module.finrank_pi_fintype] using h

end
end DistinctDistances.TrackA
