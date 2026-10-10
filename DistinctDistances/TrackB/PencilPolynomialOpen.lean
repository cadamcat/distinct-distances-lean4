import DistinctDistances.TrackB.TangentLineSupport

namespace DistinctDistances.TrackB
noncomputable section
open LinearMap (BilinForm)

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
  [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N]

/-- A pencil regular at zero meets every nonempty polynomial open in its scalar
parameter. This is the finite-spectrum density step of concentration.tex:837–843. -/
theorem linear_pencil_bijective_polynomial_open (C J : M →ₗ[ℂ] N)
    (hC : Function.Bijective C) (f : Polynomial ℂ) (hf : f ≠ 0) :
    ∃ t : ℂ, f.eval t ≠ 0 ∧ Function.Bijective (C + t • J) := by
  classical
  let E : M ≃ₗ[ℂ] N := LinearEquiv.ofBijective C hC
  let T : Module.End ℂ M := E.symm.toLinearMap.comp J
  let bad : Set ℂ := ({0} ∪ ((fun z : ℂ => -(z⁻¹)) '' spectrum ℂ T)) ∪ {t | f.IsRoot t}
  have hbad : bad.Finite :=
    ((Set.finite_singleton (0 : ℂ)).union ((Module.End.finite_spectrum T).image _)).union
      (Polynomial.finite_setOfPred_isRoot hf)
  obtain ⟨t, ht⟩ := hbad.exists_notMem
  have ht0 : t ≠ 0 := by
    intro h
    apply ht
    exact Or.inl (Or.inl (Set.mem_singleton_iff.mpr h))
  have hspec : -(t⁻¹) ∉ spectrum ℂ T := by
    intro h
    apply ht
    exact Or.inl (Or.inr ⟨-(t⁻¹), h, by simp⟩)
  have hft : f.eval t ≠ 0 := by
    intro h
    apply ht
    exact Or.inr h
  let Q : Module.End ℂ M := algebraMap ℂ (Module.End ℂ M) (-(t⁻¹)) - T
  have hunit : IsUnit Q := by
    simpa only [Q, spectrum.mem_iff, not_not] using hspec
  have hinjQ : Function.Injective Q :=
    LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot _).mp hunit)
  have hinj : Function.Injective (C + t • J) := by
    intro x y hxy
    apply hinjQ
    apply E.injective
    have hs := congrArg (fun z : N => -(t⁻¹) • z) hxy
    have hc : -(t⁻¹) • C x - J x = -(t⁻¹) • C y - J y := by
      simpa [LinearMap.add_apply, LinearMap.smul_apply, smul_add, smul_smul,
        neg_mul, ht0, neg_smul, sub_eq_add_neg] using hs
    simpa [Q, T, E, Algebra.algebraMap_eq_smul_one] using hc
  exact ⟨t, hft, hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank E.finrank_eq).mp hinj⟩

variable {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]

/-- B22's final determinant-density argument, phrased in its actual skew pencil.
Singularity on one polynomial open of all alternating forms extends to every form. -/
theorem skewPencil_singular_of_polynomial_open {m : ℕ}
    (Θ : Submodule ℂ (U × Module.Dual ℂ U))
    (φ : Point m →ₗ[ℂ] alternatingForms (U := U)) (hφ : Function.Surjective φ)
    (g : Poly m) (t0 : Point m) (h0 : MvPolynomial.aeval t0 g ≠ 0)
    (hbad : ∀ t : Point m, MvPolynomial.aeval t g ≠ 0 →
      ¬ Function.Bijective (skewPencil Θ (φ t).val)) :
    ∀ B : BilinForm ℂ U, B.IsAlt → ¬ Function.Bijective (skewPencil Θ B) := by
  intro B hB hbij
  obtain ⟨tstar, htstar⟩ := hφ ⟨B, hB⟩
  let dir := t0 - tstar
  let D := φ dir
  let C := skewPencil Θ B
  let J := skewPencil Θ (B + D.val) - C
  let f := lineRestriction tstar dir g
  have hline : tstar + (1 : ℂ) • dir = t0 := by dsimp [dir]; rw [one_smul]; abel
  have hf : f ≠ 0 := by
    intro hf0
    apply h0
    calc
      MvPolynomial.aeval t0 g = f.eval 1 := by
        change MvPolynomial.aeval t0 g = (lineRestriction tstar dir g).eval 1
        rw [eval_lineRestriction, hline]
      _ = 0 := by rw [hf0, Polynomial.eval_zero]
  obtain ⟨s, hs, hreg⟩ := linear_pencil_bijective_polynomial_open C J hbij f hf
  have hpencil : skewPencil Θ (φ (tstar + s • dir)).val = C + s • J := by
    have hform : (φ (tstar + s • dir)).val = B + s • D.val := by
      rw [map_add, map_smul, htstar]
      rfl
    rw [hform]
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change x.1.2 y - (B + s • D.val) x.1.1 y =
      (x.1.2 y - B x.1.1 y) + s •
        ((x.1.2 y - (B + D.val) x.1.1 y) - (x.1.2 y - B x.1.1 y))
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hg : MvPolynomial.aeval (tstar + s • dir) g ≠ 0 := by
    simpa only [f, eval_lineRestriction] using hs
  apply hbad _ hg
  rw [hpencil]
  exact hreg

#print axioms linear_pencil_bijective_polynomial_open
#print axioms skewPencil_singular_of_polynomial_open
end
end DistinctDistances.TrackB
