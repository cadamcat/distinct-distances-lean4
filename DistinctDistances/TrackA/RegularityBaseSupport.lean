import DistinctDistances.TrackA.RegularityJetSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- Transport differentiation through the literal coefficient extension. -/
theorem fieldDirectionalDerivative_map {n : ℕ} {Ω : Type*}
    [Field Ω] [Algebra ℂ Ω] (x v : FieldPoint n Ω) (f : Poly n) :
    fieldDirectionalDerivative x v (MvPolynomial.map (algebraMap ℂ Ω) f) =
      ∑ i : Fin n, v i * MvPolynomial.aeval x (MvPolynomial.pderiv i f) := by
  simp only [fieldDirectionalDerivative_apply, MvPolynomial.pderiv_map,
    ← MvPolynomial.eval₂_eq_eval_map]
  rfl

/-- The complex-linear augmented map uses literal coefficient extension. -/
def augmentedComplexEvaluation {n a b : ℕ} {Ω : Type*}
    [Field Ω] [Algebra ℂ Ω] (points : Fin a → FieldPoint n Ω)
    (selected : Fin b → Fin a) (directions : Fin b → FieldPoint n Ω) :
    Poly n →ₗ[ℂ] (Fin (a+b) → Ω) :=
  ((augmentedFieldEvaluation points selected directions).restrictScalars ℂ).comp
    (MvPolynomial.mapAlgHom (Algebra.ofId ℂ Ω)).toLinearMap

theorem augmentedComplexEvaluation_apply {n a b : ℕ} {Ω : Type*}
    [Field Ω] [Algebra ℂ Ω] (points : Fin a → FieldPoint n Ω)
    (selected : Fin b → Fin a) (directions : Fin b → FieldPoint n Ω) (f : Poly n) :
    augmentedComplexEvaluation points selected directions f =
      augmentedFieldEvaluation points selected directions (MvPolynomial.map (algebraMap ℂ Ω) f) := rfl

/-- A directional derivative killing the base generators kills their
whole polynomial algebra. The fiber coefficients remain constant. -/
theorem fieldDirectionalDerivative_base_zero {n k : ℕ} {Ω : Type*}
    [Field Ω] [Algebra ℂ Ω] (x v : FieldPoint n Ω) (base : Fin k → Poly n)
    (hbase : ∀ j, fieldDirectionalDerivative x v
      (MvPolynomial.map (algebraMap ℂ Ω) (base j)) = 0) (p : Poly k) :
    fieldDirectionalDerivative x v
      (MvPolynomial.map (algebraMap ℂ Ω) (MvPolynomial.aeval base p)) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [fieldDirectionalDerivative_apply]
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.aeval_X, fieldDirectionalDerivative_mul, hp,
      hbase j, mul_zero, add_zero]

/-- Evaluation on a sheet respects the supplied base coordinates. -/
theorem regularity_base_evaluation {n k : ℕ} {Ω : Type*} [Field Ω] [Algebra ℂ Ω]
    (x : FieldPoint n Ω) (base : Fin k → Poly n) (t : Fin k → Ω)
    (hbase : ∀ j, MvPolynomial.aeval x (base j) = t j) (p : Poly k) :
    MvPolynomial.eval x (MvPolynomial.map (algebraMap ℂ Ω) (MvPolynomial.aeval base p)) =
      MvPolynomial.aeval t p := by
  have he : (MvPolynomial.aeval (R := ℂ) x).comp (MvPolynomial.aeval base) =
      MvPolynomial.aeval t := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using hbase j
  rw [← MvPolynomial.eval₂_eq_eval_map]
  exact AlgHom.congr_fun he p

/-- Vertical derivatives give the same scalar-multiplication identity as
values when the inputs are multiplied by any base polynomial. -/
theorem augmentedComplexEvaluation_base_mul {n k a b : ℕ} {Ω : Type*}
    [Field Ω] [Algebra ℂ Ω] (points : Fin a → FieldPoint n Ω)
    (selected : Fin b → Fin a) (directions : Fin b → FieldPoint n Ω)
    (base : Fin k → Poly n) (t : Fin k → Ω)
    (hbase : ∀ i j, MvPolynomial.aeval (points i) (base j) = t j)
    (hvertical : ∀ i j, fieldDirectionalDerivative (points (selected i)) (directions i)
      (MvPolynomial.map (algebraMap ℂ Ω) (base j)) = 0)
    (f : Poly n) (p : Poly k) :
    augmentedComplexEvaluation points selected directions (f * MvPolynomial.aeval base p) =
      MvPolynomial.aeval t p • augmentedComplexEvaluation points selected directions f := by
  simp only [augmentedComplexEvaluation_apply, map_mul]
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [augmentedFieldEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.append_left, Pi.smul_apply, smul_eq_mul, map_mul,
      regularity_base_evaluation (points i) base t (hbase i) p]
    ring
  · simp only [augmentedFieldEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.append_right, Pi.smul_apply, smul_eq_mul, fieldDirectionalDerivative_mul,
      fieldDirectionalDerivative_base_zero _ _ base (hvertical i) p,
      regularity_base_evaluation (points (selected i)) base t (hbase (selected i)) p,
      mul_zero, zero_add]

/-- Extend the selected monomials over the original complex coefficient
field, while their augmented columns are independent over the fiber field. -/
theorem augmentedComplexEvaluation_monomial_columns {n a b : ℕ} {Ω : Type*}
    [Field Ω] [Algebra ℂ Ω] (points : Fin a → FieldPoint n Ω)
    (selected : Fin b → Fin a) (directions : Fin b → FieldPoint n Ω) (q : ℕ)
    (hsurj : ∀ w, ∃ p : FieldPoly n Ω, p.totalDegree ≤ q ∧
      augmentedFieldEvaluation points selected directions p = w) :
    ∃ transverse : Fin (a+b) → Poly n,
      (∀ i, (transverse i).totalDegree ≤ q) ∧
      LinearIndependent Ω (fun i => augmentedComplexEvaluation points selected directions
        (transverse i)) := by
  obtain ⟨d, hd, hLI⟩ := field_linear_monomial_columns
    (augmentedFieldEvaluation points selected directions) q hsurj
  refine ⟨fun i => MvPolynomial.monomial (d i) 1, ?_, ?_⟩
  · intro i
    simpa only [MvPolynomial.totalDegree_monomial (d i) one_ne_zero,
      Finsupp.degree_apply, Finsupp.sum] using hd i
  · simpa only [augmentedComplexEvaluation_apply, MvPolynomial.map_monomial, map_one] using hLI

end
end DistinctDistances.TrackA
