import DistinctDistances.TrackA.RegularityRankSupport
import Mathlib.Data.Fin.Tuple.Basic

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- The direction is a coefficient tuple in the fiber field. -/
def fieldDirectionalDerivative {n : ℕ} {Ω : Type*} [Field Ω]
    (x v : FieldPoint n Ω) : FieldPoly n Ω →ₗ[Ω] Ω :=
  ∑ i : Fin n, v i • ((MvPolynomial.aeval x).toLinearMap.comp
    (MvPolynomial.pderiv i).toLinearMap)

theorem fieldDirectionalDerivative_apply {n : ℕ} {Ω : Type*} [Field Ω]
    (x v : FieldPoint n Ω) (f : FieldPoly n Ω) :
    fieldDirectionalDerivative x v f =
      ∑ i : Fin n, v i * MvPolynomial.eval x (MvPolynomial.pderiv i f) := by
  simp [fieldDirectionalDerivative, MvPolynomial.aeval_eq_eval]

theorem fieldDirectionalDerivative_mul {n : ℕ} {Ω : Type*} [Field Ω]
    (x v : FieldPoint n Ω) (f g : FieldPoly n Ω) :
    fieldDirectionalDerivative x v (f*g) =
      MvPolynomial.eval x f * fieldDirectionalDerivative x v g +
      MvPolynomial.eval x g * fieldDirectionalDerivative x v f := by
  simp only [fieldDirectionalDerivative_apply, Derivation.leibniz, smul_eq_mul,
    map_add, map_mul, mul_add, Finset.sum_add_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

/-- All values and one directional derivative at each selected sheet. -/
def augmentedFieldEvaluation {n a b : ℕ} {Ω : Type*} [Field Ω]
    (points : Fin a → FieldPoint n Ω) (selected : Fin b → Fin a)
    (directions : Fin b → FieldPoint n Ω) :
    FieldPoly n Ω →ₗ[Ω] (Fin (a+b) → Ω) where
  toFun f := Fin.append (fun i => MvPolynomial.eval (points i) f)
    (fun i => fieldDirectionalDerivative (points (selected i)) (directions i) f)
  map_add' f g := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [Fin.append_left, Fin.append_right, map_add]
  map_smul' c f := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [Fin.append_left, Fin.append_right, map_smul]

/-- First jets interpolate arbitrary directional data whenever each
selected direction is nonzero. Sheet and direction indices are injective. -/
theorem augmentedFieldEvaluation_surjective {n a b : ℕ} {Ω : Type}
    [Field Ω] [IsAlgClosed Ω] (points : Fin a → FieldPoint n Ω)
    (hpoints : Function.Injective points) (selected : Fin b → Fin a)
    (hselected : Function.Injective selected) (directions : Fin b → FieldPoint n Ω)
    (hdirections : ∀ i, directions i ≠ 0) (q : ℕ)
    (hjets : ∀ (values : FieldPoint n Ω → Ω)
      (derivatives : FieldPoint n Ω → Fin n → Ω),
      ∃ p : FieldPoly n Ω, p.totalDegree ≤ q ∧
        ∀ z ∈ Finset.univ.image points, MvPolynomial.eval z p = values z ∧
          ∀ j, MvPolynomial.eval z (MvPolynomial.pderiv j p) = derivatives z j) :
    ∀ w : Fin (a+b) → Ω, ∃ p : FieldPoly n Ω,
      p.totalDegree ≤ q ∧ augmentedFieldEvaluation points selected directions p = w := by
  have hcoordinate : ∀ i : Fin b, ∃ j : Fin n, directions i j ≠ 0 := by
    intro i
    by_contra h
    push Not at h
    exact hdirections i (funext h)
  choose coordinate hcoordinate using hcoordinate
  intro w
  let values : FieldPoint n Ω → Ω :=
    Function.extend points (fun i => w (Fin.castAdd b i)) (fun _ => 0)
  let desired : Fin b → Fin n → Ω := fun i j =>
    if j = coordinate i then w (Fin.natAdd a i) / directions i (coordinate i) else 0
  let derivatives : FieldPoint n Ω → Fin n → Ω :=
    Function.extend (points ∘ selected) desired (fun _ _ => 0)
  obtain ⟨p, hp, hval⟩ := hjets values derivatives
  refine ⟨p, hp, ?_⟩
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [augmentedFieldEvaluation, LinearMap.coe_mk, AddHom.coe_mk, Fin.append_left]
    exact (hval (points i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))).1.trans
      (hpoints.extend_apply _ _ i)
  · simp only [augmentedFieldEvaluation, LinearMap.coe_mk, AddHom.coe_mk, Fin.append_right]
    rw [fieldDirectionalDerivative_apply]
    have hd (j : Fin n) : MvPolynomial.eval (points (selected i))
        (MvPolynomial.pderiv j p) = desired i j := by
      exact ((hval _ (Finset.mem_image_of_mem _ (Finset.mem_univ (selected i)))).2 j).trans
        (congrFun ((hpoints.comp hselected).extend_apply desired (fun _ _ => 0) i) j)
    simp_rw [hd]
    simp [desired, mul_ite, mul_div_cancel₀, hcoordinate i]

/-- A linear map, including a jet map, is spanned by its ordinary
monomial columns in the supplied degree. -/
theorem field_linear_map_in_monomial_span {n r : ℕ} {Ω : Type*} [Field Ω]
    (T : FieldPoly n Ω →ₗ[Ω] (Fin r → Ω)) (q : ℕ) (p : FieldPoly n Ω)
    (hp : p.totalDegree ≤ q) :
    T p ∈ Submodule.span Ω ((fun d : Fin n →₀ ℕ =>
      T (MvPolynomial.monomial d 1)) ''
        (OAI.QuarticPowerFree.simplexExponents n q : Set (Fin n →₀ ℕ))) := by
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro d hd
  have hmono : MvPolynomial.monomial d (p.coeff d) =
      (p.coeff d) • MvPolynomial.monomial d (1 : Ω) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hmono, map_smul]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨d, (OAI.QuarticPowerFree.mem_simplexExponents d).mpr
    ((MvPolynomial.le_totalDegree hd).trans hp), rfl⟩

/-- Column selection for augmented interpolation uses linearity only. -/
theorem field_linear_monomial_columns {n r : ℕ} {Ω : Type*} [Field Ω]
    (T : FieldPoly n Ω →ₗ[Ω] (Fin r → Ω)) (q : ℕ)
    (hsurj : ∀ w, ∃ p : FieldPoly n Ω, p.totalDegree ≤ q ∧ T p = w) :
    ∃ d : Fin r → (Fin n →₀ ℕ), (∀ i, (d i).degree ≤ q) ∧
      LinearIndependent Ω (fun i => T (MvPolynomial.monomial (d i) 1)) := by
  let v := fun d : Fin n →₀ ℕ => T (MvPolynomial.monomial d 1)
  let S := OAI.QuarticPowerFree.simplexExponents n q
  have hspan : Submodule.span Ω (v '' (S : Set (Fin n →₀ ℕ))) = ⊤ := by
    apply top_unique
    intro w hw
    obtain ⟨p, hp, rfl⟩ := hsurj w
    exact field_linear_map_in_monomial_span T q p hp
  have hrank : r ≤ Module.finrank Ω (Submodule.span Ω (v '' (S : Set (Fin n →₀ ℕ)))) := by
    rw [hspan]
    simp
  obtain ⟨B, _, hBS, hBcard, hBLI⟩ := OAI.QuarticPowerFree.extend_independent_finset v S ∅
    (Finset.empty_subset _) (by simp) r (by simp) hrank
  let e := (Finset.equivFinOfCardEq hBcard).symm
  refine ⟨fun i => (e i).val, ?_, ?_⟩
  · intro i
    exact (OAI.QuarticPowerFree.mem_simplexExponents (e i).val).mp (hBS (e i).property)
  · exact hBLI.linearIndependent_restrict.comp e e.injective

end
end DistinctDistances.TrackA
