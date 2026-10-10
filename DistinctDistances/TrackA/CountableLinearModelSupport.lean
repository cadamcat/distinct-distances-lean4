import DistinctDistances.TrackA.CountableLinearSpecializationSupport
import DistinctDistances.TrackA.ScalarModelDescentSupport

set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical TensorProduct
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Descend the inverse of the distinguished chart coordinate together
with all coordinates. Injectivity of the model inclusion detects both
reducedness and the inverse relation. -/
theorem reduced_countable_model_with_unit {K A : Type} {n : ℕ}
    [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A] [IsReduced A]
    (v : Fin n → A) (i : Fin n) (hv : IsUnit (v i))
    (c : Set K) (hc : c.Countable) :
    ∃ (S : Subfield K), Countable S ∧ c ⊆ S ∧
      ∃ (m : ℕ) (I : Ideal (MvPolynomial (Fin m) S))
        (e : (K ⊗[S] (MvPolynomial (Fin m) S ⧸ I)) ≃ₐ[K] A)
        (v₀ : Fin n → MvPolynomial (Fin m) S ⧸ I),
        (∀ j, e (1 ⊗ₜ[S] v₀ j) = v j) ∧
        IsReduced (MvPolynomial (Fin m) S ⧸ I) ∧ IsUnit (v₀ i) := by
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hv
  obtain ⟨S, hS, hcS, m, I, e, w₀, hw⟩ :=
    OAI.MaximalSeshadri.BertiniIntegral.countable_model_with_elements
      (Fin.snoc v u) c hc
  have hrel : e (1 ⊗ₜ[S] w₀ i.castSucc) * e (1 ⊗ₜ[S] w₀ (Fin.last n)) = 1 := by
    rw [hw, hw, Fin.snoc_castSucc, Fin.snoc_last]
    exact hu
  obtain ⟨hred, hunit⟩ := scalar_model_reduced_and_unit e
    (w₀ i.castSucc) (w₀ (Fin.last n)) hrel
  refine ⟨S, hS, hcS, m, I, e, (fun j => w₀ j.castSucc), ?_, hred, hunit⟩
  intro j
  simpa only [Fin.snoc_castSucc] using hw j.castSucc

/-- Every injective coefficient specialization over this one countable
field gives a reduced literal linear equation in the original chart. -/
theorem reduced_linear_equation_countable_field {K A : Type} {n : ℕ}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] [IsReduced A]
    (v : Fin n → A) (i : Fin n) (hv : IsUnit (v i))
    (c : Set K) (hc : c.Countable) :
    ∃ S : Subfield K, Countable S ∧ c ⊆ S ∧
      ∀ f : MvPolynomial (Fin n) S →ₐ[S] K, Function.Injective f →
        (Ideal.span {∑ j, algebraMap K A (f (MvPolynomial.X j)) * v j}).IsRadical := by
  obtain ⟨S, hS, hcS, m, I, e, v₀, hcoords, hred, hunit⟩ :=
    reduced_countable_model_with_unit v i hv c hc
  let : IsReduced (MvPolynomial (Fin m) S ⧸ I) := hred
  refine ⟨S, hS, hcS, fun f hf => ?_⟩
  exact reduced_linear_equation_over_model e v₀ v hcoords i hunit f hf

/-- The same finite coordinate list can be specialized simultaneously on
a countable family of reduced charts, using the original common-field
and independent-parameter theorems. -/
theorem simultaneous_reduced_linear_equations {K ι : Type} {n : ℕ}
    [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K] [Countable ι]
    (A : ι → Type) [∀ t, CommRing (A t)] [∀ t, Algebra K (A t)]
    [∀ t, Algebra.FiniteType K (A t)] [∀ t, IsReduced (A t)]
    (v : ∀ t, Fin n → A t) (i : ι → Fin n) (hv : ∀ t, IsUnit (v t (i t))) :
    ∃ α : Fin n → K, ∀ t,
      (Ideal.span {∑ j, algebraMap K (A t) (α j) * v t j}).IsRadical := by
  let P (t : ι) (α : Fin n → K) (_ : K) : Prop :=
    (Ideal.span {∑ j, algebraMap K (A t) (α j) * v t j}).IsRadical
  have hP t : ∃ S : Subfield K, Countable S ∧
      ∀ f : (MvPolynomial (Fin n) S)[X] →ₐ[S] K, Function.Injective f →
        P t (fun j => f (C (MvPolynomial.X j))) (f X) := by
    obtain ⟨S, hS, _, h⟩ := reduced_linear_equation_countable_field
      (v t) (i t) (hv t) (∅ : Set K) Set.countable_empty
    refine ⟨S, hS, fun f hf => ?_⟩
    exact h (f.comp Polynomial.CAlgHom) (hf.comp Polynomial.C_injective)
  obtain ⟨S, hS, _, h⟩ :=
    OAI.MaximalSeshadri.BertiniIntegral.simultaneous_generic_hyperplane_parameters
      P hP (∅ : Set K) Set.countable_empty
  let : Countable S := hS
  obtain ⟨f, hf⟩ :=
    OAI.MaximalSeshadri.BertiniIntegral.independent_hyperplane_parameters (σ := Fin n) S
  exact ⟨fun j => f (C (MvPolynomial.X j)), h f hf⟩

end
end DistinctDistances.TrackA
