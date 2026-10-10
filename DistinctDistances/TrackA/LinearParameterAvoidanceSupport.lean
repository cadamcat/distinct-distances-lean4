import DistinctDistances.TrackA.CountableLinearModelSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Independent coefficients cannot annihilate a nonzero coordinate
vector whose entries lie in their field of independence. -/
theorem injective_linear_parameters_ne_zero {R K σ : Type}
    [Field R] [Field K] [Algebra R K] [Fintype σ]
    (f : MvPolynomial σ R →ₐ[R] K) (hf : Function.Injective f)
    (x : σ → R) (hx : ∃ i, x i ≠ 0) :
    ∑ j, f (MvPolynomial.X j) * algebraMap R K (x j) ≠ 0 := by
  obtain ⟨i, hi⟩ := hx
  let p : MvPolynomial σ R := ∑ j, MvPolynomial.X j * MvPolynomial.C (x j)
  have hp : p ≠ 0 := by
    intro hz
    have he := congrArg (MvPolynomial.eval (fun j => if j = i then (1 : R) else 0)) hz
    have hev : MvPolynomial.eval (fun j => if j = i then (1 : R) else 0) p = x i := by
      simp [p, ite_mul]
    rw [hev, map_zero] at he
    exact hi he
  intro hz
  have hC (r : R) : f (MvPolynomial.C r) = algebraMap R K r := f.commutes r
  have hfp : f p = 0 := by
    simpa only [p, map_sum, map_mul, hC] using hz
  exact hp (hf (hfp.trans (map_zero f).symm))

/-- Select one coefficient tuple that gives reduced equations on every
chart and avoids every supplied nonzero test vector. In the projective
consumer these are representatives of one point on each component. -/
theorem simultaneous_reduced_linear_equations_avoiding {K ι τ : Type} {n : ℕ}
    [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [Countable ι] [Countable τ]
    (A : ι → Type) [∀ t, CommRing (A t)] [∀ t, Algebra K (A t)]
    [∀ t, Algebra.FiniteType K (A t)] [∀ t, IsReduced (A t)]
    (v : ∀ t, Fin n → A t) (i : ι → Fin n) (hv : ∀ t, IsUnit (v t (i t)))
    (x : τ → Fin n → K) (hx : ∀ t, ∃ j, x t j ≠ 0) :
    ∃ α : Fin n → K,
      (∀ t, (Ideal.span {∑ j, algebraMap K (A t) (α j) * v t j}).IsRadical) ∧
      ∀ t, ∑ j, α j * x t j ≠ 0 := by
  let P (t : ι) (α : Fin n → K) (_ : K) : Prop :=
    (Ideal.span {∑ j, algebraMap K (A t) (α j) * v t j}).IsRadical
  have hP t : ∃ S : Subfield K, Countable S ∧
      ∀ f : (MvPolynomial (Fin n) S)[X] →ₐ[S] K, Function.Injective f →
        P t (fun j => f (C (MvPolynomial.X j))) (f X) := by
    obtain ⟨S, hS, _, h⟩ := reduced_linear_equation_countable_field
      (v t) (i t) (hv t) (∅ : Set K) Set.countable_empty
    refine ⟨S, hS, fun f hf => ?_⟩
    exact h (f.comp Polynomial.CAlgHom) (hf.comp Polynomial.C_injective)
  let c : Set K := ⋃ t, Set.range (x t)
  have hc : c.Countable := Set.countable_iUnion fun t => Set.countable_range (x t)
  obtain ⟨S, hS, hcS, h⟩ :=
    OAI.MaximalSeshadri.BertiniIntegral.simultaneous_generic_hyperplane_parameters P hP c hc
  let : Countable S := hS
  obtain ⟨f, hf⟩ :=
    OAI.MaximalSeshadri.BertiniIntegral.independent_hyperplane_parameters (σ := Fin n) S
  refine ⟨fun j => f (C (MvPolynomial.X j)), h f hf, ?_⟩
  intro t
  let x₀ : Fin n → S := fun j => ⟨x t j, hcS (Set.mem_iUnion.mpr ⟨t, j, rfl⟩)⟩
  have hx₀ : ∃ j, x₀ j ≠ 0 := by
    obtain ⟨j, hj⟩ := hx t
    exact ⟨j, fun hz => hj (congrArg Subtype.val hz)⟩
  exact injective_linear_parameters_ne_zero (f.comp Polynomial.CAlgHom)
    (hf.comp Polynomial.C_injective) x₀ hx₀

end
end DistinctDistances.TrackA
