import DistinctDistances.TrackA.Requests
import DistinctDistances.TrackA.Interpolation
import DistinctDistances.TrackA.CompressionDescent
import DistinctDistances.OAIInterface.HilbertSimplex

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open OAI.QuarticPowerFree

theorem projection_base_degree {n k : ℕ} (φ : AffineProjection n k) (j : Fin k) :
    (φ.pullback (MvPolynomial.X j)).totalDegree ≤ 1 := by
  rw [AffineProjection.pullback, MvPolynomial.aeval_X]
  change (linearCoordinate φ.linear j + MvPolynomial.C (φ.offset j)).totalDegree ≤ 1
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i hi
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  · simp

theorem generic_fiber_equations_degree {n k : ℕ} {F : AffineFamily.Family n}
    {φ : AffineProjection n k} (G : ComponentGenericFiber F φ) (E : Set (Poly n))
    (L : ℕ) (hL : 1 ≤ L) (hE : ∀ f ∈ E, f.totalDegree ≤ L) :
    ∀ f ∈ G.equations E, f.totalDegree ≤ L := by
  intro f hf
  rcases hf with ⟨p, hp, rfl⟩ | ⟨j, rfl⟩
  · exact (compression_map_degree_le _ _).trans (hE p hp)
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · exact ((compression_map_degree_le _ _).trans (projection_base_degree φ j)).trans hL
    · simp

theorem generic_fiber_isolated_list {n k : ℕ} {F : AffineFamily.Family n}
    {φ : AffineProjection n k} (G : ComponentGenericFiber F φ) (E : Set (Poly n))
    (hiso : ∀ i : Fin G.r,
      pointIdealOver (G.points i) ∈ (Ideal.span (G.equations E)).minimalPrimes) :
    IsolatedPoints (G.equations E) (Finset.univ.image G.points) := by
  intro z hz
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
  exact hiso i

/-- A sublist retains isolation in its own original fiber system. -/
theorem generic_fiber_isolated_sublist {n k : ℕ} {F : AffineFamily.Family n}
    {φ : AffineProjection n k} (G : ComponentGenericFiber F φ)
    (E : Set (Poly n)) (indices : Finset (Fin G.r))
    (hiso : ∀ j ∈ indices,
      pointIdealOver (G.points j) ∈ (Ideal.span (G.equations E)).minimalPrimes) :
    IsolatedPoints (G.equations E) (indices.image G.points) := by
  intro z hz
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
  exact hiso j hj

/-- Overlapping sheet lists cover the distinct union without counting a
sheet repeatedly. -/
theorem generic_fiber_lists_cover {n k s : ℕ} {F : AffineFamily.Family n}
    {φ : AffineProjection n k} (G : ComponentGenericFiber F φ)
    (indices : Fin s → Finset (Fin G.r))
    (hcover : ∀ j : Fin G.r, ∃ i, j ∈ indices i) (z : FieldPoint n G.Ω) :
    z ∈ Finset.univ.image G.points ↔ ∃ i, z ∈ (indices i).image G.points := by
  constructor
  · intro hz
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨i, hi⟩ := hcover j
    exact ⟨i, Finset.mem_image.mpr ⟨j, hi, rfl⟩⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)

/-- Evaluation of a bounded polynomial is in the span of the bounded
ordinary monomial columns. Its coefficients stay in the fiber field. -/
theorem field_eval_in_monomial_span {n r : ℕ} {Ω : Type*} [Field Ω]
    (points : Fin r → FieldPoint n Ω) (q : ℕ) (p : FieldPoly n Ω)
    (hp : p.totalDegree ≤ q) :
    (fun i => MvPolynomial.eval (points i) p) ∈
      Submodule.span Ω ((fun a : Fin n →₀ ℕ =>
        fun i => MvPolynomial.eval (points i) (MvPolynomial.monomial a (1 : Ω))) ''
          (simplexExponents n q : Set (Fin n →₀ ℕ))) := by
  let U := Submodule.span Ω ((fun a : Fin n →₀ ℕ =>
    fun i => MvPolynomial.eval (points i) (MvPolynomial.monomial a (1 : Ω))) ''
      (simplexExponents n q : Set (Fin n →₀ ℕ)))
  have he : (fun i => MvPolynomial.eval (points i) p) =
      ∑ a ∈ p.support, p.coeff a •
        (fun i => MvPolynomial.eval (points i) (MvPolynomial.monomial a (1 : Ω))) := by
    ext i
    conv_lhs => rw [p.as_sum, map_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, MvPolynomial.eval_monomial, one_mul]
  rw [he]
  apply Submodule.sum_mem
  intro a ha
  apply U.smul_mem
  apply Submodule.subset_span
  refine ⟨a, ?_, rfl⟩
  exact (mem_simplexExponents a).mpr ((MvPolynomial.le_totalDegree ha).trans hp)

/-- Choose ordinary monomials from a surjective bounded evaluation space.
OAI's finite independent-extension theorem does the column selection. -/
theorem field_monomial_columns {n r : ℕ} {Ω : Type*} [Field Ω]
    (points : Fin r → FieldPoint n Ω) (q : ℕ)
    (hsurj : ∀ w : Fin r → Ω, ∃ p : FieldPoly n Ω, p.totalDegree ≤ q ∧
      (fun i => MvPolynomial.eval (points i) p) = w) :
    ∃ a : Fin r → (Fin n →₀ ℕ), (∀ i, (a i).degree ≤ q) ∧
      LinearIndependent Ω (fun j => fun i =>
        MvPolynomial.eval (points i) (MvPolynomial.monomial (a j) (1 : Ω))) := by
  let v := fun a : Fin n →₀ ℕ =>
    fun i => MvPolynomial.eval (points i) (MvPolynomial.monomial a (1 : Ω))
  let S := simplexExponents n q
  have hspan : Submodule.span Ω (v '' (S : Set (Fin n →₀ ℕ))) = ⊤ := by
    apply top_unique
    intro w hw
    obtain ⟨p, hp, rfl⟩ := hsurj w
    exact field_eval_in_monomial_span points q p hp
  have hrank : r ≤ Module.finrank Ω (Submodule.span Ω (v '' (S : Set (Fin n →₀ ℕ)))) := by
    rw [hspan]
    simp
  obtain ⟨B, _, hBS, hBcard, hBLI⟩ := extend_independent_finset v S ∅
    (Finset.empty_subset _) (by simp) r (by simp) hrank
  let e := (Finset.equivFinOfCardEq hBcard).symm
  refine ⟨fun i => (e i).val, ?_, ?_⟩
  · intro i
    exact (mem_simplexExponents (e i).val).mp (hBS (e i).property)
  · exact hBLI.linearIndependent_restrict.comp e e.injective

theorem generic_fiber_source_columns {n k : ℕ} {F : AffineFamily.Family n}
    {φ : AffineProjection n k} (G : ComponentGenericFiber F φ) (q : ℕ)
    (hsurj : ∀ w : Fin G.r → G.Ω, ∃ p : FieldPoly n G.Ω, p.totalDegree ≤ q ∧
      (fun i => MvPolynomial.eval (G.points i) p) = w) :
    ∃ transverse : Fin G.r → Poly n,
      (∀ i, (transverse i).totalDegree ≤ q) ∧
      LinearIndependent G.Ω (fun i =>
        G.ev (Ideal.Quotient.mk (AffineFamily.locus F).ideal (transverse i))) := by
  obtain ⟨a, hdeg, hLI⟩ := field_monomial_columns G.points q hsurj
  refine ⟨fun i => MvPolynomial.monomial (a i) 1, ?_, ?_⟩
  · intro i
    simpa only [MvPolynomial.totalDegree_monomial (a i) one_ne_zero,
      Finsupp.degree_apply, Finsupp.sum] using hdeg i
  · have he : (fun j => G.ev (Ideal.Quotient.mk (AffineFamily.locus F).ideal
        (MvPolynomial.monomial (a j) (1 : ℂ)))) =
        (fun j => fun i => MvPolynomial.eval (G.points i)
          (MvPolynomial.monomial (a j) (1 : G.Ω))) := by
      funext j i
      rw [G.ev_coordinates]
      simp only [MvPolynomial.eval₂_monomial, map_one, MvPolynomial.eval_monomial, one_mul]
    rw [he]
    exact hLI

end
end DistinctDistances.TrackA
