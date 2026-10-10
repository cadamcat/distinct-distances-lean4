import DistinctDistances.TrackE.Directional
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Complexifying the actual counted span

`reduction.tex:197–201`: a real span of dimension at most three sits in a
complex subspace of dimension at most three. Projective directions of its
displacements sit in the projectivization of that complex subspace.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

namespace Reduction

variable {d : ℕ}

/-- Complexification is real linear, with the existing point models on both sides. -/
def cplxLinearMap : RPoint d →ₗ[ℝ] Point d where
  toFun := cplx
  map_add' := by intro x y; ext i; simp [cplx]
  map_smul' := by intro t x; ext i; simp [cplx]

/-- A real `u`-dimensional subspace is contained in a complex subspace of dimension
at most `u`. Only a real basis and the complex span of its images are needed. -/
theorem exists_complex_span_of_real_subspace (U : Submodule ℝ (RPoint d)) :
    ∃ W : Submodule ℂ (Point d), Module.finrank ℂ W ≤ Module.finrank ℝ U ∧
      ∀ v ∈ U, cplx v ∈ W := by
  classical
  let b := Module.finBasis ℝ U
  let W := Submodule.span ℂ (Set.range fun i => cplx (b i : RPoint d))
  refine ⟨W, ?_, ?_⟩
  · simpa only [W, Set.finrank, Fintype.card_fin] using
      (finrank_range_le_card (R := ℂ) (fun i => cplx (b i : RPoint d)))
  · intro v hv
    have hb : ∑ i, b.repr ⟨v, hv⟩ i • (b i : RPoint d) = v := by
      simpa only [map_sum, map_smul, Submodule.subtype_apply] using
        congrArg U.subtype (b.sum_repr ⟨v, hv⟩)
    have hc := congrArg (fun x : RPoint d => cplxLinearMap x) hb
    rw [map_sum] at hc
    simp only [map_smul] at hc
    change (∑ i, b.repr ⟨v, hv⟩ i • cplx (b i : RPoint d)) = cplx v at hc
    rw [← hc]
    change (∑ i, b.repr ⟨v, hv⟩ i • cplx (b i : RPoint d)) ∈ W.restrictScalars ℝ
    apply (W.restrictScalars ℝ).sum_mem
    intro i _
    apply (W.restrictScalars ℝ).smul_mem
    exact Submodule.subset_span ⟨i, rfl⟩

/-- A displacement in the complex span gives a projective direction submodule in it. -/
theorem radialProjection_submodule_le_of_mem (p q : RPoint d)
    (hq : cplx q ≠ cplx p) (W : Submodule ℂ (Point d))
    (hmem : cplx (q - p) ∈ W) :
    (radialProjection (cplx p) (cplx q) hq).submodule ≤ W := by
  rw [radialProjection, Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]
  have hsub : cplx (q - p) = cplx q - cplx p := by ext i; simp [cplx]
  rwa [hsub] at hmem

end Reduction

end

end DistinctDistances
