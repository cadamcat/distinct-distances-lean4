import DistinctDistances.TrackE.CommonDepthImages
import DistinctDistances.Foundations.Local
import DistinctDistances.TrackE.LocalMultiplicityAux

/-! Supplying input and finite-list wrappers for the original source projection
budgets, `sc:retained-products.family`, sparse-cones.tex:184–191. -/
namespace DistinctDistances.Request
noncomputable section

/-- Request to track A: smooth points have their actual Hilbert–Samuel multiplicity one.
The existing `TrackA.point_multiplicity_one` only treats a point ideal. -/
theorem common_smooth_multiplicity_one {d : ℕ} (X : AffineVariety d)
    (hX : X.IsIrreducible) (p : Point d) (hp : X.IsSmoothAt p) :
    X.multiplicity p = 1 := by
  exact LocalMultiplicityAux.smooth_multiplicity_one X hX p hp

end
end DistinctDistances.Request

namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

/-- Actual nonempty target charts are fixed on the source before later subfamilies. -/
theorem common_original_list_chart_witnesses {d : ℕ} (i₀ : Fin d)
    (X : AffineVariety d) (hX : X.IsIrreducible) (F : AffineFamily.Family d)
    (hchart : ∀ Y ∈ F, ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0) :
    TrackD.ForGeneralPoint X (fun p => ∀ Y ∈ F, ∃ y ∈ Y, (y - p) i₀ ≠ 0) := by
  have hne := X.points_nonempty_of_isIrreducible hX
  apply TrackD.ForGeneralPoint.finset_all hX hne F
    (fun Y p => ∃ y ∈ Y, (y - p) i₀ ≠ 0)
  intro Y hY
  have hpair := common_product_chart_general i₀ X Y (hchart Y hY)
  have hsrc : TrackD.ForGeneralPoint X
      (fun x => TrackD.ForGeneralPoint Y (fun y => (y - x) i₀ ≠ 0)) :=
    hpair.swap.fiber_right
  apply hsrc.mono
  intro x hx hin
  obtain ⟨y, hy, hxy⟩ := hin.exists
  exact ⟨y, hy, hxy⟩

/-- The complete radial degree is at least one in its original nonempty chart. -/
theorem common_radial_degree_ge_one {d : ℕ} (i₀ : Fin d)
    (Y : AffineVariety d) (hY : Y.IsIrreducible) (p : Point d)
    (hchart : ∃ y ∈ Y, (y - p) i₀ ≠ 0) :
    1 ≤ (radialImage p Y).degree := by
  obtain ⟨y, hy, hi⟩ := hchart
  have hne_p : y ≠ p := by
    intro he
    apply hi
    rw [he]
    simp
  have hactual : ∃ x ∈ Y.points, x ≠ p := ⟨y, hy, hne_p⟩
  have hirr := radialImage_irreducible p Y hY hactual
  have hcoord := common_radial_chart_coordinate_not_mem Y i₀ p ⟨y, hy, hi⟩
  have hhom : (MvPolynomial.X i₀ : Poly d).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X ℂ i₀
  have hslice_irr := TrackA.linearSlice_irreducible (radialImage p Y) hirr _ hhom hcoord
  have hdeg_eq := TrackA.linearSlice_degree (radialImage p Y) hirr _ hhom hcoord
  have hne_top : (TrackA.projectiveLinearSlice (radialImage p Y)
      (MvPolynomial.X i₀)).ideal ≠ ⊤ := hslice_irr.ne_top
  have h1 := AffineVariety.one_le_degree _ hne_top
  rw [hdeg_eq] at h1
  exact h1

end
end DistinctDistances.SparseCones
