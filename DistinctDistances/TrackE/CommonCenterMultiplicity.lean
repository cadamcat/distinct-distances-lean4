import DistinctDistances.TrackE.CommonProjectionInputs

/-! Smooth centers and distinct original equal-dimensional targets,
`sc:retained-products.family`, sparse-cones.tex:184–191. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

theorem common_general_center_multiplicity {d k : ℕ}
    (X Y : AffineVariety d) (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hk : 1 ≤ k) (hXd : X.dimension = k) (hYd : Y.dimension = k) :
    TrackD.ForGeneralPoint X (fun p => Y.multiplicity p ≤ 1) := by
  by_cases heq : X = Y
  · subst Y
    apply (TrackD.general_tangent_finrank X hX).mono
    intro p hp hdim
    have hsmooth : X.IsSmoothAt p :=
      ⟨hp, hdim.trans (X.localDimension_eq_dimension p hX hp).symm⟩
    exact le_of_eq (Request.common_smooth_multiplicity_one X hX p hsmooth)
  · obtain ⟨g, hgY, hgX⟩ := TrackA.equal_dimension_separator X Y hX hY hk hXd hYd heq
    refine ⟨g, GenericFiber.exists_point_of_not_mem X g hgX, ?_⟩
    intro p hp hgp
    have hpY : p ∉ Y := by
      intro hmem
      exact hgp ((TrackD.mem_ideal_iff_eval_zero Y g).1 hgY p hmem)
    rw [Y.multiplicity_eq_zero_off p hpY]
    norm_num

/-- One source open covers every original target, including unused carriers. -/
theorem common_original_list_center_multiplicity {d k : ℕ}
    (X : AffineVariety d) (hX : X.IsIrreducible) (hXd : X.dimension = k)
    (F : AffineFamily.Family d) (hk : 1 ≤ k) (hF : AffineFamily.IsPure F k) :
    TrackD.ForGeneralPoint X (fun p => ∀ Y ∈ F, Y.multiplicity p ≤ 1) := by
  have hne := X.points_nonempty_of_isIrreducible hX
  apply TrackD.ForGeneralPoint.finset_all hX hne F
    (fun Y p => Y.multiplicity p ≤ 1)
  intro Y hY
  have hYirr := (hF Y hY).1
  have hYdim := (hF Y hY).2
  exact common_general_center_multiplicity X Y hX hYirr hk hXd hYdim

end
end DistinctDistances.SparseCones
