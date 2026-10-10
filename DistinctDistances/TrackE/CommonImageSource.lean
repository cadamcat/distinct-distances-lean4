import DistinctDistances.TrackE.CommonImageInputs

/-! Recovery of source carriers from complete label images,
`sc:retained-products.family.source`, sparse-cones.tex:158–162. -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- The ideal of the first projection recovers the complete source carrier.
The source is irreducible and the chosen chart has an actual product witness. -/
theorem common_product_image_source_ideal (i₀ : Fin d) (X Y : AffineVariety d)
    (hX : X.IsIrreducible) (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0)
    (f : Poly d) :
    commonSourcePolynomial f ∈ (commonProductImage i₀ X Y).ideal ↔ f ∈ X.ideal := by
  constructor
  · intro hf
    obtain ⟨x₀, hx₀, y₀, hy₀, hi₀⟩ := hchart
    let g : Poly d := MvPolynomial.C (y₀ i₀) - MvPolynomial.X i₀
    have hgeneral : TrackD.ForGeneralPoint X (fun x => MvPolynomial.eval x f = 0) := by
      refine ⟨g, ⟨x₀, hx₀, ?_⟩, ?_⟩
      · simpa only [g, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X,
          Pi.sub_apply] using hi₀
      · intro x hx hnonzero
        have hi : (y₀ - x) i₀ ≠ 0 := by
          simpa only [g, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X,
            Pi.sub_apply] using hnonzero
        have hlabel := common_product_label_mem i₀ X Y x y₀ hx hy₀ hi
        have hz := (TrackD.mem_ideal_iff_eval_zero (commonProductImage i₀ X Y)
          (commonSourcePolynomial f)).mp hf _ hlabel
        simpa only [eval_common_source_polynomial] using hz
    exact (TrackD.mem_ideal_iff_eval_zero X f).mpr
      (TrackD.ForGeneralPoint.eval_zero hX f hgeneral)
  · intro hf
    intro z hz
    obtain ⟨p, hp, hg, rfl⟩ := hz
    have hxy : TrackD.productLeft p ∈ X ∧ TrackD.productRight p ∈ Y := by
      change p ∈ (TrackD.productVariety X Y).points at hp
      rw [TrackD.productVariety_points] at hp
      exact hp
    let x := TrackD.productLeft p
    let y := TrackD.productRight p
    have hp' : TrackD.productPoint x y = p := TrackD.productPoint_left_right p
    rw [← hp'] at hg ⊢
    have hi : (y - x) i₀ ≠ 0 := by
      simpa only [TrackD.eval_secantChartDenominator] using hg
    change MvPolynomial.eval (TrackD.rationalPoint
      (TrackD.secantChartNumerator i₀) (TrackD.secantChartDenominator i₀)
      (TrackD.productPoint x y)) (commonSourcePolynomial f) = 0
    rw [TrackD.rational_secant_label i₀ x y hi, eval_common_source_polynomial]
    exact (TrackD.mem_ideal_iff_eval_zero X f).mp hf x hxy.1

/-- Distinct sources have distinct complete images in every nonempty chart. -/
theorem common_product_source_eq_of_image_eq (i₀ : Fin d)
    (X Y X' Y' : AffineVariety d) (hX : X.IsIrreducible) (hX' : X'.IsIrreducible)
    (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0)
    (hchart' : ∃ x ∈ X', ∃ y ∈ Y', (y - x) i₀ ≠ 0)
    (himage : commonProductImage i₀ X Y = commonProductImage i₀ X' Y') : X = X' := by
  have hideal : (commonProductImage i₀ X Y).ideal =
      (commonProductImage i₀ X' Y').ideal := by
    rw [himage]
  have heq : X.ideal = X'.ideal := by
    ext f
    calc f ∈ X.ideal
        ↔ commonSourcePolynomial f ∈ (commonProductImage i₀ X Y).ideal :=
          (common_product_image_source_ideal i₀ X Y hX hchart f).symm
      _ ↔ commonSourcePolynomial f ∈ (commonProductImage i₀ X' Y').ideal := by
          rw [hideal]
      _ ↔ f ∈ X'.ideal :=
          common_product_image_source_ideal i₀ X' Y' hX' hchart' f
  exact AffineVariety.ext heq

end
end DistinctDistances.SparseCones
