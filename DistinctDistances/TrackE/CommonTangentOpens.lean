import DistinctDistances.TrackE.CommonNormalizationTangents
import DistinctDistances.TrackE.CommonRadialOpenLifting

/-! Fix full original product and radial tangent certificates before
choosing any mixed section or later J, sparse-cones.tex:194–207. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

theorem common_product_general_tangent_opens {d : ℕ} (i₀ : Fin d)
    (X Y : AffineVariety d) (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0) :
    TrackD.ForGeneralPoint X (fun p =>
      TrackD.ForGeneralPoint Y (fun y => commonTangentPair i₀ X Y p y)) := by
  let V := TrackD.productVariety X Y
  let f := TrackD.secantChartNumerator i₀
  let g := TrackD.secantChartDenominator i₀
  have hV := TrackD.productVariety_irreducible X Y hX hY
  have hg : g ∉ V.ideal := common_image_domain_not_mem i₀ X Y hchart
  obtain ⟨_, hgeneric⟩ := TrackD.request_rational_image_generic_tangent V hV f g hg
  have hpair0 : TrackD.ForGeneralPair X Y (fun p y => (y - p) i₀ ≠ 0 ∧
      ((TrackD.productVariety X Y).tangentSpace (TrackD.productPoint p y)).map
        (TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) (TrackD.productPoint p y)) =
        (commonProductImage i₀ X Y).tangentSpace
          (TrackD.productPoint p (TrackD.dirChart (LinearMap.proj i₀) (y - p)))) := by
    apply hgeneric.on_product.mono
    intro p hp y hy hh
    have hi : (y - p) i₀ ≠ 0 := by
      simpa only [g, TrackD.eval_secantChartDenominator] using hh.1
    refine ⟨hi, ?_⟩
    simpa only [V, f, g, commonProductImage, TrackD.rational_secant_label i₀ p y hi]
      using hh.2.1
  apply hpair0.swap.fiber_right.mono
  intro p hp htarget
  obtain ⟨y₀, hy₀, hh₀⟩ := htarget.exists
  have hchartp : ∃ y ∈ Y, (y - p) i₀ ≠ 0 := ⟨y₀, hy₀, hh₀.1⟩
  let fr := commonRadialNumerator p
  let gr := commonRadialDenominator i₀ p
  have hgr : gr ∉ Y.ideal := by
    intro hmem
    exact hh₀.1 (by simpa [gr, commonRadialDenominator, commonRadialNumerator] using
      (TrackD.mem_ideal_iff_eval_zero Y gr).1 hmem y₀ hy₀)
  obtain ⟨_, hradial⟩ := TrackD.request_rational_image_generic_tangent Y hY fr gr hgr
  apply (htarget.and hY hradial).mono
  intro y hy hh
  refine ⟨hh.1.1, hh.1.2, ?_⟩
  have hm := hh.2.2.1
  change (Y.tangentSpace y).map (TrackD.rationalDifferential
    (commonRadialNumerator p) (commonRadialDenominator i₀ p) y) =
    (commonRadialChartImage i₀ p Y).tangentSpace
      (TrackD.rationalPoint (commonRadialNumerator p) (commonRadialDenominator i₀ p) y) at hm
  rw [common_radial_chart_differential, common_radial_chart_point,
    common_radial_chart_image_eq_slice Y hY i₀ p hchartp] at hm
  exact hm

/-- All original targets keep their own good-pair target opens on one
source open. No condition is chosen from a later image subfamily. -/
theorem common_original_list_tangent_opens {d : ℕ} (i₀ : Fin d)
    (X : AffineVariety d) (hX : X.IsIrreducible) (F : AffineFamily.Family d)
    (hF : ∀ Y ∈ F, Y.IsIrreducible)
    (hchart : ∀ Y ∈ F, ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0) :
    TrackD.ForGeneralPoint X (fun p => ∀ Y ∈ F,
      TrackD.ForGeneralPoint Y (fun y => commonTangentPair i₀ X Y p y)) := by
  classical
  have hne : X.points.Nonempty := TrackD.irreducible_points_nonempty X hX
  apply TrackD.ForGeneralPoint.finset_all hX hne F _
  intro Y hY
  exact common_product_general_tangent_opens i₀ X Y hX (hF Y hY) (hchart Y hY)

end
end DistinctDistances.SparseCones
