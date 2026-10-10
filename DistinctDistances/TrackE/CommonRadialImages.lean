import DistinctDistances.TrackE.CommonRadialContainment
import DistinctDistances.TrackD.TripleViewpoint

/-! Complete common projected target images at a general original source,
`sc:retained-products.family`, sparse-cones.tex:158–178. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section
variable {d : ℕ}

/-- Equal complete chart product images have equal complete radial images
on one source open. No degree, dimension or rank premise is required. -/
theorem common_product_images_general_radial_eq (i₀ : Fin d)
    (X Y Y' : AffineVariety d) (hX : X.IsIrreducible)
    (hY : Y.IsIrreducible) (hY' : Y'.IsIrreducible)
    (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0)
    (hchart' : ∃ x ∈ X, ∃ y ∈ Y', (y - x) i₀ ≠ 0)
    (heq : commonProductImage i₀ X Y = commonProductImage i₀ X Y') :
    TrackD.ForGeneralPoint X (fun x => radialImage x Y = radialImage x Y') := by
  have one (Y₁ Y₂ : AffineVariety d) (h₁ : Y₁.IsIrreducible)
      (h₂ : Y₂.IsIrreducible)
      (hchart₂ : ∃ x ∈ X, ∃ y ∈ Y₂, (y - x) i₀ ≠ 0)
      (himage : commonProductImage i₀ X Y₁ = commonProductImage i₀ X Y₂) :
      TrackD.ForGeneralPoint X (fun x =>
        (radialImage x Y₁).Subvariety (radialImage x Y₂)) := by
    let f := TrackD.secantChartNumerator i₀
    let g := TrackD.secantChartDenominator i₀
    obtain ⟨a, ha, hlift⟩ := common_product_image_contains_open i₀ X Y₂ hX h₂ hchart₂
    have ha₂ : a ∉ (commonProductImage i₀ X Y₂).ideal := ha
    have ha₁ : a ∉ (commonProductImage i₀ X Y₁).ideal := by
      rwa [himage]
    have hopen := (TrackD.rational_image_nonzero_open
      (TrackD.productVariety X Y₁) f g a ha₁).on_product
    have hpair : TrackD.ForGeneralPair X Y₁ (fun x y =>
        ∃ hy : y ≠ x, radialProjection x y hy ∈ radialImage x Y₂) := by
      apply hopen.mono
      intro x hx y hy hh
      have hi : (y - x) i₀ ≠ 0 := by
        simpa only [g, TrackD.eval_secantChartDenominator] using hh.1
      let z := TrackD.rationalPoint f g (TrackD.productPoint x y)
      have hz₁ : z ∈ commonProductImage i₀ X Y₁ :=
        TrackD.rationalPoint_mem_image (TrackD.productVariety X Y₁) f g
          (TrackD.productPoint x y) (AffineVariety.subset_closure _ ⟨x, hx, y, hy, rfl⟩) hh.1
      have hz₂ : z ∈ commonProductImage i₀ X Y₂ := by
        rwa [← himage]
      obtain ⟨x', hx', y', hy', hi', hlabel⟩ := hlift z hz₂ hh.2
      have heqLabel : TrackD.productPoint x (TrackD.dirChart (LinearMap.proj i₀) (y - x)) =
          TrackD.productPoint x' (TrackD.dirChart (LinearMap.proj i₀) (y' - x')) := by
        rw [← TrackD.rational_secant_label i₀ x y hi]
        exact hlabel.symm
      obtain ⟨_, hxy, hxy', hdir⟩ := common_equal_labels_direction i₀ x y x' y' hi hi' heqLabel
      refine ⟨hxy, ?_⟩
      rw [hdir]
      exact ProjectiveVariety.subset_closure _ ⟨y', hy', hxy', rfl⟩
    apply hpair.swap.fiber_right.mono
    intro x hx htarget
    exact common_radial_generic_subset Y₁ h₁ x (radialImage x Y₂) htarget
  have hforward := one Y Y' hY hY' hchart' heq
  have hbackward := one Y' Y hY' hY hchart heq.symm
  apply (hforward.and hX hbackward).mono
  intro x hx hh
  exact ProjectiveVariety.ext (le_antisymm hh.2 hh.1)

/-- One common source open for the original finite target list, before
any later image subfamily or density restriction is chosen. -/
theorem common_product_family_radial_eq (i₀ : Fin d)
    (X : AffineVariety d) (hX : X.IsIrreducible) (F : AffineFamily.Family d)
    (hF : ∀ Y ∈ F, Y.IsIrreducible)
    (hchart : ∀ Y ∈ F, ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0) :
    TrackD.ForGeneralPoint X (fun x => ∀ Y ∈ F, ∀ Y' ∈ F,
      commonProductImage i₀ X Y = commonProductImage i₀ X Y' →
        radialImage x Y = radialImage x Y') := by
  classical
  have hne : X.points.Nonempty :=
    AffineVariety.points_nonempty_of_isIrreducible X hX
  obtain ⟨x0, hx0⟩ := hne
  let I := F ×ˢ F
  have hI : ∀ p ∈ I, TrackD.ForGeneralPoint X (fun x =>
      commonProductImage i₀ X p.1 = commonProductImage i₀ X p.2 →
        radialImage x p.1 = radialImage x p.2) := by
    intro p hp
    have hp' : p.1 ∈ F ∧ p.2 ∈ F := Finset.mem_product.mp hp
    have hY := hF p.1 hp'.1
    have hY' := hF p.2 hp'.2
    have hc := hchart p.1 hp'.1
    have hc' := hchart p.2 hp'.2
    by_cases heq : commonProductImage i₀ X p.1 = commonProductImage i₀ X p.2
    · have hgen := common_product_images_general_radial_eq i₀ X p.1 p.2
        hX hY hY' hc hc' heq
      exact hgen.mono (fun x _ h _ => h)
    · exact ⟨1, ⟨x0, hx0, by simp⟩, fun x _ _ hcontra => absurd hcontra heq⟩
  have hall := TrackD.ForGeneralPoint.finset_all hX ⟨x0, hx0⟩ I _ hI
  apply hall.mono
  intro x hx hall Y hYmem Y' hY'mem heq
  exact hall (Y, Y') (Finset.mem_product.mpr ⟨hYmem, hY'mem⟩) heq

end
end DistinctDistances.SparseCones
