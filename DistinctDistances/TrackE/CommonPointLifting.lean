import DistinctDistances.TrackE.CommonLiftingInputs
import DistinctDistances.TrackE.CommonImageInputs

/-! Point-level lifting for the actual complete secant product images,
`sc:retained-products.family`, sparse-cones.tex:158–178. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

/-- One nonempty complete-image open lifts to actual source and target
points of the same product in the nonzero secant chart. -/
theorem common_product_image_contains_open {d : ℕ} (i₀ : Fin d)
    (X Y : AffineVariety d) (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0) :
    ∃ h : Poly (d + d), h ∉ (commonProductImage i₀ X Y).ideal ∧
      ∀ z ∈ commonProductImage i₀ X Y, MvPolynomial.eval z h ≠ 0 →
        ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0 ∧
          TrackD.productPoint x (TrackD.dirChart (LinearMap.proj i₀) (y - x)) = z := by
  let V := TrackD.productVariety X Y
  have hV : V.IsIrreducible := TrackD.productVariety_irreducible X Y hX hY
  let f := TrackD.secantChartNumerator i₀
  let g := TrackD.secantChartDenominator i₀
  have hg : g ∉ V.ideal := common_image_domain_not_mem i₀ X Y hchart
  letI : V.ideal.IsPrime := hV
  let K := FractionRing (Poly (d + d) ⧸ V.ideal)
  let φ : Poly (d + d) →ₐ[ℂ] K := TrackD.coordinateFieldMap V.ideal K
  have hφker : RingHom.ker φ = V.ideal := TrackD.coordinateFieldMap_kernel V.ideal K
  have hφg : φ g ≠ 0 := by
    intro hz
    exact hg (hφker ▸ RingHom.mem_ker.mpr hz)
  let θ := commonReciprocalEvaluation K φ g
  let P : Ideal (Poly (d + d + 1)) := RingHom.ker θ
  haveI : P.IsPrime := RingHom.ker_isPrime θ
  let Ψ := commonReciprocalLabelMap f
  have hcomp : θ.comp Ψ = TrackD.rationalFieldPullback K φ f g :=
    common_reciprocal_composition K φ f g
  have hkernel : P.comap Ψ = (TrackD.rationalImage V f g).ideal := by
    calc
      P.comap Ψ = RingHom.ker (θ.comp Ψ) := rfl
      _ = RingHom.ker (TrackD.rationalFieldPullback K φ f g) := by rw [hcomp]
      _ = _ := TrackD.rationalFieldPullback_kernel V hV K f g hg
  have hOne : (1 : Poly (d + d + 1)) ∉ P := by
    change θ 1 ≠ 0
    simpa using (one_ne_zero : (1 : K) ≠ 0)
  obtain ⟨h, hh, hlift⟩ := ImageOpen.polynomial_point_image_contains_open Ψ P 1 hOne
  refine ⟨h, by rwa [hkernel] at hh, ?_⟩
  intro z hz hzh
  have hzP : ∀ a ∈ P.comap Ψ, MvPolynomial.aeval z a = 0 := by
    intro a ha
    rw [hkernel] at ha
    simpa only [MvPolynomial.aeval_eq_eval] using hz a ha
  obtain ⟨q, hq, _, hcoord⟩ := hlift z hzP (by
    simpa only [MvPolynomial.aeval_eq_eval] using hzh)
  have hx := common_reciprocal_point_source V K φ hφker g q hq
  obtain ⟨hxg, hrecip⟩ := common_reciprocal_point_denominator K φ g hφg q hq
  let w : Point (d + d) := Fin.tail q
  have hw : w ∈ TrackD.productVariety X Y := hx
  have hgw : MvPolynomial.eval w g ≠ 0 := hxg
  have hz : TrackD.rationalPoint f g w = z := by
    funext i
    exact (common_reciprocal_point_label f g q hrecip i).symm.trans (hcoord i)
  have hwp : TrackD.productLeft w ∈ X ∧ TrackD.productRight w ∈ Y := by
    change w ∈ (TrackD.productVariety X Y).points at hw
    rwa [TrackD.productVariety_points] at hw
  have hi : (TrackD.productRight w - TrackD.productLeft w) i₀ ≠ 0 := by
    have hgw' : MvPolynomial.eval
        (TrackD.productPoint (TrackD.productLeft w) (TrackD.productRight w)) g ≠ 0 := by
      simpa only [TrackD.productPoint_left_right] using hgw
    simpa only [g, TrackD.eval_secantChartDenominator] using hgw'
  refine ⟨TrackD.productLeft w, hwp.1, TrackD.productRight w, hwp.2, hi, ?_⟩
  rw [← TrackD.rational_secant_label i₀ _ _ hi, TrackD.productPoint_left_right]
  exact hz

end
end DistinctDistances.SparseCones
