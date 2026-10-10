import DistinctDistances.TrackE.CommonMixedInputs

/-! Actual radial labels retain the prescribed original target open,
`sc:retained-products.family`, sparse-cones.tex:194–207. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

theorem common_radial_slice_lifts_target_open {d : ℕ} (i₀ : Fin d)
    (Y : AffineVariety d) (hY : Y.IsIrreducible) (p : Point d)
    (hchart : ∃ y ∈ Y, (y - p) i₀ ≠ 0) (a : Poly d) (ha : a ∉ Y.ideal) :
    ∃ b : Poly d, b ∉ (TrackA.projectiveLinearSlice (radialImage p Y)
      (MvPolynomial.X i₀)).ideal ∧
      ∀ v ∈ TrackA.projectiveLinearSlice (radialImage p Y) (MvPolynomial.X i₀),
        MvPolynomial.eval v b ≠ 0 → ∃ y ∈ Y,
          (y - p) i₀ ≠ 0 ∧ MvPolynomial.eval y a ≠ 0 ∧
            TrackD.dirChart (LinearMap.proj i₀) (y - p) = v := by
  let f := commonRadialNumerator p
  let g := commonRadialDenominator i₀ p
  have hg : g ∉ Y.ideal := by
    intro hmem
    obtain ⟨y, hy, hi⟩ := hchart
    exact hi (by simpa [g, commonRadialDenominator, commonRadialNumerator] using
      (TrackD.mem_ideal_iff_eval_zero Y g).1 hmem y hy)
  letI : Y.ideal.IsPrime := hY
  let K := FractionRing (Poly d ⧸ Y.ideal)
  let φ : Poly d →ₐ[ℂ] K := TrackD.coordinateFieldMap Y.ideal K
  have hφker : RingHom.ker φ = Y.ideal := TrackD.coordinateFieldMap_kernel Y.ideal K
  have hφg : φ g ≠ 0 := by
    intro hz
    exact hg (hφker ▸ RingHom.mem_ker.mpr hz)
  let θ := commonReciprocalEvaluation K φ g
  let P : Ideal (Poly (d + 1)) := RingHom.ker θ
  haveI : P.IsPrime := RingHom.ker_isPrime θ
  let Ψ := commonReciprocalLabelMap f
  have hcomp : θ.comp Ψ = TrackD.rationalFieldPullback K φ f g :=
    common_reciprocal_composition K φ f g
  have hkernel : P.comap Ψ = (commonRadialChartImage i₀ p Y).ideal := by
    calc
      P.comap Ψ = RingHom.ker (θ.comp Ψ) := rfl
      _ = RingHom.ker (TrackD.rationalFieldPullback K φ f g) := by rw [hcomp]
      _ = _ := TrackD.rationalFieldPullback_kernel Y hY K f g hg
  have hcut : commonTailRename a ∉ P := by
    intro hmem
    have hz : θ (commonTailRename a) = 0 := RingHom.mem_ker.mp hmem
    have hφa : φ a = 0 := by
      simpa only [θ, common_reciprocal_tail] using hz
    exact ha (hφker ▸ RingHom.mem_ker.mpr hφa)
  obtain ⟨b, hb, hlift⟩ := ImageOpen.polynomial_point_image_contains_open Ψ P
    (commonTailRename a) hcut
  have hslice := common_radial_chart_image_eq_slice Y hY i₀ p hchart
  refine ⟨b, ?_, ?_⟩
  · rwa [hkernel, hslice] at hb
  · intro v hv hvb
    have hvR : v ∈ commonRadialChartImage i₀ p Y := by rwa [hslice]
    have hvP : ∀ q ∈ P.comap Ψ, MvPolynomial.aeval v q = 0 := by
      intro q hq
      rw [hkernel] at hq
      simpa only [MvPolynomial.aeval_eq_eval] using hvR q hq
    obtain ⟨q, hq, hqa, hcoord⟩ := hlift v hvP (by
      simpa only [MvPolynomial.aeval_eq_eval] using hvb)
    have hy := common_reciprocal_point_source Y K φ hφker g q hq
    obtain ⟨hqg, hrecip⟩ := common_reciprocal_point_denominator K φ g hφg q hq
    have hi : (Fin.tail q - p) i₀ ≠ 0 := by
      simpa [g, commonRadialDenominator, commonRadialNumerator] using hqg
    have hpoint : TrackD.rationalPoint f g (Fin.tail q) = v := by
      funext i
      exact (common_reciprocal_point_label f g q hrecip i).symm.trans (hcoord i)
    refine ⟨Fin.tail q, hy, hi, ?_, ?_⟩
    · simpa only [common_eval_tail_rename] using hqa
    · rw [← common_radial_chart_point i₀ p (Fin.tail q)]
      exact hpoint

end
end DistinctDistances.SparseCones
