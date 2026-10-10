import DistinctDistances.TrackC.IntrinsicMotionCoordinates
import DistinctDistances.TrackC.RotationCross

namespace DistinctDistances.TrackC

/-- Coordinate-free equations of the rotated canonical motion flat,
motions.tex:315–346; input to global flat and section distinctness. -/
theorem canonical_flat_intrinsic (R : E 3 ≃ₗᵢ[ℝ] E 3)
    (hR : LinearMap.det R.toLinearMap = 1) (s ω d₀ d₁ : ℝ) :
    sixRotate R.symm '' Set.range (canonicalMotionParameter s ω d₀ d₁) =
      {z : E 6 | inner ℝ (motionChartAxis R) (wCoord z) = ω ∧
        motionOrthogonalPart (motionChartAxis R) (cCoord z) =
          motionChartOffset R d₀ d₁+s • cross3 (motionChartAxis R) (wCoord z)} := by
  let a := motionChartAxis R
  let e₂ : E 3 := EuclideanSpace.single (2 : Fin 3) 1
  have hrot (w c : E 3) :
      motionOrthogonalPart a (R.symm c) =
          motionChartOffset R d₀ d₁ + s • cross3 a (R.symm w) ↔
        WithLp.toLp 2 ![c 0, c 1, 0] =
          WithLp.toLp 2 ![d₀, d₁, 0] + s • cross3 e₂ w := by
    constructor
    · intro h
      have h' := congrArg R h
      rw [motionChartOrthogonalPart] at h'
      simp only [map_add, map_smul, motionChartOffset, motionChartAxis_map,
        cross3_rotation R hR, R.apply_symm_apply, a] at h'
      simpa [e₂] using h'
    · intro h
      apply R.injective
      calc
        R (motionOrthogonalPart a (R.symm c)) = WithLp.toLp 2 ![c 0, c 1, 0] := by
          rw [motionChartOrthogonalPart]
          simp [a]
        _ = WithLp.toLp 2 ![d₀, d₁, 0] + s • cross3 e₂ w := h
        _ = R (motionChartOffset R d₀ d₁ + s • cross3 a (R.symm w)) := by
          rw [map_add, map_smul, motionChartOffset, cross3_rotation R hR,
            motionChartAxis_map]
          simp [a, e₂]
  ext z
  constructor
  · rintro ⟨z₀, hz₀, rfl⟩
    rcases hz₀ with ⟨u, rfl⟩
    constructor
    · rw [wCoord_sixRotate, motionChartAxis_inner]
      simp [canonicalMotionParameter, wCoord]
    · rw [cCoord_sixRotate, wCoord_sixRotate]
      apply (hrot (wCoord (canonicalMotionParameter s ω d₀ d₁ u))
        (cCoord (canonicalMotionParameter s ω d₀ d₁ u))).2
      ext i
      fin_cases i <;> simp [canonicalMotionParameter, wCoord, cCoord, cross3, e₂] <;> ring
  · rintro ⟨haxis, horth⟩
    have haxis' : (R (wCoord z)) 2 = ω := by
      simpa only [motionChartAxis_inner] using haxis
    have hcoord :
        WithLp.toLp 2 ![(R (cCoord z)) 0, (R (cCoord z)) 1, 0] =
          WithLp.toLp 2 ![d₀, d₁, 0] +
            s • cross3 e₂ (R (wCoord z)) := by
      apply (hrot (R (wCoord z)) (R (cCoord z))).1
      simpa [a] using horth
    let u : E 3 := WithLp.toLp 2
      ![-(R (wCoord z)) 1, (R (wCoord z)) 0, (R (cCoord z)) 2]
    have hw : wCoord (canonicalMotionParameter s ω d₀ d₁ u) = R (wCoord z) := by
      ext i
      fin_cases i
      · simp [canonicalMotionParameter, wCoord, u]
      · simp [canonicalMotionParameter, wCoord, u]
      · simpa [canonicalMotionParameter, wCoord, u] using haxis'.symm
    have hc : cCoord (canonicalMotionParameter s ω d₀ d₁ u) = R (cCoord z) := by
      ext i
      fin_cases i
      · have h := congrArg (fun c : E 3 => c 0) hcoord
        simpa [canonicalMotionParameter, cCoord, u, cross3, e₂] using h.symm
      · have h := congrArg (fun c : E 3 => c 1) hcoord
        simpa [canonicalMotionParameter, cCoord, u, cross3, e₂] using h.symm
      · simp [canonicalMotionParameter, cCoord, u]
    refine ⟨canonicalMotionParameter s ω d₀ d₁ u, ⟨u, rfl⟩, ?_⟩
    apply six_ext
    · rw [wCoord_sixRotate, hw, R.symm_apply_apply]
    · rw [cCoord_sixRotate, hc, R.symm_apply_apply]

/-- Coordinate-free equations of the full physical graph,
motions.tex:300–314; input to reconstructing the motion from its flat. -/
theorem canonical_graph_intrinsic (R : E 3 ≃ₗᵢ[ℝ] E 3)
    (hR : LinearMap.det R.toLinearMap = 1) (g : Motion 3) (s ω d₀ d₁ : ℝ)
    (hgraph : ∀ x : E 3, ((x+motionConjugate R g x) 2)/2 = s ∧
      ((x-motionConjugate R g x) 0)/2 = d₀-ω*((x+motionConjugate R g x) 1)/2 ∧
      ((x-motionConjugate R g x) 1)/2 = d₁+ω*((x+motionConjugate R g x) 0)/2) :
    ∀ x : E 3,
      inner ℝ (motionChartAxis R) (x+g x) = 2*s ∧
      motionOrthogonalPart (motionChartAxis R) (x-g x) =
        ω • cross3 (motionChartAxis R) (x+g x)+2 • motionChartOffset R d₀ d₁ := by
  intro x
  let e₂ : E 3 := EuclideanSpace.single (2 : Fin 3) 1
  have hconj : motionConjugate R g (R x) = R (g x) := by
    simp
  rcases hgraph (R x) with ⟨hmeanCoord, hdelta₀, hdelta₁⟩
  rw [hconj] at hmeanCoord hdelta₀ hdelta₁
  have hmean : (R (x + g x)) 2 = 2 * s := by
    rw [map_add]
    change ((R x + R (g x)) 2) / 2 = s at hmeanCoord
    nlinarith
  have hdelta₀' : (R (x - g x)) 0 = 2 * d₀ - ω * (R (x + g x)) 1 := by
    rw [map_sub, map_add]
    change ((R x - R (g x)) 0) / 2 =
      d₀ - ω * ((R x + R (g x)) 1) / 2 at hdelta₀
    nlinarith
  have hdelta₁' : (R (x - g x)) 1 = 2 * d₁ + ω * (R (x + g x)) 0 := by
    rw [map_sub, map_add]
    change ((R x - R (g x)) 1) / 2 =
      d₁ + ω * ((R x + R (g x)) 0) / 2 at hdelta₁
    nlinarith
  have hdelta₀'' : (R x - R (g x)) 0 =
      2 * d₀ - ω * ((R x + R (g x)) 1) := by
    simpa only [map_sub, map_add] using hdelta₀'
  have hdelta₁'' : (R x - R (g x)) 1 =
      2 * d₁ + ω * ((R x + R (g x)) 0) := by
    simpa only [map_sub, map_add] using hdelta₁'
  refine ⟨?_, ?_⟩
  · rw [motionChartAxis_inner]
    exact hmean
  · have hrot :
      WithLp.toLp 2 ![(R (x - g x)) 0, (R (x - g x)) 1, 0] =
          ω • cross3 e₂ (R (x + g x)) +
            2 • WithLp.toLp 2 ![d₀, d₁, 0] := by
      ext i
      fin_cases i <;> simp [cross3, e₂, hdelta₀'', hdelta₁''] <;> ring
    apply R.injective
    calc
      R (motionOrthogonalPart (motionChartAxis R) (x - g x)) =
          WithLp.toLp 2 ![(R (x - g x)) 0, (R (x - g x)) 1, 0] := by
        rw [motionChartOrthogonalPart]
        simp
      _ = ω • cross3 e₂ (R (x + g x)) +
          2 • WithLp.toLp 2 ![d₀, d₁, 0] := hrot
      _ = R (ω • cross3 (motionChartAxis R) (x + g x)) +
          R (2 • motionChartOffset R d₀ d₁) := by
        rw [map_smul, map_nsmul, cross3_rotation R hR,
          motionChartAxis_map, motionChartOffset]
        simp [e₂]
      _ = R (ω • cross3 (motionChartAxis R) (x + g x) +
          2 • motionChartOffset R d₀ d₁) := by rw [map_add]

end DistinctDistances.TrackC
