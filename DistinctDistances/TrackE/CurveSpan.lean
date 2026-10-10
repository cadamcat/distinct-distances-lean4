import DistinctDistances.TrackE.DirectionalGeometry
import DistinctDistances.TrackE.DirectionFibers

/-!
# The curve case of the small-span direction count

`reduction.tex:197–201`: inside a three-dimensional counted span, a curve either
spans at most a plane (the greedy bound) or has a finite proper linear section
(the light-line bound). Track A supplies only the curve linear-section statement.
-/

namespace DistinctDistances

noncomputable section

namespace Reduction

variable {d : ℕ}

open Classical in
/-- The small-span curve count, conditional on track A's linear-section input.
The degree is track A's actual degree; no alternate variety model is introduced. -/
theorem curve_direction_count_of_small_span (hsections : Request.CurveLinearSections d)
    (P T : Finset (RPoint d)) (p : RPoint d) (Y : ProjectiveVariety d)
    (hY : Y.IsIrreducible) (hdim : Y.dimension = 1) (hT : T ⊆ P)
    (hdir : ∀ q ∈ T, DirMem Y p q) (U : Submodule ℝ (RPoint d))
    (hU : Module.finrank ℝ U ≤ 3) (hTU : ∀ q ∈ T, q - p ∈ U)
    (H K A : ℝ) (hA : 1 ≤ A) (hdegree : 0 ≤ (Y.degree : ℝ))
    (hlight : ∀ q ∈ T, ((P.filter (· ∈ affineSpan ℝ {p, q})).card : ℝ) ≤ H)
    (hgreedy : SpansAtMostPlane Y → (T.card : ℝ) ≤ K * A * (Y.degree : ℝ)) :
    (T.card : ℝ) ≤ (1 + |H| + |K|) * (Y.degree : ℝ) * A := by
  classical
  let C : ℝ := 1 + |H| + |K|
  have hCH : |H| ≤ C := by dsimp [C]; nlinarith [abs_nonneg K]
  have hCK : K ≤ C := by dsimp [C]; nlinarith [le_abs_self K, abs_nonneg H]
  obtain ⟨W, hW, hWU⟩ := exists_complex_span_of_real_subspace U
  rcases hsections Y hY hdim W (hW.trans hU) with hcontained | ⟨F, hFdegree, hF⟩
  · have hspan : SpansAtMostPlane Y := ⟨W, hW.trans hU, hcontained⟩
    calc
      _ ≤ K * A * (Y.degree : ℝ) := hgreedy hspan
      _ ≤ C * A * (Y.degree : ℝ) := by gcongr
      _ = C * (Y.degree : ℝ) * A := by ring
  · have hcover : ∀ q ∈ T, ∃ h : cplx q ≠ cplx p,
        radialProjection (cplx p) (cplx q) h ∈ F := by
      intro q hq
      obtain ⟨hc, hqY⟩ := hdir q hq
      refine ⟨hc, hF _ hqY ?_⟩
      exact radialProjection_submodule_le_of_mem p q hc W (hWU (q - p) (hTU q hq))
    have hcount := card_partners_on_finite_directions_le_degree P T p F |H|
      (Y.degree : ℝ) (abs_nonneg H) hT
      (fun q hq => (hlight q hq).trans (le_abs_self H)) hcover hFdegree
    calc
      _ ≤ |H| * (Y.degree : ℝ) := hcount
      _ ≤ C * (Y.degree : ℝ) := mul_le_mul_of_nonneg_right hCH hdegree
      _ ≤ C * (Y.degree : ℝ) * A := by
        have hC : 0 ≤ C := by dsimp [C]; positivity
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hA (mul_nonneg hC hdegree)

end Reduction

end

end DistinctDistances
