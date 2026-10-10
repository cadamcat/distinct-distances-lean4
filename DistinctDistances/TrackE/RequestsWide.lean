import DistinctDistances.TrackD.GenericDepth

/-! Track D request for the strict-dimension generic-list branch.
Supplier: geo:generic-depth, secants.tex:110–219 (the equal-dimension flat
slice is absent when l < k). Consumer: G5.wide, depth.tex:246–281.
Re-exported by Requests.lean to avoid a DepthAssembly import cycle. -/

namespace DistinctDistances.Request

open scoped BigOperators Classical

noncomputable section

/-- In the strict-dimension branch, no equal-dimensional flat slicing or
flat-reality assumptions are needed. The physical assignments and proper-flat
cap remain explicit. -/
theorem generic_depth_strict_dimension (d : ℕ) (hd : 3 ≤ d) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ ε > 0, ∀ ε' > 0, ∃ θ > 0, ∃ w₀ : ℝ, ∀ (P : Finset (TrackD.Pt d)) (w : ℝ),
      w₀ ≤ w → w ≤ Real.log (TrackD.cfgB P) → TrackD.RealFlatCap P c₀ →
      ∀ (k l : ℕ), l < k → 1 ≤ l → k < d → l + 1 < d →
      ∀ (𝒳 𝒴 : Finset (AffineVariety d))
        (S T : AffineVariety d → Finset (TrackD.Pt d)),
        (∀ X ∈ 𝒳, X.IsIrreducible ∧ X.dimension = k) →
        (∀ Y ∈ 𝒴, Y.IsIrreducible ∧ Y.dimension = l) →
        TrackD.Assignment P 𝒳 S → TrackD.Assignment P 𝒴 T →
        TrackD.cfgN P * Real.exp (-θ * w) ≤ TrackD.famMass 𝒳 S →
        TrackD.cfgN P * Real.exp (-θ * w) ≤ TrackD.famMass 𝒴 T →
        ∃ L : AffineVariety d → Finset (AffineVariety d),
          (∀ X ∈ 𝒳, L X ⊆ 𝒴) ∧
          ∑ X ∈ 𝒳, ∑ Y ∈ 𝒴 \ L X, ((S X).card : ℝ) * (T Y).card ≤
            ε' * TrackD.famMass 𝒳 S * TrackD.famMass 𝒴 T ∧
          ∀ X ∈ 𝒳, ∀ Y ∈ L X, TrackD.ForGeneralPair X Y (fun x y =>
            y - x ∉ X.tangentSpace x ∧ y - x ∉ Y.tangentSpace y ∧
            (TrackD.movingRoots (L X) x y).Finite ∧
            ((TrackD.movingRoots (L X) x y).ncard : ℝ) ≤ Real.exp (ε * w)) := by
  intro ε hε ε' hε'
  obtain ⟨θ, hθ, wg, hprune⟩ :=
    TrackD.generic_depth_geometric_pruning_small (d := d) c₀ hc₀ ε' hε'
  refine ⟨θ, hθ, max 1 wg, ?_⟩
  intro P w hw hwB hcap k l hlk hl hkd hld 𝒳 𝒴 S T h𝒳 h𝒴 hS hT hmassX hmassY
  obtain ⟨L, hL, hcost, hgood⟩ := hprune P w ((le_max_right _ _).trans hw) hwB hcap
    k l hkd hld 𝒳 𝒴 S T h𝒳 h𝒴 hS hT hmassX hmassY
  refine ⟨L, hL, hcost, ?_⟩
  intro X hX Y hY
  have hK : ∀ Z ∈ L X, Z.IsIrreducible ∧ Z.dimension = l :=
    fun Z hZ => h𝒴 Z (hL X hX hZ)
  have hne : k ≠ l := Nat.ne_of_gt hlk
  have hR : 1 ≤ Real.exp (ε * w) := by
    apply Real.one_le_exp_iff.mpr
    exact mul_nonneg hε.le
      (le_trans (by norm_num) ((le_max_left _ _).trans hw))
  exact TrackD.generic_depth_moving_roots_of_dichotomy X Y k l hlk.le hl
    (h𝒳 X hX).1 (h𝒳 X hX).2 (L X) hY hK
    (fun Z hZ => (hgood X hX Z hZ).1)
    (fun heq => (hne heq).elim) (Real.exp (ε * w)) hR
    (fun heq => (hne heq).elim)
    (fun Z _ => TrackD.ConstructibleSecants.generic_further_root_dichotomy X Y Z
      (h𝒳 X hX).1 (hK Y hY).1)

end

end DistinctDistances.Request
