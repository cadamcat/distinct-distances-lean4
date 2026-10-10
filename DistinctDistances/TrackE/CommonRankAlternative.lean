import DistinctDistances.TrackE.CommonLabelGroup

/-! The plateau alternative of the common label rank, sparse-cones.tex:239–306. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- sc:common-rank.plateau (sparse-cones.tex:239–306). Physical regularity
before `τ`, retained products (`k < d-1`) or the hypersurface case
(`k = d-1`), product testing into the degree-`⌊T_s(τ)⌋` label envelope,
grouping of envelope components by dimension, the Hilbert bounds of one
group, and the retained image mass for the equal-dimension group. -/
theorem common_rank_envelope_alternative {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (j : ℕ) (hj : j + 1 < d) (τ : ℝ)
    (hτ : M.b ⟨j, by omega⟩ < τ ∧ τ < M.b ⟨j + 1, hj⟩) :
    CommonRankAlternative M j τ := by
  obtain ⟨c, hc, hrank⟩ := common_label_group_rank d
  refine ⟨c, hc, fun θ hθ ρ hρ => ?_⟩
  filter_upwards [common_label_dense_group T M j hj τ hτ θ hθ ρ hρ] with i hi
  intro i₀ Γ hΓ hchart hdense
  obtain ⟨h, hh1, hh2, Γ', hΓ', hdense', hlabels, hdeg⟩ := hi i₀ Γ hΓ hchart hdense
  set L := ⌊TrackD.testDeg (regime.B i) (M.s i) τ⌋₊ with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef]
    exact Nat.le_floor (by
      simpa using common_plateau_test_degree_ge_one M ⟨j, by omega⟩ τ hτ.1 i)
  obtain ⟨hlow, hup⟩ := hrank i₀ Γ L hL h
  refine ⟨h, hh1, hh2, Γ', hΓ', hdense', ?_⟩
  have hpow : 0 ≤ (L : ℝ) ^ h := by positivity
  rcases eq_or_lt_of_le hh1 with heq | hlt
  · left
    refine ⟨heq.symm, ?_⟩
    have hd := hdeg heq.symm
    calc c * commonEqualDimLower M i j * Real.exp (-θ * M.s i) * (L : ℝ) ^ h
        = c * (commonEqualDimLower M i j * Real.exp (-θ * M.s i)) * (L : ℝ) ^ h := by ring
      _ ≤ c * ((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ) * (L : ℝ) ^ h := by
          gcongr
      _ ≤ _ := hlow
  · right
    refine ⟨hlt, fun E => ?_⟩
    have hu := hup Γ' hlabels E
    have hchoose : (0 : ℝ) ≤ ((E + h).choose h : ℝ) := Nat.cast_nonneg _
    calc c * (commonLabelRank i₀ Γ' E : ℝ) * (L : ℝ) ^ h
        ≤ c * (((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ) *
            ((E + h).choose h : ℝ)) * (L : ℝ) ^ h := by gcongr
      _ = (c * ((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ) * (L : ℝ) ^ h) *
            ((E + h).choose h : ℝ) := by ring
      _ ≤ (commonLabelRank i₀ Γ L : ℝ) * ((E + h).choose h : ℝ) :=
          mul_le_mul_of_nonneg_right hlow hchoose

end
end DistinctDistances.SparseCones
