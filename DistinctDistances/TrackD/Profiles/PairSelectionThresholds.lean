import DistinctDistances.TrackD.Profiles.PartitionPieceTolerance
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace DistinctDistances.TrackD
open Filter
open scoped BigOperators Classical Topology
noncomputable section

theorem pair_selection_good_mono {d : ℕ} (P : Finset (Pt d)) (Q : Partition d)
    (δ θ θ' ξ ξ' K s s' : ℝ) (hθ : θ ≤ θ') (hξ : ξ ≤ ξ') (hs : s' ≤ s)
    (hs0 : 0 ≤ s) (hQ : Q.Good P δ θ ξ K s) : Q.Good P δ θ' ξ' K s' := by
  refine { hQ with core_degree := ?_, pieces_good := ?_, discard := ?_ }
  · exact hQ.core_degree.trans (mul_le_mul_of_nonneg_right hθ (by
      unfold cfgN; positivity))
  · intro X hX
    obtain ⟨hgood, hwidth⟩ := hQ.pieces_good X hX
    have hg := dprofiles2_pieceGood_mono P X hθ (hs0.trans hwidth) hgood
    refine ⟨{ hg with noCapture := ?_ }, hs.trans hwidth⟩
    intro j hj b hb hT g hdeg
    apply hg.noCapture j hj b (fun i => ?_) hT g hdeg
    obtain ⟨hbefore, hafter⟩ := hb i
    constructor
    · intro hi
      have h := hbefore hi
      linarith
    · intro hi
      have h := hafter hi
      linarith
  · exact hQ.discard.trans (mul_le_mul_of_nonneg_right hθ (by
      unfold cfgN; positivity))

/-- Quantitative exclusion of a core of size more than N/4. -/
theorem pair_selection_small_core (N c C θ η : ℝ) (hN : 64 ≤ N)
    (hc : 0 ≤ c) (hcN : c ≤ N) (hC : 0 < C) (hθ : 0 < θ)
    (hθsmall : θ ≤ 1 / (128 * (C + 1))) (hη : η ≤ 1 / 64)
    (hcount : c ^ 2 ≤ 2 * (C * θ * N) * c + η * N ^ 2 + c) : c ≤ N / 4 := by
  have hN0 : 0 ≤ N := by linarith
  have hθmul := (le_div_iff₀ (by positivity : 0 < 128 * (C + 1))).mp hθsmall
  have hCt : 2 * C * θ ≤ 1 / 64 := by nlinarith
  have hmain : 2 * (C * θ * N) * c ≤ (1 / 64) * N ^ 2 := by
    calc
      _ = (2 * C * θ) * (N * c) := by ring
      _ ≤ (1 / 64) * (N * N) := mul_le_mul hCt
        (mul_le_mul_of_nonneg_left hcN hN0) (mul_nonneg hN0 hc) (by norm_num)
      _ = _ := by ring
  have htail := mul_le_mul_of_nonneg_right hη (sq_nonneg N)
  have hcsmall : c ≤ (1 / 64) * N ^ 2 := by nlinarith
  by_contra h
  have hlt : N / 4 < c := lt_of_not_ge h
  have hprod := mul_pos (sub_pos.mpr hlt) (by linarith : 0 < c + N / 4)
  nlinarith

/-- The light-line exponent and flat-cap loss are fixed before the sample. -/
theorem pair_selection_light_threshold (d : ℕ) (hd : 0 < d)
    (ρ c₀ C ε : ℝ) (hρ : 0 < ρ) (hc₀ : 0 < c₀) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ P : Finset (Pt d), N₀ ≤ P.card →
      2 ≤ cfgB P ^ ρ ∧ C * (1 / cfgB P ^ ρ + cfgB P ^ (-c₀)) ≤ ε := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  have h₁ := (tendsto_rpow_neg_atTop (div_pos hρ hdR)).comp hnat
  have h₂ := (tendsto_rpow_neg_atTop (div_pos hc₀ hdR)).comp hnat
  have hsum : Tendsto (fun n : ℕ => C *
      ((n : ℝ) ^ (-(ρ / d)) + (n : ℝ) ^ (-(c₀ / d)))) atTop (𝓝 0) := by
    simpa using (h₁.add h₂).const_mul C
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (show ∀ᶠ n : ℕ in atTop,
      1 ≤ n ∧ (n : ℝ) ^ (-(ρ / d)) ≤ 1 / 2 ∧
        C * ((n : ℝ) ^ (-(ρ / d)) + (n : ℝ) ^ (-(c₀ / d))) ≤ ε from by
    filter_upwards [eventually_ge_atTop 1,
      h₁.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hsum.eventually (Iio_mem_nhds hε)] with n hn h₁n hsn
    exact ⟨hn, h₁n.le, hsn.le⟩)
  refine ⟨N₀, ?_⟩
  intro P hP
  obtain ⟨hN, hsmall, hsum⟩ := hN₀ P.card hP
  have hNp : (0 : ℝ) < P.card := by exact_mod_cast (by omega : 0 < P.card)
  have hBp : 0 < cfgB P := Real.rpow_pos_of_pos hNp _
  have hpow : 0 < cfgB P ^ ρ := Real.rpow_pos_of_pos hBp _
  have hinv : 1 / cfgB P ^ ρ = (P.card : ℝ) ^ (-(ρ / d)) := by
    rw [one_div, ← Real.rpow_neg hBp.le]
    unfold cfgB
    rw [← Real.rpow_mul hNp.le]
    congr 1
    ring
  have hcap : cfgB P ^ (-c₀) = (P.card : ℝ) ^ (-(c₀ / d)) := by
    unfold cfgB
    rw [← Real.rpow_mul hNp.le]
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · rw [← hinv] at hsmall
    have h := (div_le_iff₀ hpow).mp hsmall
    linarith
  · simpa only [hinv, hcap] using hsum

end
end DistinctDistances.TrackD
