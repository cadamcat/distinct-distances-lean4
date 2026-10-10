import DistinctDistances.TrackD.GeoD4Cover
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Scalar thresholds converting the d4 core estimate to a uniform finitary bound. -/

namespace DistinctDistances.TrackD.GeoD4

open Filter
open scoped BigOperators Classical Topology
noncomputable section

theorem small_constants (C₁ C₂ ε : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hε : 0 < ε) :
    ∃ η > 0, 2 * C₁ * η ^ 2 ≤ ε / 4 ∧ Real.sqrt (2 * C₂ * η) ≤ ε / 4 := by
  let η := min 1 (min (ε / (8 * (C₁ + 1))) (ε ^ 2 / (32 * (C₂ + 1))))
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηa : η ≤ ε / (8 * (C₁ + 1)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hηb : η ≤ ε ^ 2 / (32 * (C₂ + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have ha := (le_div_iff₀ (by positivity : 0 < 8 * (C₁ + 1))).mp hηa
  have hb := (le_div_iff₀ (by positivity : 0 < 32 * (C₂ + 1))).mp hηb
  have hsq : η ^ 2 ≤ η := by
    nlinarith [mul_le_mul_of_nonneg_right hη1 hη.le]
  refine ⟨η, hη, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * C₁)]
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ ε / 4)).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith

theorem core_rhs (N A M η C₁ C₂ t ε : ℝ) (hN : 1 ≤ N) (hA : 1 ≤ A)
    (hM0 : 0 ≤ M) (hM : M ≤ η * A) (hη : 0 ≤ η) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (ha : 2 * C₁ * η ^ 2 ≤ ε / 4) (hb : Real.sqrt (2 * C₂ * η) ≤ ε / 4)
    (ht : t ≤ ε / 2) :
    N ^ 2 * t + 2 * C₁ * M * N * (η * N / A) +
        Real.sqrt (2 * C₂ * (η * N / A)) * N ^ ((3 : ℝ) / 2) ≤ ε * N ^ 2 := by
  have hNp : 0 < N := by linarith
  have hAp : 0 < A := by linarith
  have hmain : 2 * C₁ * M * N * (η * N / A) ≤ (ε / 4) * N ^ 2 := by
    calc
      _ ≤ 2 * C₁ * (η * A) * N * (η * N / A) := by gcongr
      _ = (2 * C₁ * η ^ 2) * N ^ 2 := by field_simp <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ha (sq_nonneg _)
  have hE : η * N / A ≤ η * N := div_le_self (by positivity) hA
  have hEs : 2 * C₂ * (η * N / A) ≤ (2 * C₂ * η) * N := by
    nlinarith [mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 2 * C₂)]
  have hpower : Real.sqrt N * N ^ ((3 : ℝ) / 2) = N ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNp]
    norm_num
  have hsqrt : Real.sqrt (2 * C₂ * (η * N / A)) * N ^ ((3 : ℝ) / 2) ≤
      (ε / 4) * N ^ 2 := by
    calc
      _ ≤ Real.sqrt ((2 * C₂ * η) * N) * N ^ ((3 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hEs) (Real.rpow_nonneg hNp.le _)
      _ = Real.sqrt (2 * C₂ * η) * N ^ 2 := by
        rw [Real.sqrt_mul (by positivity), mul_assoc, hpower]
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  have htail := mul_le_mul_of_nonneg_left ht (sq_nonneg N)
  linarith

theorem scales {d : ℕ} (P : Finset (Pt d)) (hP : 1 ≤ P.card) :
    1 ≤ cfgN P ∧ 1 ≤ cfgA P ∧ 0 ≤ cfgM P := by
  have hN : (1 : ℝ) ≤ P.card := by exact_mod_cast hP
  refine ⟨hN, ?_, ?_⟩
  · unfold cfgA
    exact Real.one_le_rpow hN (by positivity)
  · unfold cfgM
    positivity

theorem tail_threshold (d : ℕ) (hd : 4 ≤ d) (c₀ ε : ℝ) (hc₀ : 0 < c₀) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ P : Finset (Pt d), N₀ ≤ P.card → cfgB P ^ (-c₀) ≤ ε / 2 := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have ht := (tendsto_rpow_neg_atTop (div_pos hc₀ hdp)).comp tendsto_natCast_atTop_atTop
  have hhalf : (0 : ℝ) < ε / 2 := by positivity
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds hhalf))
  refine ⟨N₀, ?_⟩
  intro P hP
  have h := (hN₀ P.card hP).le
  dsimp only [Function.comp_apply] at h
  unfold cfgB
  rw [← Real.rpow_mul (Nat.cast_nonneg _)]
  convert h using 1 <;> ring

end
end DistinctDistances.TrackD.GeoD4
