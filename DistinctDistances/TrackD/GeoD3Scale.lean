import DistinctDistances.TrackD.GeoD3Cover

/-! Finitary thresholds for the dimension-three terminal estimate. -/

namespace DistinctDistances.TrackD.GeoD3
open Filter
open scoped BigOperators Classical Topology
noncomputable section

 theorem small_constant (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ η > 0, η ≤ 1 ∧ 12*C*η^2 ≤ ε/2 := by
  let η := min 1 (ε/(24*(C+1)))
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := min_le_left _ _
  have ha := (le_div_iff₀ (by positivity : 0 < 24*(C+1))).mp (min_le_right 1 (ε/(24*(C+1))))
  change η*(24*(C+1)) ≤ ε at ha
  have hsq : η^2 ≤ η := by nlinarith
  refine ⟨η, hη, hη1, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 12*C)]

 theorem core_rhs (N M η C K H v ε : ℝ) (hN : 1 ≤ N)
    (hM0 : 0 ≤ M) (hM : M ≤ η * N^((2:ℝ)/3)) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (ha : 12*C*η^2 ≤ ε/2)
    (htail : H*N^(-1:ℝ) + v + K*N^(-(1:ℝ)/9) ≤ ε/2) :
    H*N + N^2*v + 12*C*M*N*(η*N/N^((2:ℝ)/3)) +
      K*N^((5:ℝ)/3)*(η*N/N^((2:ℝ)/3))^((2:ℝ)/3) ≤ ε*N^2 := by
  have hNp : 0 < N := by linarith
  have hAp : 0 < N^((2:ℝ)/3) := Real.rpow_pos_of_pos hNp _
  have hmain : 12*C*M*N*(η*N/N^((2:ℝ)/3)) ≤ (ε/2)*N^2 := by
    calc
      _ ≤ 12*C*(η*N^((2:ℝ)/3))*N*(η*N/N^((2:ℝ)/3)) := by gcongr
      _ = (12*C*η^2)*N^2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right ha (sq_nonneg _)
  have hE : η*N/N^((2:ℝ)/3) ≤ N^((1:ℝ)/3) := by
    calc
      _ ≤ N/N^((2:ℝ)/3) :=
        div_le_div_of_nonneg_right (by nlinarith) hAp.le
      _ = N^(1:ℝ)/N^((2:ℝ)/3) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub hNp]; norm_num
  have hpowers : N^((5:ℝ)/3)*(N^((1:ℝ)/3))^((2:ℝ)/3) = N^2*N^(-(1:ℝ)/9) := by
    rw [← Real.rpow_mul hNp.le, ← Real.rpow_add hNp, ← Real.rpow_natCast, ← Real.rpow_add hNp]
    norm_num
  have htriple : K*N^((5:ℝ)/3)*(η*N/N^((2:ℝ)/3))^((2:ℝ)/3) ≤
      K*N^2*N^(-(1:ℝ)/9) := by
    calc
      _ ≤ K*N^((5:ℝ)/3)*(N^((1:ℝ)/3))^((2:ℝ)/3) := by gcongr
      _ = _ := by rw [mul_assoc, hpowers]; ring
  have hH : H*N = N^2*(H*N^(-1:ℝ)) := by
    rw [Real.rpow_neg_one]
    field_simp
  have htail := mul_le_mul_of_nonneg_left htail (sq_nonneg N)
  rw [hH]
  nlinarith

 theorem tail_threshold (c₀ ε H K : ℝ) (hc₀ : 0 < c₀) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ P : Finset (Pt 3), N₀ ≤ P.card →
      H*(cfgN P)^(-1:ℝ) + cfgB P^(-c₀) + K*(cfgN P)^(-(1:ℝ)/9) ≤ ε/2 := by
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  have h₁ := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).comp hnat
  have h₂ := (tendsto_rpow_neg_atTop (div_pos hc₀ (by norm_num : (0:ℝ)<3))).comp hnat
  have h₃ := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/9)).comp hnat
  have htotal : Tendsto (fun n : ℕ => H*(n:ℝ)^(-1:ℝ) + (n:ℝ)^(-(c₀/3)) +
      K*(n:ℝ)^(-(1:ℝ)/9)) atTop (𝓝 0) := by
    simpa [neg_div, one_div] using ((h₁.const_mul H).add h₂).add (h₃.const_mul K)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (htotal.eventually (Iio_mem_nhds (by positivity : (0:ℝ)<ε/2)))
  refine ⟨N₀, ?_⟩
  intro P hP
  have h := (hN₀ P.card hP).le
  unfold cfgN cfgB
  rw [← Real.rpow_mul (Nat.cast_nonneg _)]
  convert h using 1 <;> ring

end
end DistinctDistances.TrackD.GeoD3
