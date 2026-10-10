import DistinctDistances.TrackD.TerminalNonlinear
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Finitary thresholds for the line bound and assembly of terminal deletion. -/

namespace DistinctDistances.TrackD.GeoTerminal

open Filter
open scoped Topology BigOperators Classical

noncomputable section

theorem log_decay (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (-a) * (1 + Real.log N) ^ 2)
      atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => 1 / x ^ a) atTop (𝓝 0) := by
    apply (tendsto_rpow_neg_atTop ha).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx, one_div]
  have h1 := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => Real.log x ^ 2 / x ^ a) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) ha).tendsto_div_nhds_zero
  have ht : Tendsto
      (fun x : ℝ => 1 / x ^ a + 2 * (Real.log x / x ^ a) + Real.log x ^ 2 / x ^ a)
      atTop (𝓝 0) := by
    simpa using (h0.add (h1.const_mul 2)).add h2
  have hr : Tendsto (fun x : ℝ => x ^ (-a) * (1 + Real.log x) ^ 2)
      atTop (𝓝 0) := ht.congr' (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx]
    ring)
  exact hr.comp tendsto_natCast_atTop_atTop

theorem cfg_bounds {d : ℕ} (hd : 3 ≤ d) (P : Finset (Pt d))
    (hN : 1 ≤ P.card) :
    0 < cfgA P ∧ cfgA P ≤ cfgN P ∧ 0 ≤ cfgM P ∧ 0 < cfgN P := by
  have hN1 : (1 : ℝ) ≤ P.card := by exact_mod_cast hN
  have hNp : (0 : ℝ) < P.card := by linarith
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have he : (2 : ℝ) / d ≤ 1 := (div_le_one hdp).mpr (by exact_mod_cast (by omega : 2 ≤ d))
  refine ⟨Real.rpow_pos_of_pos hNp _, ?_, ?_, hNp⟩
  · change (P.card : ℝ) ^ ((2 : ℝ) / d) ≤ (P.card : ℝ)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 he
  · unfold cfgM
    positivity

theorem plane_cap {d : ℕ} (hd : 3 ≤ d) (P : Finset (Pt d)) (c₀ : ℝ)
    (hcap : RealFlatCap P c₀) (H : AffineSubspace ℝ (Pt d)) (hH : IsRealPlane H) :
    (occ P H : ℝ) ≤ cfgN P * cfgB P ^ (-c₀) := by
  apply hcap H
  intro htop
  have hdim := hH
  change Module.finrank ℝ H.direction = 2 at hdim
  rw [htop, AffineSubspace.direction_top, finrank_top, finrank_euclideanSpace,
    Fintype.card_fin] at hdim
  omega

theorem cap_factor {d : ℕ} (P : Finset (Pt d)) (c₀ : ℝ) :
    cfgB P ^ (-c₀) = (P.card : ℝ) ^ (-(c₀ / d)) := by
  unfold cfgB
  rw [← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

theorem line_rhs (N A M η C t ε : ℝ) (hN : 0 ≤ N) (hA : 0 < A)
    (hAN : A ≤ N) (hM0 : 0 ≤ M) (hM : M ≤ η * A)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hC : 0 < C)
    (hsmall : η * (1 + 2 * C) ≤ ε / 2) (ht : t ≤ ε / (2 * C)) :
    A * (η * N / A) * N +
        C * (M * N + N ^ 2 * t + N ^ 2 * M ^ 2 / A ^ 2) ≤ ε * N ^ 2 := by
  have hMη : M ≤ η * N := hM.trans (mul_le_mul_of_nonneg_left hAN hη0)
  have hMN : M * N ≤ η * N ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hMη hN]
  have hratio : M / A ≤ η := (div_le_iff₀ hA).mpr hM
  have hratio0 : 0 ≤ M / A := div_nonneg hM0 hA.le
  have hratio2 : (M / A) ^ 2 ≤ η := by nlinarith
  have hsquare : N ^ 2 * M ^ 2 / A ^ 2 ≤ η * N ^ 2 := by
    calc
      _ = N ^ 2 * (M / A) ^ 2 := by ring
      _ ≤ N ^ 2 * η := mul_le_mul_of_nonneg_left hratio2 (sq_nonneg _)
      _ = _ := mul_comm _ _
  have htail : N ^ 2 * t ≤ N ^ 2 * (ε / (2 * C)) :=
    mul_le_mul_of_nonneg_left ht (sq_nonneg _)
  have hmain : A * (η * N / A) * N = η * N ^ 2 := by
    field_simp
  have hcoeff : η * (1 + 2 * C) + C * (ε / (2 * C)) ≤ ε := by
    have heq : C * (ε / (2 * C)) = ε / 2 := by
      field_simp
    rw [heq]
    linarith
  calc
    _ ≤ η * N ^ 2 + C *
        (η * N ^ 2 + N ^ 2 * (ε / (2 * C)) + η * N ^ 2) := by
      rw [hmain]
      gcongr
    _ = (η * (1 + 2 * C) + C * (ε / (2 * C))) * N ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)

theorem lines_small (d : ℕ) (hd : 3 ≤ d) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ ε > 0, ∃ η > 0, ∃ N₀ : ℕ, ∀ P : Finset (Pt d), N₀ ≤ P.card →
      cfgM P ≤ η * cfgA P → RealFlatCap P c₀ →
      ∀ Cf : Pt d → ProjectiveFamily.Family d,
        (∀ p ∈ P, IsDirectionalFamily (Cf p) ∧
          (ProjectiveFamily.degree (Cf p) : ℝ) ≤ η * cfgN P / cfgA P) →
      ∀ (𝒴 : Finset (AffineVariety d)) (S : AffineVariety d → Finset (Pt d)),
        Assignment P 𝒴 S → (∀ Y ∈ 𝒴, IsLine Y → IsRealFlat Y) →
        ((terminalPairsSel P Cf 𝒴 S IsLine).card : ℝ) ≤ ε * cfgN P ^ 2 := by
  obtain ⟨K, C, hK, hC, hlines⟩ := geo_terminal_lines d hd
  intro ε hε
  let η := min (1 / (K + 1)) (min 1 (ε / (2 * (1 + 2 * C))))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηK : η ≤ 1 / (K + 1) := min_le_left _ _
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hηε : η ≤ ε / (2 * (1 + 2 * C)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hKη : K * η ≤ 1 := by
    have h := (le_div_iff₀ (by linarith : 0 < K + 1)).mp hηK
    nlinarith
  have hsmall : η * (1 + 2 * C) ≤ ε / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (1 + 2 * C))).mp hηε
    linarith
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdec := log_decay (c₀ / d) (div_pos hc₀ hdp)
  have hδ : (0 : ℝ) < ε / (2 * C) := by positivity
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hdec.eventually (Iio_mem_nhds hδ))
  refine ⟨η, hη, max N₀ 1, ?_⟩
  intro P hP hM hcap Cf hCf 𝒴 S hS hreal
  have hPN₀ : N₀ ≤ P.card := (le_max_left _ _).trans hP
  have hP1 : 1 ≤ P.card := (le_max_right _ _).trans hP
  obtain ⟨hA, hAN, hM0, hN⟩ := cfg_bounds hd P hP1
  have hKM : K * cfgM P ≤ cfgA P := by
    calc
      _ ≤ K * (η * cfgA P) := mul_le_mul_of_nonneg_left hM hK.le
      _ = (K * η) * cfgA P := by ring
      _ ≤ 1 * cfgA P := mul_le_mul_of_nonneg_right hKη hA.le
      _ = _ := one_mul _
  have hE : 0 ≤ η * cfgN P / cfgA P := by positivity
  have hcount := hlines P (cfgA P) (η * cfgN P / cfgA P)
    (cfgN P * cfgB P ^ (-c₀)) hA hKM hE
    (fun H hH => plane_cap hd P c₀ hcap H hH) Cf hCf 𝒴 S hS hreal
  have ht : cfgB P ^ (-c₀) * (1 + Real.log (cfgN P)) ^ 2 ≤ ε / (2 * C) := by
    rw [cap_factor]
    exact (hN₀ P.card hPN₀).le
  have hrhs := line_rhs (cfgN P) (cfgA P) (cfgM P) η C
    (cfgB P ^ (-c₀) * (1 + Real.log (cfgN P)) ^ 2) ε
    hN.le hA hAN hM0 hM hη.le hη1 hC hsmall ht
  change ((terminalPairsSel P Cf 𝒴 S IsLine).card : ℝ) ≤ _ at hcount
  calc
    _ ≤ _ := hcount
    _ = cfgA P * (η * cfgN P / cfgA P) * cfgN P +
        C * (cfgM P * cfgN P +
          cfgN P ^ 2 * (cfgB P ^ (-c₀) * (1 + Real.log (cfgN P)) ^ 2) +
          cfgN P ^ 2 * cfgM P ^ 2 / cfgA P ^ 2) := by ring
    _ ≤ _ := hrhs

theorem selected_union {d : ℕ} (P : Finset (Pt d))
    (Cf : Pt d → ProjectiveFamily.Family d) (𝒴 : Finset (AffineVariety d))
    (S : AffineVariety d → Finset (Pt d)) :
    terminalPairsSel P Cf 𝒴 S (fun _ => True) =
      terminalPairsSel P Cf 𝒴 S IsLine ∪
        terminalPairsSel P Cf 𝒴 S (fun Y => ¬ IsLine Y) := by
  ext pq
  simp only [terminalPairsSel, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hp, hne, Y, hY, _, hq, hproj⟩
    by_cases hline : IsLine Y
    · exact Or.inl ⟨hp, hne, Y, hY, hline, hq, hproj⟩
    · exact Or.inr ⟨hp, hne, Y, hY, hline, hq, hproj⟩
  · rintro (⟨hp, hne, Y, hY, _, hq, hproj⟩ | ⟨hp, hne, Y, hY, _, hq, hproj⟩)
    · exact ⟨hp, hne, Y, hY, trivial, hq, hproj⟩
    · exact ⟨hp, hne, Y, hY, trivial, hq, hproj⟩

theorem nonlinear_small (d : ℕ) (hd : 3 ≤ d) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ ε > 0, ∃ η > 0, ∃ N₀ : ℕ, ∀ P : Finset (Pt d), N₀ ≤ P.card →
      cfgM P ≤ η * cfgA P → RealFlatCap P c₀ →
      ∀ Cf : Pt d → ProjectiveFamily.Family d,
        (∀ p ∈ P, IsDirectionalFamily (Cf p) ∧
          (ProjectiveFamily.degree (Cf p) : ℝ) ≤ η * cfgN P / cfgA P) →
      ∀ (𝒴 : Finset (AffineVariety d)) (S : AffineVariety d → Finset (Pt d)),
        Assignment P 𝒴 S → (∀ Y ∈ 𝒴, IsCurve Y) →
        ((terminalPairsSel P Cf 𝒴 S (fun Y => ¬ IsLine Y)).card : ℝ) ≤ ε * cfgN P ^ 2 := by
  by_cases h3 : d = 3
  · subst d
    exact geo_terminal_d3 c₀ hc₀
  · exact geo_terminal_d4 d (by omega) c₀ hc₀

end
end DistinctDistances.TrackD.GeoTerminal
