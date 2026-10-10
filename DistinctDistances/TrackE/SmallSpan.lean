import DistinctDistances.TrackE.FlatCaps

/-!
# The span-at-most-three branch of the direction count

`reduction.tex:194–197`: for a direction variety of dimension at least two,
the counted partners fit in a flat of dimension at most three. The flat caps
give `O(A²)` occupancy; when the flat is the entire ambient space in dimension
three, `N = A^(3/2) ≤ A²` gives the same bound.
-/

namespace DistinctDistances

noncomputable section

namespace Reduction

variable {d : ℕ}

open Classical in
/-- All real flats of dimension at most three have occupancy at most `C A²` when
`M ≤ A`, uniformly including the full-space case in ambient dimension three. -/
theorem exists_small_flat_quadratic_bound (hd : 3 ≤ d) (hIH : IH d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset (RPoint d)), 1 ≤ P.card →
      Mcount P ≤ Ascale d P.card → ∀ F : AffineSubspace ℝ (RPoint d),
      Module.finrank ℝ F.direction ≤ 3 →
        ((P.filter (· ∈ F)).card : ℝ) ≤ C * Ascale d P.card ^ (2 : ℕ) := by
  classical
  obtain ⟨C₂, hC₂, hplane⟩ := card_inter_plane_le (d := d)
  let C₃ : ℝ := if h : 3 < d then (card_inter_flat_le_of_IH hIH 3 (by omega) h).choose else 1
  have hC₃ : 0 < C₃ := by
    dsimp [C₃]
    split_ifs with h
    · exact (card_inter_flat_le_of_IH hIH 3 (by omega) h).choose_spec.1
    · norm_num
  let C := 2 + C₂ + C₃
  have hC2 : 2 ≤ C := by dsimp [C]; linarith
  have hCplane : C₂ ≤ C := by dsimp [C]; linarith
  have hCthree : C₃ ≤ C := by dsimp [C]; linarith
  refine ⟨C, by linarith, ?_⟩
  intro P hP hMA F hF
  have hN : (1 : ℝ) ≤ P.card := by exact_mod_cast hP
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hA : 1 ≤ Ascale d P.card := Real.one_le_rpow hN (by positivity)
  have hA₀ : 0 ≤ Ascale d P.card := by linarith
  have hM₀ : 0 ≤ Mcount P := by dsimp [Mcount]; positivity
  by_cases hline : Module.finrank ℝ F.direction ≤ 1
  · calc
      _ ≤ 2 * Mcount P - 1 := card_inter_line_le P F hline
      _ ≤ 2 * Ascale d P.card := by linarith
      _ ≤ 2 * Ascale d P.card ^ (2 : ℕ) := by nlinarith
      _ ≤ C * Ascale d P.card ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hC2 (sq_nonneg _)
  · by_cases hdim2 : Module.finrank ℝ F.direction = 2
    · calc
        _ ≤ C₂ * Mcount P ^ ((4 : ℝ) / 3) := hplane P F hdim2
        _ ≤ C₂ * Ascale d P.card ^ ((4 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hM₀ hMA (by norm_num)) hC₂.le
        _ ≤ C₂ * Ascale d P.card ^ (2 : ℕ) := by
          apply mul_le_mul_of_nonneg_left _ hC₂.le
          simpa only [Real.rpow_two] using
            Real.rpow_le_rpow_of_exponent_le hA (by norm_num : (4 : ℝ) / 3 ≤ 2)
        _ ≤ C * Ascale d P.card ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_right hCplane (sq_nonneg _)
    · have hdim3 : Module.finrank ℝ F.direction = 3 := by omega
      by_cases h3d : 3 < d
      · have hflat : ((P.filter (· ∈ F)).card : ℝ) ≤ C₃ * Mcount P ^ ((3 : ℝ) / 2) := by
          simpa only [C₃, dif_pos h3d, Nat.cast_ofNat] using
            (card_inter_flat_le_of_IH hIH 3 (by omega) h3d).choose_spec.2 P F hdim3
        calc
          _ ≤ C₃ * Mcount P ^ ((3 : ℝ) / 2) := hflat
          _ ≤ C₃ * Ascale d P.card ^ ((3 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hM₀ hMA (by norm_num)) hC₃.le
          _ ≤ C₃ * Ascale d P.card ^ (2 : ℕ) := by
            apply mul_le_mul_of_nonneg_left _ hC₃.le
            simpa only [Real.rpow_two] using
              Real.rpow_le_rpow_of_exponent_le hA (by norm_num : (3 : ℝ) / 2 ≤ 2)
          _ ≤ C * Ascale d P.card ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_right hCthree (sq_nonneg _)
      · have hd3 : d = 3 := by omega
        have hNcap : (P.card : ℝ) ≤ Ascale d P.card ^ (2 : ℕ) := by
          have hexp : (2 : ℝ) / d * 2 = 4 / 3 := by rw [hd3]; norm_num
          rw [Ascale, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg P.card)]
          norm_num only [Nat.cast_ofNat]
          rw [hexp]
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (1 : ℝ) ≤ 4 / 3)
        calc
          _ ≤ (P.card : ℝ) := Nat.cast_le.mpr (Finset.card_filter_le _ _)
          _ ≤ Ascale d P.card ^ (2 : ℕ) := hNcap
          _ ≤ C * Ascale d P.card ^ (2 : ℕ) := by
            have hC1 : 1 ≤ C := by linarith
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hC1
              (sq_nonneg (Ascale d P.card))

open Classical in
/-- The occupancy bound applied to the actual span of the counted displacements. -/
theorem exists_small_span_quadratic_bound (hd : 3 ≤ d) (hIH : IH d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset (RPoint d)), 1 ≤ P.card →
      Mcount P ≤ Ascale d P.card → ∀ (p : RPoint d) (T : Finset (RPoint d)),
      T ⊆ P → ∀ U : Submodule ℝ (RPoint d), Module.finrank ℝ U ≤ 3 →
      (∀ q ∈ T, q - p ∈ U) → (T.card : ℝ) ≤ C * Ascale d P.card ^ (2 : ℕ) := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_small_flat_quadratic_bound hd hIH
  refine ⟨C, hC, ?_⟩
  intro P hP hMA p T hTP U hU hTU
  let F := AffineSubspace.mk' p U
  have hsubset : T ⊆ P.filter (· ∈ F) := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨hTP hq,
      AffineSubspace.mem_mk'.mpr (by simpa only [vsub_eq_sub] using hTU q hq)⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsubset)).trans
    (hbound P hP hMA F (by rw [AffineSubspace.direction_mk']; exact hU))

/-- A quadratic bound suffices for every direction-variety dimension at least two
and degree at least one. The degree and dimension are explicit numeric parameters here. -/
theorem direction_bound_of_quadratic_bound (T : Finset (RPoint d)) (C A degree : ℝ)
    (a : ℕ) (hC : 0 ≤ C) (hA : 1 ≤ A) (hdegree : 1 ≤ degree) (ha : 2 ≤ a)
    (hT : (T.card : ℝ) ≤ C * A ^ (2 : ℕ)) :
    (T.card : ℝ) ≤ C * degree * A ^ a := by
  calc
    _ ≤ C * A ^ (2 : ℕ) := hT
    _ ≤ C * A ^ a := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA ha) hC
    _ ≤ C * degree * A ^ a := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith : 0 ≤ A) _)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdegree hC

end Reduction

end

end DistinctDistances
