import DistinctDistances.TrackD.Profiles.EnvelopeCapture
import DistinctDistances.TrackD.Profiles.RankCore
import Mathlib.Data.Nat.Choose.Bounds

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

theorem choose_degree_bound (U h : ℕ) : ((U+h).choose h : ℝ) ≤ (U+1 : ℝ)^h := by
  have hb := Nat.choose_le_sub_pow (U+h) h
  have heq : U + h + 1 - h = U + 1 := by omega
  rw [heq] at hb
  exact_mod_cast hb

/-- Eliminate the selected envelope degree, uniformly over every earlier
testing degree U. Only the ambient-dependent Hilbert constant survives. -/
theorem envelope_rank_comparison (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (T T' : Set (Point d)) (D h : ℕ), 1 ≤ D →
      ∀ F : AffineFamily.Family d, F ⊆ envelopeComponents T D → AffineFamily.IsPure F h →
        T' ⊆ (AffineFamily.locus F).points →
        ∀ U : ℕ, (hilbertOfSet T' U : ℝ) * (c * ((D : ℝ) / (U+1 : ℝ))^h) ≤
          (hilbertOfSet T D : ℝ) := by
  obtain ⟨c, hc, hcompare⟩ := envelope_hilbert_comparison d
  refine ⟨c, hc, ?_⟩
  intro T T' D h hD F hsub hpure hT' U
  obtain ⟨hlo, hup⟩ := hcompare T T' D h hD F hsub hpure hT'
  have hdeg : (0 : ℝ) ≤ AffineFamily.degree F := by
    have hQ : (0 : ℚ) ≤ AffineFamily.degree F := by
      apply Finset.sum_nonneg
      intro V hV
      exact le_trans (by norm_num) (V.one_le_degree (hpure V hV).1.ne_top)
    exact_mod_cast hQ
  have hupper : (hilbertOfSet T' U : ℝ) ≤ (AffineFamily.degree F : ℝ) * (U+1 : ℝ)^h :=
    (hup U).trans (mul_le_mul_of_nonneg_left (choose_degree_bound U h) hdeg)
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hUR : (0 : ℝ) < U + 1 := by positivity
  have h := RankCore.eliminate_degree h hc (by norm_num : (0 : ℝ) < 1)
    hDR hUR hlo (by simpa using hupper)
  simpa only [div_one] using h

theorem floor_half {T : ℝ} (hT : 1 ≤ T) : T / 2 ≤ (⌊T⌋₊ : ℝ) := by
  have hfloor : (1 : ℕ) ≤ ⌊T⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by simpa using hT)
  have hfloorR : (1 : ℝ) ≤ ⌊T⌋₊ := by exact_mod_cast hfloor
  have hlt := Nat.lt_floor_add_one T
  linarith

theorem rounded_rank_ratio {T U : ℝ} (hT : 1 ≤ T) (hU : 1 ≤ U) :
    T / (4*U) ≤ (⌊T⌋₊ : ℝ) / ((⌊U⌋₊ : ℝ) + 1) := by
  have hnum := floor_half hT
  have hden : (⌊U⌋₊ : ℝ) + 1 ≤ 2*U := by
    have hf := Nat.floor_le (by linarith : 0 ≤ U)
    linarith
  calc
    T / (4*U) = (T/2) / (2*U) := by field_simp; ring
    _ ≤ (⌊T⌋₊ : ℝ) / (2*U) := div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (⌊T⌋₊ : ℝ) / ((⌊U⌋₊ : ℝ)+1) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hden

theorem comparison_after_rounding {T U c R R' : ℝ} (hT : 1 ≤ T) (hU : 1 ≤ U)
    (hc : 0 < c) (hR' : 0 ≤ R') (d h : ℕ) (hh : h ≤ d)
    (hcompare : R' * (c * ((⌊T⌋₊ : ℝ) / ((⌊U⌋₊ : ℝ)+1))^h) ≤ R) :
    R' * ((c / (4 : ℝ)^d) * (T/U)^h) ≤ R := by
  have hT0 : 0 ≤ T := by linarith
  have hU0 : 0 < U := by linarith
  have hp : (4 : ℝ)^h ≤ 4^d := pow_le_pow_right₀ (by norm_num) hh
  have hcoef : (c / (4 : ℝ)^d) * (T/U)^h ≤ c * (T/(4*U))^h := by
    calc
      (c / (4 : ℝ)^d) * (T/U)^h = (c * (T/U)^h) / 4^d := by ring
      _ ≤ (c * (T/U)^h) / 4^h :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hp
      _ = c * (T/(4*U))^h := by simp only [div_pow, mul_pow]; ring
  have hratio : c * (T/(4*U))^h ≤
      c * ((⌊T⌋₊ : ℝ) / ((⌊U⌋₊ : ℝ)+1))^h :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (rounded_rank_ratio hT hU) h) hc.le
  exact (mul_le_mul_of_nonneg_left (hcoef.trans hratio) hR').trans hcompare

theorem low_envelope_points_last (X : Piece d) (S : Finset (Pt d)) (D : ℕ) :
    lowEnvelopePoints X S d D = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxS, hxlow⟩ := Finset.mem_filter.mp hx
  have hxenv := subset_envelope (toC '' (S : Set (Pt d))) D ⟨x, hxS, rfl⟩
  rw [AffineVariety.points_components] at hxenv
  obtain ⟨W, hxW⟩ := Set.mem_iUnion.mp hxenv
  have hW : W.variety ∈ envelopeComponents (toC '' (S : Set (Pt d))) D :=
    Finset.mem_image.mpr ⟨W, Finset.mem_univ W, rfl⟩
  exact hxlow W.variety hW (by omega) hxW

/-- The geometric comparison consumed by rank propagation. Both constants and
the density loss are fixed before S; the same S' works for every earlier U. -/
theorem piece_rank_comparison (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (P : Finset (Pt d)) (X : Piece d) (θ ξ K : ℝ),
      0 ≤ θ → 1 ≤ K → PieceGood P θ ξ K X →
      ∀ j : ℕ, j ≤ d → ∀ b : ℝ, OnPlateau X.path.time j ξ b →
        1 ≤ testDeg (cfgB P) X.width b →
        ∀ S ⊆ X.pts, θ * X.pts.card < (S.card : ℝ) →
          ∃ (h : ℕ) (S' : Finset (Pt d)), d-j ≤ h ∧ h ≤ d ∧ S' ⊆ S ∧
            ((S.card : ℝ) - θ * X.pts.card) / (d+1 : ℝ) ≤ S'.card ∧
            ∀ U : ℝ, 1 ≤ U →
              (hilbertOfSet (toC '' (S' : Set (Pt d))) ⌊U⌋₊ : ℝ) *
                (c * (testDeg (cfgB P) X.width b / U)^h) ≤
                  (hilbertOfSet (toC '' (S : Set (Pt d)))
                    ⌊testDeg (cfgB P) X.width b⌋₊ : ℝ) := by
  obtain ⟨c, hc, hcomparison⟩ := envelope_rank_comparison d
  refine ⟨c / (4 : ℝ)^d, by positivity, ?_⟩
  intro P X θ ξ K hθ hK hX j hj b hb hT S hS hpos
  let D := ⌊testDeg (cfgB P) X.width b⌋₊
  have hD : 1 ≤ D := (Nat.le_floor_iff (by linarith)).mpr (by simpa using hT)
  have hlow : ((lowEnvelopePoints X S j D).card : ℝ) ≤ θ * X.pts.card := by
    by_cases hjlt : j < d
    · exact low_envelope_points_bound P X θ ξ K hK hX j hjlt b hb hT S hS
    · have hjeq : j = d := by omega
      rw [hjeq, low_envelope_points_last, Finset.card_empty, Nat.cast_zero]
      positivity
  obtain ⟨h, F, S', hdim, hamb, hFsub, hFpure, hS'sub, hdensity, hS'pts⟩ :=
    dense_envelope_group X S j D hj θ hlow hpos
  refine ⟨h, S', hdim, hamb, hS'sub, hdensity, ?_⟩
  intro U hU
  have hraw := hcomparison (toC '' (S : Set (Pt d))) (toC '' (S' : Set (Pt d)))
    D h hD F hFsub hFpure hS'pts ⌊U⌋₊
  exact comparison_after_rounding hT hU hc (Nat.cast_nonneg _) d h hamb hraw

end
end DistinctDistances.TrackD
