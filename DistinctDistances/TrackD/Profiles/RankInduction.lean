import DistinctDistances.TrackD.Profiles.RankDensity

namespace DistinctDistances.TrackD.RankCore

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

theorem lower_constant {c μ : ℝ} (hc : 0 < c) (hμ : 0 < μ) :
    ∃ s₀ : ℝ, ∀ s ≥ s₀, Real.exp (-μ*s) ≤ c := by
  obtain ⟨s₀, hs₀⟩ := absorb_constant (show 0 < c⁻¹ by positivity) hμ
  refine ⟨s₀, ?_⟩
  intro s hs
  have h := hs₀ s hs
  have hinv := one_div_le_one_div_of_le (show 0 < c⁻¹ by positivity) h
  simpa only [one_div, inv_inv, ← Real.exp_neg, neg_mul] using hinv

theorem comparison_exp {B s a b μ c R R' : ℝ} (hB : 0 < B)
    (hc : Real.exp (-μ*s) ≤ c) (hR' : 0 ≤ R') (h : ℕ)
    (hcompare : R' * (c * (testDeg B s b / testDeg B s a)^h) ≤ R) :
    R' * Real.exp (((h : ℝ)*(b-a)-μ)*s) ≤ R := by
  have hratio : testDeg B s b / testDeg B s a = Real.exp ((b-a)*s) := by
    rw [testDeg_shift B s a b]
    exact mul_div_cancel_left₀ _ (testDeg_pos hB s a).ne'
  have hexp : Real.exp (((h : ℝ)*(b-a)-μ)*s) =
      Real.exp (-μ*s) * (Real.exp ((b-a)*s))^h := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hc (by positivity)) hR').trans
  simpa only [hratio] using hcompare

theorem plateau_without_margin (t : Fin d → ℝ) (j : ℕ) (ξ b : ℝ) (hξ : 0 ≤ ξ)
    (hb : OnPlateau t j ξ b) : OnPlateau t j 0 b := by
  intro i
  constructor
  · intro hi
    have h := (hb i).1 hi
    linarith
  · intro hi
    have h := (hb i).2 hi
    linarith

set_option maxHeartbeats 1000000 in
/-- Strong induction on the cuts. Density thresholds are fixed in advance;
the envelope-selected subset is fed to the earlier uniform induction hypothesis. -/
theorem rank_induction (d : ℕ) (hd : 0 < d)
    (P : Finset (Pt d)) (X : Piece d) (α μ ξ K c : ℝ)
    (hα : 0 < α) (hμ : 0 < μ) (hξ : 0 < ξ) (hK : 1 ≤ K)
    (hX : PieceGood P (density α d 0 / 2) ξ K X)
    (hs : 1 ≤ X.width) (hc : Real.exp (-μ*X.width) ≤ c)
    (hcompare : ∀ j : ℕ, j ≤ d → ∀ b : ℝ, OnPlateau X.path.time j ξ b →
      1 ≤ testDeg (cfgB P) X.width b →
      ∀ S ⊆ X.pts, (density α d 0 / 2)*X.pts.card < (S.card : ℝ) →
        ∃ (h : ℕ) (S' : Finset (Pt d)), d-j ≤ h ∧ h ≤ d ∧ S' ⊆ S ∧
          ((S.card : ℝ)-(density α d 0 / 2)*X.pts.card)/(d+1 : ℝ) ≤ S'.card ∧
          ∀ U : ℝ, 1 ≤ U →
            (hilbertOfSet (toC '' (S' : Set (Pt d))) ⌊U⌋₊ : ℝ) *
              (c*(testDeg (cfgB P) X.width b / U)^h) ≤
                (hilbertOfSet (toC '' (S : Set (Pt d)))
                  ⌊testDeg (cfgB P) X.width b⌋₊ : ℝ)) :
    ∀ j : ℕ, j ≤ d → ∀ b : ℝ, OnPlateau X.path.time j ξ b →
      1 ≤ testDeg (cfgB P) X.width b →
      ∀ S ⊆ X.pts, density α d j * X.pts.card ≤ (S.card : ℝ) →
        sigma (cfgB P) X.width X.path.time b *
          Real.exp (-((j : ℝ)*(2*(d : ℝ)^2*ξ+μ)+μ)*X.width) ≤
            (hilbertOfSet (toC '' (S : Set (Pt d)))
              ⌊testDeg (cfgB P) X.width b⌋₊ : ℝ) := by
  have hspos : 0 < X.width := by linarith
  obtain ⟨hB, hwidth, hN, hn⟩ := piece_width_bounds P X _ ξ K hd hX hspos
  let B := cfgB P
  let s := X.width
  let q := 2*(d : ℝ)^2*ξ+μ
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hHB (S' : Finset (Pt d)) (hS' : 0 < (S'.card : ℝ)) (U : ℕ) :
      (1 : ℝ) ≤ hilbertOfSet (toC '' (S' : Set (Pt d))) U := by
    have hcard : 0 < S'.card := by exact_mod_cast hS'
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard
    exact_mod_cast hilbert_positive (toC '' (S' : Set (Pt d))) ⟨toC x, x, hx, rfl⟩ U
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj b hb hT S hS hSdense
    have hmin := density_mono hα.le d (Nat.zero_le j)
    have hjpos := density_pos hα d j
    have hpos : (density α d 0 / 2)*X.pts.card < (S.card : ℝ) := by
      nlinarith [mul_pos hjpos hn, mul_le_mul_of_nonneg_right hmin hn.le]
    obtain ⟨h, S', hdim, hamb, hS'S, hS'dense, hcomparison⟩ :=
      hcompare j hj b hb hT S hS hpos
    have hS'pos : 0 < (S'.card : ℝ) :=
      (div_pos (sub_pos.mpr hpos) (by positivity)).trans_le hS'dense
    have hR' : ∀ U, (0 : ℝ) ≤ hilbertOfSet (toC '' (S' : Set (Pt d))) U := fun _ => Nat.cast_nonneg _
    by_cases hjzero : j = 0
    · subst j
      have hheq : h = d := by omega
      have hcR := hcomparison 1 (by norm_num)
      have hlow := hHB S' hS'pos 1
      have hbase : c*(testDeg B s b)^d ≤
          (hilbertOfSet (toC '' (S : Set (Pt d))) ⌊testDeg B s b⌋₊ : ℝ) := by
        have hnonneg : 0 ≤ c*(testDeg B s b)^d := by
          have hcpos : 0 < c := (Real.exp_pos _).trans_le hc
          positivity
        have hh := mul_le_mul_of_nonneg_right hlow hnonneg
        have hcR' : (hilbertOfSet (toC '' (S' : Set (Pt d))) 1 : ℝ) *
            (c*(testDeg B s b)^d) ≤
              (hilbertOfSet (toC '' (S : Set (Pt d))) ⌊testDeg B s b⌋₊ : ℝ) := by
          simpa only [Nat.floor_one, hheq, div_one, B, s] using hcR
        simpa only [one_mul] using hh.trans hcR'
      rw [plateau_zero_sigma B s b hB.le hspos.le X.path.time ξ hξ.le hb]
      have hexp := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (testDeg B s b)^d)
      simpa [B, s, mul_comm] using hexp.trans (by simpa only [mul_comm] using hbase)
    · have hj1 : 1 ≤ j := by omega
      obtain ⟨r, a, z, hrj, ha, hz, haz, hzb, hgap⟩ :=
        preceding_cluster hd X.path.time hX.mono ξ hξ j hj1 hj b hb
      have hSdenseR : density α d r * X.pts.card ≤ (S'.card : ℝ) :=
        selected_density hα hn d j r hj hrj hSdense hS'dense
      have hS'X := hS'S.trans hS
      have hb0 := plateau_without_margin X.path.time j ξ b hξ.le hb
      let R := (hilbertOfSet (toC '' (S : Set (Pt d))) ⌊testDeg B s b⌋₊ : ℝ)
      by_cases hUa : 1 ≤ testDeg B s a
      · let R' := (hilbertOfSet (toC '' (S' : Set (Pt d))) ⌊testDeg B s a⌋₊ : ℝ)
        have hstart := ih r hrj (by omega) a ha hUa S' hS'X hSdenseR
        have hcmp := comparison_exp hB hc (hR' _) h (hcomparison (testDeg B s a) hUa)
        have hstep := propagate_step hB.le hspos.le haz hzb hgap X.path.time j h hj hdim hz hb0
          hstart hcmp
        have hloss : (r : ℝ)*q+μ+μ+(d : ℝ)*(2*(d : ℝ)*ξ) ≤ (j : ℝ)*q+μ := by
          have hrR : (r : ℝ)+1 ≤ j := by exact_mod_cast (show r+1 ≤ j by omega)
          nlinarith [mul_le_mul_of_nonneg_right hrR hq]
        have he := Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (neg_le_neg hloss) hspos.le)
        exact (mul_le_mul_of_nonneg_left he (sigma_nonneg hB.le _ _ _)).trans hstep
      · let a₀ := -Real.log B / s
        have hT0 : testDeg B s a₀ = 1 := by
          have hsne : s ≠ 0 := hspos.ne'
          have heq : a₀*s = -Real.log B := by dsimp [a₀]; field_simp [hsne]
          unfold testDeg
          rw [heq, Real.exp_neg, Real.exp_log hB]
          exact mul_inv_cancel₀ hB.ne'
        have ha₀ : a₀ ≤ -1 := by
          apply (div_le_iff₀ hspos).mpr
          dsimp [B, s] at hwidth ⊢
          linarith
        have ha0lt : a < a₀ := by
          by_contra hn
          have hm := testDeg_mono hB.le hspos.le (le_of_not_gt hn)
          rw [hT0] at hm
          exact hUa hm
        have ha0z : a₀ ≤ z := by
          let i : Fin d := ⟨0, hd⟩
          have ht0 := (hX.time_range i).1
          have htz := (hz i).1 (by dsimp [i]; omega)
          linarith
        have hgap0 : z-a₀ ≤ 2*(d : ℝ)*ξ := by linarith
        have hσ0 : sigma B s X.path.time a₀ = 1 := sigma_one_start B s X.path.time a₀ hB.le
          hspos.le hT0 (fun i => ha₀.trans (hX.time_range i).1)
        have hstart : sigma B s X.path.time a₀ * Real.exp (-μ*s) ≤
            (hilbertOfSet (toC '' (S' : Set (Pt d))) ⌊testDeg B s a₀⌋₊ : ℝ) := by
          rw [hσ0, one_mul, hT0, Nat.floor_one]
          exact (Real.exp_le_one_iff.mpr (by nlinarith)).trans (hHB S' hS'pos 1)
        have hcmp := comparison_exp hB hc (hR' _) h (hcomparison (testDeg B s a₀)
          (by rw [hT0]))
        have hstep := propagate_step hB.le hspos.le ha0z hzb hgap0 X.path.time j h hj hdim hz hb0
          hstart hcmp
        have hloss : μ+μ+(d : ℝ)*(2*(d : ℝ)*ξ) ≤ (j : ℝ)*q+μ := by
          have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
          nlinarith [mul_le_mul_of_nonneg_right hjR hq]
        have he := Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (neg_le_neg hloss) hspos.le)
        exact (mul_le_mul_of_nonneg_left he (sigma_nonneg hB.le _ _ _)).trans hstep

end
end DistinctDistances.TrackD.RankCore
