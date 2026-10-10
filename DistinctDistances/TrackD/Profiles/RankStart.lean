import DistinctDistances.TrackD.Profiles.EnvelopeRank
import DistinctDistances.TrackD.Profiles.Clusters

namespace DistinctDistances.TrackD.RankCore

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

theorem hilbert_positive (T : Set (Point d)) (hT : T.Nonempty) (D : ℕ) :
    1 ≤ hilbertOfSet T D := by
  let V := AffineVariety.closure T
  have hproper : V.ideal ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hT
    intro htop
    have hone : (1 : Poly d) ∈ V.ideal := by rw [htop]; trivial
    have hzero := hone x hx
    simpa using hzero
  let v : V.restrictionSpace D := ⟨Ideal.Quotient.mk V.ideal (1 : Poly d),
    ⟨1, OAI.QuarticPowerFree.mem_totalSpace.mpr (by simp), rfl⟩⟩
  have hv : v ≠ 0 := by
    intro h
    have hzero : Ideal.Quotient.mk V.ideal (1 : Poly d) = 0 := congrArg Subtype.val h
    have hone := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    apply hproper
    apply top_unique
    intro f _
    have hmem := V.ideal.mul_mem_left f hone
    simpa only [mul_one] using hmem
  letI : Nontrivial (V.restrictionSpace D) := nontrivial_of_ne v 0 hv
  exact Nat.succ_le_of_lt (Module.finrank_pos (R := ℂ) (M := V.restrictionSpace D))

theorem piece_width_bounds (P : Finset (Pt d)) (X : Piece d) (θ ξ K : ℝ)
    (hd : 0 < d) (hX : PieceGood P θ ξ K X) (hs : 0 < X.width) :
    0 < cfgB P ∧ X.width ≤ Real.log (cfgB P) ∧ 0 < cfgN P ∧ 0 < (X.pts.card : ℝ) := by
  obtain ⟨a, ha⟩ := hX.width_dyadic
  have hpow : (1 : ℝ) ≤ 2^a := one_le_pow₀ (by norm_num)
  have hlog : 0 < Real.log (cfgB P) := by
    rw [ha] at hs
    have hden := pow_pos (by norm_num : (0 : ℝ) < 2) a
    have hprod := mul_pos hs hden
    rw [div_mul_cancel₀ _ hden.ne'] at hprod
    exact hprod
  have hwidth : X.width ≤ Real.log (cfgB P) := by
    rw [ha]
    exact div_le_self hlog.le hpow
  have hN : 0 < cfgN P := by
    by_contra h
    have hz : P.card = 0 := by unfold cfgN at h; norm_cast at h; omega
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hBzero : cfgB P = 0 := by
      unfold cfgB
      rw [hz, Nat.cast_zero, Real.zero_rpow (by positivity : (1 : ℝ) / d ≠ 0)]
    rw [hBzero, Real.log_zero] at hlog
    linarith
  have hB : 0 < cfgB P := Real.rpow_pos_of_pos hN _
  have hn : 0 < (X.pts.card : ℝ) :=
    (mul_pos hN (Real.exp_pos _)).trans_le hX.size
  exact ⟨hB, hwidth, hN, hn⟩

theorem plateau_zero_sigma (B s b : ℝ) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (t : Fin d → ℝ) (ξ : ℝ) (hξ : 0 ≤ ξ) (hb : OnPlateau t 0 ξ b) :
    sigma B s t b = (testDeg B s b)^d := by
  have hmin (i : Fin d) : min (testDeg B s b) (cutScale B s t i) = testDeg B s b := by
    apply min_eq_left
    exact testDeg_mono hB hs (by have := (hb i).2 (Nat.zero_le _); linarith)
  simp only [sigma, hmin, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem sigma_one_start (B s : ℝ) (t : Fin d → ℝ) (a : ℝ)
    (hB : 0 ≤ B) (hs : 0 ≤ s) (hT : testDeg B s a = 1)
    (ha : ∀ i, a ≤ t i) : sigma B s t a = 1 := by
  have hmin (i : Fin d) : min (testDeg B s a) (cutScale B s t i) = 1 := by
    change min (testDeg B s a) (testDeg B s (t i)) = 1
    rw [min_eq_left (testDeg_mono hB hs (ha i)), hT]
  simp only [sigma, hmin, Finset.prod_const, one_pow]

end
end DistinctDistances.TrackD.RankCore
