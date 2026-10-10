import DistinctDistances.TrackD.Profiles.PartitionGrid

/-! The initial outer window has no inherited lower-boundary hypothesis.
Below time -1 its admissible tests have degree less than one, so they capture
no points. This is distinct from the inherited boundary of later windows,
`profiles.tex:85–90, 196–206`. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

theorem partition_constant_capture_empty (π : CutPath d) (S : Finset (Pt d))
    (g : Poly d) (hdegree : (g.totalDegree : ℝ) < 1) : π.captured 0 S g = ∅ := by
  classical
  have hdegreeNat : g.totalDegree < 1 := by exact_mod_cast hdegree
  have hzeroDegree : g.totalDegree = 0 := by omega
  have hconstant : g = MvPolynomial.C (g.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzeroDegree
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxS, hxg, hproper⟩ := Finset.mem_filter.mp hx
  have hcoeff : g.coeff 0 = 0 := by
    rw [hconstant] at hxg
    simpa only [MvPolynomial.eval_C] using hxg
  have hgzero : g = 0 := by rw [hconstant, hcoeff]; simp
  let Z : AffineVariety d := AffineVariety.whole
  have hZideal : Z.ideal = ⊥ := Ideal.radical_bot_of_isReduced
  have hsys : π.system 0 = ⊥ := by simp [CutPath.system]
  have hZ : Z ∈ π.localCarriers 0 (toC x) := by
    constructor
    · change Z.ideal ∈ (π.system 0).minimalPrimes
      rw [hsys, hZideal, Ideal.minimalPrimes_eq_subsingleton_self]
      simp
    · change toC x ∈ MvPolynomial.zeroLocus ℂ Z.ideal
      rw [hZideal]
      intro f hf
      have hfzero := Ideal.mem_bot.mp hf
      simp [hfzero]
  exact hproper Z hZ (hgzero.symm ▸ Z.ideal.zero_mem)

theorem partition_degree_absorption_strict (B s a b ξ K : ℝ)
    (hB : 0 < B) (hs : 0 ≤ s) (hK : 0 < K)
    (hgap : a + ξ / 4 ≤ b) (hlarge : Real.log K < ξ / 4 * s) :
    K * testDeg B s a < testDeg B s b := by
  rw [RankCore.testDeg_shift B s a b]
  have hfactor : K < Real.exp ((b - a) * s) := by
    rw [← Real.exp_log hK]
    apply Real.exp_lt_exp.mpr
    exact hlarge.trans_le (mul_le_mul_of_nonneg_right (by linarith) hs)
  simpa only [mul_comm K] using mul_lt_mul_of_pos_left hfactor (RankCore.testDeg_pos hB s a)

/-- Every admissible low test in the outermost window is a constant. -/
theorem partition_outer_low_capture (π : CutPath d) (S : Finset (Pt d))
    (B ξ K : ℝ) (hB : 1 < B) (hK : 1 ≤ K)
    (hlarge : Real.log K < ξ / 4 * Real.log B)
    (b : ℝ) (hb : b + ξ / 4 ≤ -1) (g : Poly d)
    (hg : (g.totalDegree : ℝ) ≤ K * testDeg B (Real.log B) b) :
    π.captured 0 S g = ∅ := by
  have hBpos : 0 < B := by linarith
  have hbase : testDeg B (Real.log B) (-1) = 1 := by
    simp only [testDeg, neg_one_mul, Real.exp_neg, Real.exp_log hBpos]
    exact mul_inv_cancel₀ hBpos.ne'
  apply partition_constant_capture_empty π S g
  have hstrict := partition_degree_absorption_strict B (Real.log B) b (-1) ξ K
    hBpos (Real.log_pos hB).le (by linarith) hb hlarge
  rw [hbase] at hstrict
  exact hg.trans_lt hstrict

end
end DistinctDistances.TrackD
