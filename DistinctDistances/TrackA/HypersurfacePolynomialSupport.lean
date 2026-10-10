import DistinctDistances.TrackA.HypersurfaceJetsSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators
open OAI.PiExponentJets.W32

theorem choose_difference_sum (n s t : ℕ) (hn : 0 < n) (hst : s ≤ t) :
    (t+n).choose n - (t-s+n).choose n =
      ∑ j ∈ Finset.range s, (t-j+(n-1)).choose (n-1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have ih' := ih (by omega)
    rw [Finset.sum_range_succ, ← ih']
    have hstep := Nat.choose_succ_left (t-(s+1)+n) n hn
    have harg : t-(s+1)+n+1 = t-s+n := by omega
    have harg' : t-(s+1)+n = t-s+(n-1) := by omega
    rw [harg] at hstep
    rw [harg'] at hstep
    have hle : (t-s+n).choose n ≤ (t+n).choose n := Nat.choose_le_choose n (by omega)
    rw [harg']
    omega

def hypersurfaceJetPolynomial (n s : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range s, Polynomial.taylor (-(j : ℚ)) (polynomialGrowth (n-1))

theorem hypersurfaceJetPolynomial_degree_le (n s : ℕ) :
    (hypersurfaceJetPolynomial n s).natDegree ≤ n-1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  simpa using (polynomialGrowth_natDegree (n-1)).le

theorem hypersurfaceJetPolynomial_coeff (n s : ℕ) :
    (hypersurfaceJetPolynomial n s).coeff (n-1) = (s : ℚ) * ((n-1).factorial : ℚ)⁻¹ := by
  unfold hypersurfaceJetPolynomial
  rw [Polynomial.finsetSum_coeff]
  have hc (j : ℕ) :
      (Polynomial.taylor (-(j : ℚ)) (polynomialGrowth (n-1))).coeff (n-1) =
        ((n-1).factorial : ℚ)⁻¹ := by
    rw [OAI.QuarticPowerFree.coeff_taylor_high _ _ _ (polynomialGrowth_natDegree (n-1)).le]
    simpa only [Polynomial.leadingCoeff, polynomialGrowth_natDegree] using
      polynomialGrowth_leadingCoeff (n-1)
  simp_rw [hc]
  simp

theorem hypersurfaceJetPolynomial_eval (n s t : ℕ) (hn : 0 < n) (hst : s ≤ t) :
    (hypersurfaceJetPolynomial n s).eval (t : ℚ) =
      (((t+n).choose n - (t-s+n).choose n : ℕ) : ℚ) := by
  rw [choose_difference_sum n s t hn hst, Nat.cast_sum]
  unfold hypersurfaceJetPolynomial
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjt : j ≤ t := by have := Finset.mem_range.mp hj; omega
  rw [Polynomial.taylor_eval]
  have hcast : (t : ℚ) + -(j : ℚ) = ((t-j : ℕ) : ℚ) := by
    rw [Nat.cast_sub hjt]
    ring
  rw [hcast, polynomialGrowth_eval]

end
end DistinctDistances.TrackA
