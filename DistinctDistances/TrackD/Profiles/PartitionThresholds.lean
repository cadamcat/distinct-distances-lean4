import DistinctDistances.TrackD.Profiles.Defs

/-! Uniform mass bookkeeping for the fixed finite regularization grid,
`profiles.tex:134–185`. The grid and all threshold weights precede the sample. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

/-- A surviving residual loses at most half the current threshold exponent,
then the sum of later exponents. A previously saturated test keeps its original
node threshold. -/
theorem partition_fragmentation_bound (m n c a r : ℝ)
    (hsize : m * Real.exp (-a / 2 - r) ≤ n)
    (hcapture : c ≤ m * Real.exp (-a)) :
    c ≤ n * Real.exp (-a / 2 + r) := by
  have h := mul_le_mul_of_nonneg_right hsize (Real.exp_nonneg (-a / 2 + r))
  have heq : m * Real.exp (-a / 2 - r) * Real.exp (-a / 2 + r) =
      m * Real.exp (-a) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq] at h
  exact hcapture.trans h

/-- The geometric threshold hierarchy gives the paper's `7/18` exponent. -/
theorem partition_fragmentation_uniform (m n c a r u : ℝ) (hn : 0 ≤ n)
    (hu : u ≤ a) (hr : r ≤ a / 9)
    (hsize : m * Real.exp (-a / 2 - r) ≤ n)
    (hcapture : c ≤ m * Real.exp (-a)) :
    c ≤ n * Real.exp (-7 * u / 18) := by
  calc
    c ≤ n * Real.exp (-a / 2 + r) :=
      partition_fragmentation_bound m n c a r hsize hcapture
    _ ≤ n * Real.exp (-7 * u / 18) := by
      apply mul_le_mul_of_nonneg_left _ hn
      apply Real.exp_le_exp.mpr
      linarith

/-- Multiplicative branch losses add in the exponent; each event is visited
at most once on a trace. -/
theorem partition_trace_mass (n : ℕ) (mass weight : ℕ → ℝ)
    (hstep : ∀ i < n, mass i * Real.exp (-weight i) ≤ mass (i + 1)) :
    mass 0 * Real.exp (-(∑ i ∈ Finset.range n, weight i)) ≤ mass n := by
  have main : ∀ k, k ≤ n →
      mass 0 * Real.exp (-(∑ i ∈ Finset.range k, weight i)) ≤ mass k := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hnext := hstep k (by omega)
        have heq : mass 0 * Real.exp (-(∑ i ∈ Finset.range (k + 1), weight i)) =
            (mass 0 * Real.exp (-(∑ i ∈ Finset.range k, weight i))) *
              Real.exp (-weight k) := by
          rw [Finset.sum_range_succ, neg_add, Real.exp_add]
          ring
        rw [heq]
        exact (mul_le_mul_of_nonneg_right hprev (Real.exp_nonneg _)).trans hnext
  exact main n le_rfl

/-- At a fixed event the parent nodes are disjoint. Summing residual losses
uses the original mass of each parent, without a factor for the number of
parents, batches, or terminal descendants. -/
theorem partition_discard_mass {α ι : Type*} [Fintype ι] (P : Finset α)
    (nodes : ι → Finset (Finset α)) (bad : ι → Finset α → Finset α) (a : ι → ℝ)
    (hsubset : ∀ i, ∀ S ∈ nodes i, S ⊆ P)
    (hdisj : ∀ i, (nodes i : Set (Finset α)).PairwiseDisjoint id)
    (hbad : ∀ i, ∀ S ∈ nodes i,
      ((bad i S).card : ℝ) ≤ Real.exp (-a i / 2) * S.card) :
    (∑ i, ∑ S ∈ nodes i, ((bad i S).card : ℝ)) ≤
      P.card * ∑ i, Real.exp (-a i / 2) := by
  classical
  calc
    _ ≤ ∑ i, Real.exp (-a i / 2) * P.card := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ ∑ S ∈ nodes i, Real.exp (-a i / 2) * S.card :=
          Finset.sum_le_sum (fun S hS => hbad i S hS)
        _ = Real.exp (-a i / 2) * ((nodes i).biUnion id).card := by
          rw [← Finset.mul_sum]
          congr 1
          norm_cast
          exact (Finset.card_biUnion (hdisj i)).symm
        _ ≤ Real.exp (-a i / 2) * P.card := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          exact_mod_cast Finset.card_le_card
            (Finset.biUnion_subset.mpr (fun S hS => hsubset i S hS))
    _ = _ := by rw [← Finset.sum_mul]; ring

end
end DistinctDistances.TrackD
