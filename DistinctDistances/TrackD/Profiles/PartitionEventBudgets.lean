import DistinctDistances.TrackD.Profiles.PartitionThresholds

/-! Tail budgets for the finite event ordering in the regularization tree,
`profiles.tex:134–166`. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

def partitionEventTail (a : Fin K → ℝ) (q : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin K => q ≤ i.val), a i

theorem partition_event_tail_nonneg (a : Fin K → ℝ) (ha : ∀ i, 0 ≤ a i) (q : ℕ) :
    0 ≤ partitionEventTail a q :=
  Finset.sum_nonneg (fun i hi => ha i)

theorem partition_event_tail_antitone (a : Fin K → ℝ) (ha : ∀ i, 0 ≤ a i)
    (q r : ℕ) (hqr : q ≤ r) : partitionEventTail a r ≤ partitionEventTail a q := by
  unfold partitionEventTail
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    obtain ⟨hi, hr⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hi, hqr.trans hr⟩
  · intro i hi hnot
    exact ha i

theorem partition_event_tail_succ (a : Fin K → ℝ) (q : ℕ) (hq : q < K) :
    partitionEventTail a q = a ⟨q, hq⟩ + partitionEventTail a (q + 1) := by
  classical
  have hset : Finset.univ.filter (fun i : Fin K => q ≤ i.val) =
      insert ⟨q, hq⟩ (Finset.univ.filter (fun i : Fin K => q + 1 ≤ i.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff, Fin.val_mk]
    omega
  have hnot : (⟨q, hq⟩ : Fin K) ∉ Finset.univ.filter (fun i : Fin K => q + 1 ≤ i.val) := by
    simp
  unfold partitionEventTail
  rw [hset, Finset.sum_insert hnot]

theorem partition_event_child_mass (a : Fin K → ℝ) (q : ℕ) (hq : q < K)
    (m n : ℝ) (hchild : m * Real.exp (-a ⟨q, hq⟩) ≤ n) :
    m * Real.exp (-partitionEventTail a q) ≤
      n * Real.exp (-partitionEventTail a (q + 1)) := by
  have h := mul_le_mul_of_nonneg_right hchild (Real.exp_nonneg (-partitionEventTail a (q + 1)))
  rw [partition_event_tail_succ a q hq]
  convert h using 1
  rw [neg_add, Real.exp_add]
  ring

theorem partition_event_residual_mass (a : Fin K → ℝ) (ha : ∀ i, 0 ≤ a i)
    (q r : ℕ) (hq : q < K) (hr : q + 1 ≤ r)
    (m n leaf : ℝ) (hn : 0 ≤ n)
    (hresidual : m * Real.exp (-a ⟨q, hq⟩ / 2) ≤ n)
    (hleaf : n * Real.exp (-partitionEventTail a r) ≤ leaf) :
    m * Real.exp (-a ⟨q, hq⟩ / 2 - partitionEventTail a (q + 1)) ≤ leaf := by
  calc
    _ = (m * Real.exp (-a ⟨q, hq⟩ / 2)) *
        Real.exp (-partitionEventTail a (q + 1)) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ n * Real.exp (-partitionEventTail a (q + 1)) :=
      mul_le_mul_of_nonneg_right hresidual (Real.exp_nonneg _)
    _ ≤ n * Real.exp (-partitionEventTail a r) := by
      apply mul_le_mul_of_nonneg_left _ hn
      exact Real.exp_le_exp.mpr (neg_le_neg (partition_event_tail_antitone a ha (q + 1) r hr))
    _ ≤ leaf := hleaf

end
end DistinctDistances.TrackD
