import DistinctDistances.TrackC.BisectionBalance
import DistinctDistances.TrackC.BisectionCount

open Filter
open scoped Topology BigOperators

namespace DistinctDistances.TrackC

/-- Positive limiting evaluations saturate the smoothed sign to +1. -/
theorem bisection_positive_softSign_limit (a : ℕ → ℝ) (A : ℝ) (hA : 0 < A)
    (ha : Tendsto a atTop (𝓝 A)) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    Tendsto (fun n => softSign (((φ n + 1 : ℕ) : ℝ) * a n)) atTop (𝓝 (1 : ℝ)) := by
  have hcast : Tendsto (fun n => (φ n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
  have hn : Tendsto (fun n => ((φ n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa using tendsto_atTop_add_const_right atTop (1 : ℝ) hcast
  exact tendsto_softSign_atTop.comp (hn.atTop_mul_pos hA ha)

/-- Finite simultaneous linear bisection, proved by compact coefficient-sphere limits. -/
theorem bisection_linear_family (d m : ℕ) (S : Fin m → Finset (E d))
    (L : E d → E (m+1) →L[ℝ] ℝ) :
    ∃ c : E (m+1), ‖c‖ = 1 ∧ ∀ j : Fin m,
      (((S j).filter (fun x => 0 < L x c)).card : ℝ) ≤ (S j).card / 2 ∧
      (((S j).filter (fun x => L x c < 0)).card : ℝ) ≤ (S j).card / 2 := by
  classical
  choose c hcNorm hcZero using bisection_zero_imbalance d m S L
  have hmember (n : ℕ) : c n ∈ Metric.sphere (0 : E (m+1)) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hcNorm n
  obtain ⟨a, haSphere, φ, hφ, ha⟩ :=
    (isCompact_sphere (0 : E (m+1)) 1).isSeqCompact.subseq_of_frequently_in
      (Frequently.of_forall hmember)
  have haNorm : ‖a‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using haSphere
  refine ⟨a, haNorm, ?_⟩
  intro j
  let w := fun n x => softSign (((φ n + 1 : ℕ) : ℝ) * L x (c (φ n)))
  have hbal (n : ℕ) : ∑ x ∈ S j, w n x = 0 := by
    have h := congrArg (fun z : E m => z j) (hcZero (φ n))
    simpa [w, bisectionImbalance] using h
  have hvalue (x : E d) : Tendsto (fun n => L x (c (φ n))) atTop (𝓝 (L x a)) :=
    (L x).continuous.continuousAt.tendsto.comp ha
  constructor
  · apply bisection_subset_half d (S j) ((S j).filter (fun x => 0 < L x a))
      (Finset.filter_subset _ _) w hbal
    · intro n x hx
      exact neg_one_le_softSign _
    · intro x hx
      exact bisection_positive_softSign_limit _ _ (Finset.mem_filter.mp hx).2 (hvalue x) φ hφ
  · apply bisection_subset_half d (S j) ((S j).filter (fun x => L x a < 0))
      (Finset.filter_subset _ _) (fun n x => -w n x)
    · intro n
      simpa only [Finset.sum_neg_distrib, hbal, neg_zero]
    · intro n x hx
      exact neg_le_neg (softSign_le_one _)
    · intro x hx
      have h := bisection_positive_softSign_limit
        (fun n => -L x (c (φ n))) (-L x a) (neg_pos.mpr (Finset.mem_filter.mp hx).2)
        (hvalue x).neg φ hφ
      simpa [w, mul_neg] using h

end DistinctDistances.TrackC
