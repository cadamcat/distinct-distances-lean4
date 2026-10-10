import DistinctDistances.TrackC.SoftSign
import DistinctDistances.OAIInterface.Borsuk

open scoped BigOperators

namespace DistinctDistances.TrackC

/-- The continuous odd imbalance map for a finite collection of point sets. -/
noncomputable def bisectionImbalance (d m : ℕ) (S : Fin m → Finset (E d))
    (L : E d → E (m+1) →L[ℝ] ℝ) (n : ℕ) (c : E (m+1)) : E m :=
  WithLp.toLp 2 (fun j => ∑ x ∈ S j, softSign (((n+1 : ℕ) : ℝ) * L x c))

theorem bisectionImbalance_continuous (d m : ℕ) (S : Fin m → Finset (E d))
    (L : E d → E (m+1) →L[ℝ] ℝ) (n : ℕ) :
    Continuous (bisectionImbalance d m S L n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp
  apply continuous_pi
  intro j
  exact continuous_finset_sum (S j) (fun x hx =>
    softSign_continuous.comp (continuous_const.mul (L x).continuous))

theorem bisectionImbalance_neg (d m : ℕ) (S : Fin m → Finset (E d))
    (L : E d → E (m+1) →L[ℝ] ℝ) (n : ℕ) (c : E (m+1)) :
    bisectionImbalance d m S L n (-c) = -bisectionImbalance d m S L n c := by
  ext j
  simp [bisectionImbalance, mul_neg, Finset.sum_neg_distrib]

/-- Borsuk's dimension bound gives normalized coefficients with zero imbalance. -/
theorem bisection_zero_imbalance (d m : ℕ) (S : Fin m → Finset (E d))
    (L : E d → E (m+1) →L[ℝ] ℝ) (n : ℕ) :
    ∃ c : E (m+1), ‖c‖ = 1 ∧ bisectionImbalance d m S L n c = 0 := by
  classical
  let H := bisectionImbalance d m S L n
  by_contra! hno
  have hnzero : ∀ c : E (m+1), ‖c‖ = 1 → H c ≠ 0 := hno
  let f : E (m+1) → E m := fun c => OAI.BorsukNine.SimplicialChains.unitRadial (H c)
  have hdim : m+1 ≤ m := DistinctDistances.OAIInterface.odd_sphere_dimension_bound
    (m+1) m (by omega) f
    ((OAI.BorsukNine.SimplicialChains.unitRadial_continuousOn
      (S := {z : E m | z ≠ 0}) (fun z hz => hz)).comp
      (bisectionImbalance_continuous d m S L n).continuousOn
      (fun c hc => hnzero c hc))
    (fun c hc => OAI.BorsukNine.SimplicialChains.unitRadial_norm (hnzero c hc))
    (by
      intro c hc
      change OAI.BorsukNine.SimplicialChains.unitRadial (H (-c)) =
        -OAI.BorsukNine.SimplicialChains.unitRadial (H c)
      rw [show H (-c) = -H c from bisectionImbalance_neg d m S L n c]
      exact OAI.BorsukNine.SimplicialChains.unitRadial_neg (H c))
  omega

end DistinctDistances.TrackC
