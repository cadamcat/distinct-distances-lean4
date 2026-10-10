import DistinctDistances.TrackA.AffineCutHilbertSupport
import DistinctDistances.TrackA.AffinePrimeFiltrationSupport
import OAI.NumberTheory.PiExponent.LocalAlgebra.ComponentMultiplicitySum

namespace DistinctDistances.TrackA
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical BigOperators
open Filter OAI.QuarticPowerFree

theorem affine_hilbert_top {n : ℕ} :
    coordinateHilbert (⊤ : Ideal (Poly n)) = 0 := by
  apply polynomial_eq_of_eventually_nat_eval_eq
  filter_upwards [coordinateHilbert_eventually (⊤ : Ideal (Poly n))] with T hT
  rw [← hT]
  have hz : Module.finrank ℂ (affineFilteredSpace (⊤ : Ideal (Poly n)) T) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [hz]
  simp

theorem coefficient_filtration_telescope (U V : ℕ → ℚ) (N : ℕ)
    (hstep : ∀ i < N, U (i+1) + V i ≤ U i) :
    (∑ i ∈ Finset.range N, V i) + U N ≤ U 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hprev := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    rw [Finset.sum_range_succ]
    have hlast := hstep N (Nat.lt_succ_self _)
    linarith

/-- Affine associativity inequality with actual localized quotient lengths.
All selected components have the degree of the top Hilbert coefficient. -/
theorem affine_component_multiplicity_sum {n : ℕ} {τ : Type*} [Fintype τ]
    (I : Ideal (Poly n)) (k : ℕ) (hdeg : (coordinateHilbert I).natDegree ≤ k)
    (Q : τ → Ideal (Poly n)) (hQ : ∀ a, Q a ∈ I.minimalPrimes)
    (hQinj : Function.Injective Q) (hdim : ∀ a, affineDimension (Q a) = k) :
    ∃ m : τ → ℕ,
      (∀ a, ∀ hprime : (Q a).IsPrime,
        (letI := hprime; Module.length (Localization.AtPrime (Q a))
          (Localization.AtPrime (Q a) ⧸ I.map
            (algebraMap (Poly n) (Localization.AtPrime (Q a))))) = (m a : ℕ∞)) ∧
      (∑ a, (m a : ℚ) * affineDegree (Q a)) ≤
        (k.factorial : ℚ) * (coordinateHilbert I).coeff k := by
  obtain ⟨N, J, f, hmono, hstart, hend, hstep⟩ := affine_cyclic_prime_filtration (Poly n) I
  have hIle : ∀ i, I ≤ J i := fun i => hstart.symm.le.trans
    ((monotone_nat_of_le_succ hmono) (Nat.zero_le i))
  let P : ℕ → Ideal (Poly n) := fun i => (J i).colon {f i}
  have hIP : ∀ i, I ≤ P i := by
    intro i x hx
    apply Submodule.mem_colon_singleton.mpr
    exact (J i).mul_mem_right (f i) (hIle i hx)
  have hJdeg : ∀ i, (coordinateHilbert (J i)).natDegree ≤ k := fun i =>
    (affine_hilbert_degree_mono I (J i) (hIle i)).trans hdeg
  have hPdeg : ∀ i, (coordinateHilbert (P i)).natDegree ≤ k := fun i =>
    (affine_hilbert_degree_mono I (P i) (hIP i)).trans hdeg
  let U : ℕ → ℚ := fun i => (coordinateHilbert (J i)).coeff k
  let W : ℕ → ℚ := fun i => (coordinateHilbert (P i)).coeff k
  have hcoef : ∀ i < N, U (i+1) + W i ≤ U i := by
    intro i hi
    have h := affine_colon_step_coefficient (J i) (f i) k (hJdeg i) (hPdeg i)
    rw [← (hstep i hi).2] at h
    simpa only [U, W, P, add_comm] using h
  have ht := coefficient_filtration_telescope U W N hcoef
  have hUend : U N = 0 := by simp [U, hend, affine_hilbert_top]
  have hUzero : U 0 = (coordinateHilbert I).coeff k := by
    dsimp [U]
    rw [hstart]
  rw [hUend, add_zero, hUzero] at ht
  let m : τ → ℕ := fun a => ∑ i ∈ Finset.range N, if P i = Q a then 1 else 0
  have hm : ∀ a, ∀ hprime : (Q a).IsPrime,
      (letI := hprime; Module.length (Localization.AtPrime (Q a))
        (Localization.AtPrime (Q a) ⧸ I.map
          (algebraMap (Poly n) (Localization.AtPrime (Q a))))) = (m a : ℕ∞) := by
    intro a hprime
    letI := hprime
    have h := OAI.PiExponentJets.W22.localized_cyclic_filtration_length I (Q a) (hQ a)
      J hmono hstart N hend f (fun i hi => (hstep i hi).2) (fun i hi => (hstep i hi).1)
    simpa only [m, P, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using h
  refine ⟨m, hm, ?_⟩
  have hg := OAI.PiExponentJets.W22.grouped_count_weighted_sum_eq N P Q
    (fun a => (k.factorial : ℚ) * (coordinateHilbert (Q a)).coeff k)
  have hsum : (∑ a, (m a : ℚ) * affineDegree (Q a)) =
      ∑ i ∈ Finset.range N, ∑ a,
        if P i = Q a then (k.factorial : ℚ) * (coordinateHilbert (Q a)).coeff k else 0 := by
    calc
      _ = ∑ a, (m a : ℚ) * ((k.factorial : ℚ) * (coordinateHilbert (Q a)).coeff k) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [affineDegree, hdim a]
      _ = _ := hg
  rw [hsum]
  have hgroup : (∑ i ∈ Finset.range N, ∑ a,
      if P i = Q a then (k.factorial : ℚ) * (coordinateHilbert (Q a)).coeff k else 0) ≤
      (k.factorial : ℚ) * ∑ i ∈ Finset.range N, W i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply OAI.PiExponentJets.W22.distinct_selected_factor_weight_le Q hQinj (P i)
      (fun a => (k.factorial : ℚ) * (coordinateHilbert (Q a)).coeff k)
      ((k.factorial : ℚ) * W i)
    · exact mul_nonneg (Nat.cast_nonneg _) (affine_hilbert_coefficient_nonneg (P i) k (hPdeg i))
    · intro a heq
      dsimp [W]
      rw [heq]
  exact hgroup.trans (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _))

end
end DistinctDistances.TrackA
