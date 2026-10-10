import DistinctDistances.TrackC.BisectionSpace

open scoped BigOperators

namespace DistinctDistances.TrackC

/-- A monomial grid gives the degree-space lower bound used at each bisection level. -/
theorem polynomial_space_grid_lower (d k : ℕ) :
    (k+1)^d ≤ Nat.choose (d*k+d) d := by
  classical
  let e : (Fin d → Fin (k+1)) → (Fin d →₀ ℕ) :=
    fun v => Finsupp.equivFunOnFinite.symm (fun i => (v i).val)
  have he : Function.Injective e := by
    intro v w hvw
    funext i
    apply Fin.ext
    have h := congrArg (fun q : Fin d →₀ ℕ => q i) hvw
    simpa [e] using h
  have hdegree (v : Fin d → Fin (k+1)) : (e v).degree ≤ d*k := by
    change (e v).sum (fun _ n => n) ≤ d*k
    rw [Finsupp.sum_fintype]
    · calc
        (∑ i : Fin d, (e v) i) ≤ ∑ _i : Fin d, k := by
          apply Finset.sum_le_sum
          intro i hi
          have h := (v i).isLt
          change (v i).val ≤ k
          omega
        _ = d*k := by simp
    · intro i
      rfl
  have hsub : Finset.univ.image e ⊆ OAI.QuarticPowerFree.simplexExponents d (d*k) := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    exact (OAI.QuarticPowerFree.mem_simplexExponents (e v)).mpr (hdegree v)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ he, Finset.card_univ,
    OAI.QuarticPowerFree.card_simplexExponents] at hcard
  simpa using hcard

/-- The degree needed for the j-th simultaneous bisection grows by blocks of d levels.
Natural division here intentionally means the integer level-block number. -/
theorem bisection_level_dimension (d j : ℕ) (hd : 1 ≤ d) :
    2^j < Nat.choose (d * 2^(j/d+1) + d) d := by
  have hgrid := polynomial_space_grid_lower d (2^(j/d+1))
  have hj : j < d * (j/d+1) := by
    have hmod := Nat.mod_lt j (by omega : 0 < d)
    have hsum := Nat.mod_add_div j d
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hpow : 2^j < (2^(j/d+1))^d := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by simpa [Nat.mul_comm] using hj)
  exact hpow.trans_le ((Nat.pow_le_pow_left (by omega) d).trans hgrid)

end DistinctDistances.TrackC
