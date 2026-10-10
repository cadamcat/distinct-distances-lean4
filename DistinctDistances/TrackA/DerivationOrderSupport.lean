import DistinctDistances.TrackA.Definitions

namespace DistinctDistances.TrackA
noncomputable section

/-- A derivation loses at most one power of any ideal. This is the
local polynomial order estimate consumed by the polar construction. -/
theorem derivation_mem_pow {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (I : Ideal A) (r : ℕ) (f : A)
    (hf : f ∈ I^(r+1)) : D f ∈ I^r := by
  induction r generalizing f with
  | zero => simp
  | succ r ih =>
    rw [pow_succ] at hf
    apply Submodule.mul_induction_on (C := fun z => D z ∈ I^(r+1)) hf
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      apply Ideal.add_mem
      · exact Ideal.mul_mem_right (D b) (I^(r+1)) ha
      · rw [pow_succ]
        exact Ideal.mul_mem_mul_rev (ih a ha) hb
    · intro a b ha hb
      rw [map_add]
      exact Ideal.add_mem _ ha hb

theorem pderiv_order_drop {n : ℕ} (f : Poly n) (p : Point n) (r : ℕ)
    (hf : OrderAtLeast f p r) (i : Fin n) :
    OrderAtLeast (MvPolynomial.pderiv i f) p (r-1) := by
  cases r with
  | zero => simp [OrderAtLeast]
  | succ r =>
    exact derivation_mem_pow (MvPolynomial.pderiv i) (pointIdealOver p) r f hf

end
end DistinctDistances.TrackA
