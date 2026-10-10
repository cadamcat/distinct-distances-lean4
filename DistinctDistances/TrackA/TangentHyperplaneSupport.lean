import DistinctDistances.TrackA.Definitions

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open MvPolynomial

/-- The first-order polynomial centered at p, with zero constant value there. -/
def tangentLinearPart {n : ℕ} (f : Poly n) (p : Point n) : Poly n :=
  ∑ i : Fin n, C (aeval p (pderiv i f)) * (X i - C (p i))

theorem tangentLinearPart_degree {n : ℕ} (f : Poly n) (p : Point n) :
    (tangentLinearPart f p).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i hi
  calc
    _ ≤ (C (aeval p (pderiv i f))).totalDegree + (X i - C (p i)).totalDegree :=
      totalDegree_mul _ _
    _ ≤ 0 + 1 := Nat.add_le_add (by simp) (by
      simpa only [totalDegree_X, totalDegree_C, Nat.max_zero] using totalDegree_sub (X i) (C (p i)))
    _ = 1 := rfl

theorem tangentLinearPart_eval {n : ℕ} (f : Poly n) (p z : Point n) :
    eval z (tangentLinearPart f p) = differential f p (z-p) := by
  simp [tangentLinearPart, differential, LinearMap.sum_apply,
    LinearMap.smul_apply, Pi.sub_apply, smul_eq_mul]

theorem tangentLinearPart_mem {n : ℕ} (f : Poly n) (p : Point n) :
    tangentLinearPart f p ∈ pointIdeal p := by
  rw [pointIdeal, mem_vanishingIdeal_singleton_iff]
  simp [tangentLinearPart]

theorem tangentLinearPart_C {n : ℕ} (a : ℂ) (p : Point n) :
    tangentLinearPart (C a) p = 0 := by
  simp [tangentLinearPart, pderiv_C]

theorem tangentLinearPart_add {n : ℕ} (f g : Poly n) (p : Point n) :
    tangentLinearPart (f+g) p = tangentLinearPart f p + tangentLinearPart g p := by
  simp only [tangentLinearPart, map_add, C_add, add_mul, Finset.sum_add_distrib]

theorem tangentLinearPart_mul_X {n : ℕ} (f : Poly n) (p : Point n) (j : Fin n) :
    tangentLinearPart (f * X j) p =
      C (p j) * tangentLinearPart f p + C (aeval p f) * (X j - C (p j)) := by
  have hc (i : Fin n) :
      aeval p (pderiv i (f * X j)) =
        aeval p (pderiv i f) * p j + if i = j then aeval p f else 0 := by
    by_cases hi : i = j
    · subst i
      simp [pderiv_mul, mul_comm, add_comm]
    · simp [pderiv_mul, hi, Ne.symm hi, mul_comm]
  unfold tangentLinearPart
  simp_rw [hc, C_add, add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [C_mul]
    ring
  · rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      simp [hij]
    · simp

/-- Algebraic Taylor remainder, proved by polynomial induction. -/
theorem tangent_first_order_remainder {n : ℕ} (f : Poly n) (p : Point n) :
    f - C (aeval p f) - tangentLinearPart f p ∈ pointIdeal p ^ 2 := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [tangentLinearPart_C]
  | add f g hf hg =>
    have heq :
        f + g - C (aeval p (f+g)) - tangentLinearPart (f+g) p =
          (f - C (aeval p f) - tangentLinearPart f p) +
            (g - C (aeval p g) - tangentLinearPart g p) := by
      rw [map_add, C_add, tangentLinearPart_add]
      ring
    rw [heq]
    exact (pointIdeal p ^ 2).add_mem hf hg
  | mul_X f j hf =>
    have heq :
        f * X j - C (aeval p (f * X j)) - tangentLinearPart (f*X j) p =
          (f - C (aeval p f) - tangentLinearPart f p) * X j +
            tangentLinearPart f p * (X j - C (p j)) := by
      rw [map_mul, aeval_X, C_mul, tangentLinearPart_mul_X]
      ring
    rw [heq]
    apply (pointIdeal p ^ 2).add_mem ((pointIdeal p ^ 2).mul_mem_right _ hf)
    have hj : X j - C (p j) ∈ pointIdeal p := by
      rw [pointIdeal, mem_vanishingIdeal_singleton_iff]
      simp
    simpa only [pow_two] using
      Ideal.mul_mem_mul (tangentLinearPart_mem f p) hj

theorem tangent_linear_local_order {n : ℕ} (V : AffineVariety n) (p : Point n)
    (f : Poly n) (hf : f ∈ V.ideal) (hp : p ∈ V.points) :
    localClass V p (tangentLinearPart f p) ∈ carrierMaximalIdeal V p ^ 2 := by
  letI : CommRing (CarrierLocalRing V p) :=
    { __ := (inferInstance : Ring (CarrierLocalRing V p))
      mul_comm := fun a b => mul_comm a b }
  let θ : Poly n →+* CarrierLocalRing V p :=
    (Ideal.Quotient.mk (localizedIdeal V.ideal p)).comp
      (algebraMap (Poly n) (PointLocalRing p))
  have hzero : θ f = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_map_of_mem _ hf
  have heval : aeval p f = 0 := hp f hf
  have hrem := tangent_first_order_remainder f p
  rw [heval, C_0, sub_zero] at hrem
  have hmap : θ (f - tangentLinearPart f p) ∈ (pointIdeal p ^ 2).map θ :=
    Ideal.mem_map_of_mem θ hrem
  rw [Ideal.map_pow θ (pointIdeal p) 2, map_sub, hzero, zero_sub] at hmap
  exact (carrierMaximalIdeal V p ^ 2).neg_mem_iff.mp hmap

theorem transverse_defining_differential {n : ℕ} (V : AffineVariety n)
    (p v : Point n) (hv : v ∉ V.tangentSpace p) :
    ∃ f : Poly n, f ∈ V.ideal ∧ differential f p v ≠ 0 := by
  change v ∉ ⨅ f : V.ideal, LinearMap.ker (differential f.val p) at hv
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hv
  push Not at hv
  obtain ⟨f, hf⟩ := hv
  exact ⟨f.val, f.property, hf⟩

theorem tangent_hyperplane_core {n : ℕ} (C X : AffineVariety n)
    (hCX : C.Subvariety X) (p z : Point n) (hp : p ∈ C.points)
    (htransverse : z-p ∉ X.tangentSpace p) :
    ∃ f : Poly n, f.totalDegree ≤ 1 ∧ eval z f ≠ 0 ∧
      localClass C p f ∈ carrierMaximalIdeal C p ^ 2 := by
  obtain ⟨f, hf, hd⟩ := transverse_defining_differential X p (z-p) htransverse
  refine ⟨tangentLinearPart f p, tangentLinearPart_degree f p, ?_, ?_⟩
  · rw [tangentLinearPart_eval]
    exact hd
  · exact tangent_linear_local_order C p f (hCX hf) hp

end
end DistinctDistances.TrackA
