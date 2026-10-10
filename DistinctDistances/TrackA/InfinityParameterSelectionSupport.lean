import DistinctDistances.TrackA.SimultaneousNormalizationSupport

set_option backward.isDefEq.respectTransparency false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Forget the original homogenizing coordinate. -/
def successorCoordinateProjection (n : ℕ) : LinearProjection (n+1) n :=
  LinearMap.pi fun i : Fin n => LinearMap.proj i.succ

theorem successorCoordinateProjection_single_zero (n : ℕ) :
    successorCoordinateProjection n (Pi.single 0 1) = 0 := by
  ext i
  simp [successorCoordinateProjection, Pi.single_apply]

theorem successorCoordinateProjection_single_succ {n : ℕ} (i : Fin n) :
    successorCoordinateProjection n (Pi.single i.succ 1) = Pi.single i 1 := by
  ext j
  simp [successorCoordinateProjection, Pi.single_apply]

/-- Pulling a linear coordinate back through the tail projection is
exactly renaming its variables to successor cone coordinates. -/
theorem linearCoordinate_comp_successorProjection {n s : ℕ}
    (ψ : LinearProjection n s) (j : Fin s) :
    linearCoordinate (ψ.comp (successorCoordinateProjection n)) j =
      MvPolynomial.rename Fin.succ (linearCoordinate ψ j) := by
  unfold linearCoordinate
  rw [Fin.sum_univ_succ]
  simp only [LinearMap.comp_apply, successorCoordinateProjection_single_zero,
    map_zero, Pi.zero_apply, MvPolynomial.C_0, zero_mul, zero_add,
    successorCoordinateProjection_single_succ]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X]

/-- Successor-renamed linear coordinates retain the actual quotient's
inherited scalar action. -/
theorem quotient_successor_linearCoordinate_eq_sum {n s : ℕ}
    (I : Ideal (Poly (n+1))) (ψ : LinearProjection n s) (j : Fin s) :
    Ideal.Quotient.mk I (MvPolynomial.rename Fin.succ (linearCoordinate ψ j)) =
      ∑ i : Fin n, ψ (Pi.single i 1) j • Ideal.Quotient.mk I (MvPolynomial.X i.succ) := by
  rw [← linearCoordinate_comp_successorProjection, quotient_linearCoordinate_eq_sum,
    Fin.sum_univ_succ]
  simp only [LinearMap.comp_apply, successorCoordinateProjection_single_zero,
    map_zero, Pi.zero_apply, zero_smul, zero_add, successorCoordinateProjection_single_succ]

/-- Finite independent parameters on a homogeneous quotient where X0 is
zero are represented by a surjective linear map in the original n affine
coordinates. Their number is the actual quotient Krull dimension. -/
theorem infinity_quotient_linear_normalization {n k : ℕ}
    (I : Ideal (Poly (n+1)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    (hne : I ≠ ⊤) (hzero : MvPolynomial.X 0 ∈ I)
    (hd : ringKrullDim (Poly (n+1) ⧸ I) = (k : WithBot ℕ∞)) :
    ∃ ψ : LinearProjection n k, Function.Surjective ψ ∧
      Function.Injective (MvPolynomial.aeval (R := ℂ) (fun j =>
        Ideal.Quotient.mk I (MvPolynomial.rename Fin.succ (linearCoordinate ψ j)))) ∧
      (MvPolynomial.aeval (R := ℂ) (fun j =>
        Ideal.Quotient.mk I (MvPolynomial.rename Fin.succ (linearCoordinate ψ j)))).Finite := by
  obtain ⟨s, _, z, _, hz, hi, hf⟩ := homogeneous_quotient_linear_normalization I hI hne
  have hs : s = k := by
    have he : (s : WithBot ℕ∞) = (k : WithBot ℕ∞) :=
      (homogeneous_normalization_dimension I z hi hf).symm.trans hd
    exact_mod_cast he
  subst s
  let x : Fin n → Poly (n+1) ⧸ I := fun i => Ideal.Quotient.mk I (MvPolynomial.X i.succ)
  have hz0 : Ideal.Quotient.mk I (MvPolynomial.X 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hzero
  have hspan : Submodule.span ℂ
      (Set.range (fun i : Fin (n+1) => Ideal.Quotient.mk I (MvPolynomial.X i))) ≤
        Submodule.span ℂ (Set.range x) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    cases i using Fin.cases with
    | zero =>
      change Ideal.Quotient.mk I (MvPolynomial.X 0) ∈ Submodule.span ℂ (Set.range x)
      rw [hz0]
      exact Submodule.zero_mem _
    | succ i => exact Submodule.subset_span (Set.mem_range_self i)
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hspan (hz j))
  let ψ : LinearProjection n k := Matrix.mulVecLin c
  have hcoeff (j : Fin k) (i : Fin n) : ψ (Pi.single i 1) j = c j i := by
    simp [ψ, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite]
  have hψ (j : Fin k) :
      Ideal.Quotient.mk I (MvPolynomial.rename Fin.succ (linearCoordinate ψ j)) = z j := by
    rw [quotient_successor_linearCoordinate_eq_sum]
    simpa only [hcoeff] using hc j
  have hψfull (j : Fin k) :
      Ideal.Quotient.mk I (linearCoordinate (ψ.comp (successorCoordinateProjection n)) j) = z j := by
    rw [linearCoordinate_comp_successorProjection]
    exact hψ j
  have hsurjfull := quotient_parameters_projection_surjective I z
    (ψ.comp (successorCoordinateProjection n)) hψfull hi
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨v, hv⟩ := hsurjfull y
    exact ⟨successorCoordinateProjection n v, hv⟩
  have he : (fun j => Ideal.Quotient.mk I
      (MvPolynomial.rename Fin.succ (linearCoordinate ψ j))) = z := funext hψ
  exact ⟨ψ, hsurj, by rwa [he], by rwa [he]⟩

end
end DistinctDistances.TrackA
