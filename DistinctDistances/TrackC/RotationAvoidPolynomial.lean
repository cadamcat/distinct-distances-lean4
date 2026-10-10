import DistinctDistances.TrackC.HomogeneousRotation
import DistinctDistances.TrackC.RotationDetWitness

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

def rotationParameterVector (u : Fin 4 → ℝ) : E 3 := WithLp.toLp 2 (fun i => u i.succ)

def rotationDenominatorPolynomial : Poly 4 :=
  MvPolynomial.X 0^2+MvPolynomial.X 1^2+MvPolynomial.X 2^2+MvPolynomial.X 3^2

def rotationNumeratorPolynomial : Matrix (Fin 3) (Fin 3) (Poly 4) :=
  let a := MvPolynomial.X (0:Fin 4)
  let w₀ := MvPolynomial.X (1:Fin 4)
  let w₁ := MvPolynomial.X (2:Fin 4)
  let w₂ := MvPolynomial.X (3:Fin 4)
  !![a^2+w₀^2-w₁^2-w₂^2,2*(w₀*w₁+a*w₂),2*(w₀*w₂-a*w₁);
     2*(w₀*w₁-a*w₂),a^2-w₀^2+w₁^2-w₂^2,2*(w₁*w₂+a*w₀);
     2*(w₀*w₂+a*w₁),2*(w₁*w₂-a*w₀),a^2-w₀^2-w₁^2+w₂^2]

def rotationNormalPolynomial (S : Matrix (Fin 3) (Fin 3) ℝ) (n : E 3) : Poly 4 :=
  Matrix.det (rotationDenominatorPolynomial • ((1+normalOuterMatrix n).map MvPolynomial.C)+
    rotationNumeratorPolynomial*S.map MvPolynomial.C)

set_option maxHeartbeats 2000000 in
theorem rotationNormalPolynomial_eval (S : Matrix (Fin 3) (Fin 3) ℝ) (n : E 3) (u : Fin 4 → ℝ) :
    MvPolynomial.eval u (rotationNormalPolynomial S n) =
      Matrix.det (homRotationDenominator (u 0) (rotationParameterVector u) • (1+normalOuterMatrix n)+
        homRotationNumerator (u 0) (rotationParameterVector u)*S) := by
  simp [rotationNormalPolynomial,rotationDenominatorPolynomial,rotationNumeratorPolynomial,
    rotationParameterVector,homRotationDenominator,homRotationNumerator,normalOuterMatrix,
    Matrix.det_fin_three,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,Matrix.one_apply]
  ring

set_option maxHeartbeats 2000000 in
theorem rotationNormalPolynomial_basis (S : Matrix (Fin 3) (Fin 3) ℝ) (n : E 3) (j : Fin 4) :
    MvPolynomial.eval (Pi.single j (1:ℝ)) (rotationNormalPolynomial S n) =
      Matrix.det (1+coordinateEvenSigns j*S+normalOuterMatrix n) := by
  rw [rotationNormalPolynomial_eval]
  have hD : homRotationDenominator ((Pi.single j (1:ℝ) : Fin 4 → ℝ) 0) (rotationParameterVector (Pi.single j 1)) = 1 := by
    fin_cases j <;> simp [homRotationDenominator,rotationParameterVector]
  have hM : homRotationNumerator ((Pi.single j (1:ℝ) : Fin 4 → ℝ) 0) (rotationParameterVector (Pi.single j 1)) = coordinateEvenSigns j := by
    ext i k
    fin_cases j <;> fin_cases i <;> fin_cases k
    all_goals simp [homRotationNumerator,rotationParameterVector,coordinateEvenSigns]
  rw [hD,hM,one_smul]
  congr 1
  abel

theorem rotationNormalPolynomial_ne_zero (S : Matrix (Fin 3) (Fin 3) ℝ)
    (hS : Matrix.det S = -1) (n : E 3) (hn : n ≠ 0) : rotationNormalPolynomial S n ≠ 0 := by
  obtain ⟨j,hj⟩ := coordinate_rotation_det_witness S hS n hn
  intro hz
  have h := rotationNormalPolynomial_basis S n j
  rw [hz,map_zero] at h
  exact hj h.symm

set_option maxHeartbeats 2000000 in
theorem rotationNormalPolynomial_certificate (S : Matrix (Fin 3) (Fin 3) ℝ) (n : E 3) (u : Fin 4 → ℝ)
    (hD : homRotationDenominator (u 0) (rotationParameterVector u) ≠ 0)
    (hP : MvPolynomial.eval u (rotationNormalPolynomial S n) ≠ 0) :
    Matrix.det (1+homRotationMatrix (u 0) (rotationParameterVector u)*S+normalOuterMatrix n) ≠ 0 := by
  intro hz
  have heq : homRotationDenominator (u 0) (rotationParameterVector u) • (1+normalOuterMatrix n)+
      homRotationNumerator (u 0) (rotationParameterVector u)*S =
      homRotationDenominator (u 0) (rotationParameterVector u) •
        (1+homRotationMatrix (u 0) (rotationParameterVector u)*S+normalOuterMatrix n) := by
    ext i j
    simp [homRotationMatrix,Matrix.mul_apply,Fin.sum_univ_three]
    field_simp [hD]
    ring
  apply hP
  rw [rotationNormalPolynomial_eval,heq,Matrix.det_smul,hz,mul_zero]

/-- Finite polynomial avoidance in the homogeneous proper rotation parameters. -/
theorem finite_rotation_normal_certificates {ι : Type*} (I : Finset ι)
    (S : ι → Matrix (Fin 3) (Fin 3) ℝ) (N : ι → Finset (E 3))
    (hS : ∀ i ∈ I,Matrix.det (S i) = -1) (hN : ∀ i ∈ I,∀ n ∈ N i,n ≠ 0) :
    ∃ u : Fin 4 → ℝ,0 < homRotationDenominator (u 0) (rotationParameterVector u) ∧
      ∀ i ∈ I,∀ n ∈ N i,
        Matrix.det (1+homRotationMatrix (u 0) (rotationParameterVector u)*S i+normalOuterMatrix n) ≠ 0 := by
  have hDen : rotationDenominatorPolynomial ≠ 0 := by
    intro hz
    have h := congrArg (MvPolynomial.eval (Pi.single (0:Fin 4) (1:ℝ))) hz
    norm_num [rotationDenominatorPolynomial] at h
  let P := rotationDenominatorPolynomial*(∏ i ∈ I,∏ n ∈ N i,rotationNormalPolynomial (S i) n)
  have hP : P ≠ 0 := mul_ne_zero hDen (Finset.prod_ne_zero_iff.mpr (fun i hi =>
    Finset.prod_ne_zero_iff.mpr (fun n hn => rotationNormalPolynomial_ne_zero (S i) (hS i hi) n (hN i hi n hn))))
  have hex : ∃ u : Fin 4 → ℝ,MvPolynomial.eval u P ≠ 0 := by
    by_contra! hzero
    apply hP
    apply MvPolynomial.funext
    intro u
    simpa using hzero u
  obtain ⟨u,hu⟩ := hex
  change MvPolynomial.eval u (rotationDenominatorPolynomial*(∏ i ∈ I,∏ n ∈ N i,rotationNormalPolynomial (S i) n)) ≠ 0 at hu
  rw [map_mul,map_prod] at hu
  obtain ⟨hDu,hProd⟩ := mul_ne_zero_iff.mp hu
  have hD : homRotationDenominator (u 0) (rotationParameterVector u) ≠ 0 := by
    simpa [rotationDenominatorPolynomial,homRotationDenominator,rotationParameterVector] using hDu
  refine ⟨u,lt_of_le_of_ne (homRotationDenominator_nonneg _ _) hD.symm,?_⟩
  intro i hi n hn
  have hp := Finset.prod_ne_zero_iff.mp hProd i hi
  rw [map_prod] at hp
  exact rotationNormalPolynomial_certificate (S i) n u hD (Finset.prod_ne_zero_iff.mp hp n hn)

end DistinctDistances.TrackC
