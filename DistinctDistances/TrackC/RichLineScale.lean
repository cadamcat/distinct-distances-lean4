import DistinctDistances.TrackC.RichLineArithmetic

namespace DistinctDistances.TrackC

noncomputable section

set_option maxHeartbeats 2000000 in
/-- Quantitative scale choice for the polynomial uniform rich-line proof. -/
theorem rich_partition_scale_choice (p C θ A Q L s k : ℝ)
    (hp : 0 < p) (hC : 0 < C) (hθ : 0 < θ) (hA : 0 < A) (hQ : 0 < Q)
    (hL : 0 < L) (hs : 0 < s) (hk : 1 ≤ k)
    (hθC : 2*C ≤ θ) (hθQ : 4000000*p*C*Q^2 ≤ θ) (hAC : 2*C ≤ A)
    (hAD : 200000000*p*θ ≤ A^2) (hADsq : 2000*p*θ ≤ A)
    (hACell : 8000000*p*C*Q*θ ≤ A^2)
    (hglobal : s ≤ C*(L^2/k^3+L/k))
    (hlarge : A*(L^((3:ℝ)/2)/k^2+L/k) < s) :
    ∃ r : ℕ,1 ≤ r ∧ p*r ≤ s*k/(100000000*L) ∧
      (p*r)^2 ≤ L/1000000 ∧ p*r ≤ 2*p*θ*L^2/(s*k^3) ∧
      C*((Q*L/(r:ℝ)^2)^2/k^3+(Q*L/(r:ℝ)^2)/k) < s/(2000000*p*(r:ℝ)^3) := by
  have hkpos : 0 < k := by linarith
  have hline : 2*C*L/k < s := by
    calc
      _ = (2*C)*(L/k) := by ring
      _ ≤ A*(L/k) := mul_le_mul_of_nonneg_right hAC (by positivity)
      _ ≤ A*(L^((3:ℝ)/2)/k^2+L/k) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hA.le
      _ < _ := hlarge
  have habs : s ≤ 2*C*L^2/k^3 := by
    have hg : s ≤ C*L^2/k^3+C*L/k := by convert hglobal using 1 <;> ring
    have hline' : 2*(C*L/k) < s := by convert hline using 1 <;> ring
    have hsum : s ≤ 2*(C*L^2/k^3) := by linarith only [hg,hline']
    convert hsum using 1 <;> ring
  let q := θ*L^2/(s*k^3)
  have hq : 1 ≤ q := by
    have hg := (le_div_iff₀ (by positivity : (0:ℝ) < k^3)).mp habs
    apply (le_div_iff₀ (by positivity : (0:ℝ) < s*k^3)).mpr
    have ht := mul_le_mul_of_nonneg_right hθC (sq_nonneg L)
    linarith
  let r : ℕ := ⌈q⌉₊
  have hrlower : q ≤ (r:ℝ) := Nat.le_ceil q
  have hrone : (1:ℝ) ≤ r := hq.trans hrlower
  have hr : 1 ≤ r := by exact_mod_cast hrone
  have hrpos : (0:ℝ) < r := by positivity
  have hrupper : (r:ℝ) ≤ 2*q := by
    have hc : (r:ℝ) < q+1 := Nat.ceil_lt_add_one (by linarith : 0 ≤ q)
    linarith
  have hleading : A*L^((3:ℝ)/2) < s*k^2 := by
    have hf : A*L^((3:ℝ)/2)/k^2 < s := by
      calc
        _ = A*(L^((3:ℝ)/2)/k^2) := by ring
        _ ≤ A*(L^((3:ℝ)/2)/k^2+L/k) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hA.le
        _ < _ := hlarge
    exact (div_lt_iff₀ (by positivity : (0:ℝ) < k^2)).mp hf
  have hpow : (L^((3:ℝ)/2))^2 = L^3 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hL.le]
    norm_num
  have hsq : (A*L^((3:ℝ)/2))^2 < (s*k^2)^2 :=
    (sq_lt_sq₀ (by positivity) (by positivity)).mpr hleading
  have hSquare : A^2*L^3 < s^2*k^4 := by
    calc
      _ = (A*L^((3:ℝ)/2))^2 := by rw [mul_pow,hpow]
      _ < _ := hsq
      _ = _ := by ring
  have hdegree : p*(r:ℝ) ≤ 2*p*θ*L^2/(s*k^3) := by
    calc
      _ ≤ p*(2*q) := mul_le_mul_of_nonneg_left hrupper hp.le
      _ = _ := by dsimp [q];ring
  have hsmall : 2*p*θ*L^2/(s*k^3) ≤ s*k/(100000000*L) := by
    apply (div_le_div_iff₀ (by positivity : (0:ℝ) < s*k^3)
      (by positivity : (0:ℝ) < 100000000*L)).mpr
    calc
      _ = (200000000*p*θ)*L^3 := by ring
      _ ≤ A^2*L^3 := mul_le_mul_of_nonneg_right hAD (by positivity)
      _ ≤ s^2*k^4 := hSquare.le
      _ = _ := by ring
  have hcoef : 4000000*p^2*θ^2 ≤ A^2 := by
    have h := (sq_le_sq₀ (by positivity : 0 ≤ 2000*p*θ) hA.le).mpr hADsq
    convert h using 1 <;> ring
  have hkpow : k^4 ≤ k^6 := by
    have hk2 : 1 ≤ k^2 := one_le_pow₀ hk
    nlinarith [mul_nonneg (pow_nonneg hkpos.le 4) (sub_nonneg.mpr hk2)]
  have hsmallSq : (2*p*θ*L^2/(s*k^3))^2 ≤ L/1000000 := by
    rw [div_pow]
    apply (div_le_div_iff₀ (by positivity : (0:ℝ) < (s*k^3)^2) (by norm_num : (0:ℝ) < 1000000)).mpr
    calc
      _ = (4000000*p^2*θ^2)*L^4 := by ring
      _ ≤ A^2*L^4 := mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = (A^2*L^3)*L := by ring
      _ ≤ (s^2*k^4)*L := mul_le_mul_of_nonneg_right hSquare.le hL.le
      _ ≤ (s^2*k^6)*L := by gcongr
      _ = _ := by ring
  have hfirst : C*Q^2*L^2/((r:ℝ)*k^3) ≤ s/(4000000*p) := by
    calc
      _ ≤ C*Q^2*L^2/(q*k^3) := by gcongr
      _ = C*Q^2*s/θ := by dsimp [q];field_simp <;> ring
      _ ≤ _ := by
        apply (div_le_div_iff₀ hθ (by positivity : (0:ℝ) < 4000000*p)).mpr
        calc
          _ = s*(4000000*p*C*Q^2) := by ring
          _ ≤ s*θ := mul_le_mul_of_nonneg_left hθQ hs.le
  have hsecond : C*Q*L*(r:ℝ)/k < s/(4000000*p) := by
    calc
      _ ≤ C*Q*L*(2*q)/k := by gcongr
      _ = 2*C*Q*θ*L^3/(s*k^4) := by dsimp [q];field_simp <;> ring
      _ < _ := by
        apply (div_lt_div_iff₀ (by positivity : (0:ℝ) < s*k^4)
          (by positivity : (0:ℝ) < 4000000*p)).mpr
        calc
          _ = (8000000*p*C*Q*θ)*L^3 := by ring
          _ ≤ A^2*L^3 := mul_le_mul_of_nonneg_right hACell (by positivity)
          _ < s^2*k^4 := hSquare
          _ = _ := by ring
  refine ⟨r,hr,hdegree.trans hsmall,?_,hdegree,?_⟩
  · exact ((sq_le_sq₀ (by positivity : 0 ≤ p*(r:ℝ)) (by positivity)).mpr hdegree).trans hsmallSq
  · have heq : s/(2000000*p*(r:ℝ)^3) = (s/(2000000*p))/(r:ℝ)^3 := by field_simp <;> ring
    rw [heq]
    apply (lt_div_iff₀ (by positivity : (0:ℝ) < (r:ℝ)^3)).mpr
    calc
      _ = C*Q^2*L^2/((r:ℝ)*k^3)+C*Q*L*(r:ℝ)/k := by field_simp <;> ring
      _ < s/(4000000*p)+s/(4000000*p) := add_lt_add_of_le_of_lt hfirst hsecond
      _ = _ := by field_simp <;> ring

/-- Absolute constants satisfying the only numerical conditions used by the geometry. -/
theorem rich_partition_constants (p C : ℝ) (hp : 0 < p) (hC : 0 < C) :
    ∃ θ A : ℝ,0 < θ ∧ 0 < A ∧
      2*C ≤ θ ∧ 4000000*p*C*(2000000*p*(p+1))^2 ≤ θ ∧ 2*C ≤ A ∧
      200000000*p*θ ≤ A^2 ∧ 2000*p*θ ≤ A ∧
      8000000*p*C*(2000000*p*(p+1))*θ ≤ A^2 := by
  let Q := 2000000*p*(p+1)
  let θ := 2+2*C+4000000*p*C*Q^2
  have hθ : 0 < θ := by dsimp [θ];positivity
  let u := 200000000*p*θ
  let v := 8000000*p*C*Q*θ
  have hu : 0 ≤ u := by dsimp [u];positivity
  have hv : 0 ≤ v := by dsimp [v,Q];positivity
  let A := 2*C+Real.sqrt u+2000*p*θ+Real.sqrt v+1
  have hA : 0 < A := by dsimp [A];positivity
  have hAu : Real.sqrt u ≤ A := by dsimp [A];nlinarith [Real.sqrt_nonneg u,Real.sqrt_nonneg v]
  have hAv : Real.sqrt v ≤ A := by dsimp [A];nlinarith [Real.sqrt_nonneg u,Real.sqrt_nonneg v]
  have hAsqu : u ≤ A^2 := by
    have h := (sq_le_sq₀ (Real.sqrt_nonneg u) hA.le).mpr hAu
    rwa [Real.sq_sqrt hu] at h
  have hAsqv : v ≤ A^2 := by
    have h := (sq_le_sq₀ (Real.sqrt_nonneg v) hA.le).mpr hAv
    rwa [Real.sq_sqrt hv] at h
  refine ⟨θ,A,hθ,hA,?_,?_,?_,hAsqu,?_,hAsqv⟩
  · have ht : 0 ≤ 4000000*p*C*Q^2 := by positivity
    dsimp [θ];linarith
  · change 4000000*p*C*Q^2 ≤ θ
    dsimp [θ];linarith
  · dsimp [A];nlinarith [Real.sqrt_nonneg u,Real.sqrt_nonneg v]
  · dsimp [A];nlinarith [Real.sqrt_nonneg u,Real.sqrt_nonneg v]

end
end DistinctDistances.TrackC
