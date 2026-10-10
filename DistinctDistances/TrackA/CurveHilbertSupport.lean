import DistinctDistances.TrackA.CurveLengthSupport
import DistinctDistances.TrackA.Intersections

namespace DistinctDistances.TrackA
noncomputable section
open Filter
open scoped Classical

/-- Comparing a second-order parameter with a degree-one cumulative
Hilbert polynomial gives the required multiplicity loss. -/
theorem curve_hilbert_double_order_bound (R : Type*) [CommRing R] (m : Ideal R) (a : R)
    (ha : a ∈ m^2) (L : ℕ)
    (hlen : Module.length R (R ⧸ Ideal.span {a}) = (L : ℕ∞))
    (P : Polynomial ℚ) (hdeg : P.natDegree ≤ 1) (N : ℕ)
    (hP : ∀ t ≥ N, ∃ v : ℕ,
      Module.length R (R ⧸ m^(t+1)) = (v : ℕ∞) ∧ P.eval (t : ℚ) = (v : ℚ)) :
    2 * P.coeff 1 ≤ (L : ℚ) := by
  have hlength (j : ℕ) : Module.length R (R ⧸ m^(2*j)) ≤ (j : ℕ∞)*(L : ℕ∞) := by
    have hpow : a^j ∈ m^(2*j) := by
      simpa only [← pow_mul] using Ideal.pow_mem_pow ha j
    have hsub : Ideal.span {a^j} ≤ m^(2*j) := Ideal.span_le.mpr (by
      intro b hb
      rcases Set.mem_singleton_iff.mp hb with rfl
      exact hpow)
    calc
      Module.length R (R ⧸ m^(2*j)) ≤ Module.length R (R ⧸ Ideal.span {a^j}) :=
        Module.length_le_of_surjective (Submodule.factor hsub) (Submodule.factor_surjective hsub)
      _ ≤ (j : ℕ∞) * Module.length R (R ⧸ Ideal.span {a}) := curve_length_span_pow_le R a j
      _ = (j : ℕ∞)*(L : ℕ∞) := by rw [hlen]
  let P₂ : Polynomial ℚ := (Polynomial.taylor (-1) P).comp (Polynomial.C 2 * Polynomial.X)
  let Q : Polynomial ℚ := Polynomial.C (L : ℚ) * Polynomial.X
  have hTaylor : (Polynomial.taylor (-1) P).natDegree ≤ 1 := by simpa using hdeg
  have hArg : (Polynomial.C (2 : ℚ)*Polynomial.X).natDegree ≤ 1 := by
    exact Polynomial.natDegree_mul_le.trans (by simp)
  have hP₂ : P₂.natDegree ≤ 1 :=
    Polynomial.natDegree_comp_le.trans
      (((Nat.mul_le_mul_left _ hArg).trans_eq (Nat.mul_one _)).trans hTaylor)
  have hQ : Q.natDegree ≤ 1 := Polynomial.natDegree_mul_le.trans (by simp)
  have hle : ∀ᶠ j : ℕ in atTop, P₂.eval (j : ℚ) ≤ Q.eval (j : ℚ) := by
    apply eventually_atTop.mpr
    refine ⟨N+1, ?_⟩
    intro j hj
    obtain ⟨v, hv, hvP⟩ := hP (2*j-1) (by omega)
    have hExp : 2*j-1+1 = 2*j := by omega
    rw [hExp] at hv
    have hb := hlength j
    rw [hv] at hb
    have hbQ : (v : ℚ) ≤ (j : ℚ)*(L : ℚ) := by exact_mod_cast hb
    have hcast : ((2*j-1 : ℕ) : ℚ) = 2*(j : ℚ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2*j)]
      push_cast
      rfl
    have heval : P₂.eval (j : ℚ) = P.eval ((2*j-1 : ℕ) : ℚ) := by
      simp only [P₂, Polynomial.eval_comp, Polynomial.taylor_eval, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      rw [hcast]
      congr 1
      ring
    rw [heval, hvP]
    simpa [Q, Polynomial.eval_mul, mul_comm] using hbQ
  have hc := OAI.QuarticPowerFree.coeff_le_of_eventually_nat_eval_le P₂ Q 1 hP₂ hQ hle
  dsimp [P₂, Q] at hc
  rw [Polynomial.comp_C_mul_X_coeff,
    OAI.QuarticPowerFree.coeff_taylor_high P (-1) 1 hdeg] at hc
  simpa [mul_comm] using hc

set_option backward.isDefEq.respectTransparency.types false in
theorem curve_double_order_length_core {n : ℕ} (C : AffineVariety n)
    (hC : C.IsIrreducible) (hdim : C.dimension = 1) (p : Point n) (hp : p ∈ C.points)
    (f : Poly n) (hf : f ∉ C.ideal)
    (horder : localClass C p f ∈ carrierMaximalIdeal C p ^ 2) :
    ∃ length : ℕ, localLengthAt (C.ideal ⊔ Ideal.span {f}) p = (length : ℕ∞) ∧
      2*C.multiplicity p ≤ (length : ℚ) := by
  letI : CommRing (CarrierLocalRing C p) :=
    { __ := (inferInstance : Ring (CarrierLocalRing C p))
      mul_comm := fun a b => mul_comm a b }
  obtain ⟨length, hlength, _⟩ := fa_bezout_curve_length C hC hdim f hf p hp
  have hlen : Module.length (CarrierLocalRing C p)
      (CarrierLocalRing C p ⧸ Ideal.span {localClass C p f}) = (length : ℕ∞) := by
    rwa [curve_cut_length_carrier] at hlength
  have hdim' : C.localDimension p = 1 :=
    (C.localDimension_eq_dimension p hC hp).trans hdim
  have hdeg : (C.localHilbertPolynomial p).natDegree ≤ 1 := by
    simpa only [AffineVariety.localDimension] using hdim'.le
  obtain ⟨N, hN⟩ := (C.localHilbert_eventually_polynomial p).choose_spec.2
  have hvalues : ∀ t ≥ N, ∃ v : ℕ,
      Module.length (CarrierLocalRing C p)
        (CarrierLocalRing C p ⧸ carrierMaximalIdeal C p ^ (t+1)) = (v : ℕ∞) ∧
      (C.localHilbertPolynomial p).eval (t : ℚ) = (v : ℚ) := by
    intro t ht
    obtain ⟨v, hv, hPv⟩ := hN t ht
    exact ⟨v, (curve_localHilbert_carrier C p t).symm.trans hv, hPv⟩
  have hbound : 2*(C.localHilbertPolynomial p).coeff 1 ≤ (length : ℚ) :=
    curve_hilbert_double_order_bound (CarrierLocalRing C p)
    (carrierMaximalIdeal C p) (localClass C p f) horder length hlen
    (C.localHilbertPolynomial p) hdeg N hvalues
  refine ⟨length, hlength, ?_⟩
  simpa [AffineVariety.multiplicity, hdim'] using hbound

end
end DistinctDistances.TrackA
