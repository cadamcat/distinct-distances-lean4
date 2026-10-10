import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic

/-!
The scalar coefficient computation in concentration.tex:717–766 and the numerical
assembly at 777–783. These declarations do not define geometric degree or prove the
singular-base incidence formula. That formula must supply the numerical hypotheses.
-/

namespace DistinctDistances.TrackB

set_option autoImplicit false

open scoped BigOperators

/-- The integral coefficient `[z^u] (1+z)^p / (1+2z)`. -/
def segreCoeff (p u : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (u + 1), (p.choose k : ℤ) * (-2 : ℤ) ^ (u - k)

/-- The scalar generating series, inverted only at a unit constant term. -/
noncomputable def scalarSegreSeries (p : ℕ) : PowerSeries ℤ :=
  (1 + PowerSeries.X) ^ p *
    PowerSeries.invOfUnit (1 + 2 * PowerSeries.X) 1

private theorem coeff_one_add_X_pow (p u : ℕ) :
    PowerSeries.coeff u ((1 + PowerSeries.X : PowerSeries ℤ) ^ p) = (p.choose u : ℤ) := by
  have hpow : (1 + PowerSeries.X : PowerSeries ℤ) ^ p =
      ((((1 : Polynomial ℤ) + Polynomial.X) ^ p : Polynomial ℤ) : PowerSeries ℤ) := by
    simp
  rw [hpow, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

private theorem coeff_two_linear_mul (f : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n ((1 + 2 * PowerSeries.X) * f) =
      PowerSeries.coeff n f + if n = 0 then 0 else 2 * PowerSeries.coeff (n - 1) f := by
  have hfactor : (1 + 2 * PowerSeries.X : PowerSeries ℤ) =
      1 + PowerSeries.C (2 : ℤ) * PowerSeries.X := by
    norm_num
  rw [hfactor, add_mul, one_mul, map_add, mul_assoc, PowerSeries.coeff_C_mul]
  rw [← pow_one (PowerSeries.X : PowerSeries ℤ), PowerSeries.coeff_X_pow_mul']
  cases n <;> simp

private theorem segreCoeff_add_twice (p u : ℕ) :
    segreCoeff p (u + 1) + 2 * segreCoeff p u = (p.choose (u + 1) : ℤ) := by
  unfold segreCoeff
  rw [Finset.sum_range_succ]
  have hs :
      (∑ k ∈ Finset.range (u + 1), (p.choose k : ℤ) * (-2 : ℤ) ^ (u + 1 - k)) =
        (-2 : ℤ) * ∑ k ∈ Finset.range (u + 1), (p.choose k : ℤ) * (-2 : ℤ) ^ (u - k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ u := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have he : u + 1 - k = (u - k) + 1 := by omega
    rw [he, pow_succ]
    ring
  rw [hs]
  simp only [Nat.sub_self, pow_zero, mul_one]
  ring

/-- B15, concentration.tex:747–748. -/
theorem scalarSegreSeries_coeff (p u : ℕ) :
    PowerSeries.coeff u (scalarSegreSeries p) = segreCoeff p u := by
  have hinv : (1 + 2 * PowerSeries.X : PowerSeries ℤ) *
      PowerSeries.invOfUnit (1 + 2 * PowerSeries.X) 1 = 1 := by
    apply PowerSeries.mul_invOfUnit
    simp
  have hseries : (1 + 2 * PowerSeries.X : PowerSeries ℤ) * scalarSegreSeries p =
      (1 + PowerSeries.X) ^ p := by
    unfold scalarSegreSeries
    calc
      (1 + 2 * PowerSeries.X : PowerSeries ℤ) *
          ((1 + PowerSeries.X : PowerSeries ℤ) ^ p *
            PowerSeries.invOfUnit (1 + 2 * PowerSeries.X) 1) =
        ((1 + 2 * PowerSeries.X : PowerSeries ℤ) *
          PowerSeries.invOfUnit (1 + 2 * PowerSeries.X) 1) *
            (1 + PowerSeries.X : PowerSeries ℤ) ^ p := by ring
      _ = (1 + PowerSeries.X : PowerSeries ℤ) ^ p := by rw [hinv, one_mul]
  have hrec (n : ℕ) :
      PowerSeries.coeff n (scalarSegreSeries p) +
          (if n = 0 then 0 else 2 * PowerSeries.coeff (n - 1) (scalarSegreSeries p)) =
        (p.choose n : ℤ) := by
    have hc := congrArg (PowerSeries.coeff n) hseries
    rw [coeff_two_linear_mul, coeff_one_add_X_pow] at hc
    exact hc
  induction u using Nat.strong_induction_on with
  | h u ih =>
    cases u with
    | zero =>
      have h0 := hrec 0
      simpa [segreCoeff] using h0
    | succ u =>
      have hprev := ih u (by omega)
      have hseriesRec := hrec (u + 1)
      simp only [if_neg (Nat.succ_ne_zero _), Nat.succ_sub_one] at hseriesRec
      have hcoeffRec := segreCoeff_add_twice p u
      nlinarith

/-- B17, concentration.tex:753. -/
theorem segreCoeff_zero (p : ℕ) : segreCoeff p 0 = 1 := by
  unfold segreCoeff
  simp

/-- B17, concentration.tex:753. Signed subtraction is in ℤ. -/
theorem segreCoeff_one (p : ℕ) : segreCoeff p 1 = (p : ℤ) - 2 := by
  unfold segreCoeff
  simp [Finset.sum_range_succ]
  ring

private theorem segreCoeff_succ_left (p : ℕ) :
    ∀ u : ℕ, 0 < u →
      segreCoeff (p + 1) u = segreCoeff p u + segreCoeff p (u - 1) := by
  intro u
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro hu
    cases u with
    | zero => omega
    | succ u =>
      cases u with
      | zero =>
        rw [segreCoeff_one, segreCoeff_one, segreCoeff_zero]
        push_cast
        ring
      | succ u =>
        have hi :
            segreCoeff (p + 1) (u + 1) =
              segreCoeff p (u + 1) + segreCoeff p u := by
          simpa using ih (u + 1) (by omega) (by omega)
        have htop := segreCoeff_add_twice (p + 1) (u + 1)
        have hchoose := Nat.choose_succ_left p (u + 2) (by omega)
        have hmid := segreCoeff_add_twice p (u + 1)
        have hlow := segreCoeff_add_twice p u
        simp only [show u + 1 + 1 = u + 2 from by omega,
          show u + 2 - 1 = u + 1 from by omega] at htop hchoose hmid
        have hchooseZ : ((p + 1).choose (u + 2) : ℤ) =
            (p.choose (u + 1) : ℤ) + (p.choose (u + 2) : ℤ) := by
          exact_mod_cast hchoose
        simp only [show u + 1 + 1 = u + 2 from by omega,
          show u + 2 - 1 = u + 1 from by omega] at ⊢
        nlinarith [hchooseZ]

/-- B17, concentration.tex:754–761. -/
theorem segreCoeff_two_step (p u : ℕ) (hp : 2 ≤ p) (hu : 2 ≤ u) :
    segreCoeff p u = ((p - 2).choose u : ℤ) + segreCoeff (p - 2) (u - 2) := by
  obtain ⟨p', hp'⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
  obtain ⟨u', hu'⟩ : ∃ u', u = u' + 2 := ⟨u - 2, by omega⟩
  rw [hp', hu']
  have h1 := segreCoeff_succ_left (p' + 1) (u' + 2) (by omega)
  have h2 := segreCoeff_succ_left p' (u' + 2) (by omega)
  have h3 := segreCoeff_succ_left p' (u' + 1) (by omega)
  have h4 := segreCoeff_add_twice p' (u' + 1)
  have h1' :
      segreCoeff (p' + 2) (u' + 2) =
        segreCoeff (p' + 1) (u' + 2) + segreCoeff (p' + 1) (u' + 1) := by
    simpa [Nat.add_assoc] using h1
  have h2' :
      segreCoeff (p' + 1) (u' + 2) =
        segreCoeff p' (u' + 2) + segreCoeff p' (u' + 1) := by
    simpa [Nat.add_assoc] using h2
  have h3' :
      segreCoeff (p' + 1) (u' + 1) =
        segreCoeff p' (u' + 1) + segreCoeff p' u' := by
    simpa [Nat.add_assoc] using h3
  simp only [Nat.add_sub_cancel] at h4 ⊢
  rw [h1', h2', h3']
  nlinarith

/-- B17. The range `u+1 ≤ p` is essential; coefficients outside it can be negative. -/
theorem segreCoeff_nonnegative (p u : ℕ) (hpu : u + 1 ≤ p) :
    0 ≤ segreCoeff p u := by
  have hmain : ∀ p u, u + 1 ≤ p → 0 ≤ segreCoeff p u := by
    intro p
    induction p using Nat.strong_induction_on with
    | h p ih =>
      intro u hpu
      cases u with
      | zero =>
        rw [segreCoeff_zero]
        norm_num
      | succ u =>
        by_cases hu : u = 0
        · subst u
          rw [segreCoeff_one]
          exact sub_nonneg.mpr (by exact_mod_cast hpu)
        · have hu' : 2 ≤ u + 1 := by omega
          have hp' : 2 ≤ p := by omega
          have hrec := segreCoeff_two_step p (u + 1) hp' hu'
          rw [hrec]
          apply add_nonneg
          · exact Int.natCast_nonneg _
          · apply ih (p - 2) (by omega) (u - 1)
            omega
  exact hmain p u hpu

section FormalSeries

variable {R : Type*} [CommRing R]

private theorem coeff_linear_mul (b : R) (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n ((1 + PowerSeries.C b * PowerSeries.X) * f) =
      PowerSeries.coeff n f + if n = 0 then 0 else b * PowerSeries.coeff (n - 1) f := by
  rw [add_mul, one_mul, map_add, mul_assoc, PowerSeries.coeff_C_mul]
  rw [← pow_one (PowerSeries.X : PowerSeries R), PowerSeries.coeff_X_pow_mul']
  cases n <;> simp

private theorem coeff_one_add_CX_pow (a : R) (p n : ℕ) :
    PowerSeries.coeff n ((1 + PowerSeries.C a * PowerSeries.X) ^ p) =
      (p.choose n : R) * a ^ n := by
  have hrescale : PowerSeries.rescale a ((1 + PowerSeries.X : PowerSeries R) ^ p) =
      (1 + PowerSeries.C a * PowerSeries.X) ^ p := by
    simp [PowerSeries.rescale_X]
  rw [← hrescale, PowerSeries.coeff_rescale]
  have hpow : (1 + PowerSeries.X : PowerSeries R) ^ p =
      ((((1 : Polynomial R) + Polynomial.X) ^ p : Polynomial R) : PowerSeries R) := by
    simp
  rw [hpow, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
  ring

private theorem scaledScalarSegreSeries_coeff (a : R) (p n : ℕ) :
    PowerSeries.coeff n
        ((1 + PowerSeries.C a * PowerSeries.X) ^ p *
          PowerSeries.invOfUnit (1 + PowerSeries.C (2 * a) * PowerSeries.X) 1) =
      ((segreCoeff p n : ℤ) : R) * a ^ n := by
  let φ : PowerSeries ℤ →+* PowerSeries R := PowerSeries.map (Int.castRingHom R)
  let invZ : PowerSeries ℤ := PowerSeries.invOfUnit
    (1 + 2 * PowerSeries.X) 1
  let invR : PowerSeries R := PowerSeries.invOfUnit
    (1 + PowerSeries.C (2 * a) * PowerSeries.X) 1
  let resInv : PowerSeries R := PowerSeries.rescale a (φ invZ)
  have hmulZ : (1 + 2 * PowerSeries.X : PowerSeries ℤ) * invZ = 1 := by
    apply PowerSeries.mul_invOfUnit
    simp [invZ]
  have hnumZ : (2 : PowerSeries ℤ) = PowerSeries.C (2 : ℤ) :=
    (map_natCast (PowerSeries.C (R := ℤ)) 2).symm
  have hnumR : (2 : PowerSeries R) = PowerSeries.C (2 : R) :=
    (map_natCast (PowerSeries.C (R := R)) 2).symm
  have hmaptwo : φ (2 : PowerSeries ℤ) = (2 : PowerSeries R) := by
    rw [hnumZ, PowerSeries.map_C]
    calc
      PowerSeries.C ((Int.castRingHom R) (2 : ℤ)) = PowerSeries.C (2 : R) := by
        congr 1
        norm_num
      _ = (2 : PowerSeries R) := hnumR.symm
  have htwoR : PowerSeries.rescale a (2 : PowerSeries R) =
      (2 : PowerSeries R) := by
    calc
      PowerSeries.rescale a (2 : PowerSeries R) =
          PowerSeries.rescale a (PowerSeries.C (2 : R)) := by rw [hnumR]
      _ = PowerSeries.C (2 : R) := by
        ext n
        cases n <;> simp [PowerSeries.coeff_rescale]
      _ = (2 : PowerSeries R) := hnumR.symm
  have hden : PowerSeries.rescale a
      (φ (1 + 2 * PowerSeries.X : PowerSeries ℤ)) =
        1 + PowerSeries.C (2 * a) * PowerSeries.X := by
    calc
      PowerSeries.rescale a (φ (1 + 2 * PowerSeries.X : PowerSeries ℤ)) =
          PowerSeries.rescale a (1 + 2 * PowerSeries.X) := by
        congr 1
        rw [map_add φ, map_mul φ, map_one, PowerSeries.map_X, hmaptwo]
      _ = 1 + (2 : PowerSeries R) * (PowerSeries.C a * PowerSeries.X) := by
        rw [map_add (PowerSeries.rescale a), map_mul (PowerSeries.rescale a),
          map_one, htwoR, PowerSeries.rescale_X]
      _ = 1 + PowerSeries.C (2 : R) * (PowerSeries.C a * PowerSeries.X) := by
        rw [hnumR]
      _ = 1 + (PowerSeries.C (2 : R) * PowerSeries.C a) * PowerSeries.X := by ring
      _ = 1 + PowerSeries.C (2 * a) * PowerSeries.X := by
        rw [← map_mul (PowerSeries.C (R := R)) (2 : R) a]
  have hmulR : (1 + PowerSeries.C (2 * a) * PowerSeries.X : PowerSeries R) * resInv = 1 := by
    have h := congrArg (fun f : PowerSeries ℤ => PowerSeries.rescale a (φ f)) hmulZ
    have hm : PowerSeries.rescale a (φ (1 + 2 * PowerSeries.X : PowerSeries ℤ)) * resInv = 1 := by
      simpa [φ, resInv] using h
    rw [hden] at hm
    exact hm
  have hinvR : invR * (1 + PowerSeries.C (2 * a) * PowerSeries.X) = 1 := by
    apply PowerSeries.invOfUnit_mul
    simp [invR]
  have hresInv : resInv = invR := by
    calc
      resInv = 1 * resInv := by simp
      _ = (invR * (1 + PowerSeries.C (2 * a) * PowerSeries.X)) * resInv := by rw [hinvR]
      _ = invR * ((1 + PowerSeries.C (2 * a) * PowerSeries.X) * resInv) := by ac_rfl
      _ = invR := by rw [hmulR]; simp
  have hseries :
      PowerSeries.rescale a (φ (scalarSegreSeries p)) =
        (1 + PowerSeries.C a * PowerSeries.X) ^ p * invR := by
    rw [scalarSegreSeries, map_mul, map_pow]
    simp [φ, invZ, invR, resInv, hresInv, PowerSeries.rescale_X]
  rw [← hseries, PowerSeries.coeff_rescale, PowerSeries.coeff_map, scalarSegreSeries_coeff]
  simp [mul_comm]

/-- The specific inverse-Chern expression; this definition is formal algebra only. -/
noncomputable def incidenceSegreSeries (e : ℕ) (a ell : R) : PowerSeries R :=
  (1 + PowerSeries.C a * PowerSeries.X) ^ e *
    PowerSeries.invOfUnit (1 + PowerSeries.C (2 * a) * PowerSeries.X) 1 *
    PowerSeries.invOfUnit (1 + PowerSeries.C (a - ell) * PowerSeries.X) 1

/-- B14, concentration.tex:731–735, the formal unit-denominator identity. -/
theorem incidenceSegreSeries_identity (e : ℕ) (a ell : R) :
    (1 + PowerSeries.C (2 * a) * PowerSeries.X) *
      (1 + PowerSeries.C (a - ell) * PowerSeries.X) *
      incidenceSegreSeries e a ell =
        (1 + PowerSeries.C a * PowerSeries.X) ^ e := by
  have h₂ : (1 + PowerSeries.C (2 * a) * PowerSeries.X) *
      PowerSeries.invOfUnit (1 + PowerSeries.C (2 * a) * PowerSeries.X) 1 = 1 := by
    apply PowerSeries.mul_invOfUnit
    simp
  have h₃ : (1 + PowerSeries.C (a - ell) * PowerSeries.X) *
      PowerSeries.invOfUnit (1 + PowerSeries.C (a - ell) * PowerSeries.X) 1 = 1 := by
    apply PowerSeries.mul_invOfUnit
    simp
  unfold incidenceSegreSeries
  calc
    (1 + PowerSeries.C (2 * a) * PowerSeries.X) *
        (1 + PowerSeries.C (a - ell) * PowerSeries.X) *
        ((1 + PowerSeries.C a * PowerSeries.X) ^ e *
          PowerSeries.invOfUnit (1 + PowerSeries.C (2 * a) * PowerSeries.X) 1 *
          PowerSeries.invOfUnit (1 + PowerSeries.C (a - ell) * PowerSeries.X) 1) =
      ((1 + PowerSeries.C (2 * a) * PowerSeries.X) *
          PowerSeries.invOfUnit (1 + PowerSeries.C (2 * a) * PowerSeries.X) 1) *
        ((1 + PowerSeries.C (a - ell) * PowerSeries.X) *
          PowerSeries.invOfUnit (1 + PowerSeries.C (a - ell) * PowerSeries.X) 1) *
        (1 + PowerSeries.C a * PowerSeries.X) ^ e := by ring
    _ = (1 + PowerSeries.C a * PowerSeries.X) ^ e := by rw [h₂, h₃]; ring

/-- B15, concentration.tex:737–748. All exponents are nonnegative in this range. -/
private def incidenceSegreCoeffFormula (e h : ℕ) (a ell : R) : R :=
  ∑ i ∈ Finset.range (h + 1),
    (segreCoeff (e - 1 - i) (h - i) : R) * ell ^ i * a ^ (h - i)

private theorem sum_range_succ_shift (f : ℕ → R) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), f (i + 1)) =
      (∑ i ∈ Finset.range (n + 2), f i) - f 0 := by
  induction n with
  | zero =>
    simp [Finset.sum_range_succ]
  | succ n ih =>
    calc
      (∑ i ∈ Finset.range (Nat.succ n + 1), f (i + 1)) =
          (∑ i ∈ Finset.range (n + 1), f (i + 1)) + f (n + 2) := by
            rw [show Nat.succ n + 1 = n + 1 + 1 by omega, Finset.sum_range_succ]
      _ = ((∑ i ∈ Finset.range (n + 2), f i) - f 0) + f (n + 2) := by rw [ih]
      _ = ((∑ i ∈ Finset.range (n + 2), f i) + f (n + 2)) - f 0 := by ring
      _ = (∑ i ∈ Finset.range (n + 3), f i) - f 0 := by
            conv_rhs =>
              rw [show n + 3 = n + 2 + 1 by omega, Finset.sum_range_succ]

private theorem incidenceSegreCoeffFormula_add_scalar (e h : ℕ) (a ell : R)
    (hhe : h + 3 ≤ e) :
    incidenceSegreCoeffFormula e (h + 1) a ell +
        a * incidenceSegreCoeffFormula e h a ell =
      ∑ i ∈ Finset.range (h + 2),
        (segreCoeff (e - i) (h + 1 - i) : R) * ell ^ i * a ^ (h + 1 - i) := by
  let f : ℕ → R := fun i =>
    (segreCoeff (e - 1 - i) (h + 1 - i) : R) * ell ^ i * a ^ (h + 1 - i)
  let g : ℕ → R := fun i =>
    (segreCoeff (e - 1 - i) (h - i) : R) * ell ^ i * a ^ (h - i)
  let b : ℕ → R := fun i =>
    (segreCoeff (e - i) (h + 1 - i) : R) * ell ^ i * a ^ (h + 1 - i)
  have hterm (i : ℕ) (hi : i ∈ Finset.range (h + 1)) : f i + a * g i = b i := by
    have hi' : i ≤ h := by have := Finset.mem_range.mp hi; omega
    have hrec := segreCoeff_succ_left (e - 1 - i) (h + 1 - i) (by omega)
    rw [show (e - 1 - i) + 1 = e - i by omega,
      show (h + 1 - i) - 1 = h - i by omega] at hrec
    have hrecR : (segreCoeff (e - i) (h + 1 - i) : R) =
        (segreCoeff (e - 1 - i) (h + 1 - i) : R) +
          (segreCoeff (e - 1 - i) (h - i) : R) := by
      simpa using congrArg (Int.castRingHom R) hrec
    dsimp [f, g, b]
    rw [hrecR]
    rw [show h + 1 - i = (h - i) + 1 by omega, pow_succ]
    ring
  have hlast : f (h + 1) = b (h + 1) := by
    simp [f, b, segreCoeff_zero]
  calc
    incidenceSegreCoeffFormula e (h + 1) a ell +
        a * incidenceSegreCoeffFormula e h a ell =
      (∑ i ∈ Finset.range (h + 2), f i) +
          a * (∑ i ∈ Finset.range (h + 1), g i) := by
        simp only [incidenceSegreCoeffFormula, f, g,
          show h + 1 + 1 = h + 2 by omega]
    _ = (∑ i ∈ Finset.range (h + 1), f i) + f (h + 1) +
          a * (∑ i ∈ Finset.range (h + 1), g i) := by
        rw [Finset.sum_range_succ]
    _ = (∑ i ∈ Finset.range (h + 1), f i) +
          a * (∑ i ∈ Finset.range (h + 1), g i) + f (h + 1) := by ring
    _ = (∑ i ∈ Finset.range (h + 1), (f i + a * g i)) + f (h + 1) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ = (∑ i ∈ Finset.range (h + 1), b i) + b (h + 1) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          exact hterm i hi
    _ = ∑ i ∈ Finset.range (h + 2), b i := by
        conv_rhs => rw [Finset.sum_range_succ]

private theorem incidenceSegreCoeffFormula_ell_shift (e h : ℕ) (a ell : R)
    (hhe : h + 3 ≤ e) :
    ell * incidenceSegreCoeffFormula e h a ell =
      (∑ i ∈ Finset.range (h + 2),
        (segreCoeff (e - i) (h + 1 - i) : R) * ell ^ i * a ^ (h + 1 - i)) -
        (segreCoeff e (h + 1) : R) * a ^ (h + 1) := by
  let g : ℕ → R := fun i =>
    (segreCoeff (e - 1 - i) (h - i) : R) * ell ^ i * a ^ (h - i)
  let b : ℕ → R := fun i =>
    (segreCoeff (e - i) (h + 1 - i) : R) * ell ^ i * a ^ (h + 1 - i)
  have hterm (i : ℕ) (hi : i ∈ Finset.range (h + 1)) : ell * g i = b (i + 1) := by
    have hi' : i ≤ h := by have := Finset.mem_range.mp hi; omega
    have hp : e - (i + 1) = e - 1 - i := by omega
    have hu : h + 1 - (i + 1) = h - i := by omega
    dsimp [g, b]
    rw [hp, hu, pow_succ]
    ring
  calc
    ell * incidenceSegreCoeffFormula e h a ell =
        ∑ i ∈ Finset.range (h + 1), ell * g i := by
      simp only [incidenceSegreCoeffFormula, g]
      rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range (h + 1), b (i + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i hi
    _ = (∑ i ∈ Finset.range (h + 2), b i) - b 0 :=
      sum_range_succ_shift b h
    _ = (∑ i ∈ Finset.range (h + 2), b i) -
          (segreCoeff e (h + 1) : R) * a ^ (h + 1) := by
      simp [b]

private theorem incidenceSegreCoeffFormula_succ (e h : ℕ) (a ell : R)
    (hhe : h + 3 ≤ e) :
    incidenceSegreCoeffFormula e (h + 1) a ell +
        (a - ell) * incidenceSegreCoeffFormula e h a ell =
      (segreCoeff e (h + 1) : R) * a ^ (h + 1) := by
  rw [sub_mul]
  calc
    incidenceSegreCoeffFormula e (h + 1) a ell +
        (a * incidenceSegreCoeffFormula e h a ell -
          ell * incidenceSegreCoeffFormula e h a ell) =
      (incidenceSegreCoeffFormula e (h + 1) a ell +
        a * incidenceSegreCoeffFormula e h a ell) -
        ell * incidenceSegreCoeffFormula e h a ell := by ring
    _ = (∑ i ∈ Finset.range (h + 2),
          (segreCoeff (e - i) (h + 1 - i) : R) * ell ^ i * a ^ (h + 1 - i)) -
        ((∑ i ∈ Finset.range (h + 2),
          (segreCoeff (e - i) (h + 1 - i) : R) * ell ^ i * a ^ (h + 1 - i)) -
          (segreCoeff e (h + 1) : R) * a ^ (h + 1)) := by
      rw [incidenceSegreCoeffFormula_add_scalar e h a ell hhe,
        incidenceSegreCoeffFormula_ell_shift e h a ell hhe]
    _ = (segreCoeff e (h + 1) : R) * a ^ (h + 1) := by ring

theorem incidenceSegreSeries_coeff (e h : ℕ) (a ell : R) (hhe : h + 2 ≤ e) :
    PowerSeries.coeff h (incidenceSegreSeries e a ell) =
      ∑ i ∈ Finset.range (h + 1),
        (segreCoeff (e - 1 - i) (h - i) : R) * ell ^ i * a ^ (h - i) := by
  have hunit : (1 + PowerSeries.C (a - ell) * PowerSeries.X : PowerSeries R) *
      PowerSeries.invOfUnit (1 + PowerSeries.C (a - ell) * PowerSeries.X) 1 = 1 := by
    apply PowerSeries.mul_invOfUnit
    simp
  have hprod :
      (1 + PowerSeries.C (a - ell) * PowerSeries.X) * incidenceSegreSeries e a ell =
        (1 + PowerSeries.C a * PowerSeries.X) ^ e *
          PowerSeries.invOfUnit (1 + PowerSeries.C (2 * a) * PowerSeries.X) 1 := by
    unfold incidenceSegreSeries
    calc
      (1 + PowerSeries.C (a - ell) * PowerSeries.X) *
          ((1 + PowerSeries.C a * PowerSeries.X) ^ e *
            PowerSeries.invOfUnit (1 + PowerSeries.C (2 * a) * PowerSeries.X) 1 *
            PowerSeries.invOfUnit (1 + PowerSeries.C (a - ell) * PowerSeries.X) 1) =
        ((1 + PowerSeries.C a * PowerSeries.X) ^ e *
            PowerSeries.invOfUnit (1 + PowerSeries.C (2 * a) * PowerSeries.X) 1) *
          ((1 + PowerSeries.C (a - ell) * PowerSeries.X) *
            PowerSeries.invOfUnit (1 + PowerSeries.C (a - ell) * PowerSeries.X) 1) := by ring
      _ = (1 + PowerSeries.C a * PowerSeries.X) ^ e *
          PowerSeries.invOfUnit (1 + PowerSeries.C (2 * a) * PowerSeries.X) 1 := by
        rw [hunit]
        ring
  have hrec (n : ℕ) :
      PowerSeries.coeff (n + 1) (incidenceSegreSeries e a ell) +
          (a - ell) * PowerSeries.coeff n (incidenceSegreSeries e a ell) =
        (segreCoeff e (n + 1) : R) * a ^ (n + 1) := by
    have hc := congrArg (PowerSeries.coeff (n + 1)) hprod
    rw [coeff_linear_mul] at hc
    rw [scaledScalarSegreSeries_coeff a e (n + 1)] at hc
    simpa using hc
  have hmain : ∀ n, n + 2 ≤ e →
      PowerSeries.coeff n (incidenceSegreSeries e a ell) =
        incidenceSegreCoeffFormula e n a ell := by
    intro n
    induction n with
    | zero =>
      intro hn
      simp [incidenceSegreSeries, incidenceSegreCoeffFormula, segreCoeff_zero]
    | succ n ih =>
      intro hn
      have hprev : n + 2 ≤ e := by omega
      have hp := ih hprev
      have hs := hrec n
      rw [hp] at hs
      have hf := incidenceSegreCoeffFormula_succ e n a ell (by omega)
      exact add_right_cancel (hs.trans hf.symm)
  change PowerSeries.coeff h (incidenceSegreSeries e a ell) =
    incidenceSegreCoeffFormula e h a ell
  exact hmain h hhe

end FormalSeries

/-- B19's arithmetic step. The mixed degrees and the two geometric identities are inputs,
not fields used to define an incidence. concentration.tex:777–783. -/
theorem degreeComparison_of_mixedDegrees (e h : ℕ) (hhe : h + 2 ≤ e)
    (m : ℕ → ℝ) (parameterDegree pointDegree fiberDegree fiberBound integral : ℝ)
    (hm : ∀ i ≤ h, 0 ≤ m i)
    (htop : m h = parameterDegree)
    (hbundle : integral = ∑ i ∈ Finset.range (h + 1),
      (segreCoeff (e - 1 - i) (h - i) : ℝ) * m i)
    (hpoint : integral = fiberDegree * pointDegree)
    (hdegree : 0 ≤ pointDegree) (hfiber : fiberDegree ≤ fiberBound) :
    parameterDegree ≤ fiberBound * pointDegree := by
  have hcoeff (i : ℕ) (hi : i ≤ h) :
      0 ≤ (segreCoeff (e - 1 - i) (h - i) : ℝ) := by
    have hpos : 0 ≤ segreCoeff (e - 1 - i) (h - i) :=
      segreCoeff_nonnegative _ _ (by omega)
    exact_mod_cast hpos
  have hterms (i : ℕ) (hi : i ∈ Finset.range (h + 1)) :
      0 ≤ (segreCoeff (e - 1 - i) (h - i) : ℝ) * m i := by
    apply mul_nonneg (hcoeff i (by have := Finset.mem_range.mp hi; omega))
    exact hm i (by have := Finset.mem_range.mp hi; omega)
  have hlast : (segreCoeff (e - 1 - h) (h - h) : ℝ) = 1 := by
    simp [segreCoeff_zero]
  have hsum := Finset.single_le_sum hterms
    (Finset.mem_range.mpr (by omega : h < h + 1))
  have hparameter_le_integral : parameterDegree ≤ integral := by
    calc
      parameterDegree = 1 * m h := by rw [htop]; ring
      _ = (segreCoeff (e - 1 - h) (h - h) : ℝ) * m h := by rw [hlast]
      _ ≤ ∑ i ∈ Finset.range (h + 1),
            (segreCoeff (e - 1 - i) (h - i) : ℝ) * m i := hsum
      _ = integral := hbundle.symm
  calc
    parameterDegree ≤ integral := hparameter_le_integral
    _ = fiberDegree * pointDegree := hpoint
    _ ≤ fiberBound * pointDegree := mul_le_mul_of_nonneg_right hfiber hdegree

end DistinctDistances.TrackB
