import DistinctDistances.TrackD.Profiles.Defs

open scoped BigOperators Classical

namespace DistinctDistances
namespace TrackD

noncomputable section

private theorem first_exp_power_bound {x C : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x) :
    C * (1 + Real.sqrt (Real.log x)) * Real.exp (-(x ^ ((1 : ℝ) / 10)) / 2) ≤
      C * (2 * (2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) / x ^ 2 := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hlog : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hxpos).trans (by linarith)
  have hsqrtlog : Real.sqrt (Real.log x) ≤ Real.sqrt x :=
    (Real.sqrt_le_sqrt_iff (le_trans (by norm_num) hx)).mpr hlog
  have hsqrtone : 1 ≤ Real.sqrt x := by
    rw [← Real.sqrt_one]
    exact (Real.sqrt_le_sqrt_iff (by linarith : (0 : ℝ) ≤ x)).mpr hx
  have hsqrtle : Real.sqrt x ≤ x := (Real.sqrt_le_self_iff).mpr (Or.inr hx)
  let z : ℝ := x ^ ((1 : ℝ) / 10) / 2
  have hz0 : 0 ≤ z := by positivity
  have hzpow : z ^ 30 = x ^ 3 / (2 : ℝ) ^ 30 := by
    dsimp [z]
    calc
      (x ^ ((1 : ℝ) / 10) / 2) ^ 30 = (x ^ ((1 : ℝ) / 10)) ^ 30 / (2 : ℝ) ^ 30 := by rw [div_pow]
      _ = x ^ (((1 : ℝ) / 10) * (30 : ℝ)) / (2 : ℝ) ^ 30 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
        norm_num
      _ = x ^ 3 / (2 : ℝ) ^ 30 := by norm_num
  have htaylor := Real.pow_div_factorial_le_exp (x := z) hz0 30
  rw [hzpow] at htaylor
  have hTaylor : x ^ 3 / ((2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) ≤ Real.exp z := by
    calc
      x ^ 3 / ((2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) = (x ^ 3 / (2 : ℝ) ^ 30) / (Nat.factorial 30 : ℝ) := by ring
      _ ≤ Real.exp z := htaylor
  have hApos : 0 < x ^ 3 / ((2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) := by positivity
  have hrecip := one_div_le_one_div_of_le hApos hTaylor
  have hexp : Real.exp (-z) ≤ ((2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) / x ^ 3 := by
    calc
      Real.exp (-z) = 1 / Real.exp z := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / (x ^ 3 / ((2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ))) := hrecip
      _ = ((2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) / x ^ 3 := by field_simp
  have hpref : 1 + Real.sqrt (Real.log x) ≤ 2 * Real.sqrt x := by linarith
  have hratio : Real.sqrt x / x ≤ 1 := (div_le_one hxpos).2 hsqrtle
  have hfactor : (2 * Real.sqrt x) * (((2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) / x ^ 3) ≤
      (2 * (2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) / x ^ 2 := by
    have hK : 0 ≤ (2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ) := by positivity
    have hbase : 0 ≤ (2 * (2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) / x ^ 2 := by positivity
    calc
      (2 * Real.sqrt x) * (((2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) / x ^ 3) =
          ((2 * (2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) / x ^ 2) * (Real.sqrt x / x) := by field_simp
      _ ≤ (2 * (2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) / x ^ 2 := by
          calc
            _ ≤ ((2 * (2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) / x ^ 2) * 1 :=
              mul_le_mul_of_nonneg_left hratio hbase
            _ = _ := by ring
  calc
    C * (1 + Real.sqrt (Real.log x)) * Real.exp (-(x ^ ((1 : ℝ) / 10)) / 2) ≤
        C * (2 * Real.sqrt x) * Real.exp (-z) := by
          have heq : Real.exp (-(x ^ ((1 : ℝ) / 10)) / 2) = Real.exp (-z) := by
            congr 1
            dsimp [z]
            ring
          rw [heq]
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hpref hC
          · positivity
    _ ≤ C * (2 * Real.sqrt x) * (((2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) / x ^ 3) := by
          apply mul_le_mul_of_nonneg_left hexp
          positivity
    _ ≤ C * ((2 * (2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) / x ^ 2) := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hfactor hC
    _ = C * (2 * (2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) / x ^ 2 := by ring

private theorem second_exp_power_bound {x : ℝ} (hx : 1 ≤ x) :
    Real.exp (-(x ^ ((1 : ℝ) / 3))) ≤ (Nat.factorial 6 : ℝ) / x ^ 2 := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  let z : ℝ := x ^ ((1 : ℝ) / 3)
  have hz0 : 0 ≤ z := by positivity
  have hzpow : z ^ 6 = x ^ 2 := by
    dsimp [z]
    calc
      (x ^ ((1 : ℝ) / 3)) ^ 6 = x ^ (((1 : ℝ) / 3) * (6 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
        norm_num
      _ = x ^ 2 := by norm_num
  have htaylor := Real.pow_div_factorial_le_exp (x := z) hz0 6
  rw [hzpow] at htaylor
  have hTaylor : x ^ 2 / (Nat.factorial 6 : ℝ) ≤ Real.exp z := by simpa using htaylor
  have hApos : 0 < x ^ 2 / (Nat.factorial 6 : ℝ) := by positivity
  have hrecip := one_div_le_one_div_of_le hApos hTaylor
  calc
    Real.exp (-z) = 1 / Real.exp z := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / (x ^ 2 / (Nat.factorial 6 : ℝ)) := hrecip
    _ = (Nat.factorial 6 : ℝ) / x ^ 2 := by field_simp

private theorem inv_scale_sq_le {m : ℕ} {u : ℝ} (hu : 1 ≤ u) :
    1 / (((2 : ℝ) ^ m * u) ^ 2) ≤ (1 / u ^ 2) * ((1 : ℝ) / 2) ^ m := by
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hb : 1 ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hbpos : 0 < (2 : ℝ) ^ m := lt_of_lt_of_le (by norm_num) hb
  have hb2 : (2 : ℝ) ^ m ≤ ((2 : ℝ) ^ m) ^ 2 := by nlinarith
  have hinv : 1 / (((2 : ℝ) ^ m) ^ 2) ≤ 1 / (2 : ℝ) ^ m :=
    one_div_le_one_div_of_le hbpos (by simpa using hb2)
  have hpow : 1 / (2 : ℝ) ^ m = ((1 : ℝ) / 2) ^ m := by
    simp [one_div, inv_pow]
  calc
    1 / (((2 : ℝ) ^ m * u) ^ 2) = (1 / u ^ 2) * (1 / (((2 : ℝ) ^ m) ^ 2)) := by field_simp
    _ ≤ (1 / u ^ 2) * (1 / (2 : ℝ) ^ m) := mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (1 / u ^ 2) * ((1 : ℝ) / 2) ^ m := by rw [hpow]

private noncomputable def firstSeries (C u : ℝ) (m : ℕ) : ℝ :=
  C * (1 + Real.sqrt (Real.log ((2 : ℝ) ^ m * u))) *
    Real.exp (-(((2 : ℝ) ^ m * u) ^ ((1 : ℝ) / 10)) / 2)

private noncomputable def secondSeries (u : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-((2 : ℝ) ^ m * u) ^ ((1 : ℝ) / 3))

private theorem firstSeries_le (C u : ℝ) (hC : 0 ≤ C) (hu : 1 ≤ u) (m : ℕ) :
      firstSeries C u m ≤ (C * (2 * (2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) / u ^ 2) * ((1 : ℝ) / 2) ^ m := by
  have hb : 1 ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hx : 1 ≤ (2 : ℝ) ^ m * u := by nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ) ^ m by positivity) (show 0 ≤ u by linarith)]
  have hpoint := first_exp_power_bound hC hx
  have hscale := inv_scale_sq_le hu (m := m)
  dsimp [firstSeries]
  calc
    C * (1 + Real.sqrt (Real.log ((2 : ℝ) ^ m * u))) *
        Real.exp (-(((2 : ℝ) ^ m * u) ^ ((1 : ℝ) / 10)) / 2) ≤
        C * (2 * (2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) / ((2 : ℝ) ^ m * u) ^ 2 := hpoint
    _ ≤ (C * (2 * (2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ)) / u ^ 2) * ((1 : ℝ) / 2) ^ m := by
      let A : ℝ := C * (2 * (2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ))
      have hA : 0 ≤ A := by positivity
      calc
        A / ((2 : ℝ) ^ m * u) ^ 2 = A * (1 / ((2 : ℝ) ^ m * u) ^ 2) := by ring
        _ ≤ A * ((1 / u ^ 2) * ((1 : ℝ) / 2) ^ m) := mul_le_mul_of_nonneg_left hscale hA
        _ = (A / u ^ 2) * ((1 : ℝ) / 2) ^ m := by ring

private theorem secondSeries_le (u : ℝ) (hu : 1 ≤ u) (m : ℕ) :
    secondSeries u m ≤ ((Nat.factorial 6 : ℝ) / u ^ 2) * ((1 : ℝ) / 2) ^ m := by
  have hx : 1 ≤ (2 : ℝ) ^ m * u := by
    have hb : 1 ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ) ^ m by positivity) (show 0 ≤ u by linarith)]
  have hpoint := second_exp_power_bound hx
  have hscale := inv_scale_sq_le hu (m := m)
  dsimp [secondSeries]
  calc
    Real.exp (-((2 : ℝ) ^ m * u) ^ ((1 : ℝ) / 3)) ≤ (Nat.factorial 6 : ℝ) / ((2 : ℝ) ^ m * u) ^ 2 := hpoint
    _ ≤ ((Nat.factorial 6 : ℝ) / u ^ 2) * ((1 : ℝ) / 2) ^ m := by
      let A : ℝ := Nat.factorial 6
      have hA : 0 ≤ A := by positivity
      calc
        A / ((2 : ℝ) ^ m * u) ^ 2 = A * (1 / ((2 : ℝ) ^ m * u) ^ 2) := by ring
        _ ≤ A * ((1 / u ^ 2) * ((1 : ℝ) / 2) ^ m) := mul_le_mul_of_nonneg_left hscale hA
        _ = (A / u ^ 2) * ((1 : ℝ) / 2) ^ m := by ring

theorem prof_partition_discard_aux (C : ℝ) (hC : 0 ≤ C) :
    ∀ ε > 0, ∃ u₀ : ℝ, ∀ u ≥ u₀,
      Summable (fun m : ℕ => C * (1 + Real.sqrt (Real.log (2 ^ m * u))) *
        Real.exp (-(2 ^ m * u) ^ ((1 : ℝ) / 10) / 2)) ∧
      ∑' m : ℕ, C * (1 + Real.sqrt (Real.log (2 ^ m * u))) *
        Real.exp (-(2 ^ m * u) ^ ((1 : ℝ) / 10) / 2) ≤ ε ∧
      Summable (fun m : ℕ => Real.exp (-(2 ^ m * u) ^ ((1 : ℝ) / 3))) ∧
      ∑' m : ℕ, Real.exp (-(2 ^ m * u) ^ ((1 : ℝ) / 3)) ≤ ε := by
  intro ε hε
  let A₁ : ℝ := C * (2 * (2 : ℝ) ^ 30 * (Nat.factorial 30 : ℝ))
  let A₂ : ℝ := Nat.factorial 6
  let D₁ : ℝ := 2 * A₁
  let D₂ : ℝ := 2 * A₂
  let M : ℝ := max D₁ D₂
  let u₀ : ℝ := Real.sqrt (M / ε + 1)
  have hA₁ : 0 ≤ A₁ := by positivity
  have hA₂ : 0 ≤ A₂ := by positivity
  have hD₁ : 0 ≤ D₁ := by positivity
  have hD₂ : 0 ≤ D₂ := by positivity
  have hM : 0 ≤ M := by dsimp [M]; exact le_trans hD₁ (le_max_left _ _)
  have hD₁M : D₁ ≤ M := by dsimp [M]; exact le_max_left _ _
  have hD₂M : D₂ ≤ M := by dsimp [M]; exact le_max_right _ _
  have hroot : u₀ ^ 2 = M / ε + 1 := by
    dsimp [u₀]
    exact Real.sq_sqrt (by positivity)
  have hu₀ : 1 ≤ u₀ := by
    dsimp [u₀]
    have hfrac : 0 ≤ M / ε := div_nonneg hM hε.le
    have harg : 1 ≤ M / ε + 1 := by linarith
    have harg0 : 0 ≤ M / ε + 1 := by linarith
    have h := (Real.sqrt_le_sqrt_iff harg0).2 harg
    simpa using h
  have hMle : M ≤ ε * u₀ ^ 2 := by
    rw [hroot]
    have hdiv : ε * (M / ε) = M := by field_simp [ne_of_gt hε]
    calc
      M ≤ ε * (M / ε) + ε := by rw [hdiv]; nlinarith [hε]
      _ = ε * (M / ε + 1) := by ring
  refine ⟨u₀, ?_⟩
  intro u hu
  have hu0 : 1 ≤ u := hu₀.trans hu
  have huPos : 0 < u := lt_of_lt_of_le (by norm_num) hu0
  have huSq : u₀ ^ 2 ≤ u ^ 2 := by
    calc
      u₀ ^ 2 = u₀ * u₀ := by ring
      _ ≤ u * u₀ := mul_le_mul_of_nonneg_right hu (Real.sqrt_nonneg _)
      _ ≤ u * u := mul_le_mul_of_nonneg_left hu huPos.le
      _ = u ^ 2 := by ring
  have hD₁u : D₁ ≤ ε * u ^ 2 := by
    calc
      D₁ ≤ M := hD₁M
      _ ≤ ε * u₀ ^ 2 := hMle
      _ ≤ ε * u ^ 2 := mul_le_mul_of_nonneg_left huSq hε.le
  have hD₂u : D₂ ≤ ε * u ^ 2 := by
    calc
      D₂ ≤ M := hD₂M
      _ ≤ ε * u₀ ^ 2 := hMle
      _ ≤ ε * u ^ 2 := mul_le_mul_of_nonneg_left huSq hε.le
  have hD₁div : D₁ / u ^ 2 ≤ ε := (div_le_iff₀ (by positivity)).2 hD₁u
  have hD₂div : D₂ / u ^ 2 ≤ ε := (div_le_iff₀ (by positivity)).2 hD₂u
  have hgeom₁ : Summable (fun m : ℕ => (A₁ / u ^ 2) * ((1 : ℝ) / 2) ^ m) :=
    (summable_geometric_two).mul_left (A₁ / u ^ 2)
  have hgeom₂ : Summable (fun m : ℕ => (A₂ / u ^ 2) * ((1 : ℝ) / 2) ^ m) :=
    (summable_geometric_two).mul_left (A₂ / u ^ 2)
  have hpoint₁ (m : ℕ) : firstSeries C u m ≤ (A₁ / u ^ 2) * ((1 : ℝ) / 2) ^ m := by
    simpa [A₁, div_eq_mul_inv, mul_assoc] using firstSeries_le C u hC hu0 m
  have hpoint₂ (m : ℕ) : secondSeries u m ≤ (A₂ / u ^ 2) * ((1 : ℝ) / 2) ^ m := by
    simpa [A₂] using secondSeries_le u hu0 m
  have hsum₁ : Summable (firstSeries C u) :=
    Summable.of_nonneg_of_le (fun m => by dsimp [firstSeries]; positivity) hpoint₁ hgeom₁
  have hsum₂ : Summable (secondSeries u) :=
    Summable.of_nonneg_of_le (fun m => by dsimp [secondSeries]; positivity) hpoint₂ hgeom₂
  have htsum₁ : ∑' m : ℕ, firstSeries C u m ≤ (A₁ / u ^ 2) * 2 := by
    calc
      ∑' m : ℕ, firstSeries C u m ≤ ∑' m : ℕ, (A₁ / u ^ 2) * ((1 : ℝ) / 2) ^ m :=
        hsum₁.tsum_le_tsum hpoint₁ hgeom₁
      _ = (A₁ / u ^ 2) * 2 := by rw [tsum_mul_left, tsum_geometric_two]
  have htsum₂ : ∑' m : ℕ, secondSeries u m ≤ (A₂ / u ^ 2) * 2 := by
    calc
      ∑' m : ℕ, secondSeries u m ≤ ∑' m : ℕ, (A₂ / u ^ 2) * ((1 : ℝ) / 2) ^ m :=
        hsum₂.tsum_le_tsum hpoint₂ hgeom₂
      _ = (A₂ / u ^ 2) * 2 := by rw [tsum_mul_left, tsum_geometric_two]
  have htail₁ : (A₁ / u ^ 2) * 2 ≤ ε := by
    have : (A₁ / u ^ 2) * 2 = D₁ / u ^ 2 := by dsimp [D₁, A₁]; ring
    rw [this]
    exact hD₁div
  have htail₂ : (A₂ / u ^ 2) * 2 ≤ ε := by
    have : (A₂ / u ^ 2) * 2 = D₂ / u ^ 2 := by dsimp [D₂, A₂]; ring
    rw [this]
    exact hD₂div
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Summable (firstSeries C u)
    exact hsum₁
  · change (∑' m : ℕ, firstSeries C u m) ≤ ε
    exact htsum₁.trans htail₁
  · change Summable (secondSeries u)
    exact hsum₂
  · change (∑' m : ℕ, secondSeries u m) ≤ ε
    exact htsum₂.trans htail₂


end

end TrackD
end DistinctDistances
