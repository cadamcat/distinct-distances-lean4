import DistinctDistances.TrackC.Incidence
import DistinctDistances.TrackC.CircleAlgebra
import DistinctDistances.TrackC.PartitionHolder

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- Positive-radius Euclidean circles, with no multiplicities. -/
structure Circle where
  center : E 2
  radius : ℝ
  radius_pos : 0 < radius

def circleSet (c : Circle) : Set (E 2) := {x | dist x c.center = c.radius}
def onCircle (f : Poly 2) (c : Circle) : Prop := ∀ x ∈ circleSet c, evalR f x = 0

def circlePolynomial (c : Circle) : Poly 2 :=
  (MvPolynomial.X 0 - MvPolynomial.C (c.center 0)) ^ 2 +
  (MvPolynomial.X 1 - MvPolynomial.C (c.center 1)) ^ 2 -
  MvPolynomial.C (c.radius ^ 2)

def circleIncidences (X : Finset (E 2)) (C : Finset Circle) : ℕ :=
  ∑ x ∈ X, (C.filter (fun c => x ∈ circleSet c)).card

/-- Elementary circle geometry for the planar replacement; no paper counterpart.
Consumer: ci:weak-planar-distances. -/
theorem circle_intersections (c c' : Circle) (hne : c ≠ c') :
    FiniteCardBound (circleSet c ∩ circleSet c') 2 := by
  classical
  let S := circleSet c ∩ circleSet c'
  let s : EuclideanGeometry.Sphere (E 2) := ⟨c.center, c.radius⟩
  let s' : EuclideanGeometry.Sphere (E 2) := ⟨c'.center, c'.radius⟩
  have hs : s ≠ s' := by
    intro h
    have hc : c.center = c'.center := by
      exact congrArg EuclideanGeometry.Sphere.center h
    have hr : c.radius = c'.radius := by
      exact congrArg EuclideanGeometry.Sphere.radius h
    apply hne
    cases c with
    | mk center radius hpos =>
      cases c' with
      | mk center' radius' hpos' =>
        dsimp at hc hr
        subst center'
        subst radius'
        rfl
  have hencard : S.encard ≤ 2 := by
    by_cases hsmall : S.encard ≤ 1
    · exact hsmall.trans (by norm_num)
    · have hlarge : 1 < S.encard := lt_of_not_ge hsmall
      obtain ⟨p₁, p₂, hp₁, hp₂, hp₁₂⟩ := Set.one_lt_encard_iff.mp hlarge
      have hp₁s₁ : p₁ ∈ s := by
        change dist p₁ c.center = c.radius
        exact hp₁.1
      have hp₂s₁ : p₂ ∈ s := by
        change dist p₂ c.center = c.radius
        exact hp₂.1
      have hp₁s₂ : p₁ ∈ s' := by
        change dist p₁ c'.center = c'.radius
        exact hp₁.2
      have hp₂s₂ : p₂ ∈ s' := by
        change dist p₂ c'.center = c'.radius
        exact hp₂.2
      have hd : Module.finrank ℝ (E 2) = 2 := by simp [E]
      have hsubset : S ⊆ ({p₁, p₂} : Set (E 2)) := by
        intro p hp
        have hps₁ : p ∈ s := by
          change dist p c.center = c.radius
          exact hp.1
        have hps₂ : p ∈ s' := by
          change dist p c'.center = c'.radius
          exact hp.2
        have hpEq := EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
          hd hs hp₁₂ hp₁s₁ hp₂s₁ hps₁ hp₁s₂ hp₂s₂ hps₂
        rcases hpEq with h | h <;> simp [h]
      calc
        S.encard ≤ ({p₁, p₂} : Set (E 2)).encard := Set.encard_le_encard hsubset
        _ = 2 := Set.encard_pair hp₁₂
  have hfin : S.Finite := Set.finite_of_encard_le_coe hencard
  have hncard : S.ncard ≤ 2 :=
    (Set.encard_le_coe_iff_finite_ncard_le.mp hencard).2
  exact ⟨hfin, by exact_mod_cast hncard⟩

/-- Three distinct points belong to at most one positive-radius circle. -/
theorem circle_three_points (X : Finset (E 2)) (hX : X.card = 3) :
    FiniteCardBound {c : Circle | (X : Set (E 2)) ⊆ circleSet c} 1 := by
  classical
  let S : Set Circle := {c | (X : Set (E 2)) ⊆ circleSet c}
  have hencard : S.encard ≤ 1 := by
    apply Set.encard_le_one_iff.mpr
    intro c c' hc hc'
    by_contra hne
    have hcommon : (X : Set (E 2)) ⊆ circleSet c ∩ circleSet c' := by
      intro x hx
      exact ⟨hc hx, hc' hx⟩
    obtain ⟨hfin, hbound⟩ := circle_intersections c c' hne
    have hcard : (circleSet c ∩ circleSet c').ncard ≤ 2 := by
      exact_mod_cast hbound
    have hle : X.card ≤ (circleSet c ∩ circleSet c').ncard := by
      simpa using Set.ncard_le_ncard hcommon hfin
    omega
  have hsmall := Set.encard_le_coe_iff_finite_ncard_le.mp hencard
  exact ⟨hsmall.1, by exact_mod_cast hsmall.2⟩

/-- Squared Euclidean distance in the two coordinate variables. -/
theorem circlePolynomial_eval (c : Circle) (x : E 2) :
    evalR (circlePolynomial c) x = (dist x c.center)^2 - c.radius^2 := by
  have hdist := EuclideanSpace.dist_sq_eq x c.center
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at hdist
  simp only [circlePolynomial, evalR, map_add, map_sub, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C]
  rw [hdist]

/-- Rational circle parametrization and factor theorem. -/
theorem circle_polynomial_factor (c : Circle) :
    Irreducible (circlePolynomial c) ∧ (circlePolynomial c).totalDegree = 2 ∧
      ∀ f : Poly 2, onCircle f c ↔ circlePolynomial c ∣ f := by
  refine ⟨circleEquation_irreducible (c.center 0) (c.center 1) c.radius,
    circleEquation_totalDegree (c.center 0) (c.center 1) c.radius, ?_⟩
  intro f
  constructor
  · intro hf
    apply circleEquation_dvd_of_vanish (c.center 0) (c.center 1) c.radius c.radius_pos f
    intro x y hxy
    let z : E 2 := WithLp.toLp 2 ![x,y]
    have hdist : (dist z c.center)^2 = c.radius^2 := by
      rw [EuclideanSpace.dist_sq_eq]
      simpa [Fin.sum_univ_two, Real.dist_eq, sq_abs, z] using hxy
    have hz : z ∈ circleSet c := by
      change dist z c.center = c.radius
      nlinarith [(dist_nonneg : 0 ≤ dist z c.center), c.radius_pos]
    exact hf z hz
  · rintro ⟨g, rfl⟩ x hx
    have hzero : evalR (circlePolynomial c) x = 0 := by
      rw [circlePolynomial_eval]
      change dist x c.center = c.radius at hx
      rw [hx]
      ring
    change MvPolynomial.eval x (circlePolynomial c * g) = 0
    change MvPolynomial.eval x (circlePolynomial c) = 0 at hzero
    rw [map_mul, hzero, zero_mul]

private def circleRestrDen : Polynomial ℝ := 1 + Polynomial.X ^ 2

private def circleRestrLeftA (c : Circle) : Polynomial ℝ :=
  Polynomial.C (c.center 0) * circleRestrDen +
    Polynomial.C c.radius * (1 - Polynomial.X ^ 2)

private def circleRestrLeftB (c : Circle) : Polynomial ℝ :=
  Polynomial.C (c.center 1) * circleRestrDen +
    Polynomial.C c.radius * (2 * Polynomial.X)

private def circleRestrTopA (c : Circle) : Polynomial ℝ :=
  Polynomial.C (c.center 0) * circleRestrDen +
    Polynomial.C c.radius * (2 * Polynomial.X)

private def circleRestrTopB (c : Circle) : Polynomial ℝ :=
  Polynomial.C (c.center 1) * circleRestrDen +
    Polynomial.C c.radius * (Polynomial.X ^ 2 - 1)

private def circleRestrPoint (A B : Polynomial ℝ) (t : ℝ) : E 2 :=
  WithLp.toLp 2 ![(A.eval t) / circleRestrDen.eval t,
    (B.eval t) / circleRestrDen.eval t]

private def circleRestrPoly (f : Poly 2) (A B : Polynomial ℝ) : Polynomial ℝ :=
  ∑ e ∈ f.support,
    Polynomial.C (f.coeff e) * A ^ (e 0) * B ^ (e 1) *
      circleRestrDen ^ (f.totalDegree - e.sum (fun _ k => k))

private theorem circleRestrPoly_eval (f : Poly 2) (A B : Polynomial ℝ) (t : ℝ) :
    (circleRestrPoly f A B).eval t =
      (circleRestrDen.eval t) ^ f.totalDegree * evalR f (circleRestrPoint A B t) := by
  classical
  rw [circleRestrPoly]
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, circleRestrDen]
  conv_rhs =>
    arg 2
    arg 1
    rw [f.as_sum]
  simp only [evalR, MvPolynomial.eval_sum, MvPolynomial.eval_monomial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hN : e.sum (fun _ k => k) ≤ f.totalDegree := MvPolynomial.le_totalDegree he
  rw [Finsupp.prod_fintype e (fun n k => (circleRestrPoint A B t).ofLp n ^ k)
    (by intro n; simp)]
  simp [circleRestrPoint, circleRestrDen, Fin.prod_univ_two]
  have hd : 1 + t ^ 2 ≠ 0 := by positivity
  have hN' : e 0 + e 1 ≤ f.totalDegree := by
    simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using hN
  have hsum : e.sum (fun _ k => k) = e 0 + e 1 := by
    simp [Finsupp.sum_fintype, Fin.sum_univ_two]
  rw [hsum, div_pow, div_pow]
  field_simp [hd]
  have hpow : (1 + t ^ 2) ^ (f.totalDegree - (e 0 + e 1)) *
      (1 + t ^ 2) ^ (e 0 + e 1) = (1 + t ^ 2) ^ f.totalDegree := by
    rw [← pow_add, Nat.sub_add_cancel hN']
  calc
    _ = f.coeff e * (Polynomial.eval t A) ^ (e 0) * (Polynomial.eval t B) ^ (e 1) *
        ((1 + t ^ 2) ^ (f.totalDegree - (e 0 + e 1)) *
          ((1 + t ^ 2) ^ (e 0) * (1 + t ^ 2) ^ (e 1))) := by ring
    _ = f.coeff e * (Polynomial.eval t A) ^ (e 0) * (Polynomial.eval t B) ^ (e 1) *
        ((1 + t ^ 2) ^ (f.totalDegree - (e 0 + e 1)) * (1 + t ^ 2) ^ (e 0 + e 1)) := by
          rw [← pow_add]
    _ = _ := by rw [hpow]

private theorem circleRestrDen_degree : circleRestrDen.natDegree ≤ 2 := by
  dsimp [circleRestrDen]
  have hpow : (Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by
    calc
      _ ≤ 2 * (Polynomial.X : Polynomial ℝ).natDegree := Polynomial.natDegree_pow_le
      _ = 2 := by simp
  calc
    (1 + Polynomial.X ^ 2).natDegree ≤
        max (Polynomial.natDegree (1 : Polynomial ℝ)) ((Polynomial.X ^ 2).natDegree) :=
      Polynomial.natDegree_add_le _ _
    _ ≤ 2 := max_le (by simp) hpow

private theorem circleRestrConstMul_degree (a : ℝ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ 2) : (Polynomial.C a * p).natDegree ≤ 2 := by
  calc
    _ ≤ (Polynomial.C a).natDegree + p.natDegree := Polynomial.natDegree_mul_le
    _ ≤ 0 + 2 := Nat.add_le_add (by simp) hp
    _ = 2 := by simp

private theorem circleRestrLinear_degree :
    (2 * Polynomial.X : Polynomial ℝ).natDegree ≤ 2 := by
  calc
    _ ≤ (Polynomial.C (2 : ℝ)).natDegree + (Polynomial.X : Polynomial ℝ).natDegree := by
      simpa using (Polynomial.natDegree_mul_le
        (p := Polynomial.C (2 : ℝ)) (q := (Polynomial.X : Polynomial ℝ)))
    _ ≤ 2 := by simp

private theorem circleRestrSquareSub_degree :
    (1 - Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by
  have hpow : (Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by
    calc
      _ ≤ 2 * (Polynomial.X : Polynomial ℝ).natDegree := Polynomial.natDegree_pow_le
      _ = 2 := by simp
  calc
    _ ≤ max (Polynomial.natDegree (1 : Polynomial ℝ)) (Polynomial.natDegree (Polynomial.X ^ 2)) :=
      Polynomial.natDegree_sub_le _ _
    _ ≤ 2 := max_le (by simp) hpow

private theorem circleRestrSquareSubReversed_degree :
    (Polynomial.X ^ 2 - 1 : Polynomial ℝ).natDegree ≤ 2 := by
  have hpow : (Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by
    calc
      _ ≤ 2 * (Polynomial.X : Polynomial ℝ).natDegree := Polynomial.natDegree_pow_le
      _ = 2 := by simp
  calc
    _ ≤ max (Polynomial.natDegree (Polynomial.X ^ 2)) (Polynomial.natDegree (1 : Polynomial ℝ)) :=
      Polynomial.natDegree_sub_le _ _
    _ ≤ 2 := max_le hpow (by simp)

private theorem circleRestrLeftA_degree (c : Circle) : (circleRestrLeftA c).natDegree ≤ 2 := by
  unfold circleRestrLeftA
  exact (Polynomial.natDegree_add_le_of_degree_le
    (circleRestrConstMul_degree _ _ circleRestrDen_degree)
    (circleRestrConstMul_degree _ _ circleRestrSquareSub_degree))

private theorem circleRestrLeftB_degree (c : Circle) : (circleRestrLeftB c).natDegree ≤ 2 := by
  unfold circleRestrLeftB
  exact (Polynomial.natDegree_add_le_of_degree_le
    (circleRestrConstMul_degree _ _ circleRestrDen_degree)
    (circleRestrConstMul_degree _ _ circleRestrLinear_degree))

private theorem circleRestrTopA_degree (c : Circle) : (circleRestrTopA c).natDegree ≤ 2 := by
  unfold circleRestrTopA
  exact (Polynomial.natDegree_add_le_of_degree_le
    (circleRestrConstMul_degree _ _ circleRestrDen_degree)
    (circleRestrConstMul_degree _ _ circleRestrLinear_degree))

private theorem circleRestrTopB_degree (c : Circle) : (circleRestrTopB c).natDegree ≤ 2 := by
  unfold circleRestrTopB
  exact (Polynomial.natDegree_add_le_of_degree_le
    (circleRestrConstMul_degree _ _ circleRestrDen_degree)
    (circleRestrConstMul_degree _ _ circleRestrSquareSubReversed_degree))

private theorem circleRestrPoly_degree (f : Poly 2) (A B : Polynomial ℝ)
    (hA : A.natDegree ≤ 2) (hB : B.natDegree ≤ 2) :
    (circleRestrPoly f A B).natDegree ≤ 2 * f.totalDegree := by
  classical
  unfold circleRestrPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  let i := e 0
  let j := e 1
  let k := f.totalDegree - e.sum (fun _ d => d)
  have hsum : e.sum (fun _ d => d) = i + j := by
    simp [i, j, Finsupp.sum_fintype, Fin.sum_univ_two]
  have hsumle : i + j ≤ f.totalDegree := by
    simpa [hsum] using (MvPolynomial.le_totalDegree he)
  have hpowA : (A ^ i).natDegree ≤ i * 2 :=
    Polynomial.natDegree_pow_le_of_le i hA
  have hpowB : (B ^ j).natDegree ≤ j * 2 :=
    Polynomial.natDegree_pow_le_of_le j hB
  have hpowD : (circleRestrDen ^ k).natDegree ≤ k * 2 :=
    Polynomial.natDegree_pow_le_of_le k circleRestrDen_degree
  have h1 : (Polynomial.C (f.coeff e) * A ^ i).natDegree ≤ i * 2 := by
    calc
      _ ≤ (Polynomial.C (f.coeff e)).natDegree + (A ^ i).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 0 + i * 2 := Nat.add_le_add (by simp) hpowA
      _ = i * 2 := by simp
  have h2 : ((Polynomial.C (f.coeff e) * A ^ i) * B ^ j).natDegree ≤ i * 2 + j * 2 := by
    calc
      _ ≤ (Polynomial.C (f.coeff e) * A ^ i).natDegree + (B ^ j).natDegree := Polynomial.natDegree_mul_le
      _ ≤ i * 2 + j * 2 := Nat.add_le_add h1 hpowB
  have h3 : (((Polynomial.C (f.coeff e) * A ^ i) * B ^ j) * circleRestrDen ^ k).natDegree ≤
      i * 2 + j * 2 + k * 2 := by
    calc
      _ ≤ ((Polynomial.C (f.coeff e) * A ^ i) * B ^ j).natDegree + (circleRestrDen ^ k).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ i * 2 + j * 2 + k * 2 := Nat.add_le_add h2 hpowD
  have harith : i * 2 + j * 2 + k * 2 = 2 * f.totalDegree := by
    dsimp [k]
    rw [hsum]
    have hcancel : i + j + (f.totalDegree - (i + j)) = f.totalDegree :=
      Nat.add_sub_of_le hsumle
    omega
  simpa [i, j, k] using h3.trans_eq harith

private def circleRestrLeftException (c : Circle) : E 2 :=
  WithLp.toLp 2 ![c.center 0 - c.radius, c.center 1]

private def circleRestrTopException (c : Circle) : E 2 :=
  WithLp.toLp 2 ![c.center 0, c.center 1 + c.radius]

private lemma circleRestr_coords_sq (c : Circle) (x : E 2) (hx : x ∈ circleSet c) :
    (x 0 - c.center 0) ^ 2 + (x 1 - c.center 1) ^ 2 = c.radius ^ 2 := by
  change dist x c.center = c.radius at hx
  have h := congrArg (fun z : ℝ => z ^ 2) hx
  rw [EuclideanSpace.dist_sq_eq] at h
  simpa [Real.dist_eq, Fin.sum_univ_two] using h

private lemma circleRestrLeft_coord0 (c : Circle) (t : ℝ) :
    circleRestrPoint (circleRestrLeftA c) (circleRestrLeftB c) t 0 =
      c.center 0 + c.radius * (1 - t ^ 2) / (1 + t ^ 2) := by
  simp [circleRestrPoint, circleRestrLeftA, circleRestrLeftB, circleRestrDen]
  field_simp
  <;> ring_nf

private lemma circleRestrLeft_coord1 (c : Circle) (t : ℝ) :
    circleRestrPoint (circleRestrLeftA c) (circleRestrLeftB c) t 1 =
      c.center 1 + c.radius * (2 * t) / (1 + t ^ 2) := by
  simp [circleRestrPoint, circleRestrLeftA, circleRestrLeftB, circleRestrDen]
  field_simp
  <;> ring_nf

private lemma circleRestrTop_coord0 (c : Circle) (t : ℝ) :
    circleRestrPoint (circleRestrTopA c) (circleRestrTopB c) t 0 =
      c.center 0 + c.radius * (2 * t) / (1 + t ^ 2) := by
  simp [circleRestrPoint, circleRestrTopA, circleRestrTopB, circleRestrDen]
  field_simp
  <;> ring_nf

private lemma circleRestrTop_coord1 (c : Circle) (t : ℝ) :
    circleRestrPoint (circleRestrTopA c) (circleRestrTopB c) t 1 =
      c.center 1 + c.radius * (t ^ 2 - 1) / (1 + t ^ 2) := by
  simp [circleRestrPoint, circleRestrTopA, circleRestrTopB, circleRestrDen]
  field_simp
  <;> ring_nf

private lemma circleRestrLeft_mem (c : Circle) (t : ℝ) :
    circleRestrPoint (circleRestrLeftA c) (circleRestrLeftB c) t ∈ circleSet c := by
  have hc : (circleRestrPoint (circleRestrLeftA c) (circleRestrLeftB c) t 0 - c.center 0) ^ 2 +
      (circleRestrPoint (circleRestrLeftA c) (circleRestrLeftB c) t 1 - c.center 1) ^ 2 =
        c.radius ^ 2 := by
    rw [circleRestrLeft_coord0, circleRestrLeft_coord1]
    have hd : 1 + t ^ 2 ≠ 0 := by positivity
    field_simp [hd]
    <;> ring_nf
  have hdsq : dist (circleRestrPoint (circleRestrLeftA c) (circleRestrLeftB c) t) c.center ^ 2 =
      c.radius ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    simpa [Real.dist_eq, Fin.sum_univ_two] using hc
  change dist (circleRestrPoint (circleRestrLeftA c) (circleRestrLeftB c) t) c.center = c.radius
  exact (sq_eq_sq₀ dist_nonneg c.radius_pos.le).mp hdsq

private lemma circleRestrTop_mem (c : Circle) (t : ℝ) :
    circleRestrPoint (circleRestrTopA c) (circleRestrTopB c) t ∈ circleSet c := by
  have hc : (circleRestrPoint (circleRestrTopA c) (circleRestrTopB c) t 0 - c.center 0) ^ 2 +
      (circleRestrPoint (circleRestrTopA c) (circleRestrTopB c) t 1 - c.center 1) ^ 2 =
        c.radius ^ 2 := by
    rw [circleRestrTop_coord0, circleRestrTop_coord1]
    have hd : 1 + t ^ 2 ≠ 0 := by positivity
    field_simp [hd]
    <;> ring_nf
  have hdsq : dist (circleRestrPoint (circleRestrTopA c) (circleRestrTopB c) t) c.center ^ 2 =
      c.radius ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    simpa [Real.dist_eq, Fin.sum_univ_two] using hc
  change dist (circleRestrPoint (circleRestrTopA c) (circleRestrTopB c) t) c.center = c.radius
  exact (sq_eq_sq₀ dist_nonneg c.radius_pos.le).mp hdsq

private lemma circleRestrLeft_ne_top (c : Circle) :
    circleRestrLeftException c ≠ circleRestrTopException c := by
  intro h
  have hh := congrArg (fun z : E 2 => z 0) h
  simp [circleRestrLeftException, circleRestrTopException] at hh
  nlinarith [c.radius_pos]

private lemma circleRestrInvLeftX (a b r x y : ℝ) (hr : 0 < r)
    (hxy : (x - a) ^ 2 + (y - b) ^ 2 = r ^ 2) (hden : r + (x - a) ≠ 0) :
    a + r * (1 - ((y - b) / (r + (x - a))) ^ 2) /
      (1 + ((y - b) / (r + (x - a))) ^ 2) = x := by
  field_simp [hden]
  nlinarith [hxy]

private lemma circleRestrInvLeftY (a b r x y : ℝ)
    (hxy : (x - a) ^ 2 + (y - b) ^ 2 = r ^ 2) (hden : r + (x - a) ≠ 0) :
    b + r * (2 * ((y - b) / (r + (x - a)))) /
      (1 + ((y - b) / (r + (x - a))) ^ 2) = y := by
  have hrel : (r + (x - a)) ^ 2 + (y - b) ^ 2 = 2 * r * (r + (x - a)) := by
    nlinarith [hxy]
  field_simp [hden]
  rw [hrel]
  ring

private lemma circleRestrLeft_inverse (c : Circle) (x : E 2)
    (hx : x ∈ circleSet c) (hne : x ≠ circleRestrLeftException c) :
    circleRestrPoint (circleRestrLeftA c) (circleRestrLeftB c)
      ((x 1 - c.center 1) / (c.radius + (x 0 - c.center 0))) = x := by
  have hcoords := circleRestr_coords_sq c x hx
  have hden : c.radius + (x 0 - c.center 0) ≠ 0 := by
    intro hzero
    have hx0 : x 0 - c.center 0 = -c.radius := by linarith
    have hcoords' : c.radius ^ 2 + (x 1 - c.center 1) ^ 2 = c.radius ^ 2 := by
      simpa [hx0] using hcoords
    have hxsq : (x 1 - c.center 1) ^ 2 = 0 := by linarith [hcoords']
    have hx1 : x 1 - c.center 1 = 0 := (sq_eq_zero_iff).mp hxsq
    apply hne
    ext i
    fin_cases i
    · change x 0 = c.center 0 - c.radius
      nlinarith [hx0]
    · change x 1 = c.center 1
      nlinarith [hx1]
  have hx0 : (circleRestrPoint (circleRestrLeftA c) (circleRestrLeftB c)
      ((x 1 - c.center 1) / (c.radius + (x 0 - c.center 0)))) 0 = x 0 := by
    rw [circleRestrLeft_coord0]
    simpa using circleRestrInvLeftX (c.center 0) (c.center 1) c.radius (x 0) (x 1)
      c.radius_pos hcoords hden
  have hx1 : (circleRestrPoint (circleRestrLeftA c) (circleRestrLeftB c)
      ((x 1 - c.center 1) / (c.radius + (x 0 - c.center 0)))) 1 = x 1 := by
    rw [circleRestrLeft_coord1]
    simpa using circleRestrInvLeftY (c.center 0) (c.center 1) c.radius (x 0) (x 1)
      hcoords hden
  ext i
  fin_cases i
  · exact hx0
  · exact hx1

private lemma circleRestrInvTopX (a b r x y : ℝ)
    (hxy : (x - a) ^ 2 + (y - b) ^ 2 = r ^ 2) (hden : r - (y - b) ≠ 0) :
    a + r * (2 * ((x - a) / (r - (y - b)))) /
      (1 + ((x - a) / (r - (y - b))) ^ 2) = x := by
  have hrel : (r - (y - b)) ^ 2 + (x - a) ^ 2 = 2 * r * (r - (y - b)) := by
    nlinarith [hxy]
  field_simp [hden]
  rw [hrel]
  ring

private lemma circleRestrInvTopY (a b r x y : ℝ)
    (hxy : (x - a) ^ 2 + (y - b) ^ 2 = r ^ 2) (hden : r - (y - b) ≠ 0) :
    b + r * (((x - a) / (r - (y - b))) ^ 2 - 1) /
      (1 + ((x - a) / (r - (y - b))) ^ 2) = y := by
  have hrel : (r - (y - b)) ^ 2 + (x - a) ^ 2 = 2 * r * (r - (y - b)) := by
    nlinarith [hxy]
  have hnum : (x - a) ^ 2 - (r - (y - b)) ^ 2 =
      2 * (y - b) * (r - (y - b)) := by nlinarith [hxy]
  field_simp [hden]
  rw [hrel, hnum]
  ring

private lemma circleRestrTop_inverse (c : Circle) (x : E 2)
    (hx : x ∈ circleSet c) (hne : x ≠ circleRestrTopException c) :
    circleRestrPoint (circleRestrTopA c) (circleRestrTopB c)
      ((x 0 - c.center 0) / (c.radius - (x 1 - c.center 1))) = x := by
  have hcoords := circleRestr_coords_sq c x hx
  have hden : c.radius - (x 1 - c.center 1) ≠ 0 := by
    intro hzero
    have hx1 : x 1 - c.center 1 = c.radius := by linarith
    have hcoords' : (x 0 - c.center 0) ^ 2 + c.radius ^ 2 = c.radius ^ 2 := by
      simpa [hx1] using hcoords
    have hxsq : (x 0 - c.center 0) ^ 2 = 0 := by linarith [hcoords']
    have hx0 : x 0 - c.center 0 = 0 := (sq_eq_zero_iff).mp hxsq
    apply hne
    ext i
    fin_cases i
    · change x 0 = c.center 0
      nlinarith [hx0]
    · change x 1 = c.center 1 + c.radius
      nlinarith [hx1]
  have hx0 : (circleRestrPoint (circleRestrTopA c) (circleRestrTopB c)
      ((x 0 - c.center 0) / (c.radius - (x 1 - c.center 1)))) 0 = x 0 := by
    rw [circleRestrTop_coord0]
    simpa using circleRestrInvTopX (c.center 0) (c.center 1) c.radius (x 0) (x 1)
      hcoords hden
  have hx1 : (circleRestrPoint (circleRestrTopA c) (circleRestrTopB c)
      ((x 0 - c.center 0) / (c.radius - (x 1 - c.center 1)))) 1 = x 1 := by
    rw [circleRestrTop_coord1]
    simpa using circleRestrInvTopY (c.center 0) (c.center 1) c.radius (x 0) (x 1)
      hcoords hden
  ext i
  fin_cases i
  · exact hx0
  · exact hx1

private theorem circleRestr_zero_ncard_bound (f : Poly 2) (c : Circle)
    (A B : Polynomial ℝ) (q : Polynomial ℝ) (exception : E 2) (param : E 2 → ℝ)
    (hq : q = circleRestrPoly f A B) (hqne : q ≠ 0)
    (hinv : ∀ x, x ∈ circleSet c → x ≠ exception → circleRestrPoint A B (param x) = x) :
    (zeroSet f ∩ circleSet c).Finite ∧
      (zeroSet f ∩ circleSet c).ncard ≤ q.natDegree + 1 := by
  classical
  let S : Set (E 2) := zeroSet f ∩ circleSet c
  let S₀ : Set (E 2) := S \ {exception}
  have hmap : Set.MapsTo param S₀ (q.rootSet ℝ) := by
    intro x hx
    rcases (Set.mem_sdiff x).mp hx with ⟨hxS, hxexc⟩
    rcases (Set.mem_inter_iff x (zeroSet f) (circleSet c)).mp
      (by simpa [S] using hxS) with ⟨hxzero, hxcircle⟩
    have hxne : x ≠ exception := by simpa using hxexc
    have hparam := hinv x hxcircle hxne
    have heval : q.eval (param x) = circleRestrDen.eval (param x) ^ f.totalDegree *
        evalR f x := by
      calc
        q.eval (param x) = (circleRestrPoly f A B).eval (param x) := by rw [hq]
        _ = circleRestrDen.eval (param x) ^ f.totalDegree *
            evalR f (circleRestrPoint A B (param x)) := circleRestrPoly_eval f A B (param x)
        _ = circleRestrDen.eval (param x) ^ f.totalDegree * evalR f x := by rw [hparam]
    have hroot : q.eval (param x) = 0 := by rw [heval, hxzero]; simp
    rw [Polynomial.mem_rootSet_of_ne hqne]
    simpa using hroot
  have hinj : Set.InjOn param S₀ := by
    intro x hx y hy hxy
    rcases (Set.mem_sdiff x).mp hx with ⟨hxS, hxexc⟩
    rcases (Set.mem_inter_iff x (zeroSet f) (circleSet c)).mp
      (by simpa [S] using hxS) with ⟨_, hxcircle⟩
    have hxne : x ≠ exception := by simpa using hxexc
    rcases (Set.mem_sdiff y).mp hy with ⟨hyS, hyexc⟩
    rcases (Set.mem_inter_iff y (zeroSet f) (circleSet c)).mp
      (by simpa [S] using hyS) with ⟨_, hycircle⟩
    have hyne : y ≠ exception := by simpa using hyexc
    calc
      x = circleRestrPoint A B (param x) := (hinv x hxcircle hxne).symm
      _ = circleRestrPoint A B (param y) := by rw [hxy]
      _ = y := hinv y hycircle hyne
  have hrootFin : (q.rootSet ℝ).Finite := Polynomial.rootSet_finite q ℝ
  have hS₀Fin : S₀.Finite := hrootFin.of_injOn hmap hinj
  have hS₀card : S₀.ncard ≤ q.natDegree := by
    calc
      S₀.ncard = (param '' S₀).ncard := hinj.ncard_image.symm
      _ ≤ (q.rootSet ℝ).ncard :=
        Set.ncard_le_ncard (Set.image_subset_iff.mpr hmap) hrootFin
      _ ≤ q.natDegree := Polynomial.ncard_rootSet_le q ℝ
  have hsub : S ⊆ insert exception S₀ := by
    intro x hx
    by_cases hxe : x = exception
    · simp [hxe]
    · right
      exact ⟨hx, hxe⟩
  have hfinU : (insert exception S₀).Finite := hS₀Fin.insert exception
  have hSfin : S.Finite := hfinU.subset hsub
  have hScard : S.ncard ≤ q.natDegree + 1 := by
    calc
      S.ncard ≤ (insert exception S₀).ncard := Set.ncard_le_ncard hsub hfinU
      _ ≤ S₀.ncard + 1 := Set.ncard_insert_le exception S₀
      _ ≤ q.natDegree + 1 := Nat.add_le_add_right hS₀card 1
  exact ⟨by simpa [S] using hSfin, by simpa [S] using hScard⟩

/-- Restrict through the rational parametrization; two extra roots are harmless. -/
theorem polynomial_circle_zeros (f : Poly 2) (c : Circle) (hn : ¬ onCircle f c) :
    FiniteCardBound (zeroSet f ∩ circleSet c) (2 * f.totalDegree + 2) := by
  classical
  obtain ⟨p, hpCircle, hpf⟩ : ∃ p, p ∈ circleSet c ∧ evalR f p ≠ 0 := by
    by_contra h
    apply hn
    intro x hx
    by_contra hzero
    exact h ⟨x, hx, hzero⟩
  by_cases hpLeft : p = circleRestrLeftException c
  · have hpTop : p ≠ circleRestrTopException c := by
      intro htop
      exact circleRestrLeft_ne_top c (hpLeft.symm.trans htop)
    let A := circleRestrTopA c
    let B := circleRestrTopB c
    let q := circleRestrPoly f A B
    let param : E 2 → ℝ := fun x =>
      (x 0 - c.center 0) / (c.radius - (x 1 - c.center 1))
    have hqne : q ≠ 0 := by
      intro hq
      have hparam := circleRestrTop_inverse c p hpCircle hpTop
      have heval := circleRestrPoly_eval f A B (param p)
      rw [hparam] at heval
      have hq0 : q.eval (param p) = 0 := by simp [hq]
      have hmul : (circleRestrDen.eval (param p)) ^ f.totalDegree * evalR f p = 0 := by
        calc
          _ = q.eval (param p) := by simpa [q] using heval.symm
          _ = 0 := hq0
      have hden : circleRestrDen.eval (param p) ≠ 0 := by
        simpa [circleRestrDen] using (show 1 + (param p) ^ 2 ≠ 0 by positivity)
      rcases mul_eq_zero.mp hmul with hpow | hz
      · exact (pow_ne_zero _ hden) hpow
      · exact hpf hz
    obtain ⟨hfinite, hcard⟩ := circleRestr_zero_ncard_bound f c A B q
      (circleRestrTopException c) param (by rfl) hqne
      (fun x hx hne => circleRestrTop_inverse c x hx hne)
    have hqdeg : q.natDegree ≤ 2 * f.totalDegree := by
      simpa [q, A, B] using circleRestrPoly_degree f
        (circleRestrTopA c) (circleRestrTopB c)
        (circleRestrTopA_degree c) (circleRestrTopB_degree c)
    have hnat : (zeroSet f ∩ circleSet c).ncard ≤ 2 * f.totalDegree + 1 := by
      exact hcard.trans (Nat.add_le_add_right hqdeg 1)
    have hnat' : (zeroSet f ∩ circleSet c).ncard ≤ 2 * f.totalDegree + 2 := by omega
    refine ⟨hfinite, ?_⟩
    exact_mod_cast hnat'
  · let A := circleRestrLeftA c
    let B := circleRestrLeftB c
    let q := circleRestrPoly f A B
    let param : E 2 → ℝ := fun x =>
      (x 1 - c.center 1) / (c.radius + (x 0 - c.center 0))
    have hqne : q ≠ 0 := by
      intro hq
      have hparam := circleRestrLeft_inverse c p hpCircle hpLeft
      have heval := circleRestrPoly_eval f A B (param p)
      rw [hparam] at heval
      have hq0 : q.eval (param p) = 0 := by simp [hq]
      have hmul : (circleRestrDen.eval (param p)) ^ f.totalDegree * evalR f p = 0 := by
        calc
          _ = q.eval (param p) := by simpa [q] using heval.symm
          _ = 0 := hq0
      have hden : circleRestrDen.eval (param p) ≠ 0 := by
        simpa [circleRestrDen] using (show 1 + (param p) ^ 2 ≠ 0 by positivity)
      rcases mul_eq_zero.mp hmul with hpow | hz
      · exact (pow_ne_zero _ hden) hpow
      · exact hpf hz
    obtain ⟨hfinite, hcard⟩ := circleRestr_zero_ncard_bound f c A B q
      (circleRestrLeftException c) param (by rfl) hqne
      (fun x hx hne => circleRestrLeft_inverse c x hx hne)
    have hqdeg : q.natDegree ≤ 2 * f.totalDegree := by
      simpa [q, A, B] using circleRestrPoly_degree f
        (circleRestrLeftA c) (circleRestrLeftB c)
        (circleRestrLeftA_degree c) (circleRestrLeftB_degree c)
    have hnat : (zeroSet f ∩ circleSet c).ncard ≤ 2 * f.totalDegree + 1 := by
      exact hcard.trans (Nat.add_le_add_right hqdeg 1)
    have hnat' : (zeroSet f ∩ circleSet c).ncard ≤ 2 * f.totalDegree + 2 := by omega
    refine ⟨hfinite, ?_⟩
    exact_mod_cast hnat'

private theorem circleRestr_root_between (p : Polynomial ℝ) (a b : ℝ)
    (hneg : p.eval a * p.eval b < 0) :
    ∃ z ∈ Set.uIcc a b, p.eval z = 0 := by
  have hzero : (0 : ℝ) ∈ Set.uIcc (p.eval a) (p.eval b) := by
    rcases mul_neg_iff.mp hneg with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simp only [Set.mem_uIcc]
      exact Or.inr ⟨hb.le, ha.le⟩
    · simp only [Set.mem_uIcc]
      exact Or.inl ⟨ha.le, hb.le⟩
  have himage : Set.uIcc (p.eval a) (p.eval b) ⊆
      (fun x : ℝ => p.eval x) '' Set.uIcc a b :=
    intermediate_value_uIcc (f := fun x : ℝ => p.eval x) (a := a) (b := b)
      p.continuous.continuousOn
  have hzmem : (0 : ℝ) ∈ p.eval '' Set.uIcc a b := himage hzero
  rcases hzmem with ⟨z, hz, hval⟩
  exact ⟨z, hz, hval⟩

private theorem evalR_list_prod (fs : List (Poly 2)) (x : E 2) :
    evalR fs.prod x = (fs.map fun g => evalR g x).prod := by
  induction fs with
  | nil => simp [evalR]
  | cons f fs ih =>
    change MvPolynomial.eval x.ofLp (f * fs.prod) =
      MvPolynomial.eval x.ofLp f *
        (fs.map fun g => MvPolynomial.eval x.ofLp g).prod
    change MvPolynomial.eval x.ofLp fs.prod =
      (fs.map fun g => MvPolynomial.eval x.ofLp g).prod at ih
    rw [MvPolynomial.eval_mul, ih]

private theorem circleRestr_product_root_between_factor (fs : List (Poly 2))
    (A B : Polynomial ℝ) (i : Fin fs.length) (a b : ℝ)
    (hneg : evalR (fs.get i) (circleRestrPoint A B a) *
      evalR (fs.get i) (circleRestrPoint A B b) < 0) :
    ∃ z ∈ Set.uIcc a b,
      (circleRestrPoly (fs.get i) A B).eval z = 0 ∧
      (circleRestrPoly fs.prod A B).eval z = 0 := by
  classical
  let f := fs.get i
  let p := circleRestrPoly f A B
  have hdena : 0 < circleRestrDen.eval a := by simp [circleRestrDen]; positivity
  have hdenb : 0 < circleRestrDen.eval b := by simp [circleRestrDen]; positivity
  have hpa : p.eval a = circleRestrDen.eval a ^ f.totalDegree * evalR f (circleRestrPoint A B a) := by
    exact circleRestrPoly_eval f A B a
  have hpb : p.eval b = circleRestrDen.eval b ^ f.totalDegree * evalR f (circleRestrPoint A B b) := by
    exact circleRestrPoly_eval f A B b
  have hpneg : p.eval a * p.eval b < 0 := by
    rw [hpa, hpb]
    calc
      _ = (circleRestrDen.eval a ^ f.totalDegree * circleRestrDen.eval b ^ f.totalDegree) *
          (evalR f (circleRestrPoint A B a) * evalR f (circleRestrPoint A B b)) := by ring
      _ < 0 := mul_neg_of_pos_of_neg
        (mul_pos (pow_pos hdena _) (pow_pos hdenb _)) hneg
  obtain ⟨z, hz, hpzero⟩ := circleRestr_root_between p a b hpneg
  have hfzero : evalR f (circleRestrPoint A B z) = 0 := by
    have hmul : circleRestrDen.eval z ^ f.totalDegree * evalR f (circleRestrPoint A B z) = 0 := by
      calc
        _ = p.eval z := (circleRestrPoly_eval f A B z).symm
        _ = 0 := hpzero
    have hdenz : circleRestrDen.eval z ^ f.totalDegree ≠ 0 := by
      apply pow_ne_zero
      simp [circleRestrDen]
      positivity
    exact (mul_eq_zero.mp hmul).resolve_left hdenz
  have hmemzero : (0 : ℝ) ∈ fs.map (fun g => evalR g (circleRestrPoint A B z)) := by
    apply List.mem_map.mpr
    exact ⟨f, List.get_mem fs i, hfzero⟩
  have hprodzero : evalR fs.prod (circleRestrPoint A B z) = 0 := by
    rw [evalR_list_prod]
    exact List.prod_eq_zero hmemzero
  have hqzero : (circleRestrPoly fs.prod A B).eval z = 0 := by
    rw [circleRestrPoly_eval, hprodzero]
    simp
  exact ⟨z, hz, hpzero, hqzero⟩

private theorem circleRestr_sign_cells_bound (fs : List (Poly 2))
    (cells : Finset (Set (E 2)))
    (hcells : ∀ R ∈ cells, ∃ σ, R = signCell fs σ)
    (hdisj : ∀ R ∈ cells, ∀ R' ∈ cells, R ≠ R' → Disjoint R R')
    (c : Circle) (A B : Polynomial ℝ) (exception : E 2) (param : E 2 → ℝ)
    (hinv : ∀ x, x ∈ circleSet c → x ≠ exception →
      circleRestrPoint A B (param x) = x)
    (q : Polynomial ℝ) (hq : q = circleRestrPoly fs.prod A B) (hqne : q ≠ 0) :
    (cells.filter (fun R => (R ∩ circleSet c).Nonempty)).card ≤ q.natDegree + 2 := by
  classical
  let F := cells.filter (fun R => (R ∩ circleSet c).Nonempty)
  let F₀ := F.filter (fun R => exception ∉ R)
  let Fₑ := F.filter (fun R => exception ∈ R)
  let rootFin := Polynomial.rootSet_finite q ℝ
  let roots : Finset ℝ := rootFin.toFinset
  let idx : ℝ → ℕ := fun t => (roots.filter (fun z => z < t)).card
  have hrootCard : roots.card ≤ q.natDegree := by
    simpa [roots] using (Polynomial.ncard_rootSet_le q ℝ)
  have hidxIncrease {a b z : ℝ} (haz : a < z) (hzb : z < b)
      (hz : z ∈ roots) : idx a < idx b := by
    change (roots.filter (fun w => w < a)).card <
      (roots.filter (fun w => w < b)).card
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro w hw
      rcases Finset.mem_filter.mp hw with ⟨hwr, hwa⟩
      exact Finset.mem_filter.mpr ⟨hwr, hwa.trans (haz.trans hzb)⟩
    · intro heq
      have hzb' : z ∈ roots.filter (fun w => w < b) :=
        Finset.mem_filter.mpr ⟨hz, hzb⟩
      have hza' : z ∈ roots.filter (fun w => w < a) := by
        rw [← heq] at hzb'
        exact hzb'
      exact lt_asymm haz (Finset.mem_filter.mp hza').2
  have hFₑcard : Fₑ.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro R hR R' hR'
    by_contra hne
    have hRcell : R ∈ cells := (Finset.mem_filter.mp
      (Finset.mem_filter.mp hR).1).1
    have hR'cell : R' ∈ cells := (Finset.mem_filter.mp
      (Finset.mem_filter.mp hR').1).1
    have hdis := hdisj R hRcell R' hR'cell hne
    exact (Set.disjoint_left.mp hdis)
      (Finset.mem_filter.mp hR).2 (Finset.mem_filter.mp hR').2
  have hpartition : Fₑ.card + F₀.card = F.card := by
    simpa [Fₑ, F₀, F] using
      (Finset.card_filter_add_card_filter_not (fun R => exception ∈ R))
  let α := {R : Set (E 2) // R ∈ F₀}
  have hCells (R : α) : R.1 ∈ cells := by
    exact (Finset.mem_filter.mp
      (Finset.mem_filter.mp R.2).1).1
  have hInter (R : α) : (R.1 ∩ circleSet c).Nonempty := by
    exact (Finset.mem_filter.mp
      (Finset.mem_filter.mp R.2).1).2
  let point (R : α) : E 2 := Classical.choose (hInter R)
  have hpoint (R : α) : point R ∈ R.1 ∩ circleSet c :=
    Classical.choose_spec (hInter R)
  have hpointNe (R : α) : point R ≠ exception := by
    intro heq
    have hnot : exception ∉ R.1 := (Finset.mem_filter.mp R.2).2
    apply hnot
    rw [← heq]
    exact (hpoint R).1
  let t (R : α) : ℝ := param (point R)
  have hchart (R : α) : circleRestrPoint A B (t R) = point R :=
    hinv (point R) (hpoint R).2 (hpointNe R)
  let sig (R : α) : Fin fs.length → Bool :=
    Classical.choose (hcells R.1 (hCells R))
  have hsig (R : α) : R.1 = signCell fs (sig R) :=
    Classical.choose_spec (hcells R.1 (hCells R))
  have hsign (R : α) : ∀ i : Fin fs.length,
      if sig R i then 0 < evalR (fs.get i) (point R)
      else evalR (fs.get i) (point R) < 0 := by
    have hm : point R ∈ signCell fs (sig R) := by
      rw [← hsig R]
      exact (hpoint R).1
    change ∀ i : Fin fs.length, _
    exact hm
  have hidxInj : Function.Injective (fun R : α => idx (t R)) := by
    intro R R' hidx
    by_contra hne
    have hsigNe : sig R ≠ sig R' := by
      intro hs
      apply hne
      apply Subtype.ext
      calc
        R.1 = signCell fs (sig R) := hsig R
        _ = signCell fs (sig R') := by rw [hs]
        _ = R'.1 := (hsig R').symm
    obtain ⟨i, hσ⟩ : ∃ i : Fin fs.length, sig R i ≠ sig R' i := by
      by_contra h
      push_neg at h
      apply hsigNe
      funext i
      exact h i
    have hfactorNeg : evalR (fs.get i) (circleRestrPoint A B (t R)) *
        evalR (fs.get i) (circleRestrPoint A B (t R')) < 0 := by
      rw [hchart R, hchart R']
      have hleft := hsign R i
      have hright := hsign R' i
      cases hσR : sig R i <;> cases hσR' : sig R' i
      · simp [hσR, hσR'] at hσ
      · simp [hσR] at hleft
        simp [hσR'] at hright
        exact mul_neg_of_neg_of_pos hleft hright
      · simp [hσR] at hleft
        simp [hσR'] at hright
        exact mul_neg_of_pos_of_neg hleft hright
      · simp [hσR, hσR'] at hσ
    obtain ⟨z, hzU, hpzero, hzprod⟩ := circleRestr_product_root_between_factor
      fs A B i (t R) (t R') hfactorNeg
    have hzq : q.eval z = 0 := by simpa [hq] using hzprod
    have hzrootSet : z ∈ q.rootSet ℝ := by
      rw [Polynomial.mem_rootSet_of_ne hqne]
      exact hzq
    have hzroot : z ∈ roots := rootFin.mem_toFinset.mpr hzrootSet
    have hfactorAne : evalR (fs.get i) (circleRestrPoint A B (t R)) ≠ 0 := by
      intro hzero
      rw [hzero] at hfactorNeg
      norm_num at hfactorNeg
    have hfactorBne : evalR (fs.get i) (circleRestrPoint A B (t R')) ≠ 0 := by
      intro hzero
      rw [hzero] at hfactorNeg
      norm_num at hfactorNeg
    let p := circleRestrPoly (fs.get i) A B
    have hpA : p.eval (t R) = circleRestrDen.eval (t R) ^ (fs.get i).totalDegree *
        evalR (fs.get i) (circleRestrPoint A B (t R)) := by
      exact circleRestrPoly_eval (fs.get i) A B (t R)
    have hpB : p.eval (t R') = circleRestrDen.eval (t R') ^ (fs.get i).totalDegree *
        evalR (fs.get i) (circleRestrPoint A B (t R')) := by
      exact circleRestrPoly_eval (fs.get i) A B (t R')
    have hpAne : p.eval (t R) ≠ 0 := by
      rw [hpA]
      exact mul_ne_zero (pow_ne_zero _ (by simp [circleRestrDen]; positivity)) hfactorAne
    have hpBne : p.eval (t R') ≠ 0 := by
      rw [hpB]
      exact mul_ne_zero (pow_ne_zero _ (by simp [circleRestrDen]; positivity)) hfactorBne
    have hidxDiff : idx (t R) < idx (t R') ∨ idx (t R') < idx (t R) := by
      simp only [Set.mem_uIcc] at hzU
      rcases hzU with ⟨hzA, hzB⟩ | ⟨hzB, hzA⟩
      · have hltA : t R < z := by
          rcases eq_or_lt_of_le hzA with heq | hlt
          · subst z
            exact (hpAne hpzero).elim
          · exact hlt
        have hltB : z < t R' := by
          rcases eq_or_lt_of_le hzB with heq | hlt
          · subst z
            exact (hpBne hpzero).elim
          · exact hlt
        exact Or.inl (hidxIncrease hltA hltB hzroot)
      · have hltB : t R' < z := by
          rcases eq_or_lt_of_le hzB with heq | hlt
          · subst z
            exact (hpBne hpzero).elim
          · exact hlt
        have hltA : z < t R := by
          rcases eq_or_lt_of_le hzA with heq | hlt
          · subst z
            exact (hpAne hpzero).elim
          · exact hlt
        exact Or.inr (hidxIncrease hltB hltA hzroot)
    rcases hidxDiff with hlt | hlt
    · exact (ne_of_lt hlt) hidx
    · exact (ne_of_gt hlt) hidx
  have hidxlt (R : α) : idx (t R) < roots.card + 1 := by
    apply Nat.lt_succ_of_le
    change (roots.filter (fun z => z < t R)).card ≤ roots.card
    exact Finset.card_filter_le _ _
  let embed (R : α) : Fin (roots.card + 1) := ⟨idx (t R), hidxlt R⟩
  have hembed : Function.Injective embed := by
    intro R R' heq
    apply hidxInj
    exact congrArg Fin.val heq
  have hF₀card : F₀.card ≤ roots.card + 1 := by
    calc
      F₀.card = Fintype.card α := by simp [α]
      _ ≤ Fintype.card (Fin (roots.card + 1)) := Fintype.card_le_of_injective embed hembed
      _ = roots.card + 1 := Fintype.card_fin _
  have hFcard : F.card ≤ F₀.card + 1 := by omega
  calc
    (cells.filter (fun R => (R ∩ circleSet c).Nonempty)).card = F.card := by rfl
    _ ≤ F₀.card + 1 := hFcard
    _ ≤ roots.card + 1 + 1 := Nat.add_le_add_right hF₀card 1
    _ ≤ q.natDegree + 2 := by omega

/-- Circle crossing bound for the sign classes, without connected-cell topology. -/
theorem circle_sign_cells (fs : List (Poly 2)) (cells : Finset (Set (E 2)))
    (hcells : ∀ R ∈ cells, ∃ σ, R = signCell fs σ)
    (hdisj : ∀ R ∈ cells, ∀ R' ∈ cells, R ≠ R' → Disjoint R R')
    (c : Circle) (hn : ¬ onCircle fs.prod c) :
    (cells.filter (fun R => (R ∩ circleSet c).Nonempty)).card ≤
      2 * fs.prod.totalDegree + 2 := by
  classical
  obtain ⟨p, hpcircle, hpf⟩ : ∃ p, p ∈ circleSet c ∧ evalR fs.prod p ≠ 0 := by
    by_contra h
    apply hn
    intro x hx
    by_contra hzero
    exact h ⟨x, hx, hzero⟩
  have chartBound (A B : Polynomial ℝ) (exception : E 2) (param : E 2 → ℝ)
      (hA : A.natDegree ≤ 2) (hB : B.natDegree ≤ 2)
      (hinv : ∀ x, x ∈ circleSet c → x ≠ exception →
        circleRestrPoint A B (param x) = x)
      (hpne : p ≠ exception) :
      (cells.filter (fun R => (R ∩ circleSet c).Nonempty)).card ≤
        2 * fs.prod.totalDegree + 2 := by
    let q := circleRestrPoly fs.prod A B
    have hqne : q ≠ 0 := by
      intro hqzero
      have hinvp := hinv p hpcircle hpne
      have heval : q.eval (param p) = circleRestrDen.eval (param p) ^
          fs.prod.totalDegree * evalR fs.prod p := by
        calc
          q.eval (param p) = (circleRestrPoly fs.prod A B).eval (param p) := by rfl
          _ = circleRestrDen.eval (param p) ^ fs.prod.totalDegree *
              evalR fs.prod (circleRestrPoint A B (param p)) :=
                circleRestrPoly_eval fs.prod A B (param p)
          _ = _ := by rw [hinvp]
      have hzero : q.eval (param p) = 0 := by simp [q, hqzero]
      have hmul : circleRestrDen.eval (param p) ^ fs.prod.totalDegree *
          evalR fs.prod p = 0 := by rw [← heval]; exact hzero
      have hden : circleRestrDen.eval (param p) ≠ 0 := by
        simp [circleRestrDen]
        positivity
      rcases mul_eq_zero.mp hmul with hpow | hval
      · exact (pow_ne_zero _ hden) hpow
      · exact hpf hval
    have hcount := circleRestr_sign_cells_bound fs cells hcells hdisj c A B
      exception param hinv q rfl hqne
    have hqdeg : q.natDegree ≤ 2 * fs.prod.totalDegree := by
      dsimp [q]
      exact circleRestrPoly_degree fs.prod A B hA hB
    omega
  by_cases hpLeft : p = circleRestrLeftException c
  · have hpTop : p ≠ circleRestrTopException c := by
      intro htop
      exact circleRestrLeft_ne_top c (hpLeft.symm.trans htop)
    exact chartBound (circleRestrTopA c) (circleRestrTopB c)
      (circleRestrTopException c)
      (fun x => (x 0 - c.center 0) / (c.radius - (x 1 - c.center 1)))
      (circleRestrTopA_degree c) (circleRestrTopB_degree c)
      (fun x hx hne => circleRestrTop_inverse c x hx hne) hpTop
  · exact chartBound (circleRestrLeftA c) (circleRestrLeftB c)
      (circleRestrLeftException c)
      (fun x => (x 1 - c.center 1) / (c.radius + (x 0 - c.center 0)))
      (circleRestrLeftA_degree c) (circleRestrLeftB_degree c)
      (fun x hx hne => circleRestrLeft_inverse c x hx hne) hpLeft

/-- K_{3,2}-free bipartite count in the direction consumed by circle cells. -/
theorem three_point_incidence_bound : ∃ K : ℝ, 0 < K ∧
    ∀ (α β : Type) (A : Finset α) (B : Finset β) (edges : Finset (α × β)),
      (∀ ab ∈ edges, ab.1 ∈ A ∧ ab.2 ∈ B) →
      (∀ T : Finset α, T ⊆ A → T.card = 3 →
        (B.filter (fun b => ∀ a ∈ T, (a, b) ∈ edges)).card ≤ 1) →
      (edges.card : ℝ) ≤ K * ((A.card : ℝ) * (B.card : ℝ) ^ ((2 : ℝ) / 3) + B.card) := by
  classical
  refine ⟨10, by norm_num, ?_⟩
  intro α β A B edges hedges hthree
  let deg : β → ℕ := fun b => (edges.filter (fun ab => ab.2 = b)).card
  let neigh : β → Finset α := fun b =>
    (edges.filter (fun ab => ab.2 = b)).image Prod.fst
  let triples : β → Finset (Finset α) := fun b => (neigh b).powersetCard 3
  have hneigh_subset (b : β) : neigh b ⊆ A := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨ab, hab, rfl⟩
    exact (hedges ab (Finset.mem_filter.mp hab).1).1
  have hneigh_edge (b : β) {a : α} (ha : a ∈ neigh b) : (a, b) ∈ edges := by
    rcases Finset.mem_image.mp ha with ⟨ab, hab, hfst⟩
    have hab' := Finset.mem_filter.mp hab
    have hpair : ab = (a, b) := Prod.ext hfst hab'.2
    simpa [hpair] using hab'.1
  have hdeg_neigh (b : β) : deg b = (neigh b).card := by
    dsimp [deg, neigh]
    rw [Finset.card_image_of_injOn]
    intro ab hab ab' hab' hfst
    apply Prod.ext hfst
    exact (Finset.mem_filter.mp hab).2.trans (Finset.mem_filter.mp hab').2.symm
  have hmaps : (edges : Set (α × β)).MapsTo Prod.snd (B : Set β) := by
    intro ab hab
    exact (hedges ab (Finset.mem_coe.mp hab)).2
  have hsumdeg : edges.card = ∑ b ∈ B, deg b := by
    simpa [deg] using Finset.card_eq_sum_card_fiberwise hmaps
  have htriples_disjoint : (B : Set β).PairwiseDisjoint triples := by
    intro b hb b' hb' hbb'
    apply Finset.disjoint_left.mpr
    intro T hTb hTb'
    have hT := Finset.mem_powersetCard.mp hTb
    have hT' := Finset.mem_powersetCard.mp hTb'
    have hTA : T ⊆ A := hT.1.trans (hneigh_subset b)
    have hTcard : T.card = 3 := hT.2
    have hbcommon : b ∈ B.filter (fun z => ∀ a ∈ T, (a, z) ∈ edges) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hb, ?_⟩
      intro a ha
      exact hneigh_edge b (hT.1 ha)
    have hb'common : b' ∈ B.filter (fun z => ∀ a ∈ T, (a, z) ∈ edges) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hb', ?_⟩
      intro a ha
      exact hneigh_edge b' (hT'.1 ha)
    have hpair : ({b, b'} : Finset β) ⊆
        B.filter (fun z => ∀ a ∈ T, (a, z) ∈ edges) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hbcommon
      · exact hb'common
    have htwo : 2 ≤ (B.filter (fun z => ∀ a ∈ T, (a, z) ∈ edges)).card := by
      calc
        2 = ({b, b'} : Finset β).card := by simp [hbb']
        _ ≤ _ := Finset.card_le_card hpair
    have hone := hthree T hTA hTcard
    omega
  have htriples_subset : B.biUnion triples ⊆ A.powersetCard 3 := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨b, hb, hTb⟩
    have hT' := Finset.mem_powersetCard.mp hTb
    exact Finset.mem_powersetCard.mpr ⟨hT'.1.trans (hneigh_subset b), hT'.2⟩
  have htriple_count : (∑ b ∈ B, Nat.choose (deg b) 3) ≤ Nat.choose A.card 3 := by
    calc
      _ = (B.biUnion triples).card := by
        rw [Finset.card_biUnion htriples_disjoint]
        simp [triples, Finset.card_powersetCard, hdeg_neigh]
      _ ≤ (A.powersetCard 3).card := Finset.card_le_card htriples_subset
      _ = Nat.choose A.card 3 := by simp [Finset.card_powersetCard]
  have hsumdegR : (∑ b ∈ B, (deg b : ℝ)) = edges.card := by
    exact_mod_cast hsumdeg.symm
  have hchoose_sumR : (∑ b ∈ B, (Nat.choose (deg b) 3 : ℝ)) ≤ (A.card : ℝ) ^ 3 := by
    calc
      _ = ((∑ b ∈ B, Nat.choose (deg b) 3 : ℕ) : ℝ) := by simp
      _ ≤ (Nat.choose A.card 3 : ℝ) := by exact_mod_cast htriple_count
      _ ≤ (A.card : ℝ) ^ 3 := by
        exact_mod_cast (Nat.choose_le_pow A.card 3)
  have hdegree_cube (b : β) : (deg b : ℝ) ^ 3 ≤
      162 * (Nat.choose (deg b) 3 : ℝ) + 8 := by
    by_cases hsmall : deg b < 3
    · have hle : deg b ≤ 2 := by omega
      have hleR : (deg b : ℝ) ≤ 2 := by exact_mod_cast hle
      have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (deg b : ℝ)) hleR 3
      have hchoose : 0 ≤ (Nat.choose (deg b) 3 : ℝ) := by positivity
      nlinarith
    · have hlarge : 3 ≤ deg b := by omega
      have hsub : deg b + 1 - 3 = deg b - 2 := by omega
      have hpow_choose := Nat.pow_le_choose (α := ℝ) 3 (deg b)
      rw [hsub] at hpow_choose
      have hfactorR : ((deg b - 2 : ℕ) : ℝ) ^ 3 ≤
          6 * (Nat.choose (deg b) 3 : ℝ) := by
        have hmul := (div_le_iff₀ (by norm_num : (0 : ℝ) < 6)).mp hpow_choose
        norm_num at hmul ⊢
        nlinarith
      have hlinNat : deg b ≤ 3 * (deg b - 2) := by omega
      have hlin : (deg b : ℝ) ≤ 3 * ((deg b - 2 : ℕ) : ℝ) := by
        exact_mod_cast hlinNat
      have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (deg b : ℝ)) hlin 3
      norm_num at hpow ⊢
      nlinarith [hfactorR]
  have hsumcube : (∑ b ∈ B, (deg b : ℝ) ^ 3) ≤
      162 * (A.card : ℝ) ^ 3 + 8 * B.card := by
    calc
      _ ≤ ∑ b ∈ B, (162 * (Nat.choose (deg b) 3 : ℝ) + 8) :=
        Finset.sum_le_sum fun b hb => hdegree_cube b
      _ = 162 * (∑ b ∈ B, (Nat.choose (deg b) 3 : ℝ)) + 8 * B.card := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
        ring
      _ ≤ _ := by nlinarith [hchoose_sumR]
  have hJensen := pow_sum_le_card_mul_sum_pow
    (s := B) (f := fun b => (deg b : ℝ)) (by intro b hb; positivity) 2
  let n : ℝ := A.card
  let m : ℝ := B.card
  let q : ℝ := m ^ ((2 : ℝ) / 3)
  have hm : 0 ≤ m := by positivity
  have hn : 0 ≤ n := by positivity
  have hq : 0 ≤ q := by positivity
  have hq3 : q ^ 3 = m ^ 2 := by
    dsimp [q]
    rw [← Real.rpow_natCast _ 3]
    rw [← Real.rpow_mul hm]
    norm_num
  have hE3 : (edges.card : ℝ) ^ 3 ≤ 162 * n ^ 3 * m ^ 2 + 8 * m ^ 3 := by
    calc
      _ = (∑ b ∈ B, (deg b : ℝ)) ^ 3 := by rw [hsumdegR]
      _ ≤ (B.card : ℝ) ^ 2 * ∑ b ∈ B, (deg b : ℝ) ^ 3 := hJensen
      _ ≤ (B.card : ℝ) ^ 2 * (162 * n ^ 3 + 8 * B.card) :=
        mul_le_mul_of_nonneg_left hsumcube (by positivity)
      _ = _ := by dsimp [n, m]; ring
  have hx : 0 ≤ n * q := mul_nonneg hn hq
  have hy : 0 ≤ m := hm
  have hcross : (n * q) ^ 3 + m ^ 3 ≤ (n * q + m) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (n * q)) hy,
      mul_nonneg hx (sq_nonneg m)]
  have hE3' : (edges.card : ℝ) ^ 3 ≤ (10 * (n * q + m)) ^ 3 := by
    have hx3 : (n * q) ^ 3 = n ^ 3 * m ^ 2 := by rw [mul_pow, hq3]
    have hrewrite : 162 * n ^ 3 * m ^ 2 + 8 * m ^ 3 =
        162 * (n * q) ^ 3 + 8 * m ^ 3 := by rw [hx3]; ring
    rw [hrewrite] at hE3
    have hx3nonneg : 0 ≤ (n * q) ^ 3 := by positivity
    have hy3nonneg : 0 ≤ m ^ 3 := by positivity
    have hsmall : 162 * (n * q) ^ 3 + 8 * m ^ 3 ≤
        162 * ((n * q) ^ 3 + m ^ 3) := by nlinarith
    have hlarge : 162 * ((n * q) ^ 3 + m ^ 3) ≤
        1000 * ((n * q + m) ^ 3) := by
      calc
        162 * ((n * q) ^ 3 + m ^ 3) ≤ 1000 * ((n * q) ^ 3 + m ^ 3) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ ≤ 1000 * ((n * q + m) ^ 3) :=
          mul_le_mul_of_nonneg_left hcross (by norm_num)
    calc
      (edges.card : ℝ) ^ 3 ≤ 162 * (n * q) ^ 3 + 8 * m ^ 3 := hE3
      _ ≤ 162 * ((n * q) ^ 3 + m ^ 3) := hsmall
      _ ≤ 1000 * ((n * q + m) ^ 3) := hlarge
      _ = (10 * (n * q + m)) ^ 3 := by ring
  have hfinal : (edges.card : ℝ) ≤ 10 * (n * q + m) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hE3'
  simpa [n, m, q] using hfinal

private lemma circlePolynomial_zero_iff (c : Circle) (x : E 2) :
    evalR (circlePolynomial c) x = 0 ↔ x ∈ circleSet c := by
  rw [circleSet, Set.mem_setOf_eq, circlePolynomial_eval]
  constructor
  · intro h
    have hdn : 0 ≤ dist x c.center := dist_nonneg
    apply (sq_eq_sq₀ hdn c.radius_pos.le).mp
    nlinarith
  · intro h
    rw [h]
    ring

private lemma circle_has_three_points (c : Circle) :
    ∃ X : Finset (E 2), X.card = 3 ∧ (X : Set (E 2)) ⊆ circleSet c := by
  let e0 : E 2 := EuclideanSpace.single (0 : Fin 2) 1
  let e1 : E 2 := EuclideanSpace.single (1 : Fin 2) 1
  let p0 : E 2 := c.center + c.radius • e0
  let p1 : E 2 := c.center + c.radius • e1
  let p2 : E 2 := c.center - c.radius • e0
  have he0 : ‖e0‖ = 1 := by simp [e0, E]
  have he1 : ‖e1‖ = 1 := by simp [e1, E]
  have hp0 : p0 ∈ circleSet c := by
    change dist p0 c.center = c.radius
    simp [p0, dist_eq_norm, norm_smul, he0, abs_of_pos c.radius_pos]
  have hp1 : p1 ∈ circleSet c := by
    change dist p1 c.center = c.radius
    simp [p1, dist_eq_norm, norm_smul, he1, abs_of_pos c.radius_pos]
  have hp2 : p2 ∈ circleSet c := by
    change dist p2 c.center = c.radius
    simp [p2, norm_smul, he0, abs_of_pos c.radius_pos]
  have h01 : p0 ≠ p1 := by
    intro h
    have hh := congrArg (fun x : E 2 => x 0) h
    simp [p0, p1, e0, e1] at hh
    nlinarith [c.radius_pos]
  have h02 : p0 ≠ p2 := by
    intro h
    have hh := congrArg (fun x : E 2 => x 0) h
    simp [p0, p2, e0] at hh
    nlinarith [c.radius_pos]
  have h12 : p1 ≠ p2 := by
    intro h
    have hh := congrArg (fun x : E 2 => x 0) h
    simp [p1, p2, e0, e1] at hh
    nlinarith [c.radius_pos]
  refine ⟨{p0, p1, p2}, ?_, ?_⟩
  · simp [h01, h02, h12]
  · intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hp0
    · exact hp1
    · exact hp2

private theorem circlePolynomial_dvd_eq (c c' : Circle)
    (hdiv : circlePolynomial c ∣ circlePolynomial c') : c = c' := by
  by_contra hne
  obtain ⟨X, hX, hXc⟩ := circle_has_three_points c
  have hXc' : (X : Set (E 2)) ⊆ circleSet c' := by
    intro x hx
    have hon : onCircle (circlePolynomial c') c :=
      (circle_polynomial_factor c).2.2 _ |>.2 hdiv
    apply (circlePolynomial_zero_iff c' x).mp
    exact hon x (hXc hx)
  let S : Set Circle := {d | (X : Set (E 2)) ⊆ circleSet d}
  obtain ⟨hfin, hbound⟩ := circle_three_points X hX
  have hpair : ({c, c'} : Set Circle) ⊆ S := by
    intro d hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl
    · exact hXc
    · exact hXc'
  have hcard := Set.ncard_le_ncard hpair hfin
  rw [Set.ncard_pair hne] at hcard
  have hbound' : S.ncard ≤ 1 := by exact_mod_cast hbound
  omega

private theorem circle_offDiag_count (X : Finset (E 2)) (C : Finset Circle) :
    (∑ x ∈ X, ((C.filter (fun c => x ∈ circleSet c)).offDiag.card : ℝ)) =
      ∑ ab ∈ C.offDiag,
        ((X.filter (fun x => x ∈ circleSet ab.1 ∧ x ∈ circleSet ab.2)).card : ℝ) := by
  classical
  simp_rw [show ∀ x : E 2,
      ((C.filter (fun c => x ∈ circleSet c)).offDiag.card : ℝ) =
        ∑ ab ∈ C.offDiag,
          if x ∈ circleSet ab.1 ∧ x ∈ circleSet ab.2 then (1 : ℝ) else 0 from
    fun x => by
      let I := C.filter (fun c => x ∈ circleSet c)
      have heq : I.offDiag = C.offDiag.filter
          (fun ab => x ∈ circleSet ab.1 ∧ x ∈ circleSet ab.2) := by
        ext ab
        simp [I, and_left_comm, and_assoc, and_comm]
      rw [heq]
      simp]
  rw [Finset.sum_comm]
  simp

private theorem common_circle_points_le_two (X : Finset (E 2)) (c c' : Circle)
    (hne : c ≠ c') :
    ((X.filter (fun x => x ∈ circleSet c ∧ x ∈ circleSet c')).card : ℝ) ≤ 2 := by
  let S : Set (E 2) := circleSet c ∩ circleSet c'
  let Y := X.filter (fun x => x ∈ circleSet c ∧ x ∈ circleSet c')
  obtain ⟨hfin, hbound⟩ := circle_intersections c c' hne
  have hsub : (Y : Set (E 2)) ⊆ S := by
    intro x hx
    have hxY : x ∈ Y := by simpa using hx
    exact Finset.mem_filter.mp hxY |>.2
  have hcard : Y.card ≤ S.ncard := by
    have h := Set.ncard_le_ncard hsub hfin
    simpa only [Set.ncard_coe_finset] using h
  have hcardR : (Y.card : ℝ) ≤ (S.ncard : ℝ) := by exact_mod_cast hcard
  exact hcardR.trans hbound

/-- Factor count and pairwise intersection bound control contained circles. -/
theorem contained_circle_incidence_bound (f : Poly 2) (hf : f ≠ 0)
    (X : Finset (E 2)) (C : Finset Circle) (hC : ∀ c ∈ C, onCircle f c) :
    2 * C.card ≤ f.totalDegree ∧
      (circleIncidences X C : ℝ) ≤ X.card + (f.totalDegree : ℝ) ^ 2 := by
  classical
  have hpairwise : (↑C : Set Circle).Pairwise (fun c c' =>
      IsRelPrime (circlePolynomial c) (circlePolynomial c')) := by
    intro c hc c' hc' hne
    exact ((circle_polynomial_factor c).1).isRelPrime_iff_not_dvd.mpr
      (fun hd => hne (circlePolynomial_dvd_eq c c' hd))
  have hprod_dvd : (∏ c ∈ C, circlePolynomial c) ∣ f :=
    Finset.prod_dvd_of_isRelPrime hpairwise (by
      intro c hc
      exact ((circle_polynomial_factor c).2.2 f).mp (hC c hc))
  have hprod_ne (T : Finset Circle) : (∏ c ∈ T, circlePolynomial c) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro c hc
    exact (circle_polynomial_factor c).1.ne_zero
  have hdegprod : ∀ T : Finset Circle,
      (∏ c ∈ T, circlePolynomial c).totalDegree = 2 * T.card := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert c T hct ih =>
      rw [Finset.prod_insert hct]
      rw [MvPolynomial.totalDegree_mul_of_isDomain
        (circle_polynomial_factor c).1.ne_zero (hprod_ne T)]
      rw [(circle_polynomial_factor c).2.1, ih]
      simp only [Finset.card_insert_of_notMem hct]
      ring
  have hdegC : 2 * C.card ≤ f.totalDegree := by
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hprod_dvd hf
    rw [hdegprod C] at hle
    exact hle
  have hpoint (x : E 2) :
      ((C.filter (fun c => x ∈ circleSet c)).card : ℝ) ≤
        1 + ((C.filter (fun c => x ∈ circleSet c)).offDiag.card : ℝ) := by
    let I := C.filter (fun c => x ∈ circleSet c)
    have hnat : I.card ≤ 1 + I.offDiag.card := by
      by_cases hsmall : I.card ≤ 1
      · interval_cases hcard : I.card <;> simp [hcard, Finset.offDiag_card]
      · have htwo : 2 ≤ I.card := by omega
        have hreal : (I.card : ℝ) ≤ 1 + (I.offDiag.card : ℝ) := by
          rw [Finset.offDiag_card]
          have hmul : I.card ≤ I.card * I.card := by nlinarith
          rw [Nat.cast_sub hmul, Nat.cast_mul]
          push_cast
          nlinarith [sq_nonneg ((I.card : ℝ) - 1)]
        exact_mod_cast hreal
    exact_mod_cast hnat
  have hswap := circle_offDiag_count X C
  have hpair_sum :
      (∑ ab ∈ C.offDiag,
        ((X.filter (fun x => x ∈ circleSet ab.1 ∧ x ∈ circleSet ab.2)).card : ℝ)) ≤
        ∑ ab ∈ C.offDiag, (2 : ℝ) := by
    apply Finset.sum_le_sum
    intro ab hab
    exact common_circle_points_le_two X ab.1 ab.2 (Finset.mem_offDiag.mp hab).2.2
  have hinc : (circleIncidences X C : ℝ) ≤
      (X.card : ℝ) + 2 * (C.offDiag.card : ℝ) := by
    calc
      (circleIncidences X C : ℝ) =
          ∑ x ∈ X, ((C.filter (fun c => x ∈ circleSet c)).card : ℝ) := by
            simp [circleIncidences]
      _ ≤ ∑ x ∈ X,
          (1 + ((C.filter (fun c => x ∈ circleSet c)).offDiag.card : ℝ)) :=
            Finset.sum_le_sum (fun x hx => hpoint x)
      _ = (X.card : ℝ) +
          ∑ x ∈ X, ((C.filter (fun c => x ∈ circleSet c)).offDiag.card : ℝ) := by
            simp [Finset.sum_add_distrib]
      _ = (X.card : ℝ) +
          ∑ ab ∈ C.offDiag,
            ((X.filter (fun x => x ∈ circleSet ab.1 ∧ x ∈ circleSet ab.2)).card : ℝ) := by
            rw [hswap]
      _ ≤ (X.card : ℝ) + ∑ ab ∈ C.offDiag, (2 : ℝ) := by linarith [hpair_sum]
      _ = (X.card : ℝ) + 2 * (C.offDiag.card : ℝ) := by simp; ring
  have hOff_le : (C.offDiag.card : ℝ) ≤ (C.card : ℝ) ^ 2 := by
    have hnat : C.offDiag.card ≤ C.card ^ 2 := by
      rw [Finset.offDiag_card]
      calc
        C.card * C.card - C.card ≤ C.card * C.card := Nat.sub_le _ _
        _ = C.card ^ 2 := by simp [pow_two]
    exact_mod_cast hnat
  let m : ℝ := C.card
  let d : ℝ := f.totalDegree
  have hm2 : 2 * m ≤ d := by
    dsimp [m, d]
    exact_mod_cast hdegC
  have hm0 : 0 ≤ m := by positivity
  have hd0 : 0 ≤ d := by positivity
  have hml : m ≤ d := by linarith
  have hpairdeg : 2 * m ^ 2 ≤ d ^ 2 := by
    calc
      2 * m ^ 2 = (2 * m) * m := by ring
      _ ≤ d * m := mul_le_mul_of_nonneg_right hm2 hm0
      _ ≤ d * d := mul_le_mul_of_nonneg_left hml hd0
      _ = d ^ 2 := by ring
  have hinc' : (circleIncidences X C : ℝ) ≤ (X.card : ℝ) + d ^ 2 := by
    calc
      (circleIncidences X C : ℝ) ≤ (X.card : ℝ) + 2 * (C.offDiag.card : ℝ) := hinc
      _ ≤ (X.card : ℝ) + 2 * m ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left hOff_le (by norm_num : 0 ≤ (2 : ℝ))
        linarith
      _ ≤ (X.card : ℝ) + d ^ 2 := by linarith [hpairdeg]
  refine ⟨hdegC, ?_⟩
  simpa [d] using hinc'

theorem circle_relationMass (X : Finset (E 2)) (C : Finset Circle) :
    relationMass X C (fun x c => x ∈ circleSet c) = (circleIncidences X C : ℝ) := by
  rw [relationMass_sum_card]
  simp [circleIncidences]

set_option maxHeartbeats 1000000 in
/-- The finite KST input specialized to ordinary positive-radius circles. -/
theorem circle_cell_mass_bound : ∃ K : ℝ, 0 < K ∧
    ∀ (X : Finset (E 2)) (C : Finset Circle),
      relationMass X C (fun x c => x ∈ circleSet c) ≤
        K*((X.card:ℝ)*(C.card:ℝ)^((2:ℝ)/3)+C.card) := by
  obtain ⟨K,hK,hbound⟩ := three_point_incidence_bound
  refine ⟨K,hK,?_⟩
  intro X C
  letI : DecidableEq (E 2 × Circle) := Classical.decEq _
  let edges := relationEdges X C (fun x c => x ∈ circleSet c)
  rw [relationMass_edges]
  apply hbound (E 2) Circle X C edges
  · intro ab hab
    exact Finset.mem_product.mp (Finset.mem_filter.mp hab).1
  · intro U hUX hU
    have hcircle := circle_three_points U hU
    let B := C.filter (fun c => ∀ x ∈ U, (x,c) ∈ edges)
    have hsub : (B : Set Circle) ⊆ {c : Circle | (U : Set (E 2)) ⊆ circleSet c} := by
      intro c hc x hx
      have he := (Finset.mem_filter.mp hc).2 x hx
      exact (Finset.mem_filter.mp he).2
    have hcard := finset_card_le_ncard B _ hcircle.1 hsub
    have hreal : (B.card:ℝ) ≤ 1 := (Nat.cast_le.mpr hcard).trans hcircle.2
    have hn : B.card ≤ 1 := Nat.cast_le.mp (by simpa using hreal : (B.card:ℝ) ≤ (1:ℕ))
    convert hn using 1
    congr 1
    ext c
    simp only [B, Finset.mem_filter]

/-- Each noncontained circle contributes only its polynomial restriction roots on the boundary. -/
theorem circle_boundary_mass (f : Poly 2) (X : Finset (E 2)) (C : Finset Circle)
    (hC : ∀ c ∈ C, ¬ onCircle f c) :
    relationMass (pointsIn X (zeroSet f)) C (fun x c => x ∈ circleSet c) ≤
      (C.card:ℝ)*(2*(f.totalDegree:ℝ)+2) := by
  rw [relationMass_pointsIn]
  calc
    _ ≤ ∑ _c ∈ C, (2*(f.totalDegree:ℝ)+2) := by
      apply Finset.sum_le_sum
      intro c hc
      exact cloudMass_le_finite_bound X _ _ (polynomial_circle_zeros f c (hC c hc))
    _ = _ := by simp; ring

/-- Polynomial sign partitioning at the three-point circle incidence exponent. -/
theorem circle_partition_construct : ∃ K : ℝ, 0 < K ∧
    ∀ (X : Finset (E 2)) (C : Finset Circle) (r : ℕ), 1 ≤ r →
      (circleIncidences X C:ℝ) ≤ K*((X.card:ℝ)*(C.card:ℝ)^((2:ℝ)/3)/(r:ℝ)^((2:ℝ)/3)+
        (C.card:ℝ)*r+X.card+(r:ℝ)^2) := by
  obtain ⟨p,hp,hpart⟩ := ci_partition_dim 2 (by norm_num)
  obtain ⟨k,hk,hcell⟩ := circle_cell_mass_bound
  let D := 2*p+2
  let H := p*D^((2:ℝ)/3)*p^((1:ℝ)/3)
  let K := k*H+(k+1)*D+1+p^2
  have hD : 0 < D := by dsimp [D]; linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro X C r hr
  have hrone : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0:ℝ) < r := by positivity
  obtain ⟨fs,cells,hf,hdeg,hcard,hcells,hdisj,hcover,hline⟩ := hpart X r hr
  let f := fs.prod
  let C₀ := C.filter (fun c => onCircle f c)
  let C₁ := C.filter (fun c => ¬ onCircle f c)
  let a : Set (E 2) → ℝ := fun R => (pointsIn X R).card
  let b : Set (E 2) → ℝ := fun R => (C₁.filter (fun c => (R ∩ circleSet c).Nonempty)).card
  have hC₁ : ∀ c ∈ C₁, ¬ onCircle f c := fun c hc => (Finset.mem_filter.mp hc).2
  have hC₁card : (C₁.card:ℝ) ≤ C.card := by exact_mod_cast Finset.card_filter_le C (fun c => ¬onCircle f c)
  have hcross : 2*(f.totalDegree:ℝ)+2 ≤ D*r := by dsimp [D]; dsimp [f]; nlinarith
  have hsum : (∑ R ∈ cells, b R) ≤ D*(C.card:ℝ)*r := by
    have hswap := relationMass_swap cells C₁ (fun R c => (R ∩ circleSet c).Nonempty)
    rw [relationMass_sum_card, relationMass_sum_card] at hswap
    have hc : (∑ R ∈ cells, b R) ≤ (C₁.card:ℝ)*(2*(f.totalDegree:ℝ)+2) := by
      rw [show (∑ R ∈ cells,b R) = ∑ c ∈ C₁, ((cells.filter (fun R => (R ∩ circleSet c).Nonempty)).card:ℝ) from hswap]
      calc
        _ ≤ ∑ _c ∈ C₁, (2*(f.totalDegree:ℝ)+2) := by
          apply Finset.sum_le_sum
          intro c hc
          exact_mod_cast circle_sign_cells fs cells (fun R hR => (hcells R hR).1) hdisj c (hC₁ c hc)
        _ = _ := by simp; ring
    calc
      _ ≤ (C₁.card:ℝ)*(2*(f.totalDegree:ℝ)+2) := hc
      _ ≤ (C.card:ℝ)*(D*r) := mul_le_mul hC₁card hcross (by positivity) (by positivity)
      _ = _ := by ring
  have hweighted : (∑ R ∈ cells, a R*(b R)^((2:ℝ)/3)) ≤
      H*(X.card:ℝ)*(C.card:ℝ)^((2:ℝ)/3)/(r:ℝ)^((2:ℝ)/3) :=
    partition_two_thirds_sum cells a b p D X.card C.card r hp.le hD.le (by positivity) (by positivity) hrpos
      (fun R hR => ⟨Nat.cast_nonneg _,(hcells R hR).2.2⟩)
      (fun R _ => Nat.cast_nonneg _) hcard hsum
  have hcellSum : (∑ R ∈ cells, relationMass (pointsIn X R) C₁ (fun x c => x ∈ circleSet c)) ≤
      k*(H*(X.card:ℝ)*(C.card:ℝ)^((2:ℝ)/3)/(r:ℝ)^((2:ℝ)/3)+D*(C.card:ℝ)*r) := by
    calc
      _ ≤ ∑ R ∈ cells, k*(a R*(b R)^((2:ℝ)/3)+b R) := by
        apply Finset.sum_le_sum
        intro R hR
        rw [relationMass_restrict_right (pointsIn X R) C₁ (fun x c => x ∈ circleSet c)
          (fun c => (R ∩ circleSet c).Nonempty) (by
            intro x hx c hc hxc
            exact ⟨x,(Finset.mem_filter.mp hx).2,hxc⟩)]
        exact hcell _ _
      _ = k*((∑ R ∈ cells,a R*(b R)^((2:ℝ)/3))+(∑ R ∈ cells,b R)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hweighted hsum) hk.le
  have houtside : relationMass (pointsIn X (zeroSet f)ᶜ) C₁ (fun x c => x ∈ circleSet c) ≤
      k*(H*(X.card:ℝ)*(C.card:ℝ)^((2:ℝ)/3)/(r:ℝ)^((2:ℝ)/3)+D*(C.card:ℝ)*r) := by
    apply (relationMass_cover _ _ _ cells (fun R => pointsIn X R) ?_).trans hcellSum
    intro x hx
    have hxX : x ∈ X := (mem_pointsIn X _ x).mp hx |>.1
    have hxoff : x ∈ (zeroSet f)ᶜ := (mem_pointsIn X _ x).mp hx |>.2
    rw [← hcover] at hxoff
    obtain ⟨R,hR,hxR⟩ := (by simpa using hxoff : ∃ R ∈ cells,x ∈ R)
    exact ⟨R,hR,Finset.mem_filter.mpr ⟨hxX,hxR⟩⟩
  have hboundary : relationMass (pointsIn X (zeroSet f)) C₁ (fun x c => x ∈ circleSet c) ≤ D*(C.card:ℝ)*r := by
    calc
      _ ≤ (C₁.card:ℝ)*(2*(f.totalDegree:ℝ)+2) := circle_boundary_mass f X C₁ hC₁
      _ ≤ (C.card:ℝ)*(D*r) := mul_le_mul hC₁card hcross (by positivity) (by positivity)
      _ = _ := by ring
  have hcontained : relationMass X C₀ (fun x c => x ∈ circleSet c) ≤ X.card+p^2*(r:ℝ)^2 := by
    have hc := (contained_circle_incidence_bound f hf X C₀ (fun c hc => (Finset.mem_filter.mp hc).2)).2
    rw [← circle_relationMass] at hc
    have hd : (f.totalDegree:ℝ)^2 ≤ p^2*(r:ℝ)^2 := by
      have hd := hdeg
      change (f.totalDegree:ℝ) ≤ p*r at hd
      nlinarith [show (0:ℝ) ≤ (f.totalDegree:ℝ) from Nat.cast_nonneg _]
    linarith
  have htotal : (circleIncidences X C:ℝ) ≤
      k*H*((X.card:ℝ)*(C.card:ℝ)^((2:ℝ)/3)/(r:ℝ)^((2:ℝ)/3))+
      (k+1)*D*((C.card:ℝ)*r)+(X.card:ℝ)+p^2*(r:ℝ)^2 := by
    have hsplit := relationMass_split_right X C (fun x c => x ∈ circleSet c) (fun c => onCircle f c)
    have hsplitX := relationMass_split_left X C₁ (fun x c => x ∈ circleSet c) (fun x => x ∈ zeroSet f)
    rw [circle_relationMass] at hsplit
    change (circleIncidences X C:ℝ) = relationMass X C₀ (fun x c => x ∈ circleSet c)+relationMass X C₁ (fun x c => x ∈ circleSet c) at hsplit
    have hcomp : X.filter (fun x => x ∉ zeroSet f) = pointsIn X (zeroSet f)ᶜ := by
      ext x; simp [pointsIn]
    rw [hcomp] at hsplitX
    change relationMass X C₁ (fun x c => x ∈ circleSet c) = relationMass (pointsIn X (zeroSet f)) C₁ (fun x c => x ∈ circleSet c)+
      relationMass (pointsIn X (zeroSet f)ᶜ) C₁ (fun x c => x ∈ circleSet c) at hsplitX
    calc
      _ = relationMass X C₀ (fun x c => x ∈ circleSet c) +
          (relationMass (pointsIn X (zeroSet f)) C₁ (fun x c => x ∈ circleSet c) +
           relationMass (pointsIn X (zeroSet f)ᶜ) C₁ (fun x c => x ∈ circleSet c)) := by
        rw [hsplit,hsplitX]
      _ ≤ ((X.card:ℝ)+p^2*(r:ℝ)^2) +
          (D*(C.card:ℝ)*r+k*(H*(X.card:ℝ)*(C.card:ℝ)^((2:ℝ)/3)/(r:ℝ)^((2:ℝ)/3)+D*(C.card:ℝ)*r)) :=
        add_le_add hcontained (add_le_add hboundary houtside)
      _ = _ := by ring
  have hnonD : 0 ≤ (k+1)*D := by positivity
  have hnonH : 0 ≤ k*H := by positivity
  have hcoeff₁ : k*H ≤ K := by dsimp [K]; nlinarith [sq_nonneg p]
  have hcoeff₂ : (k+1)*D ≤ K := by dsimp [K]; nlinarith [sq_nonneg p]
  have hcoeff₃ : (1:ℝ) ≤ K := by dsimp [K]; nlinarith [sq_nonneg p]
  have hcoeff₄ : p^2 ≤ K := by dsimp [K]; linarith
  apply htotal.trans
  calc
    _ ≤ K*((X.card:ℝ)*(C.card:ℝ)^((2:ℝ)/3)/(r:ℝ)^((2:ℝ)/3))+
        K*((C.card:ℝ)*r)+K*(X.card:ℝ)+K*(r:ℝ)^2 := by
          gcongr
          exact le_mul_of_one_le_left (Nat.cast_nonneg _) hcoeff₃
    _ = _ := by ring

/-- Cell KST, crossing counts and boundary incidence estimate before optimization. -/
theorem circle_partition_estimate : ∃ K : ℝ, 0 < K ∧
    ∀ (X : Finset (E 2)) (C : Finset Circle) (r : ℕ), 1 ≤ r →
      (circleIncidences X C : ℝ) ≤ K *
        ((X.card : ℝ) * (C.card : ℝ) ^ ((2 : ℝ) / 3) / (r : ℝ) ^ ((2 : ℝ) / 3) +
          (C.card : ℝ) * r + X.card + (r : ℝ) ^ 2) := by
  exact circle_partition_construct

set_option maxHeartbeats 2000000
/-- Pach--Sharir exponents in the only size regime consumed by distance circles. -/
theorem ci_point_circle_incidence : ∃ K : ℝ, 0 < K ∧
    ∀ (X : Finset (E 2)) (C : Finset Circle), X.card ≤ C.card →
      (circleIncidences X C : ℝ) ≤ K *
        ((X.card : ℝ) ^ ((3 : ℝ) / 5) * (C.card : ℝ) ^ ((4 : ℝ) / 5) +
          X.card + C.card) := by
  obtain ⟨Kp, hKp, hpartition⟩ := circle_partition_estimate
  let G : ℝ := 8 * Kp + 1
  have hG : 0 < G := by dsimp [G]; positivity
  have hGpart : 5 * Kp ≤ G := by dsimp [G]; linarith [hKp]
  have hGlarge : 4 * Kp ≤ G := by dsimp [G]; linarith [hKp]
  refine ⟨G, hG, ?_⟩
  intro X C hXC
  let n : ℝ := X.card
  let m : ℝ := C.card
  let p : ℝ := (3 : ℝ) / 5
  let q : ℝ := (2 : ℝ) / 3
  let s : ℝ := (1 : ℝ) / 5
  let u : ℝ := (2 : ℝ) / 5
  let v : ℝ := (2 : ℝ) / 15
  let main : ℝ := n ^ p * m ^ ((4 : ℝ) / 5)
  let target : ℝ := main + n + m
  have hncast : n = (X.card : ℝ) := rfl
  have hmcast : m = (C.card : ℝ) := rfl
  have hnm : n ≤ m := by dsimp [n, m]; exact_mod_cast hXC
  have hnonnegN : 0 ≤ n := by positivity
  have hnonnegM : 0 ≤ m := by positivity
  have hzeroCase : X.card = 0 →
      (circleIncidences X C : ℝ) ≤ G * target := by
    intro hXzero
    have hXempty : X = ∅ := Finset.card_eq_zero.mp hXzero
    have hI : circleIncidences X C = 0 := by simp [circleIncidences, hXempty]
    rw [hI]
    have hT : 0 ≤ target := by dsimp [target, main]; positivity
    simpa using mul_nonneg hG.le hT
  by_cases hXzero : X.card = 0
  · exact hzeroCase hXzero
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast Nat.pos_of_ne_zero hXzero
  have hmpos : 0 < m := lt_of_lt_of_le hnpos hnm
  have hnle : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hXzero
  have hmle : 1 ≤ m := hnle.trans hnm
  have htargetNonneg : 0 ≤ target := by
    dsimp [target, main]
    positivity
  have hmainNonneg : 0 ≤ main := by dsimp [main]; positivity
  have hrootCube : (m ^ ((1 : ℝ) / 3)) ^ 3 = m := by
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hnonnegM]
    norm_num
  have hpowSplit : m ^ ((1 : ℝ) / 3) * m ^ ((2 : ℝ) / 3) = m := by
    rw [← Real.rpow_add hmpos]
    norm_num
  have htargetM : m ≤ target := by
    dsimp [target]
    linarith [hmainNonneg, hnonnegN]
  by_cases hlarge : n ^ 3 ≤ m
  · have hroot : n ≤ m ^ ((1 : ℝ) / 3) := by
      have hcube : n ^ 3 ≤ (m ^ ((1 : ℝ) / 3)) ^ 3 := by
        rw [hrootCube]
        exact hlarge
      exact (pow_le_pow_iff_left₀ (n := 3) hnpos.le
        (Real.rpow_nonneg hnonnegM _) (by norm_num)).1 hcube
    have hterm : n * m ^ q ≤ m := by
      calc
        n * m ^ q ≤ m ^ ((1 : ℝ) / 3) * m ^ ((2 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg hnonnegM _)
        _ = m := hpowSplit
    have hpartOne : (circleIncidences X C : ℝ) ≤
        Kp * (n * m ^ q + m + n + 1) := by
      simpa [n, m, q] using hpartition X C 1 (by norm_num)
    have htermsOne : n * m ^ q + m + n + 1 ≤ 4 * m := by
      nlinarith [hterm, hnm, hmle]
    have hlargePart : (circleIncidences X C : ℝ) ≤ (4 * Kp) * m := by
      calc
        _ ≤ Kp * (n * m ^ q + m + n + 1) := hpartOne
        _ ≤ Kp * (4 * m) := mul_le_mul_of_nonneg_left htermsOne hKp.le
        _ = (4 * Kp) * m := by ring
    have hlargeResult : (4 * Kp) * m ≤ G * target :=
      calc
        (4 * Kp) * m ≤ G * m := mul_le_mul_of_nonneg_right hGlarge hnonnegM
        _ ≤ G * target := mul_le_mul_of_nonneg_left htargetM hG.le
    exact hlargePart.trans hlargeResult
  · have hsmall : m < n ^ 3 := lt_of_not_ge hlarge
    let t : ℝ := n ^ p / m ^ s
    let rNat : ℕ := ⌊t⌋₊
    let r : ℝ := rNat
    have htpos : 0 < t := by dsimp [t]; positivity
    have ht5 : t ^ 5 = n ^ 3 / m := by
      dsimp [t, p, s]
      have hnum : (n ^ ((3 : ℝ) / 5)) ^ 5 = n ^ 3 := by
        rw [← Real.rpow_natCast _ 5, ← Real.rpow_mul hnpos.le]
        norm_num
      have hden : (m ^ ((1 : ℝ) / 5)) ^ 5 = m := by
        rw [← Real.rpow_natCast _ 5, ← Real.rpow_mul hmpos.le]
        norm_num
      rw [div_pow, hnum, hden]
    have htgt : 1 < t := by
      have hratio : 1 < n ^ 3 / m := by
        apply (lt_div_iff₀ hmpos).2
        simpa only [one_mul] using hsmall
      have hpow : (1 : ℝ) ^ 5 < t ^ 5 := by simpa [ht5] using hratio
      exact (pow_lt_pow_iff_left₀ (n := 5) (by norm_num) (le_of_lt htpos)
        (by norm_num)).1 hpow
    have hrone : 1 ≤ rNat := by
      dsimp [rNat]
      exact_mod_cast (Nat.one_le_floor_iff t).2 htgt.le
    have hrle : r ≤ t := by
      dsimp [r, rNat]
      exact Nat.floor_le htpos.le
    have hrhalf : t / 2 ≤ r := by
      by_cases ht2 : t < 2
      · have hrfloorlt : rNat < 2 := by
          dsimp [rNat]
          exact (Nat.floor_lt htpos.le).2 ht2
        have hreq : rNat = 1 := by omega
        dsimp [r]
        rw [hreq]
        linarith
      · have ht2' : 2 ≤ t := le_of_not_gt ht2
        have htfloor := Nat.lt_floor_add_one t
        dsimp [r, rNat]
        linarith
    have hmfact : m / m ^ s = m ^ ((4 : ℝ) / 5) := by
      have hsplit : m ^ s * m ^ ((4 : ℝ) / 5) = m := by
        rw [← Real.rpow_add hmpos]
        norm_num [s]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hmpos s)]
      nlinarith [hsplit]
    have hMainEq : m * t = main := by
      dsimp [t, main]
      calc
        m * (n ^ p / m ^ s) = n ^ p * (m / m ^ s) := by ring
        _ = n ^ p * m ^ ((4 : ℝ) / 5) := by rw [hmfact]
        _ = _ := rfl
    have hnSplit : n ^ u * n ^ p = n := by
      rw [← Real.rpow_add hnpos]
      norm_num [u, p]
    have hmSplit : m ^ q * m ^ v = m ^ ((4 : ℝ) / 5) := by
      rw [← Real.rpow_add hmpos]
      norm_num [q, v]
    have hnDiv : n / n ^ u = n ^ p := by
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hnpos u)]
      nlinarith [hnSplit]
    have htq : t ^ q = n ^ u / m ^ v := by
      dsimp [t, p, q, s, u, v]
      rw [Real.div_rpow (Real.rpow_nonneg hnonnegN ((3 : ℝ) / 5))
        (Real.rpow_nonneg hnonnegM ((1 : ℝ) / 5)),
        ← Real.rpow_mul hnpos.le, ← Real.rpow_mul hmpos.le]
      congr 1 <;> norm_num
    have hterm1id : n * m ^ q / t ^ q = main := by
      calc
        n * m ^ q / t ^ q = (n / n ^ u) * (m ^ q * m ^ v) := by
          rw [htq]
          field_simp [ne_of_gt (Real.rpow_pos_of_pos hnpos u),
            ne_of_gt (Real.rpow_pos_of_pos hmpos v)]
          <;> ring
        _ = main := by rw [hnDiv, hmSplit]
    have hnmPow : n ^ p ≤ m ^ p := Real.rpow_le_rpow hnpos.le hnm (by norm_num [p])
    have hmpow : m ^ ((2 : ℝ) / 5) ≤ m := by
      calc
        m ^ ((2 : ℝ) / 5) ≤ m ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hmle (by norm_num)
        _ = m := Real.rpow_one m
    have htle : t ≤ m := by
      dsimp [t]
      have hpow : n ^ p / m ^ s ≤ m ^ ((2 : ℝ) / 5) := by
        apply (div_le_iff₀ (Real.rpow_pos_of_pos hmpos s)).2
        calc
          n ^ p ≤ m ^ p := hnmPow
          _ = m ^ ((2 : ℝ) / 5) * m ^ s := by
            rw [← Real.rpow_add hmpos]
            congr 1 <;> norm_num [p, s]
      exact hpow.trans hmpow
    have htsq : t ^ 2 ≤ main := by
      calc
        t ^ 2 ≤ m * t := by nlinarith [htle, le_of_lt htpos]
        _ = main := hMainEq
    have h2pow : (2 : ℝ) ^ q ≤ 2 := by
      calc
        (2 : ℝ) ^ q ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (y := q) (z := 1)
            (by norm_num) (by norm_num [q])
        _ = 2 := Real.rpow_one 2
    have hdivpow : (t / 2) ^ q = t ^ q / (2 : ℝ) ^ q :=
      Real.div_rpow htpos.le (by norm_num) q
    have hrpow : (t / 2) ^ q ≤ r ^ q :=
      Real.rpow_le_rpow (by positivity) hrhalf (by norm_num [q])
    have hden : t ^ q / 2 ≤ r ^ q := by
      calc
        t ^ q / 2 ≤ t ^ q / (2 : ℝ) ^ q :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg htpos.le q)
            (Real.rpow_pos_of_pos (by norm_num) q) h2pow
        _ = (t / 2) ^ q := hdivpow.symm
        _ ≤ r ^ q := hrpow
    have hrpowpos : 0 < r ^ q := by
      have hrpos : 0 < r := by
        dsimp [r]
        have hNatPos : 0 < rNat := by omega
        exact_mod_cast hNatPos
      exact Real.rpow_pos_of_pos hrpos q
    have hterm1 : n * m ^ q / r ^ q ≤ 2 * main := by
      calc
        n * m ^ q / r ^ q ≤ n * m ^ q / (t ^ q / 2) :=
          div_le_div_of_nonneg_left
            (mul_nonneg hnonnegN (Real.rpow_nonneg hnonnegM q))
            (div_pos (Real.rpow_pos_of_pos htpos q) (by norm_num)) hden
        _ = 2 * (n * m ^ q / t ^ q) := by
          field_simp
          <;> ring
        _ = 2 * main := by rw [hterm1id]
    have hterm2 : m * r ≤ main := by
      calc
        m * r ≤ m * t := mul_le_mul_of_nonneg_left hrle hnonnegM
        _ = main := hMainEq
    have hrpow2 : r ^ 2 ≤ t ^ 2 :=
      pow_le_pow_left₀ (by positivity : 0 ≤ r) hrle 2
    have hterm4 : r ^ 2 ≤ main := hrpow2.trans htsq
    have hsumTerms : n * m ^ q / r ^ q + m * r + n + r ^ 2 ≤
        ((2 * main + main) + n) + main :=
      add_le_add (add_le_add (add_le_add hterm1 hterm2) le_rfl) hterm4
    have hterms : n * m ^ q / r ^ q + m * r + n + r ^ 2 ≤ 5 * target := by
      calc
        _ ≤ ((2 * main + main) + n) + main := hsumTerms
        _ = 4 * main + n := by ring
        _ ≤ 5 * (main + n + m) := by
          have hM : 4 * main ≤ 5 * main := by nlinarith [hmainNonneg]
          have hN : n ≤ 5 * n := by nlinarith [hnonnegN]
          have hM2 : 0 ≤ 5 * m := by positivity
          calc
            4 * main + n ≤ 5 * main + 5 * n := add_le_add hM hN
            _ ≤ 5 * main + 5 * n + 5 * m := le_add_of_nonneg_right hM2
            _ = 5 * (main + n + m) := by ring
        _ = 5 * target := by simp [target]
    have hrNat : 1 ≤ rNat := hrone
    have hpartBound : (circleIncidences X C : ℝ) ≤ Kp *
        (n * m ^ q / r ^ q + m * r + n + r ^ 2) := by
      simpa [n, m, q, r, rNat] using hpartition X C rNat hrNat
    calc
      (circleIncidences X C : ℝ) ≤ Kp *
          (n * m ^ q / r ^ q + m * r + n + r ^ 2) := hpartBound
      _ ≤ Kp * (5 * target) := mul_le_mul_of_nonneg_left hterms hKp.le
      _ ≤ G * target := by
        calc
          Kp * (5 * target) = (5 * Kp) * target := by ring
          _ ≤ G * target := mul_le_mul_of_nonneg_right hGpart htargetNonneg
set_option maxHeartbeats 200000

/-- Circles centered at every point with every positive distance as radius. -/
theorem distance_circles (X : Finset (E 2)) (hX : 2 ≤ X.card) :
    ∃ C : Finset Circle, C.card = X.card * (positiveDistances X).card ∧
      circleIncidences X C = X.card * (X.card - 1) := by
  classical
  let D := positiveDistances X
  have hDpos : ∀ r ∈ D, 0 < r := by
    intro r hr
    change r ∈ X.offDiag.image (fun xy => dist xy.1 xy.2) at hr
    rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
    exact dist_pos.mpr (Finset.mem_offDiag.mp hp).2.2
  have hdistmem {x y : E 2} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
      dist x y ∈ D := by
    change dist x y ∈ X.offDiag.image (fun xy => dist xy.1 xy.2)
    exact Finset.mem_image.mpr
      ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩, rfl⟩
  let P := X ×ˢ D
  let f : E 2 × ℝ → Circle := fun p =>
    if hp : 0 < p.2 then ⟨p.1, p.2, hp⟩ else ⟨p.1, 1, by norm_num⟩
  let C := P.image f
  have hpPos {p : E 2 × ℝ} (hp : p ∈ P) : 0 < p.2 :=
    hDpos p.2 (Finset.mem_product.mp hp).2
  have hf (p : E 2 × ℝ) (hp : p ∈ P) :
      f p = ⟨p.1, p.2, hpPos hp⟩ := by
    simp [f, hpPos hp]
  have hinj : Set.InjOn f (P : Set (E 2 × ℝ)) := by
    intro p hp q hq h
    rw [hf p hp, hf q hq] at h
    exact Prod.ext (congrArg Circle.center h) (congrArg Circle.radius h)
  have hCcard : C.card = X.card * D.card := by
    calc
      C.card = P.card := by
        dsimp [C]
        rw [Finset.card_image_of_injOn hinj]
      _ = X.card * D.card := by simp [P]
  have hrad {x y : E 2} (hx : x ∈ X) (hy : y ∈ X) :
      (D.filter (fun r => dist x y = r)).card = if x ≠ y then 1 else 0 := by
    by_cases hxy : x = y
    · subst y
      have hzero : 0 ∉ D := by
        intro hz
        have hp := hDpos 0 hz
        norm_num at hp
      have hfilter : D.filter (fun r => dist x x = r) = ∅ := by
        ext r
        simp only [Finset.mem_filter, Finset.notMem_empty, dist_self]
        constructor
        · rintro ⟨hr, heq⟩
          exact hzero (heq ▸ hr)
        · intro hfalse
          exact False.elim hfalse
      rw [hfilter]
      simp
    · have hd := hdistmem hx hy hxy
      have hfilter : D.filter (fun r => dist x y = r) = {dist x y} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨_, heq⟩
          exact heq.symm
        · intro heq
          subst r
          exact ⟨hd, rfl⟩
      simp [hfilter, hxy]
  have hfilteredInj (x : E 2) :
      Set.InjOn f ((P.filter (fun p => x ∈ circleSet (f p))) : Set (E 2 × ℝ)) := by
    intro p hp q hq h
    apply hinj
    · exact (Finset.mem_filter.mp hp).1
    · exact (Finset.mem_filter.mp hq).1
    · exact h
  have hfilterCard (x : E 2) (hx : x ∈ X) :
      (C.filter (fun c => x ∈ circleSet c)).card =
        ∑ y ∈ X, if x ≠ y then 1 else 0 := by
    calc
      (C.filter (fun c => x ∈ circleSet c)).card =
          (P.filter (fun p => x ∈ circleSet (f p))).card := by
        change ((P.image f).filter (fun c => x ∈ circleSet c)).card = _
        rw [Finset.filter_image]
        exact Finset.card_image_of_injOn (hfilteredInj x)
      _ = ∑ p ∈ P, if x ∈ circleSet (f p) then 1 else 0 := by
        rw [Finset.card_filter]
      _ = ∑ y ∈ X, ∑ r ∈ D, if dist x y = r then 1 else 0 := by
        change (∑ p ∈ X ×ˢ D, if x ∈ circleSet (f p) then 1 else 0) = _
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro y hy
        apply Finset.sum_congr rfl
        intro r hr
        simp [f, circleSet, hDpos r hr]
      _ = ∑ y ∈ X, if x ≠ y then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        calc
          (∑ r ∈ D, if dist x y = r then 1 else 0) =
              (D.filter (fun r => dist x y = r)).card := by
            rw [Finset.card_filter]
          _ = if x ≠ y then 1 else 0 := hrad hx hy
  have hInc : circleIncidences X C = X.card * (X.card - 1) := by
    unfold circleIncidences
    calc
      (∑ x ∈ X, (C.filter (fun c => x ∈ circleSet c)).card) =
          ∑ x ∈ X, (X.card - 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hfilterCard x hx]
        calc
          (∑ y ∈ X, if x ≠ y then 1 else 0) = (X.filter (fun y => x ≠ y)).card := by
            rw [Finset.card_filter]
          _ = X.card - 1 := by
            rw [show X.filter (fun y => x ≠ y) = X.erase x by
              ext y
              simp [and_comm, ne_comm]]
            exact Finset.card_erase_of_mem hx
      _ = X.card * (X.card - 1) := by simp
  refine ⟨C, ?_, hInc⟩
  simpa [D] using hCcard

/-- ci:weak-planar-distances, replacing CI:808–856. -/
theorem ci_weak_planar_distances : ∃ c : ℝ, 0 < c ∧
    ∀ X : Finset (E 2), 2 ≤ X.card →
      c * (X.card : ℝ) ^ ((3 : ℝ) / 4) ≤ ((positiveDistances X).card : ℝ) := by
  obtain ⟨K, hK, hInc⟩ := ci_point_circle_incidence
  let c₁ : ℝ := 1 / (8 * K)
  let c₂ : ℝ := (1 / (4 * K)) ^ ((5 : ℝ) / 4)
  let T : ℝ := max 1 (8 * K)
  let c₃ : ℝ := 1 / T ^ ((3 : ℝ) / 4)
  let c : ℝ := min c₁ (min c₂ c₃)
  have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0 < c₂ := by dsimp [c₂]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hc₃ : 0 < c₃ := by dsimp [c₃]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hcle₁ : c ≤ c₁ := min_le_left _ _
  have hcle₂ : c ≤ c₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hcle₃ : c ≤ c₃ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc, ?_⟩
  intro X hX
  let n : ℝ := X.card
  let m : ℝ := (positiveDistances X).card
  have hncast : n = (X.card : ℝ) := rfl
  have hn : 2 ≤ n := by dsimp [n]; exact_mod_cast hX
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hxpair := Finset.one_lt_card_iff.mp (show 1 < X.card by omega)
  obtain ⟨x, y, hx, hy, hxy⟩ := hxpair
  have hdmem : dist x y ∈ positiveDistances X := by
    change dist x y ∈ X.offDiag.image (fun p => dist p.1 p.2)
    exact Finset.mem_image.mpr
      ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩, rfl⟩
  have hDcard : 1 ≤ (positiveDistances X).card := by
    have hpos : 0 < (positiveDistances X).card :=
      Finset.card_pos.mpr ⟨dist x y, hdmem⟩
    omega
  have hm1 : 1 ≤ m := by dsimp [m]; exact_mod_cast hDcard
  have hm0 : 0 < m := by linarith
  obtain ⟨C, hCcard, hI⟩ := distance_circles X hX
  have hXC : X.card ≤ C.card := by
    rw [hCcard]
    calc
      X.card = X.card * 1 := by simp
      _ ≤ X.card * (positiveDistances X).card := Nat.mul_le_mul_left _ hDcard
  have hraw := hInc X C hXC
  have hCcast : (C.card : ℝ) = n * m := by
    dsimp [n, m]
    rw [hCcard, Nat.cast_mul]
  have hIcast : (circleIncidences X C : ℝ) = n * (n - 1) := by
    dsimp [n]
    rw [hI, Nat.cast_mul, Nat.cast_sub (by omega)]
    norm_num
  have hmain : n ^ ((3 : ℝ) / 5) * (n * m) ^ ((4 : ℝ) / 5) =
      n ^ ((7 : ℝ) / 5) * m ^ ((4 : ℝ) / 5) := by
    calc
      n ^ ((3 : ℝ) / 5) * (n * m) ^ ((4 : ℝ) / 5) =
          n ^ ((3 : ℝ) / 5) *
            (n ^ ((4 : ℝ) / 5) * m ^ ((4 : ℝ) / 5)) := by
              rw [Real.mul_rpow hn0.le hm0.le]
      _ = (n ^ ((3 : ℝ) / 5) * n ^ ((4 : ℝ) / 5)) *
            m ^ ((4 : ℝ) / 5) := by ring
      _ = n ^ ((7 : ℝ) / 5) * m ^ ((4 : ℝ) / 5) := by
        rw [← Real.rpow_add hn0]
        congr 1
        norm_num
  rw [hCcast, hmain, hIcast, ← hncast] at hraw
  have hlow : n * n / 2 ≤ n * (n - 1) := by nlinarith
  have hsum : n * n / 2 ≤ K *
      (n ^ ((7 : ℝ) / 5) * m ^ ((4 : ℝ) / 5) + n + n * m) :=
    hlow.trans hraw
  have hnpow : n ^ ((3 : ℝ) / 4) ≤ n := by
    calc
      n ^ ((3 : ℝ) / 4) ≤ n ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ = n := Real.rpow_one n
  by_cases hlinear : n / (8 * K) ≤ m
  · calc
      c * n ^ ((3 : ℝ) / 4) ≤ c₁ * n ^ ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hcle₁ (Real.rpow_nonneg hn0.le _)
      _ ≤ c₁ * n := mul_le_mul_of_nonneg_left hnpow hc₁.le
      _ = n / (8 * K) := by dsimp [c₁]; field_simp [ne_of_gt hK]
      _ ≤ m := hlinear
  · have hlinear' : m < n / (8 * K) := lt_of_not_ge hlinear
    by_cases hlarge : 8 * K ≤ n
    · have hlin₁ : K * n ≤ n * n / 8 := by
        have hh := mul_le_mul_of_nonneg_right hlarge hn0.le
        nlinarith
      have hlin₂ : K * n * m ≤ n * n / 8 := by
        calc
          K * n * m ≤ K * n * (n / (8 * K)) :=
            mul_le_mul_of_nonneg_left hlinear'.le (mul_nonneg hK.le hn0.le)
          _ = n * n / 8 := by field_simp [ne_of_gt hK]
      have hmainlower : n * n / 4 ≤
          K * (n ^ ((7 : ℝ) / 5) * m ^ ((4 : ℝ) / 5)) := by
        nlinarith [hsum, hlin₁, hlin₂]
      have hpowN : n ^ ((3 : ℝ) / 5) * n ^ ((7 : ℝ) / 5) = n * n := by
        rw [← Real.rpow_add hn0]
        norm_num [Real.rpow_natCast]
        ring
      have hmul : n ^ ((3 : ℝ) / 5) * n ^ ((7 : ℝ) / 5) ≤
          (4 * K * m ^ ((4 : ℝ) / 5)) * n ^ ((7 : ℝ) / 5) := by
        rw [hpowN]
        nlinarith [hmainlower]
      have hNpow : 0 < n ^ ((7 : ℝ) / 5) := by positivity
      have hratio : n ^ ((3 : ℝ) / 5) ≤ 4 * K * m ^ ((4 : ℝ) / 5) :=
        (mul_le_mul_iff_left₀ hNpow).mp hmul
      have hdiv : n ^ ((3 : ℝ) / 5) / (4 * K) ≤ m ^ ((4 : ℝ) / 5) := by
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [hratio]
      have hraised := Real.rpow_le_rpow (by positivity) hdiv
        (by norm_num : 0 ≤ (5 : ℝ) / 4)
      have hleft :
          (n ^ ((3 : ℝ) / 5) / (4 * K)) ^ ((5 : ℝ) / 4) =
            c₂ * n ^ ((3 : ℝ) / 4) := by
        dsimp [c₂]
        rw [Real.div_rpow (by positivity) (by positivity)]
        rw [← Real.rpow_mul hn0.le]
        rw [Real.div_rpow (by norm_num) (by positivity)]
        norm_num
        ring
      have hright : (m ^ ((4 : ℝ) / 5)) ^ ((5 : ℝ) / 4) = m := by
        rw [← Real.rpow_mul hm0.le]
        norm_num
      have hmainresult : c₂ * n ^ ((3 : ℝ) / 4) ≤ m := by
        calc
          c₂ * n ^ ((3 : ℝ) / 4) =
              (n ^ ((3 : ℝ) / 5) / (4 * K)) ^ ((5 : ℝ) / 4) := hleft.symm
          _ ≤ (m ^ ((4 : ℝ) / 5)) ^ ((5 : ℝ) / 4) := hraised
          _ = m := hright
      exact (mul_le_mul_of_nonneg_right hcle₂ (Real.rpow_nonneg hn0.le _)).trans hmainresult
    · have hsmall : n < 8 * K := lt_of_not_ge hlarge
      have hnT : n ≤ T := (le_of_lt hsmall).trans (le_max_right 1 (8 * K))
      have hpow := Real.rpow_le_rpow hn0.le hnT (by norm_num : 0 ≤ (3 : ℝ) / 4)
      have hcmSmall : c₃ * n ^ ((3 : ℝ) / 4) ≤ 1 := by
        calc
          c₃ * n ^ ((3 : ℝ) / 4) ≤ c₃ * T ^ ((3 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_left hpow hc₃.le
          _ = 1 := by
            dsimp [c₃]
            field_simp [ne_of_gt (Real.rpow_pos_of_pos hT _)]
      calc
        c * n ^ ((3 : ℝ) / 4) ≤ c₃ * n ^ ((3 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right hcle₃ (Real.rpow_nonneg hn0.le _)
        _ ≤ 1 := hcmSmall
        _ ≤ m := hm1

/-- ci:planar-occupancy, replaces the exponent in CI:858–874;
consumer: reduction.tex:27–28, 56, flat-cap exponent c_0 = 1/3. -/
theorem ci_planar_occupancy : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (X : Finset (E d)) (M : ℝ), 1 ≤ M →
      ((positiveDistances X).card : ℝ) ≤ M →
      ∀ H : Plane d, ((pointsOn X H).card : ℝ) ≤ C * M ^ ((4 : ℝ) / 3) := by
  obtain ⟨c, hc, hweak⟩ := ci_weak_planar_distances
  let q : ℝ := (4 : ℝ) / 3
  let C₀ : ℝ := (1 / c) ^ q
  let C : ℝ := max 1 C₀
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hCone : 1 ≤ C := le_max_left _ _
  have hCC₀ : C₀ ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro d X M hM hΔ H
  let p : H.1 := ⟨Classical.choose H.2.1, Classical.choose_spec H.2.1⟩
  haveI : Nonempty H.1 := ⟨p⟩
  have hdim : Module.finrank ℝ H.1.direction = 2 := H.2.2
  let indexEquiv : Fin (Module.finrank ℝ H.1.direction) ≃ Fin 2 :=
    Equiv.cast (congrArg Fin hdim)
  let ob : OrthonormalBasis (Fin 2) ℝ H.1.direction :=
    (stdOrthonormalBasis ℝ H.1.direction).reindex indexEquiv
  let li : H.1.direction ≃ₗᵢ[ℝ] E 2 := ob.repr
  let e : H.1 ≃ᵃⁱ[ℝ] E 2 :=
    (AffineIsometryEquiv.constVSub ℝ p).trans li.toAffineIsometryEquiv
  let Y := pointsOn X H
  let φ : E d → E 2 := fun x =>
    if hx : x ∈ H.1 then e ⟨x, hx⟩ else 0
  have hYmem {x : E d} (hx : x ∈ Y) : x ∈ H.1 := by
    simp only [Y, pointsOn, Finset.mem_filter] at hx
    exact hx.2
  have hφ {x : E d} (hx : x ∈ Y) : φ x = e ⟨x, hYmem hx⟩ := by
    simp [φ, hYmem hx]
  have hφInj : Set.InjOn φ (Y : Set (E d)) := by
    intro x hx y hy hxy
    have hEq : (⟨x, hYmem hx⟩ : H.1) = ⟨y, hYmem hy⟩ :=
      e.injective (by simpa [hφ hx, hφ hy] using hxy)
    exact congrArg Subtype.val hEq
  let F := Y.image φ
  have hFcard : F.card = Y.card := Finset.card_image_of_injOn hφInj
  have hdistSubset : positiveDistances F ⊆ positiveDistances X := by
    intro r hr
    change r ∈ F.offDiag.image (fun z => dist z.1 z.2) at hr
    rcases Finset.mem_image.mp hr with ⟨z, hz, rfl⟩
    rcases z with ⟨u, v⟩
    rcases Finset.mem_offDiag.mp hz with ⟨huF, hvF, huv⟩
    rcases Finset.mem_image.mp huF with ⟨x, hxY, hxu⟩
    rcases Finset.mem_image.mp hvF with ⟨y, hyY, hyv⟩
    have hxy : x ≠ y := by
      intro h
      apply huv
      rw [← hxu, ← hyv, h]
    have hdist : dist (φ x) (φ y) = dist x y := by
      rw [hφ hxY, hφ hyY]
      simpa only [Subtype.dist_eq] using
        e.isometry.dist_eq (⟨x, hYmem hxY⟩ : H.1) ⟨y, hYmem hyY⟩
    have hxX : x ∈ X := by
      simp only [Y, pointsOn, Finset.mem_filter] at hxY
      exact hxY.1
    have hyX : y ∈ X := by
      simp only [Y, pointsOn, Finset.mem_filter] at hyY
      exact hyY.1
    change dist u v ∈ X.offDiag.image (fun z => dist z.1 z.2)
    exact Finset.mem_image.mpr
      ⟨(x, y), Finset.mem_offDiag.mpr ⟨hxX, hyX, hxy⟩, by
        calc
          dist x y = dist (φ x) (φ y) := hdist.symm
          _ = dist u v := by rw [hxu, hyv]⟩
  by_cases hYtwo : 2 ≤ Y.card
  · have hFtwo : 2 ≤ F.card := by rw [hFcard]; exact hYtwo
    have hweakF := hweak F hFtwo
    have hΔF : ((positiveDistances F).card : ℝ) ≤ M := by
      exact (Nat.cast_le.mpr (Finset.card_le_card hdistSubset)).trans hΔ
    have hweakY : c * (Y.card : ℝ) ^ ((3 : ℝ) / 4) ≤ M := by
      simpa only [hFcard] using hweakF.trans hΔF
    have hratio : (Y.card : ℝ) ^ ((3 : ℝ) / 4) ≤ M / c := by
      apply (le_div_iff₀ hc).2
      nlinarith [hweakY]
    have hraised := Real.rpow_le_rpow (by positivity) hratio
      (by norm_num : 0 ≤ (4 : ℝ) / 3)
    have hleft :
        ((Y.card : ℝ) ^ ((3 : ℝ) / 4)) ^ ((4 : ℝ) / 3) = (Y.card : ℝ) := by
      rw [← Real.rpow_mul (Nat.cast_nonneg Y.card)]
      norm_num
    have hInvPow : (1 / c) ^ q = 1 / c ^ q := by
      rw [Real.div_rpow (by norm_num) hc.le]
      norm_num
    have hright : (M / c) ^ ((4 : ℝ) / 3) = C₀ * M ^ ((4 : ℝ) / 3) := by
      calc
        (M / c) ^ ((4 : ℝ) / 3) = M ^ ((4 : ℝ) / 3) / c ^ ((4 : ℝ) / 3) :=
          Real.div_rpow (by positivity) hc.le _
        _ = (1 / c ^ ((4 : ℝ) / 3)) * M ^ ((4 : ℝ) / 3) := by ring
        _ = (1 / c) ^ ((4 : ℝ) / 3) * M ^ ((4 : ℝ) / 3) := by
          rw [← hInvPow]
        _ = C₀ * M ^ ((4 : ℝ) / 3) := rfl
    calc
      (Y.card : ℝ) =
          ((Y.card : ℝ) ^ ((3 : ℝ) / 4)) ^ ((4 : ℝ) / 3) := hleft.symm
      _ ≤ (M / c) ^ ((4 : ℝ) / 3) := hraised
      _ = C₀ * M ^ ((4 : ℝ) / 3) := hright
      _ ≤ C * M ^ ((4 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right hCC₀ (Real.rpow_nonneg (by linarith) _)
  · have hYsmall : Y.card ≤ 1 := by omega
    have hYsmallReal : (Y.card : ℝ) ≤ 1 := by exact_mod_cast hYsmall
    have hMpow : 1 ≤ M ^ ((4 : ℝ) / 3) :=
      Real.one_le_rpow hM (by norm_num)
    have hprod : 1 ≤ C * M ^ ((4 : ℝ) / 3) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hCone) (sub_nonneg.mpr hMpow)]
    exact hYsmallReal.trans hprod

/-- Uniform power-saving consequence for contradiction sequences. -/
theorem planar_occupancy_sequence (d : ℕ) (X : ℕ → Finset (E d)) (M B : ℕ → ℝ)
    (hM : ∀ n, 1 ≤ M n ∧ ((positiveDistances (X n)).card : ℝ) ≤ M n)
    (hB : Filter.Tendsto B Filter.atTop Filter.atTop)
    (hsmall : Filter.Tendsto (fun n => M n / (B n) ^ 2) Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop,
      ∀ H : Plane d, ((pointsOn (X n) H).card : ℝ) ≤ (B n) ^ ((8 : ℝ) / 3) := by
  obtain ⟨C, hC, hocc⟩ := ci_planar_occupancy
  let q : ℝ := (4 : ℝ) / 3
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpow : Filter.Tendsto (fun n => (M n / (B n) ^ 2) ^ q)
      Filter.atTop (nhds 0) := by
    have hcont := (Real.continuous_rpow_const hq).tendsto 0
    simpa [q, Function.comp_def] using hcont.comp hsmall
  have hscaled : Filter.Tendsto (fun n => C * (M n / (B n) ^ 2) ^ q)
      Filter.atTop (nhds 0) := by
    simpa using hpow.const_mul C
  have hsmall' : ∀ᶠ n in Filter.atTop,
      C * (M n / (B n) ^ 2) ^ q < 1 :=
    hscaled.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hB.eventually_gt_atTop 0, hsmall'] with n hBn hratio
  intro H
  have hOcc := hocc d (X n) (M n) (hM n).1 (hM n).2 H
  let m : ℝ := M n
  let b : ℝ := B n
  have hm : 0 < m := by dsimp [m]; linarith [(hM n).1]
  have hb : 0 < b := by exact hBn
  have hden : 0 < (b ^ 2 : ℝ) ^ q := by positivity
  have hdiv : (m / b ^ 2) ^ q = m ^ q / (b ^ 2 : ℝ) ^ q :=
    Real.div_rpow hm.le (sq_nonneg b) q
  have hprod : (m / b ^ 2) ^ q * (b ^ 2 : ℝ) ^ q = m ^ q := by
    rw [hdiv]
    exact div_mul_cancel₀ _ hden.ne'
  have hsq : (b ^ 2 : ℝ) ^ q = b ^ ((8 : ℝ) / 3) := by
    rw [← Real.rpow_natCast b 2, ← Real.rpow_mul hb.le]
    norm_num [q]
  have hbound : C * m ^ q ≤ b ^ ((8 : ℝ) / 3) := by
    rw [← hprod, hsq]
    calc
      C * ((m / b ^ 2) ^ q * b ^ ((8 : ℝ) / 3)) =
          (C * (m / b ^ 2) ^ q) * b ^ ((8 : ℝ) / 3) := by ring
      _ ≤ 1 * b ^ ((8 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right hratio.le (by positivity)
      _ = b ^ ((8 : ℝ) / 3) := one_mul _
  simpa [m, b, q] using hOcc.trans hbound

end DistinctDistances.TrackC
