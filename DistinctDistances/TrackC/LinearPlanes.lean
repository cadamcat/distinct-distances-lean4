import DistinctDistances.TrackC.LineAlgebra

open scoped BigOperators
open MvPolynomial
open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- The degree-one coordinate normal form consumed by plane-component counting. -/
theorem trivariate_linear_form (p : Poly 3) (hp : p.totalDegree ≤ 1) :
    p = C (p.coeff 0)+C (p.coeff (Finsupp.single 0 1))*X 0+
      C (p.coeff (Finsupp.single 1 1))*X 1+C (p.coeff (Finsupp.single 2 1))*X 2 := by
  apply MvPolynomial.ext
  intro m
  by_cases hm : m = 0 ∨ m = Finsupp.single 0 1 ∨ m = Finsupp.single 1 1 ∨ m = Finsupp.single 2 1
  · rcases hm with rfl | rfl | rfl | rfl
    all_goals simp [MvPolynomial.coeff_X,Finsupp.single_eq_single_iff,eq_comm]
  · have hc : p.coeff m = 0 := by
      by_contra hc
      have hdegree := (MvPolynomial.le_totalDegree (mem_support_iff.mpr hc)).trans hp
      have hsum : m.sum (fun _ n => n) = m 0+m 1+m 2 := by
        rw [Finsupp.sum_fintype] <;> simp [Fin.sum_univ_three]
      rw [hsum] at hdegree
      apply hm
      by_cases h0 : m 0 = 0
      · by_cases h1 : m 1 = 0
        · by_cases h2 : m 2 = 0
          · left
            ext i
            fin_cases i <;> simp [h0,h1,h2]
          · right;right;right
            have h2' : m 2 = 1 := by omega
            ext i
            fin_cases i <;> simp [h0,h1,h2']
        · right;right;left
          have h1' : m 1 = 1 := by omega
          have h2 : m 2 = 0 := by omega
          ext i
          fin_cases i <;> simp [h0,h1',h2]
      · right;left
        have h0' : m 0 = 1 := by omega
        have h1 : m 1 = 0 := by omega
        have h2 : m 2 = 0 := by omega
        ext i
        fin_cases i <;> simp [h0',h1,h2]
    simp only [not_or] at hm
    simp [MvPolynomial.coeff_X,hc,hm.1,hm.2.1,hm.2.2.1,hm.2.2.2,eq_comm]

def linearPolynomialNormal (p : Poly 3) : E 3 →ₗ[ℝ] ℝ where
  toFun y := ∑ i : Fin 3,p.coeff (Finsupp.single i 1)*y i
  map_add' y z := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' a y := by simp [Finset.mul_sum];apply Finset.sum_congr rfl;intro i hi;ring

theorem linearPolynomial_eval (p : Poly 3) (hp : p.totalDegree ≤ 1) (y : E 3) :
    evalR p y = p.coeff 0+linearPolynomialNormal p y := by
  conv_lhs => rw [trivariate_linear_form p hp]
  simp [evalR,linearPolynomialNormal,Fin.sum_univ_three]
  ring

theorem linearPolynomialNormal_surjective (p : Poly 3) (hp : p.totalDegree = 1) :
    Function.Surjective (linearPolynomialNormal p) := by
  have hcoeff : ∃ i : Fin 3,p.coeff (Finsupp.single i 1) ≠ 0 := by
    by_contra! h
    have heq := trivariate_linear_form p hp.le
    simp [h] at heq
    rw [heq,MvPolynomial.totalDegree_C] at hp
    omega
  obtain ⟨i,hi⟩ := hcoeff
  intro a
  refine ⟨EuclideanSpace.single i (a/p.coeff (Finsupp.single i 1)),?_⟩
  simp [linearPolynomialNormal]
  field_simp [hi]

/-- A degree-one real equation has an affine plane as its zero set. -/
theorem linear_polynomial_plane (p : Poly 3) (hp : p.totalDegree = 1) :
    ∃ H : Plane 3,zeroSet p = (H.1:Set (E 3)) := by
  let N := linearPolynomialNormal p
  have hN : Function.Surjective N := linearPolynomialNormal_surjective p hp
  obtain ⟨x,hx⟩ := hN (-p.coeff 0)
  have hrange : LinearMap.range N = ⊤ := LinearMap.range_eq_top.mpr hN
  have hdim : Module.finrank ℝ (LinearMap.ker N) = 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker N
    have hDom : Module.finrank ℝ (E 3) = 3 := by simp [E]
    rw [hrange,finrank_top,hDom] at h
    norm_num at h
    omega
  let H : Plane 3 := ⟨AffineSubspace.mk' x (LinearMap.ker N),
    ⟨⟨x,by simp⟩,by
      rw [AffineSubspace.direction_mk']
      exact hdim⟩⟩
  refine ⟨H,?_⟩
  ext y
  change evalR p y = 0 ↔ N (y-x) = 0
  rw [map_sub,linearPolynomial_eval p hp.le y]
  change p.coeff 0+N y = 0 ↔ N y-N x = 0
  rw [hx]
  constructor <;> intro h <;> linarith

/-- Count the listed lines supported by degree-one factors using the given plane cap. -/
theorem plane_component_line_budget (f : Poly 3) (hf : f ≠ 0) (hsq : Squarefree f)
    (L : Finset (Line 3)) (B : ℝ) (hB : 0 ≤ B) (hcap : planeCap L B) :
    ((L.filter (fun l => inPlaneComponent f l)).card:ℝ) ≤ (f.totalDegree:ℝ)*B := by
  letI : StrongNormalizationMonoid (Poly 3) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let F := (UniqueFactorizationMonoid.normalizedFactors f).toFinset.filter (fun p => p.totalDegree = 1)
  let A : Poly 3 → Finset (Line 3) := fun p => L.filter (fun l => onPolynomial p l)
  have hFcard : F.card ≤ f.totalDegree := by
    calc
      F.card = ∑ p ∈ F,p.totalDegree := by
        symm
        simpa using Finset.sum_const_nat (s := F) (m := 1) (f := MvPolynomial.totalDegree)
          (fun p hp => (Finset.mem_filter.mp hp).2)
      _ ≤ ∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors f).toFinset,p.totalDegree :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = _ := squarefree_factor_degree_sum f hf hsq
  have hA : ∀ p ∈ F,(A p).card ≤ B := by
    intro p hp
    obtain ⟨H,hH⟩ := linear_polynomial_plane p (Finset.mem_filter.mp hp).2
    have hs : A p ⊆ L.filter (fun l => l.1 ≤ H.1) := by
      intro l hl
      obtain ⟨hlL,hlp⟩ := Finset.mem_filter.mp hl
      refine Finset.mem_filter.mpr ⟨hlL,?_⟩
      intro x hx
      change x ∈ (H.1:Set (E 3))
      rw [← hH]
      exact hlp x hx
    exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans (hcap H)
  have hsub : L.filter (fun l => inPlaneComponent f l) ⊆ F.biUnion A := by
    intro l hl
    obtain ⟨hlL,p,hp,hpf,hlp⟩ := Finset.mem_filter.mp hl
    obtain ⟨q,hq,hass⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hf
      (real_linear_polynomial_irreducible p hp) hpf
    have hqF : q ∈ F := Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr hq,(real_totalDegree_associated p q hass).symm.trans hp⟩
    have hlq : onPolynomial q l := by
      obtain ⟨r,rfl⟩ := hass.dvd
      intro x hx
      change MvPolynomial.eval x (p*r) = 0
      have hz : MvPolynomial.eval x p = 0 := hlp x hx
      rw [map_mul,hz,zero_mul]
    exact Finset.mem_biUnion.mpr ⟨q,hqF,Finset.mem_filter.mpr ⟨hlL,hlq⟩⟩
  calc
    _ ≤ ((F.biUnion A).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ p ∈ F,((A p).card:ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ F,B := Finset.sum_le_sum (fun p hp => hA p hp)
    _ = (F.card:ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hFcard) hB

end DistinctDistances.TrackC
