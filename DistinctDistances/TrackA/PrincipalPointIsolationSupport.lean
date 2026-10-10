import DistinctDistances.TrackA.Definitions
import DistinctDistances.OAIInterface.PointParameters

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators

/-- The shared point ideal has the original OAI coordinate generators. -/
theorem pointIdeal_span_coordinates {n : ℕ} (x : Point n) :
    pointIdeal x = Ideal.span (Set.range (fun i : Fin n => MvPolynomial.X i - MvPolynomial.C (x i))) := by
  have he : pointIdeal x = OAI.PiExponent.WeightedBezout.pointIdeal x := by
    ext f
    rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    rfl
  rw [he, OAI.PiExponent.WeightedBezout.pointIdeal_eq_span]

/-- A finite principal-open zero locus makes each of its points a minimal
point component of the ORIGINAL ideal, without radical replacement. -/
theorem point_minimal_of_principal_finite_locus {n : ℕ} (I : Ideal (Poly n))
    (x : Point n) (hx : x ∈ MvPolynomial.zeroLocus ℂ I) (g : Poly n)
    (hgx : MvPolynomial.eval x g ≠ 0)
    (hfinite : {y : Point n | y ∈ MvPolynomial.zeroLocus ℂ I ∧ MvPolynomial.eval y g ≠ 0}.Finite) :
    pointIdeal x ∈ I.minimalPrimes := by
  have hxI : I ≤ pointIdeal x := by
    intro f hf
    rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact hx f hf
  refine ⟨⟨(pointIdeal_isMaximal x).isPrime, hxI⟩, ?_⟩
  intro Q hQ hQx
  letI : Q.IsPrime := hQ.1
  have hgQ : g ∉ Q := by
    intro h
    exact hgx (hQx h x (by simp))
  let T := hfinite.toFinset
  have hcoordinates (i : Fin n) : MvPolynomial.X i - MvPolynomial.C (x i) ∈ Q := by
    let F : Poly n := ∏ y ∈ T, (MvPolynomial.X i - MvPolynomial.C (y i))
    have hFg : F*g ∈ Q := by
      rw [← hQ.1.isRadical.radical, ← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ) Q]
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro y hy
      change MvPolynomial.eval y (F*g) = 0
      rw [map_mul]
      by_cases hgy : MvPolynomial.eval y g = 0
      · rw [hgy, mul_zero]
      · have hyI : y ∈ MvPolynomial.zeroLocus ℂ I := fun f hf => hy f (hQ.2 hf)
        have hyT : y ∈ T := hfinite.mem_toFinset.mpr ⟨hyI, hgy⟩
        have hFy : MvPolynomial.eval y F = 0 := by
          simp only [F, map_prod]
          apply Finset.prod_eq_zero hyT
          simp
        rw [hFy, zero_mul]
    have hF : F ∈ Q := (hQ.1.mem_or_mem hFg).resolve_right hgQ
    obtain ⟨y, hyT, hyQ⟩ := Ideal.IsPrime.prod_mem_iff.mp hF
    have hycoord : x i = y i := by
      have hz := hQx hyQ x (by simp)
      exact sub_eq_zero.mp (by simpa using hz)
    simpa only [← hycoord] using hyQ
  rw [pointIdeal_span_coordinates]
  exact Ideal.span_le.mpr (by rintro f ⟨i,rfl⟩; exact hcoordinates i)

/-- A minimal point component of the original ideal can be isolated by
one polynomial principal open despite other components elsewhere. -/
theorem minimal_point_principal_open {n : ℕ} (I : Ideal (Poly n)) (x : Point n)
    (hx : pointIdeal x ∈ I.minimalPrimes) :
    ∃ g : Poly n, MvPolynomial.eval x g ≠ 0 ∧
      ∀ y ∈ MvPolynomial.zeroLocus ℂ I, MvPolynomial.eval y g ≠ 0 → y = x := by
  let T := (I.finite_minimalPrimes_of_isNoetherianRing (Poly n)).toFinset.erase (pointIdeal x)
  have hw (Q : T) : ∃ f : Poly n, f ∈ Q.val ∧ f ∉ pointIdeal x := by
    have hQ : Q.val ∈ I.minimalPrimes :=
      (I.finite_minimalPrimes_of_isNoetherianRing (Poly n)).mem_toFinset.mp
        (Finset.mem_erase.mp Q.property).2
    have hne : Q.val ≠ pointIdeal x := (Finset.mem_erase.mp Q.property).1
    have hnot : ¬ Q.val ≤ pointIdeal x := by
      intro hle
      exact hne (le_antisymm hle (hx.2 hQ.1 hle))
    change ¬ ∀ f, f ∈ Q.val → f ∈ pointIdeal x at hnot
    push Not at hnot
    exact hnot
  choose f hf hnot using hw
  let g := ∏ Q : T, f Q
  have hg : g ∉ pointIdeal x := by
    intro h
    obtain ⟨Q, _, hQ⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hnot Q hQ
  have hgx : MvPolynomial.eval x g ≠ 0 := by
    simpa only [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff, MvPolynomial.aeval_eq_eval] using hg
  refine ⟨g, hgx, ?_⟩
  intro y hy hgy
  have hyI : I ≤ pointIdeal y := by
    intro f hf
    rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact hy f hf
  obtain ⟨Q, hQ, hQy⟩ := Ideal.exists_minimalPrimes_le hyI
  have he : Q = pointIdeal x := by
    by_contra hne
    let q : T := ⟨Q, Finset.mem_erase.mpr ⟨hne,
      (I.finite_minimalPrimes_of_isNoetherianRing (Poly n)).mem_toFinset.mpr hQ⟩⟩
    have hz : MvPolynomial.eval y (f q) = 0 := hQy (hf q) y (by simp)
    have hprod : (∏ Q : T, MvPolynomial.eval y (f Q)) ≠ 0 := by
      simpa only [g, map_prod] using hgy
    exact ((Finset.prod_ne_zero_iff.mp hprod) q (Finset.mem_univ _)) hz
  rw [he] at hQy
  funext i
  have hi : MvPolynomial.X i - MvPolynomial.C (x i) ∈ pointIdeal x := by
    simp [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff]
  have hz := hQy hi y (by simp)
  exact sub_eq_zero.mp (by simpa using hz)

end
end DistinctDistances.TrackA
