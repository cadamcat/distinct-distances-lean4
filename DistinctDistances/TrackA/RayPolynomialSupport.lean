import DistinctDistances.TrackA.Definitions
import DistinctDistances.TrackA.SeparatorTranslationSupport
import DistinctDistances.TrackA.ProjectiveChartSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

def rayPolynomial {n : ℕ} (p v : Point n) (f : Poly n) : Polynomial ℂ :=
  let T := OAI.PiExponent.WeightedBezout.translationEquiv p f
  ∑ j ∈ Finset.range (T.totalDegree+1),
    Polynomial.monomial j (MvPolynomial.eval v (MvPolynomial.homogeneousComponent j T))

theorem rayPolynomial_eval {n : ℕ} (p v : Point n) (f : Poly n) (t : ℂ) :
    (rayPolynomial p v f).eval t = MvPolynomial.eval (p + t • v) f := by
  rw [← separator_translation_eval p (t • v) f]
  unfold rayPolynomial
  conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent (OAI.PiExponent.WeightedBezout.translationEquiv p f)]
  simp only [map_sum, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Bridges.homogeneous_eval_smul _ (MvPolynomial.homogeneousComponent_isHomogeneous j _)]
  ring

theorem rayPolynomial_coeff {n : ℕ} (p v : Point n) (f : Poly n) (j : ℕ)
    (hj : j ≤ (OAI.PiExponent.WeightedBezout.translationEquiv p f).totalDegree) :
    (rayPolynomial p v f).coeff j = MvPolynomial.eval v
      (MvPolynomial.homogeneousComponent j (OAI.PiExponent.WeightedBezout.translationEquiv p f)) := by
  simp [rayPolynomial, Polynomial.coeff_monomial, Nat.lt_succ_iff, hj]

theorem rayPolynomial_degree_translated {n : ℕ} (p v : Point n) (f : Poly n) :
    (rayPolynomial p v f).natDegree ≤
      (OAI.PiExponent.WeightedBezout.translationEquiv p f).totalDegree := by
  unfold rayPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  apply le_trans (Polynomial.natDegree_monomial_le _)
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)

/-- Only the original OAI translation degree interface is used in this bound. -/
theorem rayPolynomial_degree {n : ℕ} (p v : Point n) (f : Poly n) :
    (rayPolynomial p v f).natDegree ≤ f.totalDegree :=
  (rayPolynomial_degree_translated p v f).trans (separator_translation_degree p f)

theorem ray_nonzero_principal_open {n : ℕ} (p : Point n) (Y : AffineVariety n)
    (f : Poly n) (hzero : f ∈ Y.ideal)
    (hproper : ∃ y ∈ Y.points, ∃ t : ℂ, MvPolynomial.eval (p + t • (y-p)) f ≠ 0) :
    ∃ (H : Poly n) (e : ℕ), H.IsHomogeneous e ∧ H ∉ (radialImage p Y).ideal ∧
      ∀ z : ProjectivePoint n, MvPolynomial.eval z.rep H ≠ 0 →
        rayPolynomial p z.rep f ≠ 0 := by
  obtain ⟨y, hy, t, hnonzero⟩ := hproper
  have hyne : y ≠ p := by
    intro h
    subst y
    apply hnonzero
    simpa [MvPolynomial.aeval_eq_eval] using hy f hzero
  have hQne : rayPolynomial p (y-p) f ≠ 0 := by
    intro h
    apply hnonzero
    rw [← rayPolynomial_eval, h]
    simp
  obtain ⟨j, hj⟩ : ∃ j, (rayPolynomial p (y-p) f).coeff j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hQne (Polynomial.ext (fun j => by simpa using hn j))
  have hjdeg : j ≤ (OAI.PiExponent.WeightedBezout.translationEquiv p f).totalDegree :=
    (Polynomial.le_natDegree_of_ne_zero hj).trans (rayPolynomial_degree_translated p (y-p) f)
  let H := MvPolynomial.homogeneousComponent j (OAI.PiExponent.WeightedBezout.translationEquiv p f)
  have hyH : MvPolynomial.eval (y-p) H ≠ 0 := by
    simpa only [rayPolynomial_coeff p (y-p) f j hjdeg] using hj
  refine ⟨H, j, MvPolynomial.homogeneousComponent_isHomogeneous _ _, ?_, ?_⟩
  · intro hH
    change H ∈ MvPolynomial.vanishingIdeal ℂ (ProjectiveVariety.nonzeroRepresentatives
      {z | ∃ x ∈ Y.points, ∃ hx : x ≠ p, radialProjection p x hx = z}) at hH
    have hyrep : y-p ∈ ProjectiveVariety.nonzeroRepresentatives
        {z | ∃ x ∈ Y.points, ∃ hx : x ≠ p, radialProjection p x hx = z} :=
      ⟨sub_ne_zero.mpr hyne, y, hy, hyne, rfl⟩
    apply hyH
    simpa only [MvPolynomial.aeval_eq_eval] using hH (y-p) hyrep
  · intro z hz hQ
    have hcoeff := rayPolynomial_coeff p z.rep f j hjdeg
    rw [hQ, Polynomial.coeff_zero] at hcoeff
    exact hz hcoeff.symm

end
end DistinctDistances.TrackA
