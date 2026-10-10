import DistinctDistances.TrackA.NarrowCylinderIsolationSupport
import DistinctDistances.Foundations.GenericFiber

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- The original cylinder coordinate map: retain the scalar variable and
reduce every original source coefficient modulo the source ideal. -/
def lineCylinderQuotientMap {n : ℕ} (V : AffineVariety n) :
    Poly (n+1) →ₐ[ℂ] Polynomial (Poly n ⧸ V.ideal) :=
  (Polynomial.mapAlgHom (Ideal.Quotient.mkₐ ℂ V.ideal)).comp
    (MvPolynomial.finSuccEquiv ℂ n).toAlgHom

theorem lineCylinderQuotientMap_coeff {n : ℕ} (V : AffineVariety n)
    (f : Poly (n+1)) (i : ℕ) :
    (lineCylinderQuotientMap V f).coeff i =
      Ideal.Quotient.mk V.ideal ((MvPolynomial.finSuccEquiv ℂ n f).coeff i) := by
  simp [lineCylinderQuotientMap, Polynomial.coeff_mapAlgHom_apply]

theorem lineCylinderQuotientMap_surjective {n : ℕ} (V : AffineVariety n) :
    Function.Surjective (lineCylinderQuotientMap V) := by
  exact (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective).comp
    (MvPolynomial.finSuccEquiv ℂ n).surjective

/-- The actual cylinder ideal consists exactly of polynomials whose scalar
coefficients vanish on the original carrier. -/
theorem lineCylinder_mem_ideal_iff {n : ℕ} (V : AffineVariety n)
    (f : Poly (n+1)) :
    f ∈ (lineCylinder V).ideal ↔
      ∀ i, (MvPolynomial.finSuccEquiv ℂ n f).coeff i ∈ V.ideal := by
  constructor
  · intro hf i
    rw [← V.vanishingIdeal_points]
    intro x hx
    have hz : Polynomial.map (MvPolynomial.eval x)
        (MvPolynomial.finSuccEquiv ℂ n f) = 0 := by
      apply Polynomial.funext
      intro t
      rw [Polynomial.eval_zero, ← MvPolynomial.eval_eq_eval_mv_eval']
      exact hf (Fin.cons t x) (by simpa using hx)
    have hi := congrArg (fun g : Polynomial ℂ => g.coeff i) hz
    simpa using hi
  · intro hf q hq
    have hz : Polynomial.map (MvPolynomial.eval (Fin.tail q))
        (MvPolynomial.finSuccEquiv ℂ n f) = 0 := by
      ext i
      simpa using hq _ (hf i)
    change MvPolynomial.eval q f = 0
    rw [← Fin.cons_self_tail q, MvPolynomial.eval_eq_eval_mv_eval', hz,
      Polynomial.eval_zero]

theorem lineCylinder_ideal_eq_ker {n : ℕ} (V : AffineVariety n) :
    (lineCylinder V).ideal = RingHom.ker (lineCylinderQuotientMap V) := by
  ext f
  rw [lineCylinder_mem_ideal_iff, RingHom.mem_ker]
  constructor
  · intro hf
    ext i
    rw [lineCylinderQuotientMap_coeff, Polynomial.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hf i)
  · intro hf i
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← lineCylinderQuotientMap_coeff, hf, Polynomial.coeff_zero]

/-- Original coordinate quotient of the literal carrier-times-line cylinder. -/
def lineCylinderQuotientEquiv {n : ℕ} (V : AffineVariety n) :
    (Poly (n+1) ⧸ (lineCylinder V).ideal) ≃ₐ[ℂ]
      Polynomial (Poly n ⧸ V.ideal) :=
  (Ideal.quotientEquivAlgOfEq ℂ (lineCylinder_ideal_eq_ker V)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (lineCylinderQuotientMap_surjective V))

theorem lineCylinderQuotientEquiv_mk {n : ℕ} (V : AffineVariety n)
    (f : Poly (n+1)) :
    lineCylinderQuotientEquiv V (Ideal.Quotient.mk (lineCylinder V).ideal f) =
      lineCylinderQuotientMap V f := by
  simp [lineCylinderQuotientEquiv]

theorem lineCylinder_irreducible {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) : (lineCylinder V).IsIrreducible := by
  letI : V.ideal.IsPrime := hV
  change (lineCylinder V).ideal.IsPrime
  rw [lineCylinder_ideal_eq_ker]
  exact RingHom.ker_isPrime _

theorem lineCylinder_dimension {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) : (lineCylinder V).dimension = V.dimension + 1 := by
  letI : V.ideal.IsPrime := hV
  letI : (lineCylinder V).ideal.IsPrime := lineCylinder_irreducible V hV
  have h := GenericFiber.affineDimension_eq_trdeg (lineCylinder V).ideal
  have he : Algebra.trdeg ℂ (Poly (n+1) ⧸ (lineCylinder V).ideal) =
      Algebra.trdeg ℂ (Polynomial (Poly n ⧸ V.ideal)) := by
    with_unfolding_all exact (lineCylinderQuotientEquiv V).trdeg_eq
  rw [he, GenericFiber.trdeg_polynomial_quotient] at h
  exact_mod_cast h

theorem lineCylinder_pure {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) : (lineCylinder V).IsPure (V.dimension+1) := by
  letI : (lineCylinder V).ideal.IsPrime := lineCylinder_irreducible V hV
  intro c
  have hc : c.val = (lineCylinder V).ideal := by
    simpa only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff]
      using c.property
  have hv : c.variety = lineCylinder V := AffineVariety.ext hc
  rw [hv]
  exact lineCylinder_dimension V hV

end
end DistinctDistances.TrackA
