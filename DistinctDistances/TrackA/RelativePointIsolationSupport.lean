import DistinctDistances.TrackA.Definitions
import DistinctDistances.Foundations.GenericFiber
import DistinctDistances.TrackA.ADepthAux

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators

/-- Minimality of the same original prime persists upon enlarging the
original ideal while remaining below that prime. -/
theorem minimal_prime_of_enlarged_ideal {n : ℕ} (I J P : Ideal (Poly n))
    (hIJ : I ≤ J) (hJP : J ≤ P) (hP : P ∈ I.minimalPrimes) :
    P ∈ J.minimalPrimes := by
  refine ⟨⟨hP.isPrime, hJP⟩, ?_⟩
  intro Q hQ hQP
  exact hP.2 ⟨hQ.1, hIJ.trans hQ.2⟩ hQP

theorem relative_isolated_point_mem {n : ℕ} (V : AffineVariety n)
    (E : Set (Poly n)) (x : Point n)
    (hx : pointIdeal x ∈ (V.ideal ⊔ Ideal.span E).minimalPrimes) :
    x ∈ V.points := by
  intro f hf
  exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x f).mp
    (hx.le (Ideal.mem_sup_left hf))

theorem relative_isolated_point_transfer {n : ℕ} (V W : AffineVariety n)
    (E : Set (Poly n)) (x : Point n) (hVW : V.ideal ≤ W.ideal)
    (hxW : x ∈ W.points)
    (hx : pointIdeal x ∈ (V.ideal ⊔ Ideal.span E).minimalPrimes) :
    pointIdeal x ∈ (W.ideal ⊔ Ideal.span E).minimalPrimes := by
  apply minimal_prime_of_enlarged_ideal _ _ _ (sup_le_sup_right hVW _)
  · refine sup_le ?_ (le_sup_right.trans hx.le)
    intro f hf
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x f).mpr (hxW f hf)
  · exact hx

/-- The original shared Hilbert dimension of an original point ideal is zero. -/
theorem pointIdeal_affineDimension_zero {n : ℕ} (x : Point n) :
    OAI.QuarticPowerFree.affineDimension (pointIdeal x) = 0 := by
  let ev : Poly n →ₐ[ℂ] ℂ := MvPolynomial.aeval x
  have hker : pointIdeal x = RingHom.ker ev.toRingHom := by
    ext f
    rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff, RingHom.mem_ker]
    rfl
  have hev : Function.Surjective ev := by
    intro c
    exact ⟨MvPolynomial.C c, by simp [ev]⟩
  let e : (Poly n ⧸ pointIdeal x) ≃ₐ[ℂ] ℂ :=
    (Ideal.quotientEquivAlgOfEq ℂ hker).trans (Ideal.quotientKerAlgEquivOfSurjective hev)
  have h := GenericFiber.affineDimension_eq_trdeg (pointIdeal x)
  rw [e.trdeg_eq, trdeg_eq_zero] at h
  exact_mod_cast h

/-- A positive-dimensional original irreducible carrier with an isolated
sample point admits one of the original equations as a proper cut. -/
theorem relative_isolated_proper_equation {n k : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hdim : V.dimension = k+1)
    (E : Set (Poly n)) (x : Point n)
    (hx : pointIdeal x ∈ (V.ideal ⊔ Ideal.span E).minimalPrimes) :
    ∃ f ∈ E, f ∉ V.ideal := by
  letI : V.ideal.IsPrime := hV
  by_contra h
  push_neg at h
  have hspan : Ideal.span E ≤ V.ideal := Ideal.span_le.mpr h
  rw [sup_eq_left.mpr hspan, Ideal.minimalPrimes_eq_subsingleton_self] at hx
  have he : pointIdeal x = V.ideal := Set.mem_singleton_iff.mp hx
  have hz := pointIdeal_affineDimension_zero x
  rw [he] at hz
  change V.dimension = 0 at hz
  omega

end
end DistinctDistances.TrackA
