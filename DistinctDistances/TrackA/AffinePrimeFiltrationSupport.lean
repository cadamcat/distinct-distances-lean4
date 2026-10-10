import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFiltration
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- Lift OAI's cyclic prime filtration of R/I back to ideals of R. -/
theorem affine_cyclic_prime_filtration (R : Type*) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) :
    ∃ (N : ℕ) (J : ℕ → Ideal R) (f : ℕ → R),
      (∀ i, J i ≤ J (i+1)) ∧ J 0 = I ∧ J N = ⊤ ∧
      ∀ i < N, ((J i).colon {f i}).IsPrime ∧ J (i+1) = J i ⊔ Ideal.span {f i} := by
  obtain ⟨N, Q, a, hmono, hzero, htop, hstep⟩ :=
    OAI.PiExponentJets.W28.LocalIntersection.exists_cyclic_prime_filtration_nat (A := R ⧸ I)
  let q := Ideal.Quotient.mk I
  let J : ℕ → Ideal R := fun i => (Q i).comap q
  choose f hf using fun i => Ideal.Quotient.mk_surjective (a i)
  refine ⟨N, J, f, fun i => Ideal.comap_mono (hmono i), ?_, ?_, ?_⟩
  · simp only [J, hzero, ← RingHom.ker_eq_comap_bot, q, Ideal.mk_ker]
  · simp only [J, htop, Ideal.comap_top]
  · intro i hi
    have hcolon : (J i).colon {f i} = ((Q i).colon {a i}).comap q := by
      ext x
      simp only [Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_comap]
      change q (x*f i) ∈ Q i ↔ q x*a i ∈ Q i
      rw [map_mul, hf]
    have hprime : ((J i).colon {f i}).IsPrime := by
      rw [hcolon]
      letI := (hstep i hi).1
      exact Ideal.IsPrime.comap q
    refine ⟨hprime, ?_⟩
    have hmap : (J i ⊔ Ideal.span {f i}).map q = Q (i+1) := by
      rw [Ideal.map_sup, Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective,
        Ideal.map_span, Set.image_singleton, hf, (hstep i hi).2]
    have hker : RingHom.ker q ≤ J i ⊔ Ideal.span {f i} := by
      apply le_trans _ le_sup_left
      intro x hx
      change q x ∈ Q i
      rw [RingHom.mem_ker.mp hx]
      exact (Q i).zero_mem
    have hback := Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective
      (J i ⊔ Ideal.span {f i})
    rw [← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker] at hback
    exact (congrArg (Ideal.comap q) hmap).symm.trans hback

end
end DistinctDistances.TrackA
