import DistinctDistances.TrackA.InfinityNormalizationSupport
import DistinctDistances.TrackA.ProjectiveCutFamilySupport
import OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension

set_option backward.isDefEq.respectTransparency false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

/-- For a prime coordinate quotient, the shared Hilbert dimension is
its actual Krull dimension. Both comparisons are original OAI results. -/
theorem prime_coordinate_krull_dimension {n : ℕ} (I : Ideal (Poly n)) (hI : I.IsPrime) :
    ringKrullDim (Poly n ⧸ I) = (OAI.QuarticPowerFree.affineDimension I : WithBot ℕ∞) := by
  letI : I.IsPrime := hI
  rw [OAI.PiExponentJets.W24.finiteType_domain_krullDim_eq_trdeg ℂ (Poly n ⧸ I)]
  have ht := OAI.QuarticPowerFree.hilbert_natDegree_eq_trdeg I
    (OAI.QuarticPowerFree.coordinateHilbert I) (OAI.QuarticPowerFree.coordinateHilbert_eventually I)
  rw [← ht]
  simp only [Cardinal.toNat_natCast]
  rfl

/-- When every minimal prime quotient has dimension k, the original
possibly nonreduced coordinate quotient also has dimension k. Lift each
chain to a minimal-prime zero locus below its first member. -/
theorem coordinate_quotient_dimension_of_minimal_primes {n : ℕ}
    (I : Ideal (Poly n)) (hne : I ≠ ⊤) (k : ℕ)
    (hd : ∀ Q ∈ I.minimalPrimes, ringKrullDim (Poly n ⧸ Q) = (k : WithBot ℕ∞)) :
    ringKrullDim (Poly n ⧸ I) = (k : WithBot ℕ∞) := by
  apply le_antisymm
  · rw [ringKrullDim_quotient, Order.krullDim]
    apply iSup_le
    intro p
    let P := p.head.val.asIdeal
    letI : P.IsPrime := p.head.val.isPrime
    have hIP : I ≤ P := p.head.property
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hIP
    let q : LTSeries (PrimeSpectrum.zeroLocus (R := Poly n) Q) :=
      { length := p.length
        toFun := fun i => ⟨(p i).val, hQP.trans (p.head_le i)⟩
        step := fun i => p.step i }
    have hlength : (q.length : WithBot ℕ∞) ≤
        Order.krullDim (PrimeSpectrum.zeroLocus (R := Poly n) Q) := by
      rw [Order.krullDim]
      exact le_iSup (fun r : LTSeries (PrimeSpectrum.zeroLocus (R := Poly n) Q) =>
        (r.length : WithBot ℕ∞)) q
    rw [← ringKrullDim_quotient Q, hd Q hQ] at hlength
    exact hlength
  · obtain ⟨⟨Q, hQ⟩⟩ := Ideal.nonempty_minimalPrimes hne
    have hle := ringKrullDim_le_of_surjective (Ideal.Quotient.factor hQ.le)
      (Ideal.Quotient.factor_surjective hQ.le)
    rwa [hd Q hQ] at hle

/-- The origin survives any homogeneous linear cut of a nonempty
projective family, so the literal scheme cut quotient is nontrivial. -/
theorem projective_family_linear_cut_ne_top {n : ℕ} (F : ProjectiveFamily.Family n)
    (hne : F.Nonempty) (hF : ∀ V ∈ F, V.IsIrreducible)
    (t : Poly n) (ht : t.IsHomogeneous 1) :
    (ProjectiveFamily.locus F).ideal ⊔ Ideal.span {t} ≠ ⊤ := by
  obtain ⟨V, hV⟩ := hne
  obtain ⟨p, hp⟩ := ProjectiveFamily.irreducible_points_nonempty V (hF V hV)
  have hrep : p.rep ∈ V.affineCone.points :=
    (ProjectiveVariety.mem_points_mk_iff V p.rep p.rep_nonzero).mp
      (by simpa only [Projectivization.mk_rep] using hp)
  have hzero : (0 : Point n) ∈ V.affineCone.points := by
    simpa only [zero_smul] using cone_smul_mem V p.rep hrep 0
  have hI : (ProjectiveFamily.locus F).ideal ≤ RingHom.ker (MvPolynomial.aeval (0 : Point n)) := by
    intro f hf
    exact hzero f (projective_family_member_subvariety F V hV hf)
  have ht0 : MvPolynomial.aeval (0 : Point n) t = 0 := by
    have h := Bridges.homogeneous_eval_smul t ht (0 : ℂ) (0 : Point n)
    simpa only [zero_smul, pow_one, zero_mul, MvPolynomial.aeval_eq_eval] using h
  have htI : Ideal.span {t} ≤ RingHom.ker (MvPolynomial.aeval (0 : Point n)) :=
    Ideal.span_le.mpr (by rintro f rfl; exact ht0)
  intro heq
  have hone : (1 : Poly n) ∈ RingHom.ker (MvPolynomial.aeval (0 : Point n)) :=
    (sup_le hI htI) (by rw [heq]; trivial)
  exact one_ne_zero (by simpa only [RingHom.mem_ker, map_one] using hone)

/-- A proper linear cut of a pure k-fold family has actual cone-quotient
Krull dimension k, including the k=0 case and nonreduced cut structure. -/
theorem projective_family_linear_cut_krull_dimension {n : ℕ}
    (F : ProjectiveFamily.Family n) (k : ℕ) (hne : F.Nonempty)
    (hF : ProjectiveFamily.IsPure F k)
    (t : Poly n) (ht : t.IsHomogeneous 1) (havoid : ∀ V ∈ F, t ∉ V.ideal) :
    ringKrullDim (Poly n ⧸ ((ProjectiveFamily.locus F).ideal ⊔ Ideal.span {t})) =
      (k : WithBot ℕ∞) := by
  apply coordinate_quotient_dimension_of_minimal_primes _
    (projective_family_linear_cut_ne_top F hne (fun V hV => (hF V hV).1) t ht) k
  intro Q hQ
  obtain ⟨V, hV, hVQ⟩ := projective_family_prime_over_locus F Q hQ.isPrime
    (le_sup_left.trans hQ.le)
  have hcut : Q ∈ (V.ideal ⊔ Ideal.span {t}).minimalPrimes := by
    refine ⟨⟨hQ.isPrime, sup_le hVQ (le_sup_right.trans hQ.le)⟩, ?_⟩
    intro P hP hPQ
    apply hQ.2 ⟨hP.1, ?_⟩ hPQ
    exact sup_le ((projective_family_member_subvariety F V hV).trans
      (le_sup_left.trans hP.2)) (le_sup_right.trans hP.2)
  letI : V.ideal.IsPrime := (hF V hV).1
  letI : Q.IsPrime := hQ.isPrime
  have hdV : OAI.QuarticPowerFree.affineDimension V.ideal = k+1 := by
    have h := V.dimension_cone (ProjectiveFamily.irreducible_points_nonempty V (hF V hV).1)
    simpa only [ProjectiveVariety.affineCone, AffineVariety.dimension, (hF V hV).2] using h
  rw [prime_coordinate_krull_dimension Q hQ.isPrime,
    OAI.QuarticPowerFree.proper_cut_component_dimension V.ideal Q t (havoid V hV) hcut hdV]

end
end DistinctDistances.TrackA
