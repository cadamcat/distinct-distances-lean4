import DistinctDistances.TrackA.JacobianHilbertSupport
import DistinctDistances.TrackA.BezoutRefinedSupport

namespace DistinctDistances.TrackA
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical
open IsLocalRing

/-- The actual global contraction of the original localized equation ideal. -/
def jacobianContractedIdeal {n q : ℕ} (x : Point n) (f : Fin q → Poly n) : Ideal (Poly n) :=
  (localizedIdeal (Ideal.span (Set.range f)) x).comap
    (algebraMap (Poly n) (PointLocalRing x))

theorem jacobianContractedIdeal_localized {n q : ℕ} (x : Point n) (f : Fin q → Poly n) :
    localizedIdeal (jacobianContractedIdeal x f) x =
      localizedIdeal (Ideal.span (Set.range f)) x :=
  IsLocalization.map_under (pointIdeal x).primeCompl (PointLocalRing x) _

theorem jacobianContractedIdeal_isPrime {n q : ℕ} (x : Point n)
    (f : Fin q → Poly n) (cols : Fin q ↪ Fin n)
    (hzero : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hdet : Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (cols j) (f i))) ≠ 0) :
    (jacobianContractedIdeal x f).IsPrime := by
  letI := localizedJacobianSpan_isPrime x f cols hzero hdet
  exact Ideal.comap_isPrime (algebraMap (Poly n) (PointLocalRing x)) _

theorem jacobianContractedIdeal_le_point {n q : ℕ} (x : Point n)
    (f : Fin q → Poly n) (cols : Fin q ↪ Fin n)
    (hzero : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hdet : Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (cols j) (f i))) ≠ 0) :
    jacobianContractedIdeal x f ≤ pointIdeal x := by
  have hprime := localizedJacobianSpan_isPrime x f cols hzero hdet
  have h := Ideal.comap_mono (f := algebraMap (Poly n) (PointLocalRing x))
    (IsLocalRing.le_maximalIdeal hprime.ne_top)
  change jacobianContractedIdeal x f ≤
    (maximalIdeal (PointLocalRing x)).under (Poly n) at h
  rwa [IsLocalization.AtPrime.under_maximalIdeal (PointLocalRing x) (pointIdeal x)] at h

/-- The reduced variety keeps exactly the contracted prime, rather than changing its ideal. -/
def jacobianContractedVariety {n q : ℕ} (x : Point n)
    (f : Fin q → Poly n) (cols : Fin q ↪ Fin n)
    (hzero : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hdet : Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (cols j) (f i))) ≠ 0) : AffineVariety n :=
  ⟨jacobianContractedIdeal x f, (jacobianContractedIdeal_isPrime x f cols hzero hdet).isRadical⟩

theorem jacobianContractedVariety_mem {n q : ℕ} (x : Point n)
    (f : Fin q → Poly n) (cols : Fin q ↪ Fin n)
    (hzero : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hdet : Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (cols j) (f i))) ≠ 0) :
    x ∈ (jacobianContractedVariety x f cols hzero hdet).points := by
  intro p hp
  exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mp
    (jacobianContractedIdeal_le_point x f cols hzero hdet hp)

/-- At the original point, the actual contracted variety has all the
local Hilbert values of the free affine space of dimension k. -/
theorem jacobianContractedVariety_localHilbert {n k : ℕ} (hk : k ≤ n) (x : Point n)
    (f : Fin (n-k) → Poly n) (cols : Fin (n-k) ↪ Fin n)
    (hzero : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hdet : Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (cols j) (f i))) ≠ 0) (t : ℕ) :
    (jacobianContractedVariety x f cols hzero hdet).localHilbert x t =
      (AffineVariety.whole (n := k)).localHilbert (0 : Point k) t := by
  let α := ↥((Set.range cols)ᶜ : Set (Fin n))
  let e : α ≃ Fin k := (Fintype.equivFin α).trans
    (finCongr (jacobianFreeCoordinate_card hk cols))
  have he := formalFree_power_length_eq_whole k e t
  unfold AffineVariety.localHilbert localLengthAt localizedIdeal
  rw [Ideal.map_sup, Ideal.map_pow,
    IsLocalization.AtPrime.map_eq_maximalIdeal (pointIdeal x) (PointLocalRing x)]
  change Module.length (PointLocalRing x) (PointLocalRing x ⧸
    localizedIdeal (jacobianContractedIdeal x f) x ⊔ maximalIdeal (PointLocalRing x)^(t+1)) = _
  rw [jacobianContractedIdeal_localized, point_local_length_eq_complex_length,
    localizedJacobianSpan_power_length x f cols hzero hdet]
  exact he

/-- The only upstream used here is the original frozen local/global
dimension comparison. All local lengths above are unconditional. -/
theorem jacobianContractedVariety_dimension {n k : ℕ} (hk : k ≤ n) (x : Point n)
    (f : Fin (n-k) → Poly n) (cols : Fin (n-k) ↪ Fin n)
    (hzero : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hdet : Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (cols j) (f i))) ≠ 0) :
    (jacobianContractedVariety x f cols hzero hdet).dimension = k := by
  let W := jacobianContractedVariety x f cols hzero hdet
  have hW : W.IsIrreducible := jacobianContractedIdeal_isPrime x f cols hzero hdet
  have hxW : x ∈ W := jacobianContractedVariety_mem x f cols hzero hdet
  have hwhole : (AffineVariety.whole (n := k)).ideal = ⊥ := Ideal.radical_bot_of_isReduced
  have hwholeIr : (AffineVariety.whole (n := k)).IsIrreducible := by
    change ((AffineVariety.whole (n := k)).ideal).IsPrime
    rw [hwhole]
    infer_instance
  have hwholeMem : (0 : Point k) ∈ AffineVariety.whole := by
    intro p hp
    rw [hwhole] at hp
    simpa only [map_zero] using congrArg (MvPolynomial.aeval (0 : Point k)) (Ideal.mem_bot.mp hp)
  have hP := localHilbertPolynomial_eq_of_eventually W x AffineVariety.whole (0 : Point k)
    (Filter.Eventually.of_forall (jacobianContractedVariety_localHilbert hk x f cols hzero hdet))
  calc
    W.dimension = W.localDimension x := (W.localDimension_eq_dimension x hW hxW).symm
    _ = (AffineVariety.whole (n := k)).localDimension (0 : Point k) :=
      congrArg Polynomial.natDegree hP
    _ = (AffineVariety.whole (n := k)).dimension :=
      AffineVariety.localDimension_eq_dimension _ _ hwholeIr hwholeMem
    _ = k := whole_dimension k

end
end DistinctDistances.TrackA
