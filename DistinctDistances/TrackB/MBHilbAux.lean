import DistinctDistances.TrackB.Compactification
import DistinctDistances.TrackB.IncidenceHilbert
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.MvPolynomial.Ideal
import OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness

/-!
Multigraded Hilbert–Serre for standard block gradings. The variable-elimination
proof uses OAI's stabilized colon theorem and quotient equivalences. The
coefficient conversion reuses the OAI single-graded Hilbert polynomial theorem
for each ambient block. All declarations here have complete proofs.
-/

namespace DistinctDistances.TrackB

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators


section RankIdentity

/-- The kernel piece of a multihomogeneous section: the quotient map restricted
to one multidegree piece. Its rank is the subtrahend in the rank identity. -/
def sectionKernel {σ : Type*} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ))
    (S : Set (σ →₀ ℕ)) : Submodule ℂ ↥(MvPolynomial.restrictSupport ℂ S) :=
  LinearMap.ker ((Ideal.Quotient.mkₐ ℂ I).toLinearMap.domRestrict
    (MvPolynomial.restrictSupport ℂ S))

theorem moduleFinite_restrictSupport {σ : Type*} [Fintype σ]
    (S : Set (σ →₀ ℕ)) [Finite ↥S] :
    Module.Finite ℂ (MvPolynomial.restrictSupport ℂ S) :=
  Module.Finite.of_basis (MvPolynomial.basisRestrictSupport ℂ S)

/-- Rank identity: image rank + kernel rank = ambient piece rank. -/
theorem section_finrank_eq {σ : Type*} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ))
    (S : Set (σ →₀ ℕ)) [Finite ↥S] :
    Module.finrank ℂ ((MvPolynomial.restrictSupport ℂ S).map
        (Ideal.Quotient.mkₐ ℂ I).toLinearMap) +
      Module.finrank ℂ (sectionKernel I S) =
      Module.finrank ℂ (MvPolynomial.restrictSupport ℂ S) := by
  haveI := moduleFinite_restrictSupport S
  have h := LinearMap.finrank_range_add_finrank_ker
    ((Ideal.Quotient.mkₐ ℂ I).toLinearMap.domRestrict
      (MvPolynomial.restrictSupport ℂ S))
  rw [LinearMap.range_domRestrict] at h
  exact h

end RankIdentity

section ExponentsFinite

theorem finite_pairExponents {n m s t : ℕ} :
    Finite ↥{d : Fin (n + m) →₀ ℕ |
      (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
      (∑ i : Fin m, d (Fin.natAdd n i)) = t} := by
  classical
  let S : Set (Fin (n + m) →₀ ℕ) :=
    {d | (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
      (∑ i : Fin m, d (Fin.natAdd n i)) = t}
  let F : Finset (Fin (n + m) → ℕ) :=
    Fintype.piFinset fun _ => Finset.range (s + t + 1)
  show Finite ↥S
  have hmem : ∀ d : ↥S, Finsupp.equivFunOnFinite (d : Fin (n + m) →₀ ℕ) ∈ ↑F := by
    intro d
    simp only [F, Fintype.mem_piFinset, Finset.mem_range]
    intro i
    have hle : (d : Fin (n + m) →₀ ℕ) i ≤ s + t := by
      calc (d : Fin (n + m) →₀ ℕ) i
          ≤ ∑ j : Fin (n + m), (d : Fin (n + m) →₀ ℕ) j :=
            Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = s + t := by rw [Fin.sum_univ_add, d.2.1, d.2.2]
    have heq : Finsupp.equivFunOnFinite (d : Fin (n + m) →₀ ℕ) i =
        (d : Fin (n + m) →₀ ℕ) i := rfl
    omega
  apply Finite.of_injective (f := fun d : ↥S => (⟨Finsupp.equivFunOnFinite
    (d : Fin (n + m) →₀ ℕ), hmem d⟩ : ↥(↑F : Set _)))
  intro a b hab
  apply Subtype.ext
  exact Finsupp.equivFunOnFinite.injective (Subtype.mk.inj hab)

theorem finite_tripleExponents {n m o s t u : ℕ} :
    Finite ↥{d : Fin (n + m + o) →₀ ℕ |
      (∑ i : Fin n, d (Fin.castAdd o (Fin.castAdd m i))) = s ∧
      (∑ i : Fin m, d (Fin.castAdd o (Fin.natAdd n i))) = t ∧
      (∑ i : Fin o, d (Fin.natAdd (n + m) i)) = u} := by
  classical
  let S : Set (Fin (n + m + o) →₀ ℕ) :=
    {d | (∑ i : Fin n, d (Fin.castAdd o (Fin.castAdd m i))) = s ∧
      (∑ i : Fin m, d (Fin.castAdd o (Fin.natAdd n i))) = t ∧
      (∑ i : Fin o, d (Fin.natAdd (n + m) i)) = u}
  let F : Finset (Fin (n + m + o) → ℕ) :=
    Fintype.piFinset fun _ => Finset.range (s + t + u + 1)
  show Finite ↥S
  have hmem : ∀ d : ↥S, Finsupp.equivFunOnFinite (d : Fin (n + m + o) →₀ ℕ) ∈ ↑F := by
    intro d
    simp only [F, Fintype.mem_piFinset, Finset.mem_range]
    intro i
    have hle : (d : Fin (n + m + o) →₀ ℕ) i ≤ s + t + u := by
      calc (d : Fin (n + m + o) →₀ ℕ) i
          ≤ ∑ j : Fin (n + m + o), (d : Fin (n + m + o) →₀ ℕ) j :=
            Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = s + t + u := by
            rw [Fin.sum_univ_add, Fin.sum_univ_add, d.2.1, d.2.2.1, d.2.2.2]
    have heq : Finsupp.equivFunOnFinite (d : Fin (n + m + o) →₀ ℕ) i =
        (d : Fin (n + m + o) →₀ ℕ) i := rfl
    omega
  apply Finite.of_injective (f := fun d : ↥S => (⟨Finsupp.equivFunOnFinite
    (d : Fin (n + m + o) →₀ ℕ), hmem d⟩ : ↥(↑F : Set _)))
  intro a b hab
  apply Subtype.ext
  exact Finsupp.equivFunOnFinite.injective (Subtype.mk.inj hab)


end ExponentsFinite

section AmbientCounts

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Split an exponent on two blocks into its block exponents. -/
def pairExponentEquiv (n m s t : ℕ) :
    {d : Fin (n + m) →₀ ℕ |
      (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
      (∑ i : Fin m, d (Fin.natAdd n i)) = t} ≃
    {d : Fin n →₀ ℕ | d.degree = s} × {d : Fin m →₀ ℕ | d.degree = t} where
  toFun d :=
    (⟨Finsupp.equivFunOnFinite.symm (fun i => d.1 (Fin.castAdd m i)), by
        simpa [Finsupp.degree_eq_sum] using d.2.1⟩,
     ⟨Finsupp.equivFunOnFinite.symm (fun i => d.1 (Fin.natAdd n i)), by
        simpa [Finsupp.degree_eq_sum] using d.2.2⟩)
  invFun d := ⟨Finsupp.equivFunOnFinite.symm (Fin.addCases d.1.1 d.2.1), by
    constructor
    · simpa [Finsupp.degree_eq_sum] using d.1.2
    · simpa [Finsupp.degree_eq_sum] using d.2.2⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    cases i using Fin.addCases <;> simp
  right_inv d := by
    apply Prod.ext <;> apply Subtype.ext <;> ext i <;> simp

/-- Ambient ranks factor as a product; this includes empty variable blocks. -/
theorem ambientPairCount (n m s t : ℕ) :
    Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
      {d : Fin (n + m) →₀ ℕ |
        (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
        (∑ i : Fin m, d (Fin.natAdd n i)) = t}) =
      n.multichoose s * m.multichoose t := by
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport ℂ _),
    Nat.card_congr (pairExponentEquiv n m s t), Nat.card_prod,
    OAI.PiExponentJets.W64.card_exponents_degree,
    OAI.PiExponentJets.W64.card_exponents_degree]
  simp

/-- The existing single-graded theorem supplies each ambient block polynomial. -/
theorem ambientBlockPolynomial (n : ℕ) :
    ∃ P : Polynomial ℚ, ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
      P.eval (s : ℚ) = (n.multichoose s : ℚ) := by
  obtain ⟨P, N, hP⟩ := OAI.PiExponentJets.W64.exists_homogeneous_hilbert_polynomial
    (Fin n) (⊥ : Ideal (Poly n))
    (Ideal.IsHomogeneous.bot (MvPolynomial.homogeneousSubmodule (Fin n) ℂ))
  refine ⟨P, N + 1, ?_⟩
  intro s hs
  simpa only [OAI.PiExponentJets.W64.quotientSection_bot_finrank_multichoose,
    Fintype.card_fin] using (hP s (by omega)).symm

/-- Ambient two-block restriction ranks are eventually polynomial. -/
theorem ambientPairCount_polynomial (n m : ℕ) :
    ∃ P : BaseHilbertPolynomial, ∃ N : ℕ, ∀ s t : ℕ, N ≤ s → N ≤ t →
      MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ))) P =
        (Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
          {d : Fin (n + m) →₀ ℕ |
            (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
            (∑ i : Fin m, d (Fin.natAdd n i)) = t}) : ℚ) := by
  obtain ⟨P, NP, hP⟩ := ambientBlockPolynomial n
  obtain ⟨Q, NQ, hQ⟩ := ambientBlockPolynomial m
  refine ⟨P.toMvPolynomial (0 : Fin 2) * Q.toMvPolynomial (1 : Fin 2), NP + NQ, ?_⟩
  intro s t hs ht
  rw [MvPolynomial.eval_mul, ambientPairCount, Nat.cast_mul]
  simp only [MvPolynomial.eval_toMvPolynomial]
  change P.eval (s : ℚ) * Q.eval (t : ℚ) = _
  rw [hP s (by omega), hQ t (by omega)]

/-- Split three blocks, retaining the nesting of the section definition. -/
def tripleExponentEquiv (n m o s t u : ℕ) :
    {d : Fin (n + m + o) →₀ ℕ |
      (∑ i : Fin n, d (Fin.castAdd o (Fin.castAdd m i))) = s ∧
      (∑ i : Fin m, d (Fin.castAdd o (Fin.natAdd n i))) = t ∧
      (∑ i : Fin o, d (Fin.natAdd (n + m) i)) = u} ≃
    ({d : Fin n →₀ ℕ | d.degree = s} × {d : Fin m →₀ ℕ | d.degree = t}) ×
      {d : Fin o →₀ ℕ | d.degree = u} where
  toFun d :=
    ((⟨Finsupp.equivFunOnFinite.symm
         (fun i => d.1 (Fin.castAdd o (Fin.castAdd m i))), by
          simpa [Finsupp.degree_eq_sum] using d.2.1⟩,
      ⟨Finsupp.equivFunOnFinite.symm
         (fun i => d.1 (Fin.castAdd o (Fin.natAdd n i))), by
          simpa [Finsupp.degree_eq_sum] using d.2.2.1⟩),
     ⟨Finsupp.equivFunOnFinite.symm (fun i => d.1 (Fin.natAdd (n + m) i)), by
        simpa [Finsupp.degree_eq_sum] using d.2.2.2⟩)
  invFun d := ⟨Finsupp.equivFunOnFinite.symm
    (Fin.addCases (Fin.addCases d.1.1.1 d.1.2.1) d.2.1), by
      refine ⟨?_, ?_, ?_⟩
      · simpa [Finsupp.degree_eq_sum] using d.1.1.2
      · simpa [Finsupp.degree_eq_sum] using d.1.2.2
      · simpa [Finsupp.degree_eq_sum] using d.2.2⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    cases i using Fin.addCases with
    | left i => cases i using Fin.addCases <;> simp
    | right i => simp
  right_inv d := by
    apply Prod.ext
    · apply Prod.ext <;> apply Subtype.ext <;> ext i <;> simp
    · apply Subtype.ext
      ext i
      simp

/-- Ambient ranks on three factors are products of the single-factor counts. -/
theorem ambientTripleCount (n m o s t u : ℕ) :
    Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
      {d : Fin (n + m + o) →₀ ℕ |
        (∑ i : Fin n, d (Fin.castAdd o (Fin.castAdd m i))) = s ∧
        (∑ i : Fin m, d (Fin.castAdd o (Fin.natAdd n i))) = t ∧
        (∑ i : Fin o, d (Fin.natAdd (n + m) i)) = u}) =
      n.multichoose s * m.multichoose t * o.multichoose u := by
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport ℂ _),
    Nat.card_congr (tripleExponentEquiv n m o s t u), Nat.card_prod, Nat.card_prod,
    OAI.PiExponentJets.W64.card_exponents_degree,
    OAI.PiExponentJets.W64.card_exponents_degree,
    OAI.PiExponentJets.W64.card_exponents_degree]
  simp

/-- Ambient three-block restriction ranks are eventually polynomial. -/
theorem ambientTripleCount_polynomial (n m o : ℕ) :
    ∃ P : IncidenceHilbertPolynomial, ∃ N : ℕ, ∀ s t u : ℕ,
      N ≤ s → N ≤ t → N ≤ u →
      MvPolynomial.eval (Fin.cons (s : ℚ) (Fin.cons (t : ℚ)
        (fun _ : Fin 1 => (u : ℚ)))) P =
        (Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
          {d : Fin (n + m + o) →₀ ℕ |
            (∑ i : Fin n, d (Fin.castAdd o (Fin.castAdd m i))) = s ∧
            (∑ i : Fin m, d (Fin.castAdd o (Fin.natAdd n i))) = t ∧
            (∑ i : Fin o, d (Fin.natAdd (n + m) i)) = u}) : ℚ) := by
  obtain ⟨P, NP, hP⟩ := ambientBlockPolynomial n
  obtain ⟨Q, NQ, hQ⟩ := ambientBlockPolynomial m
  obtain ⟨R, NR, hR⟩ := ambientBlockPolynomial o
  refine ⟨P.toMvPolynomial (0 : Fin 3) * Q.toMvPolynomial (1 : Fin 3) *
    R.toMvPolynomial (2 : Fin 3), NP + NQ + NR, ?_⟩
  intro s t u hs ht hu
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul, ambientTripleCount,
    Nat.cast_mul, Nat.cast_mul]
  simp only [MvPolynomial.eval_toMvPolynomial]
  change P.eval (s : ℚ) * Q.eval (t : ℚ) * R.eval (u : ℚ) = _
  rw [hP s (by omega), hQ t (by omega), hR u (by omega)]

end AmbientCounts

namespace HilbertMulti

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K σ M : Type*} [Field K] [AddCommMonoid M] [IsCancelAdd M]
  [DecidableEq M] (w : σ → M)

local instance gradeRightCancel : AddRightCancelMonoid M :=
  { (inferInstance : AddMonoid M) with
    add_right_cancel := fun _ _ _ h => add_right_cancel h }

/-- Restriction rank on a general weighted-homogeneous piece. -/
def sectionSpace (I : Ideal (MvPolynomial σ K)) (d : M) :
    Submodule K (MvPolynomial σ K ⧸ I) :=
  (MvPolynomial.weightedHomogeneousSubmodule K w d).map
    (Ideal.Quotient.mkₐ K I).toLinearMap

instance sectionFinite (I : Ideal (MvPolynomial σ K)) (d : M)
    [Module.Finite K (MvPolynomial.weightedHomogeneousSubmodule K w d)] :
    Module.Finite K (sectionSpace w I d) := by
  unfold sectionSpace
  infer_instance

/-- A homogeneous relation in I+(f) has a homogeneous multiplier. -/
theorem homogeneous_mem_decomposition (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K w))
    {d n : M} (f p : MvPolynomial σ K)
    (hf : f.IsWeightedHomogeneous w d) (hp : p.IsWeightedHomogeneous w (n + d))
    (hmem : p ∈ Ideal.span {f} ⊔ I) :
    ∃ a : MvPolynomial σ K, a.IsWeightedHomogeneous w n ∧ p - a * f ∈ I := by
  obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp hmem
  let an := DirectSum.decompose (MvPolynomial.weightedHomogeneousSubmodule K w) a n
  refine ⟨an.1, an.2, ?_⟩
  have hproj := congrArg
    (GradedRing.proj (MvPolynomial.weightedHomogeneousSubmodule K w) (n + d)) hab
  rw [map_add, GradedRing.proj_apply, GradedRing.proj_apply,
    GradedRing.proj_apply,
    DirectSum.coe_decompose_mul_add_of_right_mem
      (MvPolynomial.weightedHomogeneousSubmodule K w) hf,
    DirectSum.decompose_of_mem_same (MvPolynomial.weightedHomogeneousSubmodule K w) hp]
      at hproj
  have hb' := (Ideal.IsHomogeneous.mem_iff
    (MvPolynomial.weightedHomogeneousSubmodule K w) hI).mp hb (n + d)
  have heq : p - an.1 * f =
      (DirectSum.decompose (MvPolynomial.weightedHomogeneousSubmodule K w) b (n + d) :
        MvPolynomial σ K) := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [an, add_comm] using hproj.symm
  rw [heq]
  exact hb'

/-- Weighted homogeneity is preserved by colon by a homogeneous element. -/
theorem homogeneous_colon (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K w))
    {d : M} {f : MvPolynomial σ K} (hf : f.IsWeightedHomogeneous w d) :
    (I.colon {f}).IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K w) := by
  intro n a ha
  apply Submodule.mem_colon_singleton.mpr
  have haf : a * f ∈ I := by
    simpa only [smul_eq_mul] using Submodule.mem_colon_singleton.mp ha
  have h := hI (n + d) haf
  rw [DirectSum.coe_decompose_mul_add_of_right_mem
    (MvPolynomial.weightedHomogeneousSubmodule K w) hf] at h
  exact h

/-- The universal quotient map restricted to a weight piece. -/
def sectionFactor (I J : Ideal (MvPolynomial σ K)) (hIJ : I ≤ J) (d : M) :
    sectionSpace w I d →ₗ[K] sectionSpace w J d where
  toFun x := ⟨Ideal.Quotient.factorₐ K hIJ x.1, by
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    change Ideal.Quotient.mk I p = x.1 at hpx
    apply Submodule.mem_map.mpr
    refine ⟨p, hp, ?_⟩
    exact congrArg (Ideal.Quotient.factorₐ K hIJ) hpx⟩
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c x := by apply Subtype.ext; exact map_smul _ _ _

theorem sectionFactor_surjective (I J : Ideal (MvPolynomial σ K))
    (hIJ : I ≤ J) (d : M) : Function.Surjective (sectionFactor w I J hIJ d) := by
  intro y
  obtain ⟨p, hp, hpy⟩ := Submodule.mem_map.mp y.2
  refine ⟨⟨Ideal.Quotient.mk I p, Submodule.mem_map.mpr ⟨p, hp, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact hpy

/-- Multiplication on weighted quotient pieces. -/
def sectionMultiply (I : Ideal (MvPolynomial σ K)) {d : M}
    (f : MvPolynomial σ K) (hf : f.IsWeightedHomogeneous w d) (n : M) :
    sectionSpace w I n →ₗ[K] sectionSpace w I (n + d) where
  toFun x := ⟨x.1 * Ideal.Quotient.mk I f, by
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    change Ideal.Quotient.mk I p = x.1 at hpx
    apply Submodule.mem_map.mpr
    refine ⟨p * f, hp.mul hf, ?_⟩
    change Ideal.Quotient.mk I (p * f) = _
    rw [map_mul, hpx]⟩
  map_add' x y := by apply Subtype.ext; exact add_mul _ _ _
  map_smul' c x := by apply Subtype.ext; exact smul_mul_assoc _ _ _

/-- Exactness at the middle weight piece of the colon sequence. -/
theorem sectionFactor_ker_eq (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K w))
    {d : M} (f : MvPolynomial σ K) (hf : f.IsWeightedHomogeneous w d) (n : M) :
    LinearMap.ker (sectionFactor w I (Ideal.span {f} ⊔ I) le_sup_right (n + d)) =
      LinearMap.range (sectionMultiply w I f hf n) := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    change Ideal.Quotient.mk I p = x.1 at hpx
    have hz : Ideal.Quotient.mk (Ideal.span {f} ⊔ I) p = 0 := by
      have hxv := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      change (Ideal.Quotient.factorₐ K le_sup_right) x.1 = 0 at hxv
      change (Ideal.Quotient.factorₐ K le_sup_right) (Ideal.Quotient.mk I p) = 0
      rw [hpx]
      exact hxv
    obtain ⟨a, ha, hpa⟩ := homogeneous_mem_decomposition w I hI f p hf hp
      (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    apply LinearMap.mem_range.mpr
    refine ⟨⟨Ideal.Quotient.mk I a, Submodule.mem_map.mpr ⟨a, ha, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk I a * Ideal.Quotient.mk I f = x.1
    rw [← map_mul]
    have he : Ideal.Quotient.mk I (p - a * f) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hpa
    rw [map_sub, sub_eq_zero] at he
    exact he.symm.trans hpx
  · intro hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change (Ideal.Quotient.factorₐ K le_sup_right)
      (y.1 * Ideal.Quotient.mk I f) = 0
    rw [map_mul]
    change (Ideal.Quotient.factorₐ K le_sup_right) y.1 *
      Ideal.Quotient.mk (Ideal.span {f} ⊔ I) f = 0
    have hf0 : Ideal.Quotient.mk (Ideal.span {f} ⊔ I) f = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hinc : Ideal.span {f} ≤ Ideal.span {f} ⊔ I := le_sup_left
      exact hinc (Ideal.subset_span (Set.mem_singleton f))
    rw [hf0, mul_zero]

/-- The colon quotient has the same multiplication kernel. -/
theorem sectionFactor_colon_ker (I : Ideal (MvPolynomial σ K))
    {d : M} (f : MvPolynomial σ K) (hf : f.IsWeightedHomogeneous w d) (n : M) :
    LinearMap.ker (sectionFactor w I (I.colon {f})
      (OAI.PiExponentJets.W64.ideal_le_colon_singleton I f) n) =
      LinearMap.ker (sectionMultiply w I f hf n) := by
  ext x
  obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
  change Ideal.Quotient.mk I p = x.1 at hpx
  simp only [LinearMap.mem_ker, Subtype.ext_iff]
  change (Ideal.Quotient.factorₐ K
    (OAI.PiExponentJets.W64.ideal_le_colon_singleton I f)) x.1 = 0 ↔
      x.1 * Ideal.Quotient.mk I f = 0
  rw [← hpx]
  change Ideal.Quotient.mk (I.colon {f}) p = 0 ↔
    Ideal.Quotient.mk I (p * f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem,
    Submodule.mem_colon_singleton, smul_eq_mul]

/-- The same rank recurrence as the OAI single-graded colon step, on each multidegree. -/
theorem colon_rank_step (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K w))
    {d : M} (f : MvPolynomial σ K) (hf : f.IsWeightedHomogeneous w d) (n : M)
    [Module.Finite K (MvPolynomial.weightedHomogeneousSubmodule K w n)]
    [Module.Finite K (MvPolynomial.weightedHomogeneousSubmodule K w (n + d))] :
    Module.finrank K (sectionSpace w (Ideal.span {f} ⊔ I) (n + d)) +
      Module.finrank K (sectionSpace w (I.colon {f}) n) =
      Module.finrank K (sectionSpace w I (n + d)) := by
  let φ := sectionFactor w I (I.colon {f})
    (OAI.PiExponentJets.W64.ideal_le_colon_singleton I f) n
  have hc := (LinearMap.ker φ).finrank_quotient_add_finrank
  let ec := φ.quotKerEquivOfSurjective (sectionFactor_surjective w I (I.colon {f}) _ n)
  rw [ec.finrank_eq, sectionFactor_colon_ker w I f hf n] at hc
  have hm := (sectionMultiply w I f hf n).finrank_range_add_finrank_ker
  have he := (LinearMap.range (sectionMultiply w I f hf n)).finrank_quotient_add_finrank
  rw [← sectionFactor_ker_eq w I hI f hf n] at he
  let e := (sectionFactor w I (Ideal.span {f} ⊔ I) le_sup_right (n + d)).quotKerEquivOfSurjective
    (sectionFactor_surjective w I (Ideal.span {f} ⊔ I) le_sup_right (n + d))
  rw [e.finrank_eq, sectionFactor_ker_eq w I hI f hf n] at he
  omega

/-- A substitution preserving variable weights preserves homogeneous pieces. -/
theorem aeval_weighted {τ : Type*} (wt : τ → M) (g : σ → MvPolynomial τ K)
    (hg : ∀ i, (g i).IsWeightedHomogeneous wt (w i))
    {d : M} {p : MvPolynomial σ K} (hp : p.IsWeightedHomogeneous w d) :
    (MvPolynomial.aeval g p).IsWeightedHomogeneous wt d := by
  classical
  refine MvPolynomial.IsWeightedHomogeneous.induction_on
    (motive := fun p _ => (MvPolynomial.aeval g p).IsWeightedHomogeneous wt d)
    ?_ ?_ ?_ hp
  · simpa only [map_zero] using MvPolynomial.isWeightedHomogeneous_zero K wt d
  · intro p q hp hq ihp ihq
    simpa only [map_add] using ihp.add ihq
  · intro a r ha
    rw [MvPolynomial.aeval_monomial]
    have hs : (∑ i ∈ a.support, a i • w i) = d := by
      simpa only [Finsupp.weight_apply, Finsupp.sum] using ha
    have hprod := MvPolynomial.IsWeightedHomogeneous.prod a.support
      (fun i => (g i) ^ a i) (fun i => a i • w i) (fun i _ => (hg i).pow (a i))
    have h := (MvPolynomial.isWeightedHomogeneous_C wt r).mul hprod
    simpa only [Finsupp.prod, MvPolynomial.algebraMap_eq, zero_add, hs] using h

section Coordinates

variable {τ : Type*} (wo : Option τ → M)

/-- Setting one variable to zero respects the weights of the remaining variables. -/
theorem coordinateEval_weighted {p : MvPolynomial (Option τ) K} {d : M}
    (hp : p.IsWeightedHomogeneous wo d) :
    (OAI.PiExponentSiegel.W08.coordinateEval p).IsWeightedHomogeneous
      (fun i => wo (some i)) d := by
  apply aeval_weighted wo (fun i => wo (some i))
    (fun o => Option.elim o 0 MvPolynomial.X) ?_ hp
  intro o
  cases o with
  | none => exact MvPolynomial.isWeightedHomogeneous_zero _ _ _
  | some i => exact MvPolynomial.isWeightedHomogeneous_X _ _ _

theorem coordinateInclude_weighted {p : MvPolynomial τ K} {d : M}
    (hp : p.IsWeightedHomogeneous (fun i => wo (some i)) d) :
    (OAI.PiExponentSiegel.W08.coordinateInclude p).IsWeightedHomogeneous wo d := by
  change (MvPolynomial.rename Option.some p).IsWeightedHomogeneous wo d
  rw [MvPolynomial.rename_eq_aeval]
  exact aeval_weighted (fun i => wo (some i)) wo (MvPolynomial.X ∘ Option.some)
    (fun _ => MvPolynomial.isWeightedHomogeneous_X _ _ _) hp

/-- Reuse OAI's quotient equivalence, restricted to the multigraded pieces. -/
theorem coordinateQuotient_section_map (J : Ideal (MvPolynomial (Option τ) K))
    (hX : MvPolynomial.X none ∈ J) (d : M) :
    (sectionSpace wo J d).map
      (OAI.PiExponentSiegel.W08.coordinateQuotientEquiv J hX).toLinearEquiv.toLinearMap =
      sectionSpace (fun i => wo (some i))
        (OAI.PiExponentSiegel.W08.coordinateImageIdeal J) d := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr
      ⟨OAI.PiExponentSiegel.W08.coordinateEval p, coordinateEval_weighted wo hp, rfl⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    apply Submodule.mem_map.mpr
    refine ⟨Ideal.Quotient.mk J (OAI.PiExponentSiegel.W08.coordinateInclude p), ?_, ?_⟩
    · exact Submodule.mem_map.mpr
        ⟨_, coordinateInclude_weighted wo hp, rfl⟩
    · change Ideal.Quotient.mk _ (OAI.PiExponentSiegel.W08.coordinateEval
        (OAI.PiExponentSiegel.W08.coordinateInclude p)) = _
      rw [OAI.PiExponentSiegel.W08.coordinateEval_include]
      rfl

theorem coordinateQuotient_section_finrank (J : Ideal (MvPolynomial (Option τ) K))
    (hX : MvPolynomial.X none ∈ J) (d : M) :
    Module.finrank K (sectionSpace wo J d) =
      Module.finrank K (sectionSpace (fun i => wo (some i))
        (OAI.PiExponentSiegel.W08.coordinateImageIdeal J) d) := by
  exact ((OAI.PiExponentSiegel.W08.coordinateQuotientEquiv J hX).toLinearEquiv.ofSubmodules
    _ _ (coordinateQuotient_section_map wo J hX d)).finrank_eq

/-- The coordinate image ideal retains its multigrading. -/
theorem coordinateImageIdeal_weighted (J : Ideal (MvPolynomial (Option τ) K))
    (hJ : J.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K wo)) :
    (OAI.PiExponentSiegel.W08.coordinateImageIdeal J).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule K (fun i => wo (some i))) := by
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists
    (MvPolynomial.weightedHomogeneousSubmodule K wo) J).mp hJ
  rw [OAI.PiExponentSiegel.W08.coordinateImageIdeal, hS, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro q ⟨p, ⟨z, hz, rfl⟩, rfl⟩
  obtain ⟨d, hd⟩ := z.property
  exact ⟨d, coordinateEval_weighted wo hd⟩

end Coordinates

section Renaming

variable {τ : Type*} (e : σ ≃ τ)

theorem rename_weighted {p : MvPolynomial σ K} {d : M}
    (hp : p.IsWeightedHomogeneous w d) :
    (MvPolynomial.rename e p).IsWeightedHomogeneous (fun i => w (e.symm i)) d := by
  rw [MvPolynomial.rename_eq_aeval]
  apply aeval_weighted w (fun i => w (e.symm i)) (MvPolynomial.X ∘ e) ?_ hp
  intro i
  simpa using MvPolynomial.isWeightedHomogeneous_X K (fun i => w (e.symm i)) (e i)

theorem renameQuotient_section_map (J : Ideal (MvPolynomial σ K)) (d : M) :
    (sectionSpace w J d).map
      (OAI.PiExponentSiegel.W08.renameQuotientEquiv e J).toLinearEquiv.toLinearMap =
      sectionSpace (fun i => w (e.symm i)) (J.map (MvPolynomial.rename e).toRingHom) d := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr ⟨MvPolynomial.rename e p, rename_weighted w e hp, rfl⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    apply Submodule.mem_map.mpr
    refine ⟨Ideal.Quotient.mk J (MvPolynomial.rename e.symm p), ?_, ?_⟩
    · apply Submodule.mem_map.mpr
      refine ⟨_, ?_, rfl⟩
      simpa using rename_weighted (fun i => w (e.symm i)) e.symm hp
    · change Ideal.Quotient.mk _ (MvPolynomial.rename e (MvPolynomial.rename e.symm p)) = _
      exact congrArg (Ideal.Quotient.mk _)
        ((MvPolynomial.renameEquiv K e).apply_symm_apply p)

theorem renameQuotient_section_finrank (J : Ideal (MvPolynomial σ K)) (d : M) :
    Module.finrank K (sectionSpace w J d) =
      Module.finrank K (sectionSpace (fun i => w (e.symm i))
        (J.map (MvPolynomial.rename e).toRingHom) d) := by
  exact ((OAI.PiExponentSiegel.W08.renameQuotientEquiv e J).toLinearEquiv.ofSubmodules
    _ _ (renameQuotient_section_map w e J d)).finrank_eq

theorem renameImageIdeal_weighted (J : Ideal (MvPolynomial σ K))
    (hJ : J.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K w)) :
    (J.map (MvPolynomial.rename e).toRingHom).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule K (fun i => w (e.symm i))) := by
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists
    (MvPolynomial.weightedHomogeneousSubmodule K w) J).mp hJ
  rw [hS, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro q ⟨p, ⟨z, hz, rfl⟩, rfl⟩
  obtain ⟨d, hd⟩ := z.property
  exact ⟨d, rename_weighted w e hd⟩

end Renaming

section BlockWeights

variable {κ : Type*} [DecidableEq κ]


/-- Standard multigrading: each variable belongs to exactly one block. -/
def blockWeight (b : σ → κ) (i : σ) : κ →₀ ℕ := Finsupp.single (b i) 1

theorem weight_blockWeight (b : σ → κ) (d : σ →₀ ℕ) :
    Finsupp.weight (blockWeight b) d = d.mapDomain b := by
  classical
  rw [Finsupp.weight_apply, Finsupp.mapDomain]
  apply Finsupp.sum_congr
  intro i hi
  simp [blockWeight, Finsupp.smul_single]

/-- A multigraded piece is the monomial subspace of the specified block sums. -/
theorem blockPiece_eq (b : σ → κ) (d : κ →₀ ℕ) :
    MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b) d =
      MvPolynomial.restrictSupport K {a : σ →₀ ℕ | a.mapDomain b = d} := by
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  simp_rw [weight_blockWeight]
  rfl

instance blockPieceFinite [Finite σ] (b : σ → κ) (d : κ →₀ ℕ) :
    Module.Finite K (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b) d) := by
  classical
  rw [blockPiece_eq]
  have hs : {a : σ →₀ ℕ | a.mapDomain b = d}.Finite :=
    (Finsupp.finite_of_degree_eq d.degree).subset (by
      intro a ha
      change a.degree = d.degree
      rw [← Finsupp.degree_mapDomain b a, ha])
  letI := hs.fintype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K _)

/-- Evaluate a polynomial on a torus orbit, leaving the torus variables symbolic. -/
def torusPolynomial (b : σ → κ) (v : σ → K) (f : MvPolynomial σ K) :
    MvPolynomial κ K :=
  ∑ a ∈ f.support, MvPolynomial.monomial (a.mapDomain b)
    (MvPolynomial.aeval v (MvPolynomial.monomial a (f.coeff a)))

/-- Torus coefficients recover evaluation of the individual multidegree components. -/
theorem torusPolynomial_coeff (b : σ → κ) (v : σ → K) (f : MvPolynomial σ K)
    (d : κ →₀ ℕ) :
    (torusPolynomial b v f).coeff d =
      MvPolynomial.aeval v (MvPolynomial.weightedHomogeneousComponent (blockWeight b) d f) := by
  classical
  simp only [torusPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    MvPolynomial.weightedHomogeneousComponent_apply, map_sum, weight_blockWeight,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> simp_all

/-- Evaluation of the symbolic torus polynomial is evaluation on the scaled point. -/
theorem torusPolynomial_eval (b : σ → κ) (v : σ → K) (f : MvPolynomial σ K)
    (c : κ → K) :
    MvPolynomial.eval c (torusPolynomial b v f) =
      MvPolynomial.aeval (fun i => c (b i) * v i) f := by
  classical
  conv_rhs => rw [f.as_sum]
  simp only [torusPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [MvPolynomial.eval_monomial, MvPolynomial.aeval_monomial,
    MvPolynomial.aeval_monomial,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, mul_pow, Finsupp.prod_mul]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Torus-invariant sets have multihomogeneous vanishing ideals. -/
theorem vanishingIdeal_blockHomogeneous [Infinite K] (b : σ → κ) (T : Set (σ → K))
    (hT : ∀ v ∈ T, ∀ c : κ → K, (∀ j, c j ≠ 0) →
      (fun i => c (b i) * v i) ∈ T) :
    (MvPolynomial.vanishingIdeal K T).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b)) := by
  classical
  intro d f hf
  change (DirectSum.decompose
    (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b)) f d :
      MvPolynomial σ K) ∈ MvPolynomial.vanishingIdeal K T
  change ((MvPolynomial.weightedDecomposition K (blockWeight b)).decompose' f d :
    MvPolynomial σ K) ∈ MvPolynomial.vanishingIdeal K T
  rw [MvPolynomial.weightedDecomposition.decompose'_apply]
  apply MvPolynomial.mem_vanishingIdeal_iff.mpr
  intro v hv
  have hp : torusPolynomial b v f = 0 := by
    apply MvPolynomial.funext_set (fun _ : κ => ({0} : Set K)ᶜ)
      (fun _ => (Set.finite_singleton (0 : K)).infinite_compl)
    intro c hc
    rw [map_zero, torusPolynomial_eval]
    apply (MvPolynomial.mem_vanishingIdeal_iff.mp hf)
    exact hT v hv c (fun j => by simpa using hc j (Set.mem_univ j))
  rw [← torusPolynomial_coeff b v f d, hp]
  simp

/-- Outside the degrees divisible by f, adding f to the ideal has no effect. -/
theorem mem_step_of_not_le (b : σ → κ) (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b)))
    {d n : κ →₀ ℕ} (f p : MvPolynomial σ K)
    (hf : f.IsWeightedHomogeneous (blockWeight b) d)
    (hp : p.IsWeightedHomogeneous (blockWeight b) n) (hnd : ¬d ≤ n)
    (hmem : p ∈ Ideal.span {f} ⊔ I) : p ∈ I := by
  obtain ⟨a, z, hz, haz⟩ := Ideal.mem_span_singleton_sup.mp hmem
  have hproj := congrArg
    (GradedRing.proj (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b)) n) haz
  rw [map_add, GradedRing.proj_apply, GradedRing.proj_apply, GradedRing.proj_apply,
    DirectSum.coe_decompose_mul_of_right_mem_of_not_le
      (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b)) hf hnd,
    zero_add, DirectSum.decompose_of_mem_same
      (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b)) hp] at hproj
  rw [← hproj]
  exact hI n hz

theorem section_rank_step_of_not_le [Finite σ] (b : σ → κ)
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b)))
    {d n : κ →₀ ℕ} (f : MvPolynomial σ K)
    (hf : f.IsWeightedHomogeneous (blockWeight b) d) (hnd : ¬d ≤ n) :
    Module.finrank K (sectionSpace (blockWeight b) (Ideal.span {f} ⊔ I) n) =
      Module.finrank K (sectionSpace (blockWeight b) I n) := by
  let φ := sectionFactor (blockWeight b) I (Ideal.span {f} ⊔ I) le_sup_right n
  have hinj : Function.Injective φ := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    change Ideal.Quotient.mk I p = x.1 at hpx
    have hz : Ideal.Quotient.mk (Ideal.span {f} ⊔ I) p = 0 := by
      have hxv := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      change (Ideal.Quotient.factorₐ K le_sup_right) x.1 = 0 at hxv
      change (Ideal.Quotient.factorₐ K le_sup_right) (Ideal.Quotient.mk I p) = 0
      rw [hpx]
      exact hxv
    have hpI := mem_step_of_not_le b I hI f p hf
      (show p.IsWeightedHomogeneous (blockWeight b) n from hp) hnd
      (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    apply Subtype.ext
    change x.1 = 0
    rw [← hpx]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpI
  exact (LinearEquiv.ofBijective φ
    ⟨hinj, sectionFactor_surjective (blockWeight b) I _ le_sup_right n⟩).finrank_eq.symm

/-- The multigraded Hilbert series of an ideal. -/
def series (b : σ → κ) (I : Ideal (MvPolynomial σ K)) : MvPowerSeries κ ℤ :=
  fun d => (Module.finrank K (sectionSpace (blockWeight b) I d) : ℤ)

@[simp] theorem series_coeff (b : σ → κ) (I : Ideal (MvPolynomial σ K)) (d : κ →₀ ℕ) :
    MvPowerSeries.coeff d (series b I) =
      (Module.finrank K (sectionSpace (blockWeight b) I d) : ℤ) := rfl

/-- Multivariate series form of the weighted colon recurrence. -/
theorem series_colon_step [Finite σ] (b : σ → κ) (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b)))
    (i : σ) :
    series b I = series b (Ideal.span {MvPolynomial.X i} ⊔ I) +
      MvPowerSeries.X (b i) * series b (I.colon {MvPolynomial.X i}) := by
  classical
  ext d
  rw [map_add, MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul]
  simp only [series_coeff, one_mul]
  by_cases hd : Finsupp.single (b i) 1 ≤ d
  · rw [ite_eq_left hd]
    have h := colon_rank_step (blockWeight b) I hI (MvPolynomial.X i)
      (MvPolynomial.isWeightedHomogeneous_X K (blockWeight b) i)
      (d - Finsupp.single (b i) 1)
    have hdadd : d - Finsupp.single (b i) 1 + blockWeight b i = d := by
      exact tsub_add_cancel_of_le hd
    have h' :
        Module.finrank K (sectionSpace (blockWeight b) (Ideal.span {MvPolynomial.X i} ⊔ I) d) +
          Module.finrank K (sectionSpace (blockWeight b) (I.colon {MvPolynomial.X i})
            (d - Finsupp.single (b i) 1)) =
        Module.finrank K (sectionSpace (blockWeight b) I d) := by
      exact Eq.mp (congrArg (fun q : κ →₀ ℕ =>
        Module.finrank K (sectionSpace (blockWeight b) (Ideal.span {MvPolynomial.X i} ⊔ I) q) +
          Module.finrank K (sectionSpace (blockWeight b) (I.colon {MvPolynomial.X i})
            (d - Finsupp.single (b i) 1)) =
        Module.finrank K (sectionSpace (blockWeight b) I q)) hdadd) h
    exact_mod_cast h'.symm
  · rw [ite_eq_right hd, add_zero]
    exact_mod_cast (section_rank_step_of_not_le b I hI (MvPolynomial.X i)
      (MvPolynomial.isWeightedHomogeneous_X K (blockWeight b) i) hd).symm

/-- OAI's iterated colon construction also preserves the multigrading. -/
theorem iteratedColon_weighted (b : σ → κ) (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b)))
    (i : σ) (m : ℕ) :
    (OAI.PiExponentJets.W64.iteratedColon I (MvPolynomial.X i) m).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b)) := by
  induction m with
  | zero => exact hI
  | succ m ih =>
    exact homogeneous_colon (blockWeight b) _ ih
      (MvPolynomial.isWeightedHomogeneous_X K (blockWeight b) i)

/-- Telescope the finite portion of a multigraded colon chain. -/
theorem series_telescope [Finite σ] (b : σ → κ) (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b)))
    (i : σ) (m : ℕ) :
    series b I =
      (∑ j ∈ Finset.range m, MvPowerSeries.X (b i) ^ j *
        series b (Ideal.span {MvPolynomial.X i} ⊔
          OAI.PiExponentJets.W64.iteratedColon I (MvPolynomial.X i) j)) +
      MvPowerSeries.X (b i) ^ m *
        series b (OAI.PiExponentJets.W64.iteratedColon I (MvPolynomial.X i) m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs := series_colon_step b (OAI.PiExponentJets.W64.iteratedColon I (MvPolynomial.X i) m)
      (iteratedColon_weighted b I hI i m) i
    simp only [← OAI.PiExponentJets.W64.iteratedColon_succ] at hs
    rw [ih, hs, Finset.sum_range_succ, pow_succ]
    ring

/-- A stabilized colon chain gives a finite numerator after one denominator factor. -/
theorem series_stabilized [Finite σ] (b : σ → κ) (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b)))
    (i : σ) (m : ℕ)
    (hstable : OAI.PiExponentJets.W64.iteratedColon I (MvPolynomial.X i) (m + 1) =
      OAI.PiExponentJets.W64.iteratedColon I (MvPolynomial.X i) m) :
    (1 - MvPowerSeries.X (b i)) * series b I =
      (∑ j ∈ Finset.range m, MvPowerSeries.X (b i) ^ j *
        ((1 - MvPowerSeries.X (b i)) *
          series b (Ideal.span {MvPolynomial.X i} ⊔
            OAI.PiExponentJets.W64.iteratedColon I (MvPolynomial.X i) j))) +
      MvPowerSeries.X (b i) ^ m *
        series b (Ideal.span {MvPolynomial.X i} ⊔
          OAI.PiExponentJets.W64.iteratedColon I (MvPolynomial.X i) m) := by
  have hs := series_colon_step b (OAI.PiExponentJets.W64.iteratedColon I (MvPolynomial.X i) m)
    (iteratedColon_weighted b I hI i m) i
  change _ = _ + MvPowerSeries.X (b i) *
    series b (OAI.PiExponentJets.W64.iteratedColon I (MvPolynomial.X i) (m + 1)) at hs
  rw [hstable] at hs
  have he : (1 - MvPowerSeries.X (b i)) *
      series b (OAI.PiExponentJets.W64.iteratedColon I (MvPolynomial.X i) m) =
      series b (Ideal.span {MvPolynomial.X i} ⊔
        OAI.PiExponentJets.W64.iteratedColon I (MvPolynomial.X i) m) := by
    linear_combination hs
  rw [series_telescope b I hI i m, mul_add, Finset.mul_sum]
  simp_rw [← mul_assoc,
    mul_comm ((1 : MvPowerSeries κ ℤ) - MvPowerSeries.X (b i)) (MvPowerSeries.X (b i) ^ _),
    mul_assoc]
  rw [he]

/-- Denominator with one standard multigraded factor for each ambient variable. -/
def denominator [Fintype σ] (b : σ → κ) : MvPolynomial κ ℤ :=
  ∏ i : σ, (1 - MvPolynomial.X (b i))

theorem series_rename {τ : Type*} (e : σ ≃ τ) (b : σ → κ)
    (I : Ideal (MvPolynomial σ K)) :
    series b I = series (b ∘ e.symm) (I.map (MvPolynomial.rename e).toRingHom) := by
  ext d
  simp only [series_coeff]
  exact congrArg (fun n : ℕ => (n : ℤ))
    (renameQuotient_section_finrank (blockWeight b) e I d)

theorem series_coordinate {τ : Type*} (b : Option τ → κ)
    (I : Ideal (MvPolynomial (Option τ) K)) (hX : MvPolynomial.X none ∈ I) :
    series b I = series (b ∘ Option.some)
      (OAI.PiExponentSiegel.W08.coordinateImageIdeal I) := by
  ext d
  simp only [series_coeff]
  exact congrArg (fun n : ℕ => (n : ℤ))
    (coordinateQuotient_section_finrank (blockWeight b) I hX d)

theorem blockPiece_no_variables [IsEmpty σ] (b : σ → κ) (d : κ →₀ ℕ) (hd : d ≠ 0) :
    MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b) d = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro p hp
  change p = 0
  apply MvPolynomial.IsWeightedHomogeneous.eq_zero_of_no_monomials hp
  intro a
  rw [weight_blockWeight]
  have ha : a = 0 := Subsingleton.elim _ _
  simpa [ha] using hd.symm

theorem series_no_variables [IsEmpty σ] (b : σ → κ) (I : Ideal (MvPolynomial σ K)) :
    series b I = MvPowerSeries.C
      (Module.finrank K (sectionSpace (blockWeight b) I 0) : ℤ) := by
  classical
  ext d
  by_cases hd : d = 0
  · subst d
    simp
  · rw [series_coeff, MvPowerSeries.coeff_C, ite_eq_right hd]
    have hz : sectionSpace (blockWeight b) I d = ⊥ := by
      rw [sectionSpace, blockPiece_no_variables b d hd, Submodule.map_bot]
    rw [hz]
    simp

/-- Multigraded Hilbert–Serre, by the same variable-elimination argument as OAI's
single-graded theorem. The numerator records every finite colon chain. -/
theorem exists_numerator (σ : Type*) [Fintype σ] (b : σ → κ)
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b))) :
    ∃ P : MvPolynomial κ ℤ,
      (denominator b : MvPowerSeries κ ℤ) * series b I = P := by
  classical
  refine Fintype.induction_empty_option
    (P := fun τ _ => ∀ (b : τ → κ) (J : Ideal (MvPolynomial τ K)),
      J.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b)) →
      ∃ P : MvPolynomial κ ℤ,
        (denominator b : MvPowerSeries κ ℤ) * series b J = P)
    ?_ ?_ ?_ σ b I hI
  · intro α β _ e ih b J hJ
    letI : Fintype α := Fintype.ofEquiv β e.symm
    obtain ⟨P, hP⟩ := ih (b ∘ e) (J.map (MvPolynomial.rename e.symm).toRingHom)
      (renameImageIdeal_weighted (blockWeight b) e.symm J hJ)
    refine ⟨P, ?_⟩
    rw [series_rename e.symm b J]
    have hD : denominator (b ∘ e) = denominator b := by
      exact e.prod_comp (fun j => (1 - MvPolynomial.X (b j) : MvPolynomial κ ℤ))
    rw [hD] at hP
    exact hP
  · intro b J hJ
    refine ⟨MvPolynomial.C (Module.finrank K (sectionSpace (blockWeight b) J 0) : ℤ), ?_⟩
    simp only [denominator, Fintype.prod_empty, MvPolynomial.coe_one, one_mul,
      series_no_variables, MvPolynomial.coe_C]
  · intro α _ ih b J hJ
    let f : MvPolynomial (Option α) K := MvPolynomial.X none
    obtain ⟨m, hm⟩ := OAI.PiExponentJets.W06.exists_colon_pow_stable J f
    have hstable : OAI.PiExponentJets.W64.iteratedColon J f (m + 1) =
        OAI.PiExponentJets.W64.iteratedColon J f m := by
      simpa only [OAI.PiExponentJets.W64.iteratedColon_eq_colon_power] using hm
    let Jlower : ℕ → Ideal (MvPolynomial (Option α) K) :=
      fun j => Ideal.span {f} ⊔ OAI.PiExponentJets.W64.iteratedColon J f j
    have hlower : ∀ j, (Jlower j).IsHomogeneous
        (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b)) := by
      intro j
      apply Ideal.IsHomogeneous.sup
      · apply Ideal.homogeneous_span
        intro g hg
        obtain rfl := Set.mem_singleton_iff.mp hg
        exact ⟨blockWeight b none, MvPolynomial.isWeightedHomogeneous_X _ _ _⟩
      · exact iteratedColon_weighted b J hJ none j
    have hX : ∀ j, MvPolynomial.X none ∈ Jlower j := by
      intro j
      have hinc : Ideal.span {f} ≤ Jlower j := le_sup_left
      exact hinc (Ideal.subset_span (Set.mem_singleton f))
    choose P hP using fun j => ih (b ∘ Option.some)
      (OAI.PiExponentSiegel.W08.coordinateImageIdeal (Jlower j))
      (coordinateImageIdeal_weighted (blockWeight b) (Jlower j) (hlower j))
    have hseries : ∀ j,
        (denominator (b ∘ Option.some) : MvPowerSeries κ ℤ) * series b (Jlower j) = P j := by
      intro j
      rw [series_coordinate b (Jlower j) (hX j)]
      exact hP j
    let A : MvPolynomial κ ℤ := 1 - MvPolynomial.X (b none)
    let Pout : MvPolynomial κ ℤ :=
      (∑ j ∈ Finset.range m, MvPolynomial.X (b none) ^ j * (A * P j)) +
        MvPolynomial.X (b none) ^ m * P m
    refine ⟨Pout, ?_⟩
    have hD : denominator b = A * denominator (b ∘ Option.some) := by
      simp [denominator, Fintype.prod_option, A]
    rw [hD, MvPolynomial.coe_mul]
    have hs := series_stabilized b J hJ none m hstable
    have hA : (A : MvPowerSeries κ ℤ) = 1 - MvPowerSeries.X (b none) := by
      change MvPolynomial.coeToMvPowerSeries.ringHom
        ((1 : MvPolynomial κ ℤ) - MvPolynomial.X (b none)) = _
      rw [map_sub, map_one, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
        MvPolynomial.coe_X]
    rw [← hA] at hs
    change (A : MvPowerSeries κ ℤ) * series b J =
      (∑ j ∈ Finset.range m, MvPowerSeries.X (b none) ^ j *
        ((A : MvPowerSeries κ ℤ) * series b (Jlower j))) +
      MvPowerSeries.X (b none) ^ m * series b (Jlower m) at hs
    rw [mul_comm (A : MvPowerSeries κ ℤ)
      (denominator (b ∘ Option.some) : MvPowerSeries κ ℤ), mul_assoc,
      hs, mul_add, Finset.mul_sum]
    have hrearr (j : ℕ) :
        (denominator (b ∘ Option.some) : MvPowerSeries κ ℤ) *
          (MvPowerSeries.X (b none) ^ j * ((A : MvPowerSeries κ ℤ) * series b (Jlower j))) =
        MvPowerSeries.X (b none) ^ j * ((A : MvPowerSeries κ ℤ) * (P j : MvPowerSeries κ ℤ)) := by
      rw [← hseries j]
      ring
    simp_rw [hrearr]
    rw [mul_left_comm, hseries m]
    change _ = MvPolynomial.coeToMvPowerSeries.ringHom Pout
    simp only [Pout, map_add, map_sum, map_mul, map_pow,
      MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X]

end BlockWeights



section RectangularSeries

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Product coefficients on independent coordinates. -/
def rectSeries (A : κ → PowerSeries ℤ) : MvPowerSeries κ ℤ :=
  fun d => ∏ j : κ, PowerSeries.coeff (d j) (A j)

@[simp] theorem rectSeries_coeff (A : κ → PowerSeries ℤ) (d : κ →₀ ℕ) :
    MvPowerSeries.coeff d (rectSeries A) = ∏ j : κ, PowerSeries.coeff (d j) (A j) := rfl

theorem rectSeries_one : rectSeries (fun _ : κ => (1 : PowerSeries ℤ)) = 1 := by
  ext d
  by_cases hd : d = 0
  · subst d
    simp
  · obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
      by_contra h
      apply hd
      ext j
      simpa using not_exists.mp h j
    rw [rectSeries_coeff, MvPowerSeries.coeff_one, ite_eq_right hd]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [PowerSeries.coeff_one, hj])

/-- Multiplying by a coordinate denominator acts only on that coordinate's series. -/
theorem rectSeries_factor (A : κ → PowerSeries ℤ) (i : κ) :
    (1 - MvPowerSeries.X i) * rectSeries A =
      rectSeries (Function.update A i ((1 - PowerSeries.X) * A i)) := by
  classical
  ext d
  let rest : ℤ := ∏ j ∈ Finset.univ.erase i, PowerSeries.coeff (d j) (A j)
  have hfull : (∏ j : κ, PowerSeries.coeff (d j) (A j)) =
      PowerSeries.coeff (d i) (A i) * rest :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
  have hright :
      (∏ j : κ, PowerSeries.coeff (d j)
        (Function.update A i ((1 - PowerSeries.X) * A i) j)) =
      PowerSeries.coeff (d i) ((1 - PowerSeries.X) * A i) * rest := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hminus : (∏ j : κ, PowerSeries.coeff ((d - Finsupp.single i 1 : κ →₀ ℕ) j) (A j)) =
      PowerSeries.coeff (d i - 1) (A i) * rest := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj), Nat.sub_zero]
  have hc : PowerSeries.coeff (d i) ((1 - PowerSeries.X) * A i) =
      PowerSeries.coeff (d i) (A i) -
        if 1 ≤ d i then PowerSeries.coeff (d i - 1) (A i) else 0 := by
    rw [sub_mul, one_mul, map_sub, ← pow_one (PowerSeries.X : PowerSeries ℤ),
      PowerSeries.coeff_X_pow_mul']
  rw [sub_mul, one_mul, map_sub, MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul]
  simp only [rectSeries_coeff, one_mul, Finsupp.single_le_iff]
  rw [hfull, hright, hc]
  by_cases hd : 1 ≤ d i
  · rw [ite_eq_left hd, ite_eq_left hd, hminus]
    ring
  · rw [ite_eq_right hd, ite_eq_right hd]
    ring

/-- Iterating a coordinate denominator preserves the separated coefficient form. -/
theorem rectSeries_factor_pow (A : κ → PowerSeries ℤ) (i : κ) (n : ℕ) :
    (1 - MvPowerSeries.X i) ^ n * rectSeries A =
      rectSeries (Function.update A i ((1 - PowerSeries.X) ^ n * A i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, rectSeries_factor]
    congr 1
    ext j
    by_cases hj : j = i
    · subst j
      simp [pow_succ', mul_assoc]
    · simp [Function.update_of_ne hj]

/-- Apply all coordinate denominators to a product of their individual inverses. -/
theorem rectSeries_denominator (n : κ → ℕ) (A : κ → PowerSeries ℤ)
    (hA : ∀ j, (1 - PowerSeries.X) ^ n j * A j = 1) :
    (∏ j : κ, (1 - MvPowerSeries.X j) ^ n j) * rectSeries A = 1 := by
  have h (S : Finset κ) :
      (∏ j ∈ S, (1 - MvPowerSeries.X j) ^ n j) * rectSeries A =
        rectSeries (fun j => if j ∈ S then 1 else A j) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi, mul_assoc, ih, rectSeries_factor_pow]
      congr 1
      ext j
      by_cases hj : j = i
      · subst j
        simp [hi, hA]
      · simp [hj]
  simpa only [Finset.mem_univ, ite_eq_left, rectSeries_one] using h Finset.univ

def inverseDenominator (n : κ → ℕ) : MvPowerSeries κ ℤ :=
  rectSeries (fun j => (PowerSeries.invOneSubPow ℤ (n j)).val)

theorem invOneSubPow_coeff_multichoose (n d : ℕ) :
    PowerSeries.coeff d (PowerSeries.invOneSubPow ℤ n).val = (n.multichoose d : ℤ) := by
  cases n with
  | zero =>
    cases d <;> simp [PowerSeries.invOneSubPow_zero]
  | succ n =>
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk,
      Nat.multichoose_eq]
    congr 1
    have h : n + 1 + d - 1 = n + d := by omega
    rw [h, Nat.choose_symm_add]

@[simp] theorem inverseDenominator_coeff (n : κ → ℕ) (d : κ →₀ ℕ) :
    MvPowerSeries.coeff d (inverseDenominator n) =
      ∏ j : κ, ((n j).multichoose (d j) : ℤ) := by
  simp [inverseDenominator, invOneSubPow_coeff_multichoose]

/-- Number of ambient variables in each multigraded block. -/
def blockCount {σ : Type*} [Fintype σ] (b : σ → κ) (j : κ) : ℕ :=
  (Finset.univ.filter (fun i => b i = j)).card

theorem denominator_blocks {σ : Type*} [Fintype σ] (b : σ → κ) :
    denominator b = ∏ j : κ, (1 - MvPolynomial.X j) ^ blockCount b j := by
  classical
  simpa only [denominator, blockCount, Finset.prod_const] using
    (Finset.prod_fiberwise' Finset.univ b
      (fun j => (1 - MvPolynomial.X j : MvPolynomial κ ℤ))).symm

theorem denominator_inverse {σ : Type*} [Fintype σ] (b : σ → κ) :
    (denominator b : MvPowerSeries κ ℤ) * inverseDenominator (blockCount b) = 1 := by
  rw [denominator_blocks]
  change MvPolynomial.coeToMvPowerSeries.ringHom
    (∏ j : κ, (1 - MvPolynomial.X j) ^ blockCount b j) * inverseDenominator _ = _
  simp only [map_prod, map_pow, map_sub, map_one,
    MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X]
  apply rectSeries_denominator
  intro j
  have h := PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val
    ℤ 0 (blockCount b j)
  simpa [PowerSeries.invOneSubPow_zero] using h

/-- Coefficients of a finite numerator over a product denominator are eventually
polynomial. The single-factor polynomials are reused from the OAI theorem. -/
theorem coefficients_eventually_polynomial (n : κ → ℕ) (P : MvPolynomial κ ℤ) :
    ∃ Q : MvPolynomial κ ℚ, ∃ N : ℕ, ∀ d : κ →₀ ℕ,
      (∀ j, N ≤ d j) →
      MvPolynomial.eval (fun j => (d j : ℚ)) Q =
        ((MvPowerSeries.coeff d ((P : MvPowerSeries κ ℤ) * inverseDenominator n) : ℤ) : ℚ) := by
  classical
  choose U NU hU using fun j : κ => ambientBlockPolynomial (n j)
  let N : ℕ := P.totalDegree + (∑ j : κ, NU j) + 1
  let Q : MvPolynomial κ ℚ :=
    ∑ a ∈ P.support, MvPolynomial.C (P.coeff a : ℚ) *
      ∏ j : κ, ((U j).comp (Polynomial.X - Polynomial.C (a j : ℚ))).toMvPolynomial j
  refine ⟨Q, N, ?_⟩
  intro d hd
  have hbounds (a : κ →₀ ℕ) (ha : a ∈ P.support) (j : κ) :
      a j ≤ d j ∧ NU j ≤ d j - a j := by
    have ha' : a j ≤ P.totalDegree := by
      calc a j ≤ ∑ j : κ, a j :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        _ = a.degree := (Finsupp.degree_eq_sum a).symm
        _ ≤ P.totalDegree := MvPolynomial.le_totalDegree ha
    have hNU : NU j ≤ ∑ j : κ, NU j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hdj := hd j
    dsimp [N] at hdj
    omega
  have hcoef :
      MvPowerSeries.coeff d ((P : MvPowerSeries κ ℤ) * inverseDenominator n) =
        ∑ a ∈ P.support, P.coeff a *
          ∏ j : κ, ((n j).multichoose (d j - a j) : ℤ) := by
    change MvPowerSeries.coeff d
      (MvPolynomial.coeToMvPowerSeries.ringHom P * inverseDenominator n) = _
    conv_lhs => rw [P.as_sum]
    rw [map_sum, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have had : a ≤ d := fun j => (hbounds a ha j).1
    rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial,
      MvPowerSeries.coeff_monomial_mul, ite_eq_left had, inverseDenominator_coeff]
    simp only [Finsupp.tsub_apply]
  rw [hcoef]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_prod, Int.cast_natCast]
  change MvPolynomial.eval (fun j => (d j : ℚ))
    (∑ a ∈ P.support, MvPolynomial.C (P.coeff a : ℚ) *
      ∏ j : κ, ((U j).comp (Polynomial.X - Polynomial.C (a j : ℚ))).toMvPolynomial j) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [MvPolynomial.eval_toMvPolynomial, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, ← Nat.cast_sub (hbounds a ha j).1,
    hU j (d j - a j) (hbounds a ha j).2]

/-- Eventual multigraded Hilbert polynomial existence for any standard block grading. -/
theorem exists_polynomial {σ : Type*} [Fintype σ] (b : σ → κ)
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K (blockWeight b))) :
    ∃ Q : MvPolynomial κ ℚ, ∃ N : ℕ, ∀ d : κ →₀ ℕ,
      (∀ j, N ≤ d j) →
      MvPolynomial.eval (fun j => (d j : ℚ)) Q =
        (Module.finrank K (sectionSpace (blockWeight b) I d) : ℚ) := by
  obtain ⟨P, hP⟩ := exists_numerator σ b I hI
  obtain ⟨Q, N, hQ⟩ := coefficients_eventually_polynomial (blockCount b) P
  refine ⟨Q, N, ?_⟩
  have hs : series b I = (P : MvPowerSeries κ ℤ) * inverseDenominator (blockCount b) := by
    calc
      series b I = ((denominator b : MvPowerSeries κ ℤ) *
          inverseDenominator (blockCount b)) * series b I := by
        rw [denominator_inverse, one_mul]
      _ = ((denominator b : MvPowerSeries κ ℤ) * series b I) *
          inverseDenominator (blockCount b) := by ring
      _ = _ := by rw [hP]
  intro d hd
  have h := hQ d hd
  rw [← hs, series_coeff, Int.cast_natCast] at h
  exact h

end RectangularSeries


end HilbertMulti

namespace HilbertMulti

def pairBlocks (n m : ℕ) : Fin (n + m) → Fin 2 :=
  Fin.addCases (fun _ => 0) (fun _ => 1)

def tripleBlocks (n m o : ℕ) : Fin (n + m + o) → Fin 3 :=
  Fin.addCases (Fin.addCases (fun _ => 0) (fun _ => 1)) (fun _ => 2)

def pairDegree (s t : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => if j = 0 then s else t)

def tripleDegree (s t u : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => if j = 0 then s else if j = 1 then t else u)

theorem mapDomain_fin_apply {n : ℕ} {κ : Type*} [DecidableEq κ] (b : Fin n → κ)
    (a : Fin n →₀ ℕ) (j : κ) :
    (a.mapDomain b) j = ∑ i : Fin n, if b i = j then a i else 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finsupp.single_apply, eq_comm]

theorem pairBlockPiece (n m s t : ℕ) :
    MvPolynomial.weightedHomogeneousSubmodule ℂ (blockWeight (pairBlocks n m))
      (pairDegree s t) =
    MvPolynomial.restrictSupport ℂ {a : Fin (n + m) →₀ ℕ |
      (∑ i : Fin n, a (Fin.castAdd m i)) = s ∧
      (∑ i : Fin m, a (Fin.natAdd n i)) = t} := by
  rw [blockPiece_eq]
  congr 1
  ext a
  constructor
  · intro h
    have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
    have h1 := congrArg (fun d : Fin 2 →₀ ℕ => d 1) h
    simp [mapDomain_fin_apply, Fin.sum_univ_add, pairBlocks, pairDegree] at h0 h1
    exact ⟨h0, h1⟩
  · intro h
    ext j
    fin_cases j <;>
      simp [mapDomain_fin_apply, Fin.sum_univ_add, pairBlocks, pairDegree, h.1, h.2]

theorem tripleBlockPiece (n m o s t u : ℕ) :
    MvPolynomial.weightedHomogeneousSubmodule ℂ (blockWeight (tripleBlocks n m o))
      (tripleDegree s t u) =
    MvPolynomial.restrictSupport ℂ {a : Fin (n + m + o) →₀ ℕ |
      (∑ i : Fin n, a (Fin.castAdd o (Fin.castAdd m i))) = s ∧
      (∑ i : Fin m, a (Fin.castAdd o (Fin.natAdd n i))) = t ∧
      (∑ i : Fin o, a (Fin.natAdd (n + m) i)) = u} := by
  rw [blockPiece_eq]
  congr 1
  ext a
  constructor
  · intro h
    have h0 := congrArg (fun d : Fin 3 →₀ ℕ => d 0) h
    have h1 := congrArg (fun d : Fin 3 →₀ ℕ => d 1) h
    have h2 := congrArg (fun d : Fin 3 →₀ ℕ => d 2) h
    simp [mapDomain_fin_apply, Fin.sum_univ_add, tripleBlocks, tripleDegree] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  · intro h
    ext j
    fin_cases j <;>
      simp [mapDomain_fin_apply, Fin.sum_univ_add, tripleBlocks, tripleDegree,
        h.1, h.2.1, h.2.2]

end HilbertMulti

namespace IncidenceLocal

open LinearMap (BilinForm)

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- Alternating forms over the ring of a base chart. -/
def alternatingSubmodule : Submodule A (BilinForm A M) where
  carrier := {D | D.IsAlt}
  zero_mem' := LinearMap.BilinForm.isAlt_zero
  add_mem' := fun hD hE => hD.add hE
  smul_mem' := fun c _ hD => hD.smul c

/-- The covectors annihilating the chosen direction. -/
def directionAnnihilator (v : M) : Submodule A (Module.Dual A M) where
  carrier := {y | y v = 0}
  zero_mem' := rfl
  add_mem' := by
    intro y z hy hz
    change (y + z) v = 0
    change y v = 0 at hy
    change z v = 0 at hz
    simp only [LinearMap.add_apply, hy, hz, add_zero]
  smul_mem' := by
    intro c y hy
    change (c • y) v = 0
    change y v = 0 at hy
    simp only [LinearMap.smul_apply, hy, smul_zero]

/-- An anchor with l(v)=1 gives an evaluation section over any commutative ring. -/
def anchoredForm (l y : Module.Dual A M) : BilinForm A M :=
  LinearMap.BilinForm.linMulLin l y - LinearMap.BilinForm.linMulLin y l

theorem anchoredForm_isAlt (l y : Module.Dual A M) : (anchoredForm l y).IsAlt := by
  intro x
  simp only [anchoredForm, LinearMap.sub_apply, LinearMap.BilinForm.linMulLin_apply]
  ring

theorem anchoredForm_evaluate (v : M) (l : Module.Dual A M) (hl : l v = 1)
    (y : Module.Dual A M) (hy : y v = 0) : anchoredForm l y v = y := by
  ext x
  simp only [anchoredForm, LinearMap.sub_apply, LinearMap.BilinForm.linMulLin_apply,
    hl, hy, one_mul, zero_mul, sub_zero]

def evaluateDirection (v : M) :
    alternatingSubmodule (A := A) (M := M) →ₗ[A] directionAnnihilator (A := A) v where
  toFun D := ⟨D.1 v, D.2 v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def directionSection (v : M) (l : Module.Dual A M) :
    directionAnnihilator (A := A) v →ₗ[A] alternatingSubmodule (A := A) (M := M) where
  toFun y := ⟨anchoredForm l y.1, anchoredForm_isAlt l y.1⟩
  map_add' y z := by
    apply Subtype.ext
    change anchoredForm l (y.1 + z.1) = anchoredForm l y.1 + anchoredForm l z.1
    ext x w
    simp only [anchoredForm, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.BilinForm.linMulLin_apply]
    ring
  map_smul' c y := by
    apply Subtype.ext
    change anchoredForm l (c • y.1) = c • anchoredForm l y.1
    ext x w
    simp only [anchoredForm, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.BilinForm.linMulLin_apply, smul_eq_mul]
    ring

theorem evaluateDirection_section (v : M) (l : Module.Dual A M) (hl : l v = 1) :
    Function.RightInverse (directionSection v l) (evaluateDirection v) := by
  intro y
  apply Subtype.ext
  exact anchoredForm_evaluate v l hl y.1 y.2

def homogeneousMap (v : M) :
    (A × alternatingSubmodule (A := A) (M := M)) →ₗ[A] (A × directionAnnihilator (A := A) v) :=
  (LinearMap.id : A →ₗ[A] A).prodMap (evaluateDirection v)

def homogeneousSection (v : M) (l : Module.Dual A M) :
    (A × directionAnnihilator (A := A) v) →ₗ[A] (A × alternatingSubmodule (A := A) (M := M)) :=
  (LinearMap.id : A →ₗ[A] A).prodMap (directionSection v l)

theorem homogeneousMap_section (v : M) (l : Module.Dual A M) (hl : l v = 1) :
    Function.RightInverse (homogeneousSection v l) (homogeneousMap v) := by
  intro y
  apply Prod.ext
  · rfl
  · exact evaluateDirection_section v l hl y.2

section Line

variable {E : Type*} [AddCommGroup E] [Module A E]

/-- Split off a tautological line whose chosen coordinate is a unit. -/
def lineProjection (u : E) (r : Module.Dual A E) (hr : r u = 1) :
    E →ₗ[A] LinearMap.ker r where
  toFun x := ⟨x - r x • u, by
    rw [LinearMap.mem_ker, map_sub, map_smul, hr, smul_eq_mul, mul_one, sub_self]⟩
  map_add' x y := by
    apply Subtype.ext
    change x + y - r (x + y) • u = (x - r x • u) + (y - r y • u)
    simp only [map_add, add_smul]
    abel
  map_smul' c x := by
    apply Subtype.ext
    change c • x - r (c • x) • u = c • (x - r x • u)
    simp only [map_smul, smul_sub, smul_smul, smul_eq_mul]

theorem lineProjection_ker (u : E) (r : Module.Dual A E) (hr : r u = 1) :
    LinearMap.ker (lineProjection u r hr) = Submodule.span A {u} := by
  ext x
  constructor
  · intro hx
    have hz := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    change x - r x • u = 0 at hz
    exact Submodule.mem_span_singleton.mpr ⟨r x, (sub_eq_zero.mp hz).symm⟩
  · intro hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    rw [← hc]
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change c • u - r (c • u) • u = 0
    simp [map_smul, hr]

theorem lineProjection_subtype (u : E) (r : Module.Dual A E) (hr : r u = 1)
    (x : LinearMap.ker r) : lineProjection u r hr x.1 = x := by
  apply Subtype.ext
  change x.1 - r x.1 • u = x.1
  rw [LinearMap.mem_ker.mp x.2, zero_smul, sub_zero]

end Line

def quotientEvaluation (v : M) (u : A × directionAnnihilator (A := A) v)
    (r : Module.Dual A (A × directionAnnihilator (A := A) v)) (hr : r u = 1) :
    (A × alternatingSubmodule (A := A) (M := M)) →ₗ[A] LinearMap.ker r :=
  (lineProjection u r hr).comp (homogeneousMap v)

def quotientSection (v : M) (l : Module.Dual A M)
    (r : Module.Dual A (A × directionAnnihilator (A := A) v)) :
    LinearMap.ker r →ₗ[A] (A × alternatingSubmodule (A := A) (M := M)) :=
  (homogeneousSection v l).comp (LinearMap.ker r).subtype

theorem quotientEvaluation_section (v : M) (l : Module.Dual A M) (hl : l v = 1)
    (u : A × directionAnnihilator (A := A) v) (r : Module.Dual A (A × directionAnnihilator (A := A) v))
    (hr : r u = 1) :
    Function.RightInverse (quotientSection v l r) (quotientEvaluation v u r hr) := by
  intro x
  change lineProjection u r hr (homogeneousMap v (homogeneousSection v l x.1)) = x
  rw [homogeneousMap_section v l hl]
  exact lineProjection_subtype u r hr x

theorem quotientEvaluation_ker (v : M) (u : A × directionAnnihilator (A := A) v)
    (r : Module.Dual A (A × directionAnnihilator (A := A) v)) (hr : r u = 1) :
    LinearMap.ker (quotientEvaluation v u r hr) =
      (Submodule.span A {u}).comap (homogeneousMap v) := by
  rw [quotientEvaluation, LinearMap.ker_comp, lineProjection_ker u r hr]

section Pivot

variable {ι : Type*}

/-- The inverse of a unit pivot is an anchor for a coordinate direction. -/
def coordinateAnchor (i : ι) (a : Aˣ) : Module.Dual A (ι → A) :=
  (↑a⁻¹ : A) • LinearMap.proj i

theorem coordinateAnchor_apply (i : ι) (a : Aˣ) (v : ι → A) (hv : v i = a) :
    coordinateAnchor i a v = 1 := by
  simp [coordinateAnchor, LinearMap.smul_apply, LinearMap.proj_apply, hv, smul_eq_mul]

def tailEmbedding : (ι → A) →ₗ[A] (Option ι → A) where
  toFun x := fun i => i.elim 0 x
  map_add' x y := by funext i; cases i <;> simp [Pi.add_apply]
  map_smul' c x := by funext i; cases i <;> simp [smul_eq_mul]

def pivotVector : Option ι → A := fun i => i.elim 1 (fun _ => 0)

theorem pivot_decomposition (x : Option ι → A) :
    x = tailEmbedding (fun i => x (some i)) + x none • (pivotVector : Option ι → A) := by
  funext i
  cases i <;> simp [tailEmbedding, pivotVector, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Deleting a coordinate with unit coefficient identifies a linear kernel with a free module. -/
def kernelTailEquiv (r : Module.Dual A (Option ι → A)) (a : Aˣ)
    (hr : r (pivotVector : Option ι → A) = a) :
    LinearMap.ker r ≃ₗ[A] (ι → A) where
  toFun x := fun i => x.1 (some i)
  invFun x := ⟨tailEmbedding x - ((↑a⁻¹ : A) * r (tailEmbedding x)) • pivotVector, by
    rw [LinearMap.mem_ker, map_sub, map_smul, hr]
    simp only [smul_eq_mul]
    rw [mul_assoc, mul_comm (r (tailEmbedding x)), ← mul_assoc, Units.inv_mul, one_mul, sub_self]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    cases i with
    | some i => simp [tailEmbedding, pivotVector, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    | none =>
      have hzero : r (tailEmbedding (fun i => x.1 (some i))) + x.1 none * (a : A) = 0 := by
        have h := LinearMap.mem_ker.mp x.2
        rw [pivot_decomposition x.1, map_add, map_smul, hr] at h
        simpa only [smul_eq_mul] using h
      have hzero' : (↑a⁻¹ : A) * r (tailEmbedding (fun i => x.1 (some i))) + x.1 none = 0 := by
        have h := congrArg (fun z : A => (↑a⁻¹ : A) * z) hzero
        have hcancel : (↑a⁻¹ : A) * (x.1 none * (a : A)) = x.1 none := by
          calc
            _ = x.1 none * ((↑a⁻¹ : A) * (a : A)) := by ring
            _ = x.1 none := by rw [Units.inv_mul, mul_one]
        simpa only [mul_add, mul_zero, hcancel] using h
      change (tailEmbedding (fun i => x.1 (some i)) -
        ((↑a⁻¹ : A) * r (tailEmbedding (fun i => x.1 (some i)))) •
          (pivotVector : Option ι → A)) none = x.1 none
      simp only [tailEmbedding, LinearMap.coe_mk, AddHom.coe_mk, Option.elim_none,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pivotVector, mul_one, zero_sub]
      change -((↑a⁻¹ : A) * r (tailEmbedding (fun i => x.1 (some i)))) = x.1 none
      linear_combination -hzero'
  right_inv x := by
    funext i
    simp [tailEmbedding, pivotVector, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  map_add' x y := rfl
  map_smul' c x := rfl

section FreeQuotient

variable {E : Type*} [AddCommGroup E] [Module A E]

/-- Transport the unit-pivot kernel identification through a free coordinate frame. -/
def lineKernelEquiv (e : E ≃ₗ[A] (Option ι → A)) (r : Module.Dual A E) (a : Aˣ)
    (hr : r (e.symm pivotVector) = a) : LinearMap.ker r ≃ₗ[A] (ι → A) := by
  let r' := r.comp e.symm.toLinearMap
  let eqv : LinearMap.ker r ≃ₗ[A] LinearMap.ker r' :=
    { toFun := fun x => ⟨e x.1, by
        change r (e.symm (e x.1)) = 0
        rw [e.symm_apply_apply]
        exact x.2⟩
      invFun := fun x => ⟨e.symm x.1, x.2⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.1)
      map_add' := fun x y => Subtype.ext (e.map_add x.1 y.1)
      map_smul' := fun c x => Subtype.ext (e.map_smul c x.1) }
  exact eqv.trans (kernelTailEquiv r' a hr)

/-- On a free quotient chart the incidence equations admit an actual linear section. -/
theorem quotientEvaluation_free_split (v : M) (l : Module.Dual A M) (hl : l v = 1)
    (u : A × directionAnnihilator (A := A) v)
    (r : Module.Dual A (A × directionAnnihilator (A := A) v)) (hr : r u = 1)
    (e : (A × directionAnnihilator (A := A) v) ≃ₗ[A] (Option ι → A))
    (a : Aˣ) (ha : r (e.symm pivotVector) = a) :
    ∃ f : (A × alternatingSubmodule (A := A) (M := M)) →ₗ[A] (ι → A),
      ∃ s : (ι → A) →ₗ[A] (A × alternatingSubmodule (A := A) (M := M)),
        Function.RightInverse s f ∧
          LinearMap.ker f = (Submodule.span A {u}).comap (homogeneousMap v) := by
  let eqv : LinearMap.ker r ≃ₗ[A] (ι → A) :=
    lineKernelEquiv (A := A) (E := A × directionAnnihilator (A := A) v) (ι := ι) e r a ha
  let f := eqv.toLinearMap.comp (quotientEvaluation v u r hr)
  let s := (quotientSection v l r).comp eqv.symm.toLinearMap
  refine ⟨f, s, ?_, ?_⟩
  · intro x
    change eqv (quotientEvaluation v u r hr (quotientSection v l r (eqv.symm x))) = x
    rw [quotientEvaluation_section v l hl u r hr (eqv.symm x), eqv.apply_symm_apply]
  · ext x
    have hzero : eqv (quotientEvaluation v u r hr x) = 0 ↔ quotientEvaluation v u r hr x = 0 := by
      constructor
      · intro h
        exact eqv.injective (by simpa using h)
      · intro h
        rw [h, map_zero]
    change eqv (quotientEvaluation v u r hr x) = 0 ↔ _
    rw [hzero]
    change x ∈ LinearMap.ker (quotientEvaluation v u r hr) ↔ _
    rw [quotientEvaluation_ker v u r hr]

end FreeQuotient

section AnnihilatorCoordinates

variable [Fintype ι] [DecidableEq ι]

/-- A unit direction pivot makes its covector-annihilator module free over the chart ring. -/
def directionAnnihilatorEquiv (v : Option ι → A) (a : Aˣ) (hv : v none = a) :
    directionAnnihilator (A := A) v ≃ₗ[A] (ι → A) := by
  let e : Module.Dual A (Option ι → A) ≃ₗ[A] (Option ι → A) :=
    (Pi.basisFun A (Option ι)).dualBasis.equivFun
  let r : Module.Dual A (Option ι → A) :=
    { toFun := fun x => e.symm x v
      map_add' := fun x y => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun c x => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hproj : e (LinearMap.proj none) = (pivotVector : Option ι → A) := by
    ext i
    change (Pi.basisFun A (Option ι)).dualBasis.equivFun (LinearMap.proj none) i = _
    rw [Module.Basis.dualBasis_equivFun, Pi.basisFun_apply]
    cases i <;> simp [LinearMap.proj_apply, Pi.single_apply, pivotVector]
  have hr : r (pivotVector : Option ι → A) = a := by
    change e.symm pivotVector v = a
    rw [← hproj, LinearEquiv.symm_apply_apply]
    exact hv
  let eqv : directionAnnihilator (A := A) v ≃ₗ[A] LinearMap.ker r :=
    { toFun := fun y => ⟨e y.1, by
        change e.symm (e y.1) v = 0
        rw [LinearEquiv.symm_apply_apply]
        exact y.2⟩
      invFun := fun x => ⟨e.symm x.1, x.2⟩
      left_inv := fun y => Subtype.ext (e.symm_apply_apply y.1)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.1)
      map_add' := fun y z => Subtype.ext (e.map_add y.1 z.1)
      map_smul' := fun c y => Subtype.ext (e.map_smul c y.1) }
  exact eqv.trans (kernelTailEquiv r a hr)

end AnnihilatorCoordinates

end Pivot

section ChartTorsion

variable {n m : ℕ} {D : Type*} [AddCommGroup D]
  [Module (MvPolynomial (Fin (n + m)) A) D]

/-- Finitely many coordinate charts admit a common torsion exponent for each element. -/
theorem uniformChartPower (u : D)
    (hchart : ∀ (i : Fin n) (j : Fin m), ∃ N : ℕ,
      ((MvPolynomial.X (Fin.castAdd m i) * MvPolynomial.X (Fin.natAdd n j)) ^ N :
        MvPolynomial (Fin (n + m)) A) • u = 0) :
    ∃ N : ℕ, ∀ (i : Fin n) (j : Fin m),
      ((MvPolynomial.X (Fin.castAdd m i) * MvPolynomial.X (Fin.natAdd n j)) ^ N :
        MvPolynomial (Fin (n + m)) A) • u = 0 := by
  classical
  choose ns hns using hchart
  let N := Finset.univ.sup (fun ij : Fin n × Fin m => ns ij.1 ij.2)
  refine ⟨N, ?_⟩
  intro i j
  have hle : ns i j ≤ N := Finset.le_sup
    (f := fun ij : Fin n × Fin m => ns ij.1 ij.2) (Finset.mem_univ (i, j))
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, Nat.add_comm (ns i j) k, pow_add, mul_smul, hns i j, smul_zero]

/-- Uniform chart-product torsion kills polynomial multiples in large block degrees. -/
theorem blockPiece_smul_zero (u : D) (N s t : ℕ)
    (hchart : ∀ (i : Fin n) (j : Fin m),
      ((MvPolynomial.X (Fin.castAdd m i) * MvPolynomial.X (Fin.natAdd n j)) ^ N :
        MvPolynomial (Fin (n + m)) A) • u = 0)
    (hs : n * N + 1 ≤ s) (ht : m * N + 1 ≤ t)
    (f : MvPolynomial (Fin (n + m)) A)
    (hf : f ∈ MvPolynomial.restrictSupport A {d : Fin (n + m) →₀ ℕ |
      (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
        (∑ j : Fin m, d (Fin.natAdd n j)) = t}) : f • u = 0 := by
  classical
  have hsupport : (f.support : Set (Fin (n + m) →₀ ℕ)) ⊆
      {d | (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
        (∑ j : Fin m, d (Fin.natAdd n j)) = t} := hf
  have hmono (d : Fin (n + m) →₀ ℕ) (hd : d ∈ f.support) :
      MvPolynomial.monomial d (f.coeff d) • u = 0 := by
    obtain ⟨hl, hr⟩ := hsupport hd
    obtain ⟨i, hi⟩ : ∃ i : Fin n, N < d (Fin.castAdd m i) := by
      by_contra h
      push Not at h
      have hh : (∑ i : Fin n, d (Fin.castAdd m i)) ≤ n * N := by
        calc
          _ ≤ ∑ _i : Fin n, N := Finset.sum_le_sum (fun i _ => h i)
          _ = n * N := by simp
      omega
    obtain ⟨j, hj⟩ : ∃ j : Fin m, N < d (Fin.natAdd n j) := by
      by_contra h
      push Not at h
      have hh : (∑ j : Fin m, d (Fin.natAdd n j)) ≤ m * N := by
        calc
          _ ≤ ∑ _j : Fin m, N := Finset.sum_le_sum (fun j _ => h j)
          _ = m * N := by simp
      omega
    let a := Fin.castAdd m i
    let b := Fin.natAdd n j
    have hab : a ≠ b := by
      intro heq
      have hval := congrArg Fin.val heq
      change i.val = n + j.val at hval
      have hil := i.isLt
      omega
    let p := Finsupp.single a N + Finsupp.single b N
    have hp : p ≤ d := by
      intro k
      simp only [p, Finsupp.add_apply, Finsupp.single_apply]
      split_ifs with hak hbk <;> subst_vars <;> simp_all [a, b] <;> omega
    let d' := d - p
    have hdecomp : d' + Finsupp.single a N + Finsupp.single b N = d := by
      rw [add_assoc]
      exact tsub_add_cancel_of_le hp
    have hfactor : MvPolynomial.monomial d (f.coeff d) =
        MvPolynomial.monomial d' (f.coeff d) *
          ((MvPolynomial.X a * MvPolynomial.X b) ^ N : MvPolynomial (Fin (n + m)) A) := by
      rw [← hdecomp, MvPolynomial.monomial_add_single, MvPolynomial.monomial_add_single,
        mul_pow, mul_assoc]
    rw [hfactor, mul_smul, hchart i j, smul_zero]
  rw [f.as_sum, Finset.sum_smul]
  exact Finset.sum_eq_zero (fun d hd => hmono d hd)

end ChartTorsion

section ComplexFiber

variable {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]

/-- The chart-ring inverse image specializes to the actual fiber in GeometryModel. -/
theorem incidenceFiber_eq_lineInverse (v : U) (t : ℂ)
    (y : directionAnnihilator (A := ℂ) v) :
    incidenceFiber v t y.1 =
      (Submodule.span ℂ {(t, y)}).comap (homogeneousMap (A := ℂ) v) := by
  ext x
  change homogeneousEvaluation v x ∈ Submodule.span ℂ {(t, y.1)} ↔
    homogeneousMap (A := ℂ) v x ∈ Submodule.span ℂ {(t, y)}
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    apply Prod.ext
    · exact congrArg (fun z : ℂ × Module.Dual ℂ U => z.1) hc
    · apply Subtype.ext
      exact congrArg Prod.snd hc
  · intro hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    apply Prod.ext
    · exact congrArg (fun z : ℂ × directionAnnihilator (A := ℂ) v => z.1) hc
    · exact congrArg Subtype.val (congrArg Prod.snd hc)

theorem actual_incidence_kernel (v : U) (t : ℂ)
    (y : directionAnnihilator (A := ℂ) v)
    (r : Module.Dual ℂ (ℂ × directionAnnihilator (A := ℂ) v))
    (hr : r (t, y) = 1) :
    LinearMap.ker (quotientEvaluation v (t, y) r hr) = incidenceFiber v t y.1 := by
  rw [quotientEvaluation_ker v (t, y) r hr, ← incidenceFiber_eq_lineInverse]

theorem actual_incidence_quotient_surjective (v : U) (l : Module.Dual ℂ U) (hl : l v = 1)
    (t : ℂ) (y : directionAnnihilator (A := ℂ) v)
    (r : Module.Dual ℂ (ℂ × directionAnnihilator (A := ℂ) v)) (hr : r (t, y) = 1) :
    Function.Surjective (quotientEvaluation v (t, y) r hr) :=
  (quotientEvaluation_section v l hl (t, y) r hr).surjective

end ComplexFiber

section ScalarRatio

variable {n : ℕ}

/-- Clear the negative direction twist on the direction ideal using the parameter minors. -/
theorem scalarRatio_on_directionIdeal (d v : Fin n → A)
    (hminor : ∀ i j, d i * v j = d j * v i)
    (hsaturated : ∀ z : A, (∀ i, d i * z = 0) → z = 0) :
    ∃ τ : LinearMap.range (Fintype.linearCombination A d) →ₗ[A] A,
      ∀ c : Fin n → A,
        τ ⟨Fintype.linearCombination A d c, ⟨c, rfl⟩⟩ = Fintype.linearCombination A v c := by
  let D := Fintype.linearCombination A d
  let V := Fintype.linearCombination A v
  have hker : LinearMap.ker D ≤ LinearMap.ker V := by
    intro c hc
    apply LinearMap.mem_ker.mpr
    apply hsaturated
    intro j
    have hzero := LinearMap.mem_ker.mp hc
    change D c = 0 at hzero
    simp only [D, Fintype.linearCombination_apply, smul_eq_mul] at hzero
    change d j * V c = 0
    simp only [V, Fintype.linearCombination_apply, smul_eq_mul]
    calc
      d j * ∑ i, c i * v i = ∑ i, c i * (d j * v i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i, c i * (d i * v j) := by simp_rw [hminor j]
      _ = (∑ i, c i * d i) * v j := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hzero, zero_mul]
  let q := (LinearMap.ker D).liftQ V hker
  let τ := q.comp D.quotKerEquivRange.symm.toLinearMap
  refine ⟨τ, ?_⟩
  intro c
  change q (D.quotKerEquivRange.symm ⟨D c, ⟨c, rfl⟩⟩) = V c
  have hm : D.quotKerEquivRange.symm ⟨D c, ⟨c, rfl⟩⟩ = (LinearMap.ker D).mkQ c := by
    apply D.quotKerEquivRange.injective
    rw [D.quotKerEquivRange.apply_symm_apply]
    rfl
  rw [hm]
  rfl

/-- The last map of the parameter complex contains every tautological coordinate in its image. -/
theorem scalarRatio_coordinate_range (d v y : Fin n → A)
    (τ : LinearMap.range (Fintype.linearCombination A d) →ₗ[A] A)
    (hτ : ∀ c : Fin n → A,
      τ ⟨Fintype.linearCombination A d c, ⟨c, rfl⟩⟩ = Fintype.linearCombination A v c)
    (i : Fin n) :
    v i ∈ LinearMap.range (τ.coprod (Fintype.linearCombination A y)) ∧
      y i ∈ LinearMap.range (τ.coprod (Fintype.linearCombination A y)) := by
  classical
  constructor
  · refine ⟨(⟨Fintype.linearCombination A d (Pi.single i 1), ⟨Pi.single i 1, rfl⟩⟩, 0), ?_⟩
    rw [LinearMap.coprod_apply, hτ, map_zero, add_zero]
    simp [Fintype.linearCombination_apply, Pi.single_apply]
  · refine ⟨(0, Pi.single i 1), ?_⟩
    rw [LinearMap.coprod_apply, map_zero, zero_add]
    simp [Fintype.linearCombination_apply, Pi.single_apply]

end ScalarRatio

section RegularVariables

variable {σ : Type*}

/-- Eliminating a disjoint group of coordinate variables preserves regularity of the next one. -/
theorem mul_X_mem_variableIdeal_iff (S : Set σ) (i : σ) (hi : i ∉ S)
    (f : MvPolynomial σ A) :
    f * MvPolynomial.X i ∈ Ideal.span (MvPolynomial.X '' S : Set (MvPolynomial σ A)) ↔
      f ∈ Ideal.span (MvPolynomial.X '' S : Set (MvPolynomial σ A)) := by
  classical
  constructor
  · intro hf
    apply MvPolynomial.mem_ideal_span_X_image.mpr
    intro d hd
    have hd' : d + Finsupp.single i 1 ∈ (f * MvPolynomial.X i).support := by
      apply MvPolynomial.mem_support_iff.mpr
      rw [MvPolynomial.coeff_mul_X]
      exact MvPolynomial.mem_support_iff.mp hd
    obtain ⟨j, hj, hpos⟩ := MvPolynomial.mem_ideal_span_X_image.mp hf _ hd'
    have hij : i ≠ j := by rintro rfl; exact hi hj
    refine ⟨j, hj, ?_⟩
    simpa only [Finsupp.add_apply, Finsupp.single_apply, if_neg hij, add_zero] using hpos
  · intro hf
    exact Ideal.mul_mem_right _ _ hf

theorem variable_mod_ideal_regular (S : Set σ) (i : σ) (hi : i ∉ S) :
    IsRightRegular (Ideal.Quotient.mk
      (Ideal.span (MvPolynomial.X '' S : Set (MvPolynomial σ A))) (MvPolynomial.X i)) := by
  let I := Ideal.span (MvPolynomial.X '' S : Set (MvPolynomial σ A))
  intro x y hxy
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  change Ideal.Quotient.mk I f * Ideal.Quotient.mk I (MvPolynomial.X i) =
    Ideal.Quotient.mk I g * Ideal.Quotient.mk I (MvPolynomial.X i) at hxy
  apply Ideal.Quotient.eq.mpr
  apply (mul_X_mem_variableIdeal_iff S i hi (f - g)).mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_mul, map_sub, sub_mul, hxy, sub_self]

theorem ideal_of_variable_list (l : List σ) :
    Ideal.ofList (l.map (MvPolynomial.X : σ → MvPolynomial σ A)) =
      Ideal.span (MvPolynomial.X '' {i | i ∈ l} : Set (MvPolynomial σ A)) := by
  unfold Ideal.ofList
  congr 1
  ext f
  simp

/-- Distinct polynomial fiber variables are regular over any nonzero base ring. -/
theorem variables_regular [Nontrivial A] (l : List σ) (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (MvPolynomial σ A) (l.map (MvPolynomial.X : σ → MvPolynomial σ A)) := by
  classical
  let P := MvPolynomial σ A
  refine { regular_mod_prev := ?_, top_ne_smul := ?_ }
  · intro i hi
    have hil : i < l.length := by simpa only [List.length_map] using hi
    let S : Set σ := {j | j ∈ l.take i}
    have hnot : l[i] ∉ S := by
      intro hm
      obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hm
      have hki : k < i := by rw [List.length_take] at hk; omega
      have hkl : k < l.length := lt_trans hki hil
      have he' : l[k] = l[i] := by simpa only [List.getElem_take] using he
      have hsame := hl.getElem_inj_iff.mp he'
      omega
    have hI : Ideal.ofList ((l.map (MvPolynomial.X : σ → P)).take i) =
        Ideal.span (MvPolynomial.X '' S : Set P) := by
      rw [← List.map_take, ideal_of_variable_list]
    have hmul : (Ideal.ofList ((l.map (MvPolynomial.X : σ → P)).take i) •
        (⊤ : Submodule P P)) = Ideal.ofList ((l.map (MvPolynomial.X : σ → MvPolynomial σ A)).take i) :=
      Ideal.mul_top _
    rw [hmul, hI]
    simp only [List.getElem_map]
    have hreg := variable_mod_ideal_regular (A := A) S l[i] hnot
    intro x y hxy
    apply hreg
    change Ideal.Quotient.mk (Ideal.span (MvPolynomial.X '' S : Set P)) (MvPolynomial.X l[i]) * x =
      Ideal.Quotient.mk (Ideal.span (MvPolynomial.X '' S : Set P)) (MvPolynomial.X l[i]) * y at hxy
    simpa only [mul_comm] using hxy
  · intro htop
    have hone : (1 : P) ∈ Ideal.ofList (l.map (MvPolynomial.X : σ → MvPolynomial σ A)) := by
      have heq : (⊤ : Submodule P P) = Ideal.ofList (l.map (MvPolynomial.X : σ → MvPolynomial σ A)) := by
        exact htop.trans (Ideal.mul_top _)
      rw [← heq]
      trivial
    rw [ideal_of_variable_list] at hone
    obtain ⟨i, hi, hnonzero⟩ := MvPolynomial.mem_ideal_span_X_image.mp hone 0 (by simp)
    simpa using hnonzero

/-- Reuse OAI's Koszul exactness, now with the singular-base fiber variables proved regular. -/
theorem variables_koszul_exact [Nontrivial A] (l : List σ) (hl : l.Nodup) :
    ∃ ε : (OAI.PiExponentSiegelAux.W30.regularSequenceComplex
        (l.map (MvPolynomial.X : σ → MvPolynomial σ A))).X 0 →ₗ[MvPolynomial σ A]
          (MvPolynomial σ A ⧸ Ideal.ofList (l.map (MvPolynomial.X : σ → MvPolynomial σ A))),
      Function.Surjective ε ∧
      LinearMap.range ((OAI.PiExponentSiegelAux.W30.regularSequenceComplex
        (l.map (MvPolynomial.X : σ → MvPolynomial σ A))).d 1 0).hom = LinearMap.ker ε ∧
      ∀ q, LinearMap.range ((OAI.PiExponentSiegelAux.W30.regularSequenceComplex
        (l.map (MvPolynomial.X : σ → MvPolynomial σ A))).d (q + 2) (q + 1)).hom =
        LinearMap.ker ((OAI.PiExponentSiegelAux.W30.regularSequenceComplex
          (l.map (MvPolynomial.X : σ → MvPolynomial σ A))).d (q + 1) q).hom :=
  OAI.PiExponentSiegelAux.W30.regularSequenceComplex_exact _ (variables_regular l hl)

end RegularVariables

end IncidenceLocal

#print axioms IncidenceLocal.evaluateDirection_section
#print axioms IncidenceLocal.quotientEvaluation_section
#print axioms IncidenceLocal.quotientEvaluation_ker
#print axioms IncidenceLocal.kernelTailEquiv
#print axioms IncidenceLocal.directionAnnihilatorEquiv
#print axioms IncidenceLocal.quotientEvaluation_free_split
#print axioms IncidenceLocal.uniformChartPower
#print axioms IncidenceLocal.blockPiece_smul_zero
#print axioms IncidenceLocal.actual_incidence_kernel
#print axioms IncidenceLocal.scalarRatio_on_directionIdeal
#print axioms IncidenceLocal.scalarRatio_coordinate_range
#print axioms IncidenceLocal.variables_regular
#print axioms IncidenceLocal.variables_koszul_exact

end
end DistinctDistances.TrackB
