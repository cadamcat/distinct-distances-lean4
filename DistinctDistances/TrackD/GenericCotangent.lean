import DistinctDistances.TrackD.Genericity
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

variable {d : ℕ}

def coordinateFieldMap (I : Ideal (Poly d)) (K : Type*) [Field K]
    [Algebra ℂ K] [Algebra (Poly d ⧸ I) K] [IsScalarTower ℂ (Poly d ⧸ I) K] :
    Poly d →ₐ[ℂ] K :=
  (IsScalarTower.toAlgHom ℂ (Poly d ⧸ I) K).comp (Ideal.Quotient.mkₐ ℂ I)

theorem coordinateFieldMap_kernel (I : Ideal (Poly d)) (K : Type*) [Field K]
    [Algebra ℂ K] [Algebra (Poly d ⧸ I) K] [IsScalarTower ℂ (Poly d ⧸ I) K]
    [IsFractionRing (Poly d ⧸ I) K] : RingHom.ker (coordinateFieldMap I K) = I := by
  ext f
  change algebraMap (Poly d ⧸ I) K (Ideal.Quotient.mk I f) = 0 ↔ f ∈ I
  rw [← (algebraMap (Poly d ⧸ I) K).map_zero,
    (IsFractionRing.injective (Poly d ⧸ I) K).eq_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

theorem polynomial_fraction_representation (I : Ideal (Poly d)) (K : Type*) [Field K]
    [Algebra ℂ K] [Algebra (Poly d ⧸ I) K] [IsScalarTower ℂ (Poly d ⧸ I) K]
    [IsFractionRing (Poly d ⧸ I) K] (z : K) :
    ∃ a b : Poly d, coordinateFieldMap I K b ≠ 0 ∧
      coordinateFieldMap I K a = coordinateFieldMap I K b * z := by
  letI : Nontrivial (Poly d ⧸ I) := (algebraMap (Poly d ⧸ I) K).domain_nontrivial
  obtain ⟨r, s, hs, heq⟩ := IsFractionRing.div_surjective (Poly d ⧸ I) z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective s
  have hb : coordinateFieldMap I K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  refine ⟨a, b, hb, ?_⟩
  change coordinateFieldMap I K a / coordinateFieldMap I K b = z at heq
  exact ((div_eq_iff hb).mp heq).trans (mul_comm _ _)

/-- Clear the denominators of a finite family of function-field values simultaneously. -/
theorem polynomial_common_denominator (I : Ideal (Poly d)) (K : Type*) [Field K]
    [Algebra ℂ K] [Algebra (Poly d ⧸ I) K] [IsScalarTower ℂ (Poly d ⧸ I) K]
    [IsFractionRing (Poly d ⧸ I) K] {ι : Type*} (s : Finset ι) (z : ι → K) :
    ∃ q : Poly d, ∃ a : ι → Poly d, coordinateFieldMap I K q ≠ 0 ∧
      ∀ i ∈ s, coordinateFieldMap I K (a i) = coordinateFieldMap I K q * z i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun _ => 0, by simp, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨q, a, hq, ha⟩ := ih
    obtain ⟨r, t, ht, hrt⟩ := polynomial_fraction_representation I K (z i)
    refine ⟨q * t, fun j => if j = i then q * r else t * a j, ?_, ?_⟩
    · simpa only [map_mul] using mul_ne_zero hq ht
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simp only [ite_true, map_mul, hrt]
        ring
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        simp only [hji, ite_false, map_mul, ha j hj]
        ring

/-- Derivations of polynomial evaluations are determined by their coordinate values. -/
theorem derivation_poly_eval (K : Type*) [Field K] [Algebra ℂ K]
    (φ : Poly d →ₐ[ℂ] K) (δ : Derivation ℂ K K) (f : Poly d) :
    δ (φ f) = ∑ i : Fin d, φ (MvPolynomial.pderiv i f) * δ (φ (MvPolynomial.X i)) := by
  letI : Algebra (Poly d) K := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ (Poly d) K := IsScalarTower.of_algHom φ
  let δ' := δ.compAlgebraMap (Poly d)
  have hs := (KaehlerDifferential.mvPolynomialBasis ℂ (Fin d)).sum_repr
    (KaehlerDifferential.D ℂ (Poly d) f)
  have he := congrArg δ'.liftKaehlerDifferential hs
  simp only [map_sum, map_smul, KaehlerDifferential.mvPolynomialBasis_repr_apply,
    KaehlerDifferential.mvPolynomialBasis_apply,
    Derivation.liftKaehlerDifferential_comp_D] at he
  simp only [δ', Derivation.compAlgebraMap_apply, Algebra.smul_def] at he
  change (∑ i : Fin d, φ (MvPolynomial.pderiv i f) * δ (φ (MvPolynomial.X i))) = δ (φ f) at he
  exact he.symm

def velocityPairing (f : Poly d) (a : Fin d → Poly d) : Poly d :=
  ∑ i, MvPolynomial.pderiv i f * a i

@[simp] theorem eval_velocityPairing (f : Poly d) (a : Fin d → Poly d) (x : Point d) :
    MvPolynomial.eval x (velocityPairing f a) =
      differential f x (fun i => MvPolynomial.eval x (a i)) := by
  simp [velocityPairing, differential, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]

theorem image_velocityPairing (K : Type*) [Field K] [Algebra ℂ K]
    (φ : Poly d →ₐ[ℂ] K) (δ : Derivation ℂ K K) (q : Poly d) (a : Fin d → Poly d)
    (ha : ∀ i, φ (a i) = φ q * δ (φ (MvPolynomial.X i))) (f : Poly d) :
    φ (velocityPairing f a) = φ q * δ (φ f) := by
  rw [derivation_poly_eval K φ δ f, Finset.mul_sum]
  simp only [velocityPairing, map_sum, map_mul, ha]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A function-field derivation gives a polynomial tangent vector after clearing its
coordinate denominators. Generic tangent identities apply to that vector. -/
theorem generic_tangent_scalar_pairing (X : AffineVariety d) (hX : X.IsIrreducible)
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (Poly d ⧸ X.ideal) K]
    [IsScalarTower ℂ (Poly d ⧸ X.ideal) K] [IsFractionRing (Poly d ⧸ X.ideal) K]
    (δ : Derivation ℂ K K) (a b : Poly d)
    (h : ForGeneralPoint X (fun x => ∀ v ∈ X.tangentSpace x,
      MvPolynomial.eval x b * differential a x v -
        MvPolynomial.eval x a * differential b x v = 0)) :
    coordinateFieldMap X.ideal K b * δ (coordinateFieldMap X.ideal K a) -
      coordinateFieldMap X.ideal K a * δ (coordinateFieldMap X.ideal K b) = 0 := by
  let φ := coordinateFieldMap X.ideal K
  have hker : RingHom.ker φ = X.ideal := coordinateFieldMap_kernel X.ideal K
  obtain ⟨q, nums, hq, hnums⟩ := polynomial_common_denominator X.ideal K
    (Finset.univ : Finset (Fin d)) (fun i => δ (φ (MvPolynomial.X i)))
  have hn : ∀ i, φ (nums i) = φ q * δ (φ (MvPolynomial.X i)) :=
    fun i => hnums i (Finset.mem_univ i)
  have ht : ∀ x ∈ X, (fun i => MvPolynomial.eval x (nums i)) ∈ X.tangentSpace x := by
    intro x hx
    simp only [AffineVariety.tangentSpace, Submodule.mem_iInf, LinearMap.mem_ker]
    intro f
    have hfmem : f.val ∈ RingHom.ker φ := by
      rw [hker]
      exact f.property
    have hf : φ f.val = 0 := RingHom.mem_ker.mp hfmem
    have hv : φ (velocityPairing f.val nums) = 0 := by
      rw [image_velocityPairing K φ δ q nums hn, hf, map_zero, mul_zero]
    have hi : velocityPairing f.val nums ∈ X.ideal :=
      (SetLike.ext_iff.mp hker _).mp (RingHom.mem_ker.mpr hv)
    simpa only [eval_velocityPairing] using
      (mem_ideal_iff_eval_zero X _).mp hi x hx
  let F := b * velocityPairing a nums - a * velocityPairing b nums
  have hFG : ForGeneralPoint X (fun x => MvPolynomial.eval x F = 0) :=
    h.mono (fun x hx hxs => by
      simpa only [F, map_sub, map_mul, eval_velocityPairing] using
        hxs (fun i => MvPolynomial.eval x (nums i)) (ht x hx))
  have hFI : F ∈ X.ideal :=
    (mem_ideal_iff_eval_zero X F).mpr (ForGeneralPoint.eval_zero hX F hFG)
  have hFmem : F ∈ RingHom.ker φ := by
    rw [hker]
    exact hFI
  have hF0 : φ F = 0 := RingHom.mem_ker.mp hFmem
  have hm : φ q * (φ b * δ (φ a) - φ a * δ (φ b)) = 0 := by
    calc
      _ = φ F := by
        simp only [F, map_sub, map_mul, image_velocityPairing K φ δ q nums hn]
        ring
      _ = 0 := hF0
  exact (mul_eq_zero.mp hm).resolve_left hq

/-- The generic tangent criterion in the actual fraction field of the shared coordinate
ring. No generic smoothness, dimension convention, or cotangent bridge is assumed. -/
theorem generic_tangent_differential (X : AffineVariety d) (hX : X.IsIrreducible)
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (Poly d ⧸ X.ideal) K]
    [IsScalarTower ℂ (Poly d ⧸ X.ideal) K] [IsFractionRing (Poly d ⧸ X.ideal) K]
    (a b : Poly d)
    (h : ForGeneralPoint X (fun x => ∀ v ∈ X.tangentSpace x,
      MvPolynomial.eval x b * differential a x v -
        MvPolynomial.eval x a * differential b x v = 0)) :
    coordinateFieldMap X.ideal K b •
        KaehlerDifferential.D ℂ K (coordinateFieldMap X.ideal K a) -
      coordinateFieldMap X.ideal K a •
        KaehlerDifferential.D ℂ K (coordinateFieldMap X.ideal K b) = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff K _).mp
  intro l
  have hs := generic_tangent_scalar_pairing X hX K
    (l.compDer (KaehlerDifferential.D ℂ K)) a b h
  change coordinateFieldMap X.ideal K b *
      l (KaehlerDifferential.D ℂ K (coordinateFieldMap X.ideal K a)) -
    coordinateFieldMap X.ideal K a *
      l (KaehlerDifferential.D ℂ K (coordinateFieldMap X.ideal K b)) = 0 at hs
  simpa only [map_sub, map_smul, smul_eq_mul] using hs

end
end DistinctDistances.TrackD
