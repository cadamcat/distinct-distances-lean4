import DistinctDistances.TrackA.GenericLinearCutSupport
import DistinctDistances.OAIInterface.ReducedTensor

set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Reduced scalar extension is detected on the actual finite collection
of minimal-prime quotients, rather than assumed for the whole ring. -/
theorem reduced_tensor_of_minimal_prime_quotients {K R E : Type}
    [Field K] [CommRing R] [Algebra K R] [IsReduced R] [IsNoetherianRing R]
    [CommRing E] [Algebra K E]
    (hprime : ∀ p ∈ (⊥ : Ideal R).minimalPrimes, IsReduced (E ⊗[K] (R ⧸ p))) :
    IsReduced (E ⊗[K] R) := by
  let Q := (⊥ : Ideal R).minimalPrimes
  let : Fintype Q := (Ideal.finite_minimalPrimes_of_isNoetherianRing R (⊥ : Ideal R)).fintype
  let B : Q → Type := fun q => R ⧸ q.val
  let f : R →ₐ[K] ∀ q : Q, B q := AlgHom.pi fun q => Ideal.Quotient.mkₐ K q.val
  have hf : Function.Injective f := by
    intro x y h
    have hz : x-y ∈ (⊥ : Ideal R).radical := by
      rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
      intro p hp
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
      exact sub_eq_zero.mpr (congrFun h ⟨p, hp⟩)
    rw [Ideal.isRadical_bot.radical, Ideal.mem_bot] at hz
    exact sub_eq_zero.mp hz
  let g : E ⊗[K] R →ₐ[K] E ⊗[K] (∀ q : Q, B q) :=
    Algebra.TensorProduct.map (AlgHom.id K E) f
  have hg : Function.Injective g :=
    Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  let : ∀ q : Q, IsReduced (E ⊗[K] B q) := fun q => hprime q.val q.property
  let e := Algebra.TensorProduct.piRight K E E B
  let : IsReduced (E ⊗[K] (∀ q : Q, B q)) := isReduced_of_injective e e.injective
  exact isReduced_of_injective g hg

/-- Over an algebraically closed coefficient field, each prime quotient's
scalar extension is a domain by the original OpenAI tensor theorem. -/
theorem reduced_tensor_over_algClosed {K R E : Type}
    [Field K] [IsAlgClosed K] [CommRing R] [Algebra K R]
    [IsReduced R] [IsNoetherianRing R] [CommRing E] [IsDomain E] [Algebra K E] :
    IsReduced (E ⊗[K] R) := by
  apply reduced_tensor_of_minimal_prime_quotients
  intro p hp
  let : p.IsPrime := hp.isPrime
  let : IsDomain (E ⊗[K] (R ⧸ p)) :=
    OAI.MaximalSeshadri.BertiniIntegral.tensorProduct_isDomain_general
  infer_instance

/-- Finite domain extensions preserve reducedness in characteristic zero.
Apply the original finite-domain result to each actual prime quotient. -/
theorem reduced_tensor_finite_domain_charZero {K R E : Type}
    [Field K] [CharZero K] [CommRing R] [Algebra K R]
    [IsReduced R] [IsNoetherianRing R] [CommRing E] [IsDomain E] [Algebra K E]
    [Module.Finite K E] : IsReduced (E ⊗[K] R) := by
  apply reduced_tensor_of_minimal_prime_quotients
  intro p hp
  let : p.IsPrime := hp.isPrime
  let : IsReduced ((R ⧸ p) ⊗[K] E) :=
    OAI.BoundaryOnly.FormalObstruction.AlgebraicReplacement.AnalyticReducedness.reduced_flat_domain_tensor
  let e := Algebra.TensorProduct.comm K E (R ⧸ p)
  exact isReduced_of_injective e e.injective

/-- Algebraic scalar extension is obtained from finite generated integral
subalgebras; reducedness is detected on their actual tensor inclusions. -/
theorem reduced_tensor_algebraic_charZero {K R E : Type}
    [Field K] [CharZero K] [CommRing R] [Algebra K R]
    [IsReduced R] [IsNoetherianRing R] [Field E] [Algebra K E]
    [Algebra.IsAlgebraic K E] : IsReduced (E ⊗[K] R) := by
  let : IsReduced (R ⊗[K] E) := by
    apply IsReduced.tensorProduct_of_flat_of_forall_fg
    intro B hB
    let : Algebra.FiniteType K B := (B.fg_iff_finiteType).mp hB
    let : Algebra.IsIntegral K B := ⟨fun x =>
      (isIntegral_algHom_iff B.val Subtype.val_injective).mp
        (Algebra.IsAlgebraic.isAlgebraic x.val).isIntegral⟩
    let : Module.Finite K B := Algebra.IsIntegral.finite
    let : IsReduced (B ⊗[K] R) := reduced_tensor_finite_domain_charZero
    let e := Algebra.TensorProduct.comm K R B
    exact isReduced_of_injective e e.injective
  let e := Algebra.TensorProduct.comm K E R
  exact isReduced_of_injective e e.injective

/-- The finite type characteristic-zero scalar-extension result consumed
by generic hyperplane chart specialization. Algebraic closure separates
the finite separable part from the algebraically closed domain case. -/
theorem reduced_tensor_charZero_finiteType {K R E : Type}
    [Field K] [CharZero K] [CommRing R] [Algebra K R]
    [IsReduced R] [Algebra.FiniteType K R] [Field E] [Algebra K E] :
    IsReduced (E ⊗[K] R) := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  let Ω := AlgebraicClosure K
  let F := AlgebraicClosure E
  let A := Ω ⊗[K] R
  let : IsReduced A := reduced_tensor_algebraic_charZero
  let : Algebra.FiniteType Ω A := inferInstance
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing Ω A
  let f : Ω →ₐ[K] F := IsAlgClosed.lift
  let : Algebra Ω F := f.toRingHom.toAlgebra
  let : IsScalarTower K Ω F :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let : IsReduced (F ⊗[Ω] A) := reduced_tensor_over_algClosed
  let e := Algebra.TensorProduct.cancelBaseChange K Ω F F R
  let : IsReduced (F ⊗[K] R) := isReduced_of_injective e.symm e.symm.injective
  let g : E ⊗[K] R →ₐ[K] F ⊗[K] R :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E F) (AlgHom.id K R)
  have hg : Function.Injective g :=
    Module.Flat.rTensor_preserves_injective_linearMap
      (IsScalarTower.toAlgHom K E F).toLinearMap (RingHom.injective (algebraMap E F))
  exact isReduced_of_injective g hg

/-- The universal linear cut on a finite type reduced chart has reduced
geometric generic fiber in characteristic zero. This is the scalar
extension step needed before specialization into the complex numbers. -/
abbrev universalLinearGeometricRing {K R σ : Type}
    [Field K] [CommRing R] [Algebra K R] [Fintype σ]
    (v : σ → R) (E : Type) [Field E] [Algebra (FractionRing (MvPolynomial σ K)) E] :=
  let P := MvPolynomial σ K
  let F := FractionRing P
  let G := universalLinearGenericRing (K := K) v
  let _ : Algebra F G := Algebra.TensorProduct.leftAlgebra
  E ⊗[F] G

instance universalLinearGeometricRing_commRing {K R σ : Type}
    [Field K] [CommRing R] [Algebra K R] [Fintype σ]
    (v : σ → R) (E : Type) [Field E] [Algebra (FractionRing (MvPolynomial σ K)) E] :
    CommRing (universalLinearGeometricRing (K := K) v E) := by
  let P := MvPolynomial σ K
  let F := FractionRing P
  let G := universalLinearGenericRing (K := K) v
  let : CommRing G := inferInstance
  let : Algebra F G := Algebra.TensorProduct.leftAlgebra
  change CommRing (E ⊗[F] G)
  infer_instance

/-- Actual geometric generic reducedness, with the canonical coefficient
field action fixed in the tensor-ring definition. -/
theorem universalLinearEquation_geometric_generic_reduced {K R σ : Type}
    [Field K] [CharZero K] [CommRing R] [Algebra K R]
    [IsReduced R] [Algebra.FiniteType K R] [Fintype σ]
    (v : σ → R) (i : σ) (hv : IsUnit (v i))
    (E : Type) [Field E] [Algebra (FractionRing (MvPolynomial σ K)) E] :
    IsReduced (universalLinearGeometricRing (K := K) v E) := by
  let P := MvPolynomial σ K
  let F := FractionRing P
  let Q := MvPolynomial σ R ⧸ Ideal.span {universalLinearEquation v}
  let G := universalLinearGenericRing (K := K) v
  let : Algebra F G := Algebra.TensorProduct.leftAlgebra
  let : Algebra.FiniteType P (MvPolynomial σ R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K P (MvPolynomial σ R)
  let : Algebra.FiniteType P Q := inferInstance
  let : Algebra.FiniteType F G := inferInstance
  let : IsReduced G := universalLinearEquation_generic_reduced v i hv
  exact reduced_tensor_charZero_finiteType (K := F) (R := G) (E := E)

end
end DistinctDistances.TrackA
