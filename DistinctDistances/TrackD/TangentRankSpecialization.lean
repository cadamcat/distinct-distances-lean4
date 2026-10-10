import DistinctDistances.TrackD.FieldTangent
import DistinctDistances.TrackD.GenericMatrixRank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Prod

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

set_option maxHeartbeats 800000

/-- Rank of a map on another map's kernel, expressed using a stacked map.
This form specializes through polynomial matrices. -/
theorem finrank_map_kernel_add_range (K V W U : Type*) [Field K]
    [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]
    [Module K V] [Module K W] [Module K U] [Module.Finite K V]
    (f : V →ₗ[K] W) (g : V →ₗ[K] U) :
    Module.finrank K ((LinearMap.ker f).map g) +
      Module.finrank K (LinearMap.range f) =
        Module.finrank K (LinearMap.range (f.prod g)) := by
  have hrestrict := (g.domRestrict (LinearMap.ker f)).finrank_range_add_finrank_ker
  have hf := f.finrank_range_add_finrank_ker
  have hprod := (f.prod g).finrank_range_add_finrank_ker
  have hker : LinearMap.ker (g.domRestrict (LinearMap.ker f)) =
      (LinearMap.ker f ⊓ LinearMap.ker g).comap (LinearMap.ker f).subtype := by
    ext v
    simp [LinearMap.mem_ker, v.property]
  have hequiv := Submodule.comapSubtypeEquivOfLe
    (show LinearMap.ker f ⊓ LinearMap.ker g ≤ LinearMap.ker f from inf_le_left)
  rw [LinearMap.range_domRestrict, hker, hequiv.finrank_eq] at hrestrict
  rw [LinearMap.ker_prod] at hprod
  omega

def idealJacobian {n r : ℕ} (p : Fin r → Poly n) :
    Matrix (Fin r) (Fin n) (Poly n) := fun i j => MvPolynomial.pderiv j (p i)

/-- A finite ideal generating list gives all tangent equations over any receiving
field, including ordinary complex points and the coordinate function field. -/
theorem idealJacobian_kernel {n r : ℕ} (I : Ideal (Poly n))
    (p : Fin r → Poly n) (hp : Ideal.span (Set.range p) = I)
    (K : Type*) [Field K] [Algebra ℂ K] (φ : Poly n →ₐ[ℂ] K)
    (hφ : ∀ f ∈ I, φ f = 0) :
    LinearMap.ker ((idealJacobian p).map φ).mulVecLin = fieldTangent I K φ := by
  letI : Algebra (Poly n) K := φ.toRingHom.toAlgebra
  letI : Module (Poly n) K := (φ.toRingHom.toAlgebra).toModule
  letI : IsScalarTower ℂ (Poly n) K := IsScalarTower.of_algHom φ
  ext v
  rw [mem_fieldTangent]
  constructor
  · intro hv
    let δ := MvPolynomial.mkDerivation ℂ v
    have hδ : ∀ f : Poly n, δ f = ∑ i : Fin n, φ (MvPolynomial.pderiv i f) * v i := by
      intro f
      simpa [δ, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using mk_derivation_sum K v f
    have hzero : ∀ f ∈ Ideal.span (Set.range p), φ f = 0 ∧ δ f = 0 := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨i, rfl⟩ := hf
        have hi : p i ∈ I := hp ▸ Ideal.subset_span ⟨i, rfl⟩
        refine ⟨hφ (p i) hi, ?_⟩
        rw [hδ]
        have he := congrFun (LinearMap.mem_ker.mp hv) i
        simpa [idealJacobian, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using he
      | zero => simp
      | add f h hf hh ihf ihh => simp [map_add, ihf, ihh]
      | smul a f hf ih =>
        change φ (a * f) = 0 ∧ δ (a * f) = 0
        simp [map_mul, δ.leibniz, Algebra.smul_def, RingHom.algebraMap_toAlgebra, ih]
    intro f hf
    rw [← hδ]
    exact (hzero f (hp.symm ▸ hf)).2
  · intro hv
    apply LinearMap.mem_ker.mpr
    funext i
    have hi : p i ∈ I := hp ▸ Ideal.subset_span ⟨i, rfl⟩
    simpa [idealJacobian, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
      using hv (p i) hi

theorem fieldTangent_at_point {n : ℕ} (X : AffineVariety n) (x : Point n) :
    fieldTangent X.ideal ℂ (MvPolynomial.aeval x) = X.tangentSpace x := by
  ext v
  rw [mem_fieldTangent]
  simp only [AffineVariety.tangentSpace, Submodule.mem_iInf, LinearMap.mem_ker,
    differential, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul]
  exact ⟨fun h f => h f.val f.property, fun h f hf => h ⟨f, hf⟩⟩

end
end DistinctDistances.TrackD
