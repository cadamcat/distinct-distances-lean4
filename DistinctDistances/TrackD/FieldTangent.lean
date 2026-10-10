import DistinctDistances.TrackD.DerivationExtensions
import DistinctDistances.TrackD.RationalImages

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

set_option maxHeartbeats 600000

/-- Tangent equations evaluated in a field receiving the coordinate ring. -/
def fieldTangent {n : ℕ} (I : Ideal (Poly n)) (K : Type*) [Field K] [Algebra ℂ K]
    (φ : Poly n →ₐ[ℂ] K) : Submodule K (Fin n → K) :=
  ⨅ p : I, LinearMap.ker
    (∑ i : Fin n, φ (MvPolynomial.pderiv i p.val) • LinearMap.proj i)

theorem mem_fieldTangent {n : ℕ} (I : Ideal (Poly n)) (K : Type*)
    [Field K] [Algebra ℂ K] (φ : Poly n →ₐ[ℂ] K) (v : Fin n → K) :
    v ∈ fieldTangent I K φ ↔
      ∀ p ∈ I, ∑ i : Fin n, φ (MvPolynomial.pderiv i p) * v i = 0 := by
  simp only [fieldTangent, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  exact ⟨fun h p hp => h ⟨p, hp⟩, fun h p => h p.val p.property⟩

/-- Quotient-rule differential at the coordinate generic point. -/
def fieldRationalDifferential {n m : ℕ} (K : Type*) [Field K] [Algebra ℂ K]
    (φ : Poly n →ₐ[ℂ] K) (f : Fin m → Poly n) (g : Poly n) :
    (Fin n → K) →ₗ[K] (Fin m → K) :=
  LinearMap.pi fun j =>
    (φ g)⁻¹ • (∑ i : Fin n, φ (MvPolynomial.pderiv i (f j)) • LinearMap.proj i) -
      (φ (f j) / (φ g)^2) •
        (∑ i : Fin n, φ (MvPolynomial.pderiv i g) • LinearMap.proj i)

/-- Coordinate tangent vectors over a larger field give derivations of the
smaller coordinate function field with values in that larger field. -/
theorem coordinate_tangent_derivation_into {n : ℕ} (I : Ideal (Poly n))
    (E K : Type*) [Field E] [Field K]
    [Algebra ℂ E] [Algebra ℂ K] [Algebra E K] [IsScalarTower ℂ E K]
    [Algebra (Poly n ⧸ I) E] [Algebra (Poly n ⧸ I) K]
    [IsScalarTower ℂ (Poly n ⧸ I) E] [IsScalarTower ℂ (Poly n ⧸ I) K]
    [IsScalarTower (Poly n ⧸ I) E K] [IsFractionRing (Poly n ⧸ I) E]
    (v : Fin n → K)
    (hv : v ∈ fieldTangent I K
      ((IsScalarTower.toAlgHom ℂ E K).comp (coordinateFieldMap I E))) :
    ∃ δ : Derivation ℂ E K, ∀ i : Fin n,
      δ (coordinateFieldMap I E (MvPolynomial.X i)) = v i := by
  let φ := (IsScalarTower.toAlgHom ℂ E K).comp (coordinateFieldMap I E)
  letI : Algebra (Poly n) K := φ.toRingHom.toAlgebra
  letI : Module (Poly n) K := (φ.toRingHom.toAlgebra).toModule
  letI : IsScalarTower ℂ (Poly n) K := IsScalarTower.of_algHom φ
  let δ := MvPolynomial.mkDerivation ℂ v
  have hδ : ∀ p : Poly n, δ p = ∑ i : Fin n, φ (MvPolynomial.pderiv i p) * v i := by
    intro p
    simpa [δ, φ, coordinateFieldMap, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using
      mk_derivation_sum K v p
  obtain ⟨ε, hε⟩ := derivation_descends ℂ (Poly n) (Poly n ⧸ I) K
    (Ideal.Quotient.mkₐ ℂ I) Ideal.Quotient.mk_surjective
    (by
      intro p z
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      rw [IsScalarTower.algebraMap_apply (Poly n ⧸ I) E K]
      rfl) δ (by
      intro p hp
      rw [hδ]
      exact (mem_fieldTangent I K φ v).mp hv p (Ideal.Quotient.eq_zero_iff_mem.mp hp))
  letI : Algebra.FormallyEtale (Poly n ⧸ I) E :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (Poly n ⧸ I))
  obtain ⟨ζ, hζ⟩ := derivation_extends_localization ℂ (Poly n ⧸ I) E K ε
  refine ⟨ζ, ?_⟩
  intro i
  change ζ (algebraMap (Poly n ⧸ I) E (Ideal.Quotient.mk I (MvPolynomial.X i))) = v i
  exact (hζ (Ideal.Quotient.mk I (MvPolynomial.X i))).trans
    ((hε (MvPolynomial.X i)).trans (MvPolynomial.mkDerivation_X _ _ i))

/-- Characteristic-zero dominance at the function-field level: every tangent
vector of the image has a source tangent lift. The geometric specialization
step uses this theorem, rather than an unproved rank/trdeg formula. -/
theorem field_rational_tangent_surjective {n m : ℕ}
    (I : Ideal (Poly n)) (J : Ideal (Poly m)) (E K : Type*) [Field E] [Field K]
    [Algebra ℂ E] [Algebra ℂ K] [Algebra E K] [IsScalarTower ℂ E K]
    [Algebra (Poly n ⧸ I) K] [IsScalarTower ℂ (Poly n ⧸ I) K]
    [IsFractionRing (Poly n ⧸ I) K]
    [Algebra (Poly m ⧸ J) E] [Algebra (Poly m ⧸ J) K]
    [IsScalarTower ℂ (Poly m ⧸ J) E] [IsScalarTower ℂ (Poly m ⧸ J) K]
    [IsScalarTower (Poly m ⧸ J) E K] [IsFractionRing (Poly m ⧸ J) E]
    [Algebra.FormallySmooth E K]
    (f : Fin m → Poly n) (g : Poly n) (hg : coordinateFieldMap I K g ≠ 0)
    (hcoords : ∀ i : Fin m,
      algebraMap E K (coordinateFieldMap J E (MvPolynomial.X i)) =
        coordinateFieldMap I K (f i) / coordinateFieldMap I K g) :
    fieldTangent J K ((IsScalarTower.toAlgHom ℂ E K).comp (coordinateFieldMap J E)) ≤
      (fieldTangent I K (coordinateFieldMap I K)).map
        (fieldRationalDifferential K (coordinateFieldMap I K) f g) := by
  intro v hv
  obtain ⟨δ, hδ⟩ := coordinate_tangent_derivation_into J E K v hv
  obtain ⟨ζ, hζ⟩ := derivation_extends_smooth_field ℂ E K δ
  let φ := coordinateFieldMap I K
  let u : Fin n → K := fun i => ζ (φ (MvPolynomial.X i))
  refine Submodule.mem_map.mpr ⟨u, ?_, ?_⟩
  · apply (mem_fieldTangent I K φ u).mpr
    intro p hp
    rw [← derivation_poly_eval K φ ζ]
    have hpzero : φ p = 0 := RingHom.mem_ker.mp
      ((coordinateFieldMap_kernel I K).symm ▸ hp)
    rw [hpzero, map_zero]
  · funext i
    have hval : ζ (φ (f i) / φ g) = v i := by
      rw [← hcoords i, hζ, hδ]
    rw [Derivation.leibniz_div, derivation_poly_eval K φ ζ (f i),
      derivation_poly_eval K φ ζ g] at hval
    simp only [fieldRationalDifferential, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.proj_apply, smul_eq_mul]
    change (φ g)⁻¹ * (∑ j : Fin n, φ (MvPolynomial.pderiv j (f i)) * u j) -
      (φ (f i) / (φ g)^2) * (∑ j : Fin n, φ (MvPolynomial.pderiv j g) * u j) = v i
    change (φ g)⁻¹ ^ 2 * ((φ g) *
      (∑ j : Fin n, φ (MvPolynomial.pderiv j (f i)) * u j) -
      (φ (f i)) * (∑ j : Fin n, φ (MvPolynomial.pderiv j g) * u j)) = v i at hval
    field_simp [hg] at hval ⊢
    linear_combination hval

end
end DistinctDistances.TrackD
