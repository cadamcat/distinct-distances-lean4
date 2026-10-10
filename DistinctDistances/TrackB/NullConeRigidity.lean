import DistinctDistances.TrackB.NullFieldSupport
import DistinctDistances.TrackB.NullProjectiveSupport
import DistinctDistances.TrackB.AffineFlatGeometry

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators

/-- B26, concentration.tex:983–1011. Affine function-field identities on the
actual cone become homogeneous linear equations; Hilbert dimension then gives
equality with the resulting maximal isotropic projective plane. -/
theorem null_cone_coordinate_linear {e : ℕ} (he : 0 < e)
    (Y : ProjectiveVariety (e + e)) (hY : Y.IsIrreducible) (hdim : Y.dimension = e - 1)
    (K : Type*) [Field K] [Algebra ℂ K] [CharZero K]
    [Algebra (Poly (e + e) ⧸ Y.ideal) K]
    [IsScalarTower ℂ (Poly (e + e) ⧸ Y.ideal) K]
    [IsFractionRing (Poly (e + e) ⧸ Y.ideal) K]
    (ι : Fin e → Fin (e + e)) (δ : Fin e → Derivation ℂ K K)
    (hcomm : ∀ i j x, δ i (δ j x) = δ j (δ i x))
    (hcoords : ∀ i j, δ i (TrackD.coordinateFieldMap Y.ideal K (MvPolynomial.X (ι j))) =
      if i = j then 1 else 0)
    (hconstants : ∀ x : K, (∀ i, δ i x = 0) → ∃ c : ℂ, algebraMap ℂ K c = x)
    (hnull : ∀ i j, splitParameterForm K e
      (fun l => δ i (TrackD.coordinateFieldMap Y.ideal K (MvPolynomial.X l)))
      (fun l => δ j (TrackD.coordinateFieldMap Y.ideal K (MvPolynomial.X l))) = 0) :
    ∃ L : Submodule ℂ (Point (e + e)), IsMaximalIsotropic L ∧ Y = linearProjectivePlane L := by
  classical
  let φ := TrackD.coordinateFieldMap Y.ideal K
  let ξ : Fin (e + e) → K := fun l => φ (MvPolynomial.X l)
  obtain ⟨a, b, ha, hξ⟩ := null_derivations_affine e δ ξ ι hcomm hcoords hconstants hnull
  have hker : RingHom.ker φ = Y.ideal := TrackD.coordinateFieldMap_kernel Y.ideal K
  have hφC (c : ℂ) : φ (MvPolynomial.C c) = algebraMap ℂ K c := φ.commutes c
  let F : Fin (e + e) → Poly (e + e) := fun l =>
    MvPolynomial.X l - ∑ i, MvPolynomial.C (a l i) * MvPolynomial.X (ι i) - MvPolynomial.C (b l)
  have hFI : ∀ l, F l ∈ Y.ideal := by
    intro l
    rw [← hker]
    apply RingHom.mem_ker.mpr
    simp only [F, map_sub, map_sum, map_mul, hφC]
    change ξ l - ∑ i, algebraMap ℂ K (a l i) * ξ (ι i) - algebraMap ℂ K (b l) = 0
    linear_combination hξ l
  have hYclosure : ProjectiveVariety.closure Y.points = Y := by
    apply ProjectiveVariety.ext
    exact Y.vanishingIdeal_points
  have h0 : (0 : Point (e + e)) ∈ Y.affineCone.points := by
    have h := zero_mem_projective_cone Y.points (ProjectiveFamily.irreducible_points_nonempty Y hY)
    rwa [hYclosure] at h
  have hb0 : ∀ l, b l = 0 := by
    intro l
    have h := h0 (F l) (hFI l)
    have hneg : -(b l) = 0 := by simpa [F] using h
    exact neg_eq_zero.mp hneg
  have hacoords : ∀ k i, a (ι k) i = if i = k then 1 else 0 := by
    intro k i
    apply (algebraMap ℂ K).injective
    rw [ha, hcoords]
    split_ifs <;> simp
  let col : Fin e → Point (e + e) := fun i l => a l i
  let A : Point e →ₗ[ℂ] Point (e + e) :=
    { toFun := fun c => ∑ i, c i • col i
      map_add' := by intro c d; simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by intro t c; simp [Pi.smul_apply, smul_smul, Finset.smul_sum] }
  have hAcoords : ∀ c k, A c (ι k) = c k := by
    intro c k
    change (∑ i, c i • col i) (ι k) = c k
    simp [col, hacoords, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hAinj : Function.Injective A := by
    intro c d h
    funext k
    have hk := congrFun h (ι k)
    simpa only [hAcoords] using hk
  let L := LinearMap.range A
  have hLdim : Module.finrank ℂ L = e := by
    rw [LinearMap.finrank_range_of_inj hAinj, Module.finrank_fin_fun]
  have hcolnull : ∀ i j, splitParameterForm ℂ e (col i) (col j) = 0 := by
    intro i j
    apply (algebraMap ℂ K).injective
    rw [map_zero, ← splitParameterForm_baseChange]
    simp only [col, ha]
    exact hnull i j
  have hLnull : ∀ x ∈ L, parameterValue x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hx
    have hpolar : splitParameterForm ℂ e (A c) (A c) = 0 := by
      change splitParameterForm ℂ e (∑ i, c i • col i) (∑ j, c j • col j) = 0
      simp [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hcolnull]
    rw [splitParameterForm_diagonal_complex] at hpolar
    exact (mul_eq_zero.mp hpolar).resolve_left (by norm_num)
  have hXL : Y.affineCone.points ⊆ (L : Set (Point (e + e))) := by
    intro x hx
    apply LinearMap.mem_range.mpr
    refine ⟨fun i => x (ι i), ?_⟩
    funext l
    have h := hx (F l) (hFI l)
    have heq : x l = ∑ i, a l i * x (ι i) := by
      apply sub_eq_zero.mp
      simpa [F, hb0] using h
    change (∑ i, x (ι i) • col i) l = x l
    rw [heq]
    simp [Finset.sum_apply, Pi.smul_apply, col, smul_eq_mul, mul_comm]
  let W := AffineVariety.closure (L : Set (Point (e + e)))
  have hplane : {x | ∃ t : Point e, x = (0 : Point (e + e)) + A t} =
      (L : Set (Point (e + e))) := by
    ext x
    simp [L, LinearMap.mem_range, eq_comm]
  have hWprime : W.IsIrreducible := by
    have h := vanishingIdeal_affineLinearImage_prime (0 : Point (e + e)) A
    rw [hplane] at h
    exact h
  have hWdim : W.dimension = e := by
    have h := Request.affine_linear_principal_open_dimension (0 : Point (e + e)) A hAinj
      (1 : Poly (e + e)) 0 (by simp)
    have hset : {x | ∃ t : Point e, x = (0 : Point (e + e)) + A t ∧
        MvPolynomial.aeval x (1 : Poly (e + e)) ≠ 0} = (L : Set (Point (e + e))) := by
      simpa using hplane
    rw [hset] at h
    exact h
  have hconeDim : Y.affineCone.dimension = e := by
    rw [Y.dimension_cone (ProjectiveFamily.irreducible_points_nonempty Y hY), hdim]
    omega
  have hsub : Y.affineCone.Subvariety W :=
    (AffineVariety.subvariety_iff_points_subset _ _).mpr
      (hXL.trans (AffineVariety.subset_closure _))
  letI : W.ideal.IsPrime := hWprime
  letI : Y.ideal.IsPrime := hY
  have hEq : W.ideal = Y.ideal :=
    Request.affine_prime_same_dimension_eq W.ideal Y.ideal hsub hWdim hconeDim
  have hLne : ∃ x ∈ L, x ≠ 0 := by
    letI : Nontrivial L := Module.nontrivial_of_finrank_pos (by rw [hLdim]; exact he)
    obtain ⟨x, hx⟩ := exists_ne (0 : L)
    refine ⟨x.val, x.property, ?_⟩
    intro hx0
    exact hx (Subtype.ext hx0)
  refine ⟨L, ⟨hLdim, hLnull⟩, ?_⟩
  apply ProjectiveVariety.ext
  rw [linearProjectivePlane_cone_ideal L hLne]
  exact hEq.symm

#print axioms null_cone_coordinate_linear
end
end DistinctDistances.TrackB
