import DistinctDistances.TrackB.NullHessianSupport
import DistinctDistances.TrackB.ParameterImageSupport
import DistinctDistances.TrackD.GenericCotangent

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators
open LinearMap (BilinForm)

/-- The polar pairing of the split quadratic form in the actual ambient coordinates. -/
def splitParameterForm (K : Type*) [Field K] (e : ℕ) : BilinForm K (Fin (e + e) → K) :=
  ∑ i : Fin e,
    (BilinForm.linMulLin (LinearMap.proj (Fin.castAdd e i)) (LinearMap.proj (Fin.natAdd e i)) +
      BilinForm.linMulLin (LinearMap.proj (Fin.natAdd e i)) (LinearMap.proj (Fin.castAdd e i)))

theorem splitParameterForm_apply (K : Type*) [Field K] (e : ℕ) (x y : Fin (e + e) → K) :
    splitParameterForm K e x y = ∑ i : Fin e,
      (x (Fin.castAdd e i) * y (Fin.natAdd e i) +
        x (Fin.natAdd e i) * y (Fin.castAdd e i)) := by
  simp [splitParameterForm, LinearMap.sum_apply, BilinForm.linMulLin_apply]

theorem splitParameterForm_symm (K : Type*) [Field K] (e : ℕ) :
    (splitParameterForm K e).IsSymm := by
  constructor
  intro x y
  rw [splitParameterForm_apply, splitParameterForm_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- test the pairing on the two coordinate vectors. -/
theorem splitParameterForm_nondegenerate (K : Type*) [Field K] (e : ℕ) :
    (splitParameterForm K e).Nondegenerate := by
  have hleft : (splitParameterForm K e).SeparatingLeft := by
    intro x hx
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      have hcast_ne_nat : ∀ (k : Fin e), Fin.castAdd e k ≠ Fin.natAdd e j := by
        intro k h
        have hk := congrArg Fin.val h
        rw [Fin.val_castAdd, Fin.val_natAdd] at hk
        have : k.val < e := k.isLt
        omega
      have h1 := hx (fun l => if l = Fin.natAdd e j then (1 : K) else 0)
      rw [splitParameterForm_apply] at h1
      have hsum : ∑ k : Fin e,
          (x (Fin.castAdd e k) * (if Fin.natAdd e k = Fin.natAdd e j then (1 : K) else 0) +
           x (Fin.natAdd e k) * (if Fin.castAdd e k = Fin.natAdd e j then (1 : K) else 0)) =
          x (Fin.castAdd e j) := by
        rw [Finset.sum_eq_single j]
        · simp only [if_true, if_neg (hcast_ne_nat j), mul_one, mul_zero, add_zero]
        · intro k _ hkj
          have hkj_nat : Fin.natAdd e k ≠ Fin.natAdd e j := by
            intro h
            apply hkj
            have hk := congrArg Fin.val h
            rw [Fin.val_natAdd, Fin.val_natAdd] at hk
            ext
            omega
          simp only [if_neg hkj_nat, if_neg (hcast_ne_nat k), mul_zero, add_zero]
        · intro hj
          exact (hj (Finset.mem_univ j)).elim
      rw [hsum] at h1
      exact h1
    · intro j
      have hnat_ne_cast : ∀ (k : Fin e), Fin.natAdd e k ≠ Fin.castAdd e j := by
        intro k h
        have hk := congrArg Fin.val h
        rw [Fin.val_natAdd, Fin.val_castAdd] at hk
        have : j.val < e := j.isLt
        omega
      have h1 := hx (fun l => if l = Fin.castAdd e j then (1 : K) else 0)
      rw [splitParameterForm_apply] at h1
      have hsum : ∑ k : Fin e,
          (x (Fin.castAdd e k) * (if Fin.natAdd e k = Fin.castAdd e j then (1 : K) else 0) +
           x (Fin.natAdd e k) * (if Fin.castAdd e k = Fin.castAdd e j then (1 : K) else 0)) =
          x (Fin.natAdd e j) := by
        rw [Finset.sum_eq_single j]
        · simp only [if_neg (hnat_ne_cast j), if_true, mul_zero, mul_one, zero_add]
        · intro k _ hkj
          have hkj_cast : Fin.castAdd e k ≠ Fin.castAdd e j := by
            intro h
            apply hkj
            have hk := congrArg Fin.val h
            rw [Fin.val_castAdd, Fin.val_castAdd] at hk
            ext
            omega
          simp only [if_neg (hnat_ne_cast k), if_neg hkj_cast, mul_zero, add_zero]
        · intro hj
          exact (hj (Finset.mem_univ j)).elim
      rw [hsum] at h1
      exact h1
  refine ⟨hleft, ?_⟩
  intro y hy
  apply hleft
  intro x
  rw [(splitParameterForm_symm K e).eq]
  exact hy x

/-- the pairing has constant coefficients, so the product rule applies. -/
theorem splitParameterForm_derivation {K : Type*} [Field K] [Algebra ℂ K]
    (e : ℕ) (δ : Derivation ℂ K K) (x y : Fin (e + e) → K) :
    δ (splitParameterForm K e x y) =
      splitParameterForm K e (fun l => δ (x l)) y +
        splitParameterForm K e x (fun l => δ (y l)) := by
  rw [splitParameterForm_apply, splitParameterForm_apply, splitParameterForm_apply]
  simp only [map_sum, map_add, Derivation.leibniz, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- denominator clearing transports a generic null tangent identity to
every derivation of the actual coordinate fraction field. No dimension input. -/
theorem generic_null_tangent_derivation {e : ℕ} (X : AffineVariety (e + e))
    (hX : X.IsIrreducible) (g : Poly (e + e)) (hg : g ∉ X.ideal)
    (hnull : ∀ x ∈ X.points, MvPolynomial.aeval x g ≠ 0 →
      ∀ v ∈ X.tangentSpace x, parameterValue v = 0)
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (Poly (e + e) ⧸ X.ideal) K]
    [IsScalarTower ℂ (Poly (e + e) ⧸ X.ideal) K]
    [IsFractionRing (Poly (e + e) ⧸ X.ideal) K] (δ : Derivation ℂ K K) :
    splitParameterForm K e
      (fun l => δ (TrackD.coordinateFieldMap X.ideal K (MvPolynomial.X l)))
      (fun l => δ (TrackD.coordinateFieldMap X.ideal K (MvPolynomial.X l))) = 0 := by
  classical
  let φ := TrackD.coordinateFieldMap X.ideal K
  have hker : RingHom.ker φ = X.ideal := TrackD.coordinateFieldMap_kernel X.ideal K
  obtain ⟨q, nums, hq, hnums⟩ := TrackD.polynomial_common_denominator X.ideal K
    (Finset.univ : Finset (Fin (e + e))) (fun l => δ (φ (MvPolynomial.X l)))
  have hn : ∀ l, φ (nums l) = φ q * δ (φ (MvPolynomial.X l)) :=
    fun l => hnums l (Finset.mem_univ l)
  have ht : ∀ x ∈ X.points, (fun l => MvPolynomial.aeval x (nums l)) ∈ X.tangentSpace x := by
    intro x hx
    simp only [AffineVariety.tangentSpace, Submodule.mem_iInf, LinearMap.mem_ker]
    intro f
    have hfmem : f.val ∈ RingHom.ker φ := by
      rw [hker]
      exact f.property
    have hf : φ f.val = 0 := RingHom.mem_ker.mp hfmem
    have hv : φ (TrackD.velocityPairing f.val nums) = 0 := by
      rw [TrackD.image_velocityPairing K φ δ q nums hn, hf, map_zero, mul_zero]
    have hi : TrackD.velocityPairing f.val nums ∈ X.ideal :=
      (SetLike.ext_iff.mp hker _).mp (RingHom.mem_ker.mpr hv)
    have heval0 : MvPolynomial.aeval x (TrackD.velocityPairing f.val nums) = 0 := hx _ hi
    simpa only [TrackD.eval_velocityPairing, MvPolynomial.aeval_eq_eval] using heval0
  let P : Poly (e + e) :=
    ∑ i : Fin e, nums (Fin.natAdd e i) * nums (Fin.castAdd e i)
  have hPvanish : ∀ x ∈ X.points, MvPolynomial.aeval x g ≠ 0 → MvPolynomial.aeval x P = 0 := by
    intro x hx hxg
    have hnullx := hnull x hx hxg (fun l => MvPolynomial.aeval x (nums l)) (ht x hx)
    simp only [parameterValue, covectorOfPoint, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.proj_apply, firstPoint, secondPoint,
      smul_eq_mul] at hnullx
    simp only [P, map_sum, map_mul]
    exact hnullx
  have hPI : P ∈ X.ideal := principal_open_vanishing X hX g P hg hPvanish
  have hP0 : φ P = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact hPI
  have hphiP : φ P = (φ q)^2 * ∑ i : Fin e,
      δ (φ (MvPolynomial.X (Fin.natAdd e i))) * δ (φ (MvPolynomial.X (Fin.castAdd e i))) := by
    calc
      φ P = ∑ i : Fin e, φ (nums (Fin.natAdd e i)) * φ (nums (Fin.castAdd e i)) := by
        simp only [P, map_sum, map_mul]
      _ = ∑ i : Fin e, (φ q * δ (φ (MvPolynomial.X (Fin.natAdd e i)))) *
          (φ q * δ (φ (MvPolynomial.X (Fin.castAdd e i)))) := by
        simp only [hn]
      _ = (φ q)^2 * ∑ i : Fin e,
          δ (φ (MvPolynomial.X (Fin.natAdd e i))) * δ (φ (MvPolynomial.X (Fin.castAdd e i))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [hphiP] at hP0
  have hq2_ne : (φ q)^2 ≠ 0 := pow_ne_zero 2 hq
  have hsum_zero : (∑ i : Fin e,
      δ (φ (MvPolynomial.X (Fin.natAdd e i))) * δ (φ (MvPolynomial.X (Fin.castAdd e i)))) = 0 := by
    exact (mul_eq_zero.mp hP0).resolve_left hq2_ne
  rw [splitParameterForm_apply]
  calc
    (∑ i : Fin e,
      (δ (φ (MvPolynomial.X (Fin.castAdd e i))) * δ (φ (MvPolynomial.X (Fin.natAdd e i))) +
       δ (φ (MvPolynomial.X (Fin.natAdd e i))) * δ (φ (MvPolynomial.X (Fin.castAdd e i))))) =
      2 * ∑ i : Fin e,
        δ (φ (MvPolynomial.X (Fin.natAdd e i))) * δ (φ (MvPolynomial.X (Fin.castAdd e i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 2 * (0 : K) := by rw [hsum_zero]
    _ = 0 := mul_zero 2

/-- the polar pairing is twice the original quadratic value. -/
theorem splitParameterForm_diagonal_complex {e : ℕ} (x : Point (e + e)) :
    splitParameterForm ℂ e x x = 2 * parameterValue x := by
  rw [splitParameterForm_apply]
  simp only [parameterValue, covectorOfPoint, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, firstPoint, secondPoint,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- scalar extension of this constant coordinate pairing. -/
theorem splitParameterForm_baseChange {K : Type*} [Field K] [Algebra ℂ K]
    {e : ℕ} (x y : Point (e + e)) :
    splitParameterForm K e (fun l => algebraMap ℂ K (x l)) (fun l => algebraMap ℂ K (y l)) =
      algebraMap ℂ K (splitParameterForm ℂ e x y) := by
  rw [splitParameterForm_apply, splitParameterForm_apply]
  simp only [map_sum, map_add, map_mul]

/-- once the null Hessian is zero, its slopes and coordinate residuals
are common constants. This is the affine conclusion used before homogeneity. -/
theorem null_derivations_affine {K : Type*} [Field K] [Algebra ℂ K] [CharZero K]
    (e : ℕ) (δ : Fin e → Derivation ℂ K K) (ξ : Fin (e + e) → K)
    (ι : Fin e → Fin (e + e))
    (hcomm : ∀ i j x, δ i (δ j x) = δ j (δ i x))
    (hcoords : ∀ i j, δ i (ξ (ι j)) = if i = j then 1 else 0)
    (hconstants : ∀ x : K, (∀ i, δ i x = 0) → ∃ c : ℂ, algebraMap ℂ K c = x)
    (hnull : ∀ i j, splitParameterForm K e
      (fun l => δ i (ξ l)) (fun l => δ j (ξ l)) = 0) :
    ∃ a : Fin (e + e) → Fin e → ℂ, ∃ b : Fin (e + e) → ℂ,
      (∀ l i, algebraMap ℂ K (a l i) = δ i (ξ l)) ∧
      (∀ l, ξ l = algebraMap ℂ K (b l) +
        ∑ i, algebraMap ℂ K (a l i) * ξ (ι i)) := by
  classical
  have hH := commuting_derivation_null_hessian_zero e δ ξ ι
    (splitParameterForm K e) (splitParameterForm_nondegenerate K e)
    (splitParameterForm_symm K e)
    (fun i x y => splitParameterForm_derivation e (δ i) x y)
    hcomm hcoords hnull
  have hslopes : ∀ l i, ∃ c : ℂ, algebraMap ℂ K c = δ i (ξ l) :=
    fun l i => hconstants (δ i (ξ l)) (fun j => by
      rw [← hcomm]
      exact hH i j l)
  choose a ha using hslopes
  have hres : ∀ l j, δ j (ξ l - ∑ i, algebraMap ℂ K (a l i) * ξ (ι i)) = 0 := by
    intro l j
    simp only [map_sub, map_sum, Derivation.leibniz, Derivation.map_algebraMap,
      smul_eq_mul, hcoords, mul_ite, mul_one, mul_zero, add_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [ha l j]
    exact sub_self _
  choose b hb using fun l => hconstants
    (ξ l - ∑ i, algebraMap ℂ K (a l i) * ξ (ι i)) (hres l)
  refine ⟨a, b, ha, ?_⟩
  intro l
  have hbl := hb l
  linear_combination -hbl

end
end DistinctDistances.TrackB
