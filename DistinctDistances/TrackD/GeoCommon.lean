import DistinctDistances.TrackD.Basic
import OAI.NumberTheory.PowerFree.PatchBounds
import OAI.NumberTheory.PowerFree.SurfaceCounting
import OAI.NumberTheory.PowerFree.DegreeBudgets
import DistinctDistances.TrackD.GeoTangent

/-!
Linear span lemmas for `geo:generic-depth.commonflat`.

For an affine flat `S = p₀ + V` (`finrank V = r`) we build the pullback to
`r` variables, show its kernel is prime of dimension `≤ r`, and deduce that a
nonlinear irreducible variety spans its flat.  The dimension bound goes
through Hilbert-function comparison (no smooth points, no generic
projections).
-/

namespace DistinctDistances
namespace TrackD
namespace GeoCommon

open Classical

variable {d : ℕ}

theorem finrank_pi_fin (r : ℕ) : Module.finrank ℂ (Fin r → ℂ) = r := by
  rw [Module.finrank_pi]
  simp

noncomputable def coordEquiv (V : Submodule ℂ (Point d)) (r : ℕ)
    (hr : Module.finrank ℂ V = r) : (Fin r → ℂ) ≃ₗ[ℂ] V :=
  LinearEquiv.ofFinrankEq _ _ (by rw [finrank_pi_fin, hr])

theorem pi_decomp {n : ℕ} (y : Fin n → ℂ) :
    y = ∑ j : Fin n, y j • Pi.single j (1 : ℂ) := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

/-- Coordinate functions of the affine embedding `y ↦ p₀ + e y`. -/
noncomputable def sliceForms (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (e : (Fin r → ℂ) ≃ₗ[ℂ] V) : Fin d → Poly r :=
  fun i => MvPolynomial.C (p₀ i) +
    ∑ j : Fin r, MvPolynomial.C (((e (Pi.single j 1) : V) : Point d) i) *
      MvPolynomial.X j

theorem sliceForms_deg (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (e : (Fin r → ℂ) ≃ₗ[ℂ] V) (i : Fin d) :
    (sliceForms p₀ V r e i).totalDegree ≤ 1 := by
  unfold sliceForms
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le_iff.mpr ⟨?_, ?_⟩)
  · simp
  · refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
    apply Finset.sup_le
    intro j _
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    simp

theorem aeval_C_self {r : ℕ} (y : Fin r → ℂ) (c : ℂ) :
    MvPolynomial.aeval y (MvPolynomial.C c) = c := by simp

theorem finsupp_apply_le_sum {n : ℕ} (s : Fin n →₀ ℕ) (k : Fin n) :
    s k ≤ s.sum (fun _ e => e) := by
  classical
  by_cases hkS : k ∈ s.support
  · calc s k ≤ ∑ i ∈ s.support, s i :=
          Finset.single_le_sum (fun i _ => Nat.zero_le _) hkS
      _ = s.sum (fun _ e => e) := rfl
  · rw [Finsupp.notMem_support_iff.mp hkS]
    exact Nat.zero_le _

/-- A single-exponent finsupp of sum one is a single. -/
theorem finsupp_eq_single_of_sum_eq_one {n : ℕ} (s : Fin n →₀ ℕ)
    (hne : s ≠ 0) (hsum : s.sum (fun _ e => e) = 1) :
    ∃ j, s = Finsupp.single j 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, s j ≠ 0 := by
    by_contra hc
    apply hne
    apply Finsupp.ext
    intro k
    simp only [Finsupp.zero_apply]
    exact not_not.mp (fun hk => hc ⟨k, hk⟩)
  refine ⟨j, ?_⟩
  have hsj : s j = 1 := by
    have hle : s j ≤ s.sum (fun _ e => e) := finsupp_apply_le_sum s j
    omega
  apply Finsupp.ext
  intro k
  by_cases hkj : k = j
  · subst hkj
    simp [hsj]
  · have h0 : (Finsupp.single j (1:ℕ) : Fin n →₀ ℕ) k = 0 :=
      Finsupp.single_eq_of_ne hkj
    rw [h0]
    by_contra hk0
    have hkS : k ∈ s.support := Finsupp.mem_support_iff.mpr hk0
    have hjS : j ∈ s.support := Finsupp.mem_support_iff.mpr (by omega : s j ≠ 0)
    have h2 : s j + s k ≤ s.sum (fun _ e => e) := by
      calc s j + s k = ∑ i ∈ ({j, k} : Finset (Fin n)), s i := by
            rw [Finset.sum_pair (Ne.symm hkj)]
        _ ≤ ∑ i ∈ s.support, s i := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro i hi
              simp only [Finset.mem_insert, Finset.mem_singleton] at hi
              rcases hi with rfl | rfl
              · exact hjS
              · exact hkS
            · intro i _ _
              exact Nat.zero_le _
        _ = s.sum (fun _ e => e) := rfl
    omega

/-- A linear polynomial vanishing everywhere is zero. -/
theorem linear_eq_zero {r : ℕ} (f : Poly r) (hdeg : f.totalDegree ≤ 1)
    (hvan : ∀ y : Fin r → ℂ, MvPolynomial.aeval y f = 0) : f = 0 := by
  classical
  have hcoeff0 : f.coeff 0 = 0 := by
    have h0 : MvPolynomial.aeval (0 : Fin r → ℂ) f = f.coeff 0 := by
      simp [MvPolynomial.aeval_zero, MvPolynomial.constantCoeff_eq]
    rw [← h0, hvan 0]
  have hcoeff1 : ∀ j : Fin r, f.coeff (Finsupp.single j 1) = 0 := by
    intro j
    have heval : MvPolynomial.aeval (Pi.single j (1 : ℂ) : Fin r → ℂ) f
        = f.coeff (Finsupp.single j 1) := by
      rw [MvPolynomial.as_sum f, map_sum]
      rw [Finset.sum_eq_single (Finsupp.single j 1)]
      · rw [MvPolynomial.aeval_monomial]
        simp
      · intro s hs hne
        rw [MvPolynomial.aeval_monomial]
        have hcs : f.coeff s ≠ 0 := Finsupp.mem_support_iff.mp
          (Finset.mem_coe.mp hs)
        have hsum_le : s.sum (fun _ e => e) ≤ 1 := by
          by_contra hlt
          push_neg at hlt
          have hlt2 : f.totalDegree < s.sum (fun _ e => e) :=
            lt_of_le_of_lt hdeg (by omega : 1 < s.sum (fun _ e => e))
          exact hcs (MvPolynomial.coeff_eq_zero_of_totalDegree_lt hlt2)
        by_cases hs0 : s = 0
        · subst hs0
          simp [hcoeff0]
        · have hsum1 : s.sum (fun _ e => e) = 1 := by
            have hpos : 1 ≤ s.sum (fun _ e => e) := by
              obtain ⟨k, hk⟩ : ∃ k, s k ≠ 0 := by
                by_contra hc
                apply hs0
                apply Finsupp.ext
                intro k
                simp only [Finsupp.zero_apply]
                exact not_not.mp (fun hk => hc ⟨k, hk⟩)
              calc 1 ≤ s k := Nat.one_le_iff_ne_zero.mpr hk
                _ ≤ s.sum (fun _ e => e) := finsupp_apply_le_sum s k
            omega
          obtain ⟨k, hk⟩ := finsupp_eq_single_of_sum_eq_one s hs0 hsum1
          have hkj : k ≠ j := by
            intro hkj
            subst hkj
            exact hne hk
          subst hk
          have hprod : (Finsupp.single k 1).prod
              (fun i e => (Pi.single j 1 : Fin r → ℂ) i ^ e)
              = (Pi.single j 1 : Fin r → ℂ) k := by
            rw [Finsupp.prod_single_index (by simp)]
            simp
          rw [hprod]
          have hyk : (Pi.single j 1 : Fin r → ℂ) k = 0 := by simp [hkj]
          rw [hyk, mul_zero]
      · intro hcon
        rw [MvPolynomial.aeval_monomial]
        simp [Finsupp.notMem_support_iff.mp hcon]
    rw [← heval, hvan _]
  ext s
  show f.coeff s = 0
  by_cases hs0 : s = 0
  · subst hs0
    exact hcoeff0
  · by_cases hsum : 1 < s.sum (fun _ e => e)
    · have hlt : f.totalDegree < s.sum (fun _ e => e) :=
        lt_of_le_of_lt hdeg hsum
      exact MvPolynomial.coeff_eq_zero_of_totalDegree_lt hlt
    · push_neg at hsum
      have hsum1 : s.sum (fun _ e => e) = 1 := by
        have hpos : 1 ≤ s.sum (fun _ e => e) := by
          obtain ⟨j, hj⟩ : ∃ j, s j ≠ 0 := by
            by_contra hc
            apply hs0
            apply Finsupp.ext
            intro k
            simp only [Finsupp.zero_apply]
            exact not_not.mp (fun hk => hc ⟨k, hk⟩)
          calc 1 ≤ s j := Nat.one_le_iff_ne_zero.mpr hj
            _ ≤ s.sum (fun _ e => e) := finsupp_apply_le_sum s j
        omega
      obtain ⟨j, hj⟩ := finsupp_eq_single_of_sum_eq_one s hs0 hsum1
      subst hj
      exact hcoeff1 _

theorem sliceForms_eval (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (e : (Fin r → ℂ) ≃ₗ[ℂ] V) (y : Fin r → ℂ) (i : Fin d) :
    MvPolynomial.aeval y (sliceForms p₀ V r e i) = (p₀ + e y : Point d) i := by
  have hdecomp : e y = ∑ j : Fin r, y j • e (Pi.single j (1 : ℂ)) := by
    conv_lhs => rw [pi_decomp y]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul]
  have hcoord : ((e y : Point d)) i
      = ∑ j : Fin r, y j * ((((e (Pi.single j 1) : V)) : Point d) i) := by
    conv_lhs => rw [hdecomp, Submodule.coe_sum]
    simp only [Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  unfold sliceForms
  simp only [map_add, map_sum, map_mul, aeval_C_self, MvPolynomial.aeval_X,
    Pi.add_apply]
  rw [hcoord]
  apply congrArg (p₀ i + ·)
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Pullback along the affine embedding. -/
noncomputable def slicePull (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (e : (Fin r → ℂ) ≃ₗ[ℂ] V) : Poly d →ₐ[ℂ] Poly r :=
  MvPolynomial.aeval (sliceForms p₀ V r e)

theorem slicePull_comp (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (e : (Fin r → ℂ) ≃ₗ[ℂ] V) (y : Fin r → ℂ) :
    (MvPolynomial.aeval y).comp (slicePull p₀ V r e)
      = MvPolynomial.aeval (p₀ + e y : Point d) := by
  apply MvPolynomial.algHom_ext
  intro i
  show MvPolynomial.aeval y (MvPolynomial.aeval (sliceForms p₀ V r e)
      (MvPolynomial.X i)) = _
  simp only [MvPolynomial.aeval_X]
  exact sliceForms_eval p₀ V r e y i

theorem slicePull_apply (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (e : (Fin r → ℂ) ≃ₗ[ℂ] V) (y : Fin r → ℂ) (g : Poly d) :
    MvPolynomial.aeval y (slicePull p₀ V r e g)
      = MvPolynomial.aeval (p₀ + e y : Point d) g :=
  AlgHom.ext_iff.mp (slicePull_comp p₀ V r e y) g

noncomputable def sliceIdeal (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (e : (Fin r → ℂ) ≃ₗ[ℂ] V) : Ideal (Poly d) :=
  RingHom.ker (slicePull p₀ V r e).toRingHom

theorem sliceIdeal_prime (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (e : (Fin r → ℂ) ≃ₗ[ℂ] V) : (sliceIdeal p₀ V r e).IsPrime :=
  RingHom.ker_isPrime _

theorem sliceRange (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (e : (Fin r → ℂ) ≃ₗ[ℂ] V) :
    Set.range (fun y : Fin r → ℂ => (p₀ + e y : Point d))
      = ↑(AffineSubspace.mk' p₀ V) := by
  ext x
  simp only [Set.mem_range, AffineSubspace.mem_mk', SetLike.mem_coe]
  constructor
  · rintro ⟨y, rfl⟩
    have hmem : (p₀ + (e y : Point d)) -ᵥ p₀ = (e y : Point d) := by
      rw [vsub_eq_sub]
      abel
    rw [hmem]
    exact (e y).property
  · intro hx
    have hxV : x - p₀ ∈ V := by
      have := hx
      rwa [vsub_eq_sub] at this
    refine ⟨e.symm ⟨x - p₀, hxV⟩, ?_⟩
    show p₀ + ((e (e.symm ⟨x - p₀, hxV⟩) : V) : Point d) = x
    have happ : ((e (e.symm ⟨x - p₀, hxV⟩) : V) : Point d) = x - p₀ :=
      Subtype.ext_iff.mp (e.apply_symm_apply _)
    rw [happ, add_sub_cancel]

theorem totalDegree_aeval_linear_le {r : ℕ} (L : Fin d → Poly r)
    (hL : ∀ i, (L i).totalDegree ≤ 1) (g : Poly d) :
    (MvPolynomial.aeval L g).totalDegree ≤ g.totalDegree := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum g, map_sum]
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  apply Finset.sup_le
  intro s hs
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  rw [MvPolynomial.aeval_monomial]
  calc (algebraMap ℂ (Poly r) (g.coeff s) * s.prod _).totalDegree
        ≤ (algebraMap ℂ (Poly r) (g.coeff s)).totalDegree
          + (s.prod fun i k => L i ^ k).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + s.sum (fun _ e => e) := by
          apply add_le_add _ _
          · have hC : algebraMap ℂ (Poly r) (g.coeff s)
                = MvPolynomial.C (g.coeff s) := by
              rw [MvPolynomial.algebraMap_eq]
            rw [hC, MvPolynomial.totalDegree_C]
          · calc (s.prod fun i k => L i ^ k).totalDegree
                ≤ ∑ i ∈ s.support, ((L i ^ s i)).totalDegree :=
                  MvPolynomial.totalDegree_finsetProd _ _
              _ ≤ ∑ i ∈ s.support, s i := by
                  apply Finset.sum_le_sum
                  intro i _
                  calc ((L i ^ s i)).totalDegree ≤ s i * (L i).totalDegree :=
                        MvPolynomial.totalDegree_pow _ _
                    _ ≤ s i * 1 :=
                        mul_le_mul_of_nonneg_left (hL i) (Nat.zero_le _)
                    _ = s i := Nat.mul_one _
              _ = s.sum (fun _ e => e) := rfl
      _ = s.sum (fun _ e => e) := zero_add _

theorem slicePull_deg (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (e : (Fin r → ℂ) ≃ₗ[ℂ] V) (g : Poly d) :
    (slicePull p₀ V r e g).totalDegree ≤ g.totalDegree := by
  apply totalDegree_aeval_linear_le
  intro i
  exact sliceForms_deg p₀ V r e i

theorem sliceIdeal_le (X : AffineVariety d) (p₀ : Point d) (V : Submodule ℂ (Point d))
    (r : ℕ) (e : (Fin r → ℂ) ≃ₗ[ℂ] V)
    (hXsub : X.points ⊆ ↑(AffineSubspace.mk' p₀ V)) :
    sliceIdeal p₀ V r e ≤ X.ideal := by
  intro g hg
  have hker : slicePull p₀ V r e g = 0 := RingHom.mem_ker.mp hg
  have hvan : g ∈ MvPolynomial.vanishingIdeal ℂ X.points := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    have hxS := hXsub hx
    rw [← sliceRange p₀ V r e] at hxS
    obtain ⟨y, hy⟩ := hxS
    subst hy
    simp only []
    rw [← slicePull_apply p₀ V r e y g, hker]
    rfl
  rwa [AffineVariety.vanishingIdeal_points] at hvan

theorem finrank_point (d : ℕ) : Module.finrank ℂ (Point d) = d := by
  rw [Module.finrank_pi]
  simp

theorem finrank_quotDir (V : Submodule ℂ (Point d)) (r : ℕ)
    (hr : Module.finrank ℂ V = r) :
    Module.finrank ℂ (Point d ⧸ V) = d - r := by
  have htot : Module.finrank ℂ (Point d) = d := finrank_point d
  have hadd := Submodule.finrank_quotient_add_finrank V
  omega

noncomputable def quotEquiv (V : Submodule ℂ (Point d)) (r : ℕ)
    (hr : Module.finrank ℂ V = r) : (Point d ⧸ V) ≃ₗ[ℂ] (Fin (d - r) → ℂ) :=
  LinearEquiv.ofFinrankEq _ _ (by rw [finrank_quotDir V r hr, finrank_pi_fin])

noncomputable def projQuot (V : Submodule ℂ (Point d)) (r : ℕ)
    (hr : Module.finrank ℂ V = r) : Point d →ₗ[ℂ] (Fin (d - r) → ℂ) :=
  (quotEquiv V r hr).toLinearMap.comp V.mkQ

theorem projQuot_ker (V : Submodule ℂ (Point d)) (r : ℕ)
    (hr : Module.finrank ℂ V = r) : LinearMap.ker (projQuot V r hr) = V := by
  ext x
  simp only [LinearMap.mem_ker, projQuot, LinearMap.comp_apply]
  constructor
  · intro hx
    have hmk : V.mkQ x = 0 := by
      have hinj := (quotEquiv V r hr).injective
      have h0 : (quotEquiv V r hr) (V.mkQ x) = (quotEquiv V r hr) 0 := by
        simpa using hx
      exact hinj h0
    have hmem : x ∈ LinearMap.ker V.mkQ := LinearMap.mem_ker.mpr hmk
    rwa [Submodule.ker_mkQ] at hmem
  · intro hx
    have hmem : x ∈ LinearMap.ker V.mkQ := by
      rwa [Submodule.ker_mkQ]
    have hmk : V.mkQ x = 0 := LinearMap.mem_ker.mp hmem
    rw [hmk, map_zero]

/-- Linear equations cutting out the flat. -/
noncomputable def cutForms (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (hr : Module.finrank ℂ V = r) : Fin (d - r) → Poly d :=
  fun i => (∑ j : Fin d, MvPolynomial.C (((projQuot V r hr) (Pi.single j 1)) i) *
      MvPolynomial.X j) - MvPolynomial.C (((projQuot V r hr) p₀) i)

theorem cutForms_deg (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (hr : Module.finrank ℂ V = r) (i : Fin (d - r)) :
    (cutForms p₀ V r hr i).totalDegree ≤ 1 := by
  unfold cutForms
  rw [sub_eq_add_neg]
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le_iff.mpr ⟨?_, ?_⟩)
  · refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
    apply Finset.sup_le
    intro j _
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    simp
  · rw [← map_neg]
    simp

theorem cutForms_eval (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (hr : Module.finrank ℂ V = r) (x : Point d) (i : Fin (d - r)) :
    MvPolynomial.aeval x (cutForms p₀ V r hr i)
      = ((projQuot V r hr) (x - p₀)) i := by
  have hx : ((projQuot V r hr) x) i
      = ∑ j : Fin d, x j * (((projQuot V r hr) (Pi.single j 1)) i) := by
    conv_lhs => rw [pi_decomp x]
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ j : Fin d, (((projQuot V r hr) (Pi.single j 1)) i) * x j)
      = ∑ j : Fin d, x j * (((projQuot V r hr) (Pi.single j 1)) i) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hp : ((projQuot V r hr) p₀) i
      = ∑ j : Fin d, p₀ j * (((projQuot V r hr) (Pi.single j 1)) i) := by
    conv_lhs => rw [pi_decomp p₀]
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  unfold cutForms
  simp only [map_sub, map_sum, map_mul, aeval_C_self, MvPolynomial.aeval_X]
  rw [Pi.sub_apply, hx, hp, hsum]

theorem cutForms_mem (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (hr : Module.finrank ℂ V = r) (x : Point d) :
    x ∈ AffineSubspace.mk' p₀ V ↔
      ∀ i : Fin (d - r), MvPolynomial.aeval x (cutForms p₀ V r hr i) = 0 := by
  rw [AffineSubspace.mem_mk']
  constructor
  · intro hx i
    rw [cutForms_eval]
    have hx' : x - p₀ ∈ V := by rwa [vsub_eq_sub] at hx
    have hP : (projQuot V r hr) (x - p₀) = 0 :=
      LinearMap.mem_ker.mp (by rw [projQuot_ker]; exact hx')
    simp [hP]
  · intro hx
    have hP : (projQuot V r hr) (x - p₀) = 0 := by
      funext i
      show ((projQuot V r hr) (x - p₀)) i = (0 : Fin (d - r) → ℂ) i
      rw [Pi.zero_apply]
      have hi := hx i
      rwa [cutForms_eval] at hi
    have hxV : x - p₀ ∈ V := by
      have hmem : x - p₀ ∈ LinearMap.ker (projQuot V r hr) :=
        LinearMap.mem_ker.mpr hP
      rwa [projQuot_ker] at hmem
    rwa [vsub_eq_sub]

/-- The cutting forms lie in the slice ideal. -/
theorem cutForms_mem_ideal (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (hr : Module.finrank ℂ V = r) (e : (Fin r → ℂ) ≃ₗ[ℂ] V)
    (i : Fin (d - r)) : cutForms p₀ V r hr i ∈ sliceIdeal p₀ V r e := by
  have hdeg : (slicePull p₀ V r e (cutForms p₀ V r hr i)).totalDegree ≤ 1 := by
    refine le_trans (slicePull_deg p₀ V r e _) ?_
    exact cutForms_deg p₀ V r hr i
  have hvan : ∀ y : Fin r → ℂ,
      MvPolynomial.aeval y (slicePull p₀ V r e (cutForms p₀ V r hr i)) = 0 := by
    intro y
    rw [slicePull_apply]
    -- (cutForms i) vanishes at σ y ∈ S since σ y ∈ mk' p₀ V
    have hmem : (p₀ + e y : Point d) ∈ AffineSubspace.mk' p₀ V := by
      rw [AffineSubspace.mem_mk']
      have hsub : (p₀ + (e y : Point d)) -ᵥ p₀ = (e y : Point d) := by
        rw [vsub_eq_sub]
        abel
      rw [hsub]
      exact (e y).property
    have hcut := (cutForms_mem p₀ V r hr (p₀ + e y : Point d)).mp hmem i
    exact hcut
  have hzero := linear_eq_zero _ hdeg hvan
  show _ ∈ RingHom.ker _
  rw [RingHom.mem_ker]
  exact hzero

/-- The zero locus of the slice ideal is exactly the flat. -/
theorem sliceIdeal_zeroLocus (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (hr : Module.finrank ℂ V = r) (e : (Fin r → ℂ) ≃ₗ[ℂ] V) :
    MvPolynomial.zeroLocus ℂ (sliceIdeal p₀ V r e) = ↑(AffineSubspace.mk' p₀ V) := by
  ext x
  simp only [MvPolynomial.mem_zeroLocus_iff, SetLike.mem_coe]
  constructor
  · intro hx
    have hcut : ∀ i : Fin (d - r),
        MvPolynomial.aeval x (cutForms p₀ V r hr i) = 0 := by
      intro i
      exact hx _ (cutForms_mem_ideal p₀ V r hr e i)
    have hmem := (cutForms_mem p₀ V r hr x).mpr hcut
    exact hmem
  · intro hx g hg
    have hxS : x ∈ Set.range (fun y : Fin r → ℂ => (p₀ + e y : Point d)) := by
      rw [sliceRange p₀ V r e]
      exact hx
    obtain ⟨y, hy⟩ := hxS
    subst hy
    simp only []
    have hker : slicePull p₀ V r e g = 0 := RingHom.mem_ker.mp hg
    rw [← slicePull_apply p₀ V r e y g, hker]
    exact map_zero _

theorem sliceIdeal_dim_le (p₀ : Point d) (V : Submodule ℂ (Point d)) (r : ℕ)
    (hr : Module.finrank ℂ V = r) (e : (Fin r → ℂ) ≃ₗ[ℂ] V) :
    OAI.QuarticPowerFree.affineDimension (sliceIdeal p₀ V r e) ≤ r := by
  classical
  have hQdeg : ((Polynomial.X + Polynomial.C ((r : ℕ) : ℚ) : Polynomial ℚ) ^ r).natDegree
      = r := by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]
  have hfactN : ∀ T : ℕ, (T + r).factorial
      = T.factorial * ∏ i ∈ Finset.range r, (T + 1 + i) := by
    intro T
    have h1 : ∏ i ∈ Finset.range (T + r), (i + 1) = (T + r).factorial :=
      Finset.prod_range_add_one_eq_factorial _
    have h2 : ∏ i ∈ Finset.range T, (i + 1) = T.factorial :=
      Finset.prod_range_add_one_eq_factorial _
    have h3 : ∏ i ∈ Finset.range (T + r), (i + 1)
        = (∏ i ∈ Finset.range T, (i + 1))
          * ∏ i ∈ Finset.range r, (T + 1 + i) := by
      rw [Finset.prod_range_add (fun i => i + 1) T r]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      ring
    rw [h1, h2] at h3
    exact h3
  have hPR : ∀ T : ℕ, (T + r).choose r * r.factorial
      = ∏ i ∈ Finset.range r, (T + 1 + i) := by
    intro T
    have hch := Nat.choose_mul_factorial_mul_factorial (by omega : r ≤ T + r)
    rw [show T + r - r = T by omega] at hch
    have hTeq : (T + r).choose r * r.factorial * T.factorial
        = (∏ i ∈ Finset.range r, (T + 1 + i)) * T.factorial := by
      rw [hch, hfactN]
      ring
    exact mul_right_cancel₀ (Nat.factorial_ne_zero T) hTeq
  have hchoose_le : ∀ T : ℕ, (T + r).choose r ≤ (T + r) ^ r := by
    intro T
    have hr1 : 1 ≤ r.factorial := by
      have h := Nat.factorial_pos r
      omega
    calc (T + r).choose r = (T + r).choose r * 1 := (mul_one _).symm
      _ ≤ (T + r).choose r * r.factorial :=
        mul_le_mul_of_nonneg_left hr1 (Nat.zero_le _)
      _ = ∏ i ∈ Finset.range r, (T + 1 + i) := hPR T
      _ ≤ ∏ _i ∈ Finset.range r, (T + r) := by
        apply Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _) (fun i hi => ?_)
        have hiT : i < r := Finset.mem_range.mp hi
        omega
      _ = (T + r) ^ r := by
        rw [Finset.prod_const, Finset.card_range]
  have hQeval : ∀ T : ℕ, (((T + r).choose r : ℕ) : ℚ)
      ≤ ((Polynomial.X + Polynomial.C ((r : ℕ) : ℚ) : Polynomial ℚ) ^ r).eval
        (T : ℚ) := by
    intro T
    have h1 : (((T + r).choose r : ℕ) : ℚ) ≤ ((((T + r) ^ r : ℕ)) : ℚ) :=
      Nat.cast_le.mpr (hchoose_le T)
    have h2 : ((((T + r) ^ r : ℕ)) : ℚ)
        = ((Polynomial.X + Polynomial.C ((r : ℕ) : ℚ) : Polynomial ℚ) ^ r).eval
          (T : ℚ) := by
      push_cast
      simp [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C]
    rwa [h2] at h1
  have hHTle : ∀ T : ℕ,
      ((Module.finrank ℂ ↥(Submodule.map
        (Ideal.Quotient.mkₐ ℂ (sliceIdeal p₀ V r e)).toLinearMap
        (OAI.QuarticPowerFree.totalSpace T)) : ℕ) : ℚ)
      ≤ (((T + r).choose r : ℕ) : ℚ) := by
    intro T
    haveI := OAI.QuarticPowerFree.totalSpace_finite (n := d) (K := ℂ) (T := T)
    haveI := OAI.QuarticPowerFree.totalSpace_finite (n := r) (K := ℂ) (T := T)
    let Ψ : ↥(OAI.QuarticPowerFree.totalSpace (σ := Fin d) (K := ℂ) T) →ₗ[ℂ]
        Poly r :=
      (slicePull p₀ V r e).toLinearMap.comp
        (OAI.QuarticPowerFree.totalSpace (σ := Fin d) (K := ℂ) T).subtype
    let Φ : ↥(OAI.QuarticPowerFree.totalSpace (σ := Fin d) (K := ℂ) T) →ₗ[ℂ]
        (Poly d ⧸ sliceIdeal p₀ V r e) :=
      (Ideal.Quotient.mkₐ ℂ (sliceIdeal p₀ V r e)).toLinearMap.comp
        (OAI.QuarticPowerFree.totalSpace (σ := Fin d) (K := ℂ) T).subtype
    have hΨcomp : ∀ g : ↥(OAI.QuarticPowerFree.totalSpace (σ := Fin d) (K := ℂ) T),
        Ψ g = slicePull p₀ V r e (g : Poly d) := fun g => rfl
    have hΦcomp : ∀ g : ↥(OAI.QuarticPowerFree.totalSpace (σ := Fin d) (K := ℂ) T),
        Φ g = (Ideal.Quotient.mkₐ ℂ (sliceIdeal p₀ V r e)) (g : Poly d) :=
      fun g => rfl
    have hrange : LinearMap.range Φ = Submodule.map
        (Ideal.Quotient.mkₐ ℂ (sliceIdeal p₀ V r e)).toLinearMap
        (OAI.QuarticPowerFree.totalSpace T) := by
      ext y
      simp only [LinearMap.mem_range, Submodule.mem_map]
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨_, g.property, (hΦcomp g).symm⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨⟨g, hg⟩, hΦcomp _⟩
    have hker : LinearMap.ker Φ = LinearMap.ker Ψ := by
      ext g
      simp only [LinearMap.mem_ker]
      rw [hΦcomp]
      constructor
      · intro h1
        have hmk2 : Ideal.Quotient.mk (sliceIdeal p₀ V r e) (g : Poly d) = 0 := by
          rwa [Ideal.Quotient.mkₐ_eq_mk] at h1
        have hgJ : (g : Poly d) ∈ sliceIdeal p₀ V r e :=
          Ideal.Quotient.eq_zero_iff_mem.mp hmk2
        have hpi : slicePull p₀ V r e (g : Poly d) = 0 := RingHom.mem_ker.mp hgJ
        rw [hΨcomp]
        exact hpi
      · intro h2
        have hpi : slicePull p₀ V r e (g : Poly d) = 0 := by
          rwa [hΨcomp] at h2
        have hgJ : (g : Poly d) ∈ sliceIdeal p₀ V r e :=
          RingHom.mem_ker.mpr hpi
        have hmk2 : Ideal.Quotient.mk (sliceIdeal p₀ V r e) (g : Poly d) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hgJ
        have hmk : (Ideal.Quotient.mkₐ ℂ (sliceIdeal p₀ V r e)) (g : Poly d) = 0 :=
          hmk2
        exact hmk
    have hΦ := LinearMap.finrank_range_add_finrank_ker Φ
    have hΨ := LinearMap.finrank_range_add_finrank_ker Ψ
    have hrange_le : LinearMap.range Ψ
        ≤ OAI.QuarticPowerFree.totalSpace (σ := Fin r) (K := ℂ) T := by
      intro y hy
      obtain ⟨g, rfl⟩ := LinearMap.mem_range.mp hy
      rw [hΨcomp]
      rw [OAI.QuarticPowerFree.mem_totalSpace]
      have hgT : ((g : Poly d)) ∈ OAI.QuarticPowerFree.totalSpace T := g.property
      rw [OAI.QuarticPowerFree.mem_totalSpace] at hgT
      exact le_trans (slicePull_deg _ _ _ _ _) hgT
    have hrangeΨ : Module.finrank ℂ ↥(LinearMap.range Ψ)
        ≤ Module.finrank ℂ
          ↥(OAI.QuarticPowerFree.totalSpace (σ := Fin r) (K := ℂ) T) :=
      Submodule.finrank_mono hrange_le
    have hfin2 : Module.finrank ℂ
        ↥(OAI.QuarticPowerFree.totalSpace (σ := Fin r) (K := ℂ) T)
        = (T + r).choose r :=
      OAI.QuarticPowerFree.totalSpace_finrank T
    have hMeq : Module.finrank ℂ ↥(Submodule.map
        (Ideal.Quotient.mkₐ ℂ (sliceIdeal p₀ V r e)).toLinearMap
        (OAI.QuarticPowerFree.totalSpace T))
        = Module.finrank ℂ ↥(LinearMap.range Ψ) := by
      rw [← hrange]
      have h1 : Module.finrank ℂ ↥(LinearMap.range Φ)
          + Module.finrank ℂ ↥(LinearMap.ker Φ)
          = Module.finrank ℂ ↥(OAI.QuarticPowerFree.totalSpace (σ := Fin d) (K := ℂ) T) := hΦ
      have h2 : Module.finrank ℂ ↥(LinearMap.range Ψ)
          + Module.finrank ℂ ↥(LinearMap.ker Ψ)
          = Module.finrank ℂ ↥(OAI.QuarticPowerFree.totalSpace (σ := Fin d) (K := ℂ) T) := hΨ
      rw [hker] at h1
      omega
    rw [hMeq]
    exact_mod_cast le_trans hrangeΨ (le_of_eq hfin2)
  have hdim : OAI.QuarticPowerFree.affineDimension (sliceIdeal p₀ V r e)
      = (OAI.QuarticPowerFree.coordinateHilbert (sliceIdeal p₀ V r e)).natDegree :=
    rfl
  rw [hdim]
  conv_rhs => rw [← hQdeg]
  apply OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds
  · filter_upwards [OAI.QuarticPowerFree.coordinateHilbert_eventually
        (sliceIdeal p₀ V r e)] with T hT
    exact le_trans (Nat.cast_nonneg _) (le_of_eq hT)
  · filter_upwards [OAI.QuarticPowerFree.coordinateHilbert_eventually
        (sliceIdeal p₀ V r e)] with T hT
    exact le_trans (le_of_eq hT.symm)
      (le_trans (by exact_mod_cast hHTle T) (hQeval T))

theorem dim_le_of_mem_flat (X : AffineVariety d) (k : ℕ) (hX : X.IsIrreducible)
    (hk : X.dimension = k) (p₀ : Point d) (V : Submodule ℂ (Point d))
    (hXS : X.points ⊆ ↑(AffineSubspace.mk' p₀ V))
    (r : ℕ) (hr : Module.finrank ℂ V = r) : k ≤ r := by
  classical
  haveI : X.ideal.IsPrime := hX
  have e := coordEquiv V r hr
  haveI : (sliceIdeal p₀ V r e).IsPrime := sliceIdeal_prime p₀ V r e
  have hJI : sliceIdeal p₀ V r e ≤ X.ideal := sliceIdeal_le X p₀ V r e hXS
  have hdimJ := sliceIdeal_dim_le p₀ V r hr e
  have hdimX : OAI.QuarticPowerFree.affineDimension X.ideal = k := hk
  have hanti := OAI.QuarticPowerFree.affineDimension_antitone
    (sliceIdeal p₀ V r e) X.ideal hJI
  omega

theorem span_eq_of_dim_eq (X : AffineVariety d) (k : ℕ) (hX : X.IsIrreducible)
    (hk : X.dimension = k) (hXne : X.points.Nonempty)
    (p₀ : Point d) (V : Submodule ℂ (Point d))
    (hXS : X.points ⊆ ↑(AffineSubspace.mk' p₀ V))
    (r : ℕ) (hr : Module.finrank ℂ V = r) (hkr : k = r) :
    X.points = ↑(AffineSubspace.mk' p₀ V) := by
  classical
  haveI : X.ideal.IsPrime := hX
  by_cases hr0 : r = 0
  · subst hr0
    have hVbot : V = ⊥ :=
      Submodule.finrank_eq_zero.mp hr
    have hS : (↑(AffineSubspace.mk' p₀ V) : Set (Point d)) = {p₀} := by
      rw [hVbot]
      ext x
      simp only [AffineSubspace.mem_mk', SetLike.mem_coe, Set.mem_singleton_iff,
        Submodule.mem_bot]
      exact vsub_eq_zero_iff_eq
    rw [hS] at hXS ⊢
    obtain ⟨x0, hx0⟩ := hXne
    have hx0' : x0 = p₀ := Set.mem_singleton_iff.mp (hXS hx0)
    ext x
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hx
      exact Set.mem_singleton_iff.mp (hXS hx)
    · intro hxp
      subst hxp
      exact hx0' ▸ hx0
  · obtain ⟨h, hh⟩ : ∃ h, r = h + 1 := Nat.exists_eq_succ_of_ne_zero hr0
    subst hh
    have e := coordEquiv V (h + 1) hr
    haveI : (sliceIdeal p₀ V (h + 1) e).IsPrime :=
      sliceIdeal_prime p₀ V (h + 1) e
    have hJI : sliceIdeal p₀ V (h + 1) e ≤ X.ideal :=
      sliceIdeal_le X p₀ V (h + 1) e hXS
    have hdimJ_le := sliceIdeal_dim_le p₀ V (h + 1) hr e
    have hdimX : OAI.QuarticPowerFree.affineDimension X.ideal = k := hk
    have hanti := OAI.QuarticPowerFree.affineDimension_antitone
      (sliceIdeal p₀ V (h + 1) e) X.ideal hJI
    have hdimJ : OAI.QuarticPowerFree.affineDimension (sliceIdeal p₀ V (h + 1) e)
        = h + 1 := by
      omega
    have hdimX2 : OAI.QuarticPowerFree.affineDimension X.ideal = h + 1 := by
      rw [hdimX]
      exact hkr
    have hIJ : sliceIdeal p₀ V (h + 1) e = X.ideal := by
      apply OAI.QuarticPowerFree.prime_same_dimension_eq
      · exact hJI
      · exact hdimJ
      · exact hdimX2
    have hloc : X.points
        = MvPolynomial.zeroLocus ℂ (sliceIdeal p₀ V (h + 1) e) := by
      have h1 : X.points = MvPolynomial.zeroLocus ℂ X.ideal := rfl
      rwa [← hIJ] at h1
    rw [hloc, sliceIdeal_zeroLocus p₀ V (h + 1) hr e]

/-- Common-flat assembly: `span X` has full rank and equals every containing flat. -/
theorem commonflat_aux (X : AffineVariety d) (k : ℕ) (hX : X.IsIrreducible)
    (hk : X.dimension = k) (hXne : X.points.Nonempty) (hnl : ¬ IsFlat X)
    (hkd : k + 1 < d) (G : AffineSubspace ℂ (Point d))
    (hG : Module.finrank ℂ G.direction ≤ k + 1) (hXG : X.points ⊆ ↑G) :
    complexSpan X ≠ ⊤ ∧ G = complexSpan X := by
  classical
  haveI : X.ideal.IsPrime := hX
  set S : AffineSubspace ℂ (Point d) := complexSpan X with hS
  have hSG : S ≤ G := affineSpan_le.mpr hXG
  have hdir : S.direction ≤ G.direction := AffineSubspace.direction_le hSG
  have hfrank : Module.finrank ℂ S.direction ≤ Module.finrank ℂ G.direction :=
    Submodule.finrank_mono hdir
  have hstop : Module.finrank ℂ (⊤ : AffineSubspace ℂ (Point d)).direction = d := by
    rw [AffineSubspace.direction_top, finrank_top]
    exact finrank_point d
  have hSne : (S : Set (Point d)).Nonempty :=
    hXne.mono (subset_affineSpan ℂ _)
  obtain ⟨p₀, hp₀⟩ := hSne
  have hp₀' : p₀ ∈ S := hp₀
  have hSeq : S = AffineSubspace.mk' p₀ S.direction :=
    (AffineSubspace.mk'_eq hp₀').symm
  have hr_le : Module.finrank ℂ S.direction ≤ k + 1 := le_trans hfrank hG
  have hSXS : X.points ⊆ ↑(AffineSubspace.mk' p₀ S.direction) := by
    rw [← hSeq]
    exact subset_affineSpan ℂ _
  by_cases hrk : Module.finrank ℂ S.direction ≤ k
  · have hkle : k ≤ Module.finrank ℂ S.direction :=
      dim_le_of_mem_flat X k hX hk p₀ S.direction hSXS _ rfl
    have hreq : Module.finrank ℂ S.direction = k := le_antisymm hrk hkle
    have hflat : IsFlat X := by
      refine ⟨S, ?_⟩
      have heq := span_eq_of_dim_eq X k hX hk hXne p₀ S.direction hSXS _ rfl
        (by omega : k = Module.finrank ℂ ↥S.direction)
      rwa [← hSeq] at heq
    exact absurd hflat hnl
  · have hr_eq : Module.finrank ℂ S.direction = k + 1 := by omega
    have hGdir_eq : S.direction = G.direction := by
      have hle2 : Module.finrank ℂ S.direction = Module.finrank ℂ G.direction := by
        omega
      exact Submodule.eq_of_le_of_finrank_eq hdir hle2
    have hGS : S = G :=
      AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hGdir_eq ⟨p₀, hp₀⟩ hSG
    have hSne_top : S ≠ ⊤ := by
      intro htop
      have hfin : Module.finrank ℂ S.direction = d := by
        rw [htop]
        exact hstop
      omega
    exact ⟨hSne_top, hGS.symm⟩

end GeoCommon
end TrackD
end DistinctDistances
