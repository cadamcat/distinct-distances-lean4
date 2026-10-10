import DistinctDistances.TrackB.AlgebraicNullRigidity
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators
open LinearMap (BilinForm)

variable {K : Type*} [Field K] [Algebra ℂ K] [CharZero K]

/-- B26, concentration.tex:970–985, without an orthogonal coordinate chart.
The selected coordinate derivatives identify the maximal null tangent space;
differentiated null identities put the Hessian in its orthogonal complement. -/
theorem commuting_derivation_null_hessian_zero (r : ℕ)
    (δ : Fin r → Derivation ℂ K K) (ξ : Fin (r + r) → K) (ι : Fin r → Fin (r + r))
    (B : BilinForm K (Fin (r + r) → K)) (hB : B.Nondegenerate) (hSymm : B.IsSymm)
    (hBdiff : ∀ i x y, δ i (B x y) =
      B (fun l => δ i (x l)) y + B x (fun l => δ i (y l)))
    (hcomm : ∀ i j x, δ i (δ j x) = δ j (δ i x))
    (hcoords : ∀ i j, δ i (ξ (ι j)) = if i = j then 1 else 0)
    (hnull : ∀ i j, B (fun l => δ i (ξ l)) (fun l => δ j (ξ l)) = 0) :
    ∀ i j l, δ i (δ j (ξ l)) = 0 := by
  classical
  let t : Fin r → Fin (r + r) → K := fun i l => δ i (ξ l)
  let H : Fin r → Fin r → Fin (r + r) → K := fun i j l => δ i (δ j (ξ l))
  let S : Fin r → Fin r → Fin r → K := fun i j k => B (H i j) (t k)
  have hS : ∀ i j k, S i j k = S j i k := by
    intro i j k
    exact congrArg (fun x => B x (t k)) (funext fun l => hcomm i j (ξ l))
  have hdiff : ∀ i j k, S i j k + S i k j = 0 := by
    intro i j k
    have hd := congrArg (δ i) (hnull j k)
    rw [map_zero, hBdiff] at hd
    have hs : B (t j) (H i k) = B (H i k) (t j) := hSymm.eq _ _
    change B (H i j) (t k) + B (t j) (H i k) = 0 at hd
    rw [hs] at hd
    exact hd
  have hzero : ∀ i j k, S i j k = 0 := by
    intro i j k
    have e1 := hdiff i j k
    have e2 := hdiff j i k
    have e3 := hdiff k i j
    rw [hS j i k] at e2
    rw [hS k i j, hS k j i] at e3
    have htwo : (2 : K) * S i j k = 0 := by linear_combination e1 + e2 - e3
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  let A : (Fin r → K) →ₗ[K] (Fin (r + r) → K) :=
    { toFun := fun c => ∑ i, c i • t i
      map_add' := by intro c d; simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by intro a c; simp [Pi.smul_apply, smul_smul, Finset.smul_sum] }
  have hAcoords : ∀ c j, A c (ι j) = c j := by
    intro c j
    change (∑ i, c i • t i) (ι j) = c j
    simp [t, hcoords, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hAinj : Function.Injective A := by
    intro c d h
    funext j
    have hj := congrFun h (ι j)
    simpa only [hAcoords] using hj
  let L := LinearMap.range A
  have hLdim : Module.finrank K L = r := by
    rw [LinearMap.finrank_range_of_inj hAinj, Module.finrank_fin_fun]
  have hLle : L ≤ B.orthogonal L := by
    intro x hx
    apply B.mem_orthogonal_iff.mpr
    intro y hy
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hx
    obtain ⟨d, rfl⟩ := LinearMap.mem_range.mp hy
    change B (∑ i, d i • t i) (∑ j, c j • t j) = 0
    simp [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, t, hnull]
  have hLorth : L = B.orthogonal L := by
    apply Submodule.eq_of_le_of_finrank_eq hLle
    rw [B.finrank_orthogonal hB, Module.finrank_fin_fun, hLdim]
    omega
  intro i j l
  have hHL : H i j ∈ L := by
    rw [hLorth]
    apply B.mem_orthogonal_iff.mpr
    intro x hx
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hx
    change B (∑ k, c k • t k) (H i j) = 0
    have hz : ∀ k, B (t k) (H i j) = 0 := by
      intro k
      rw [hSymm.eq]
      exact hzero i j k
    simp [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hz]
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hHL
  have hc0 : c = 0 := by
    funext k
    have heq := congrFun hc (ι k)
    rw [hAcoords] at heq
    change c k = δ i (δ j (ξ (ι k))) at heq
    rw [hcoords] at heq
    split_ifs at heq <;> simpa using heq
  have hH0 : H i j = 0 := by rw [← hc, hc0, map_zero]
  exact congrFun hH0 l

#print axioms commuting_derivation_null_hessian_zero
end
end DistinctDistances.TrackB
