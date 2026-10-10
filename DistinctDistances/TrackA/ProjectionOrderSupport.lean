import DistinctDistances.TrackA.Definitions
import DistinctDistances.TrackA.ChartIdealSupport
import DistinctDistances.TrackA.PointPowerLengthSupport
import OAI.NumberTheory.PowerFree.ResidueBounds

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- Homogeneous scaling also holds in a finite jet algebra. -/
theorem homogeneous_aeval_scale {m D : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R]
    (F : Poly m) (hF : F.IsHomogeneous D) (c : R) (v : Fin m → R) :
    MvPolynomial.aeval (fun j => c * v j) F = c^D * MvPolynomial.aeval v F := by
  classical
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq,
    mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← hF.degree_eq_sum_deg_support hs]
  ring

/-- Rational chart coordinates are defined in each finite jet quotient.
The chart denominator is a unit there, so clearing it preserves order. -/
theorem homogeneous_pullback_order {n m D : ℕ} (a : Fin (m+1) → Poly n)
    (F : Poly (m+1)) (hF : F.IsHomogeneous D) (p : Point n) (i : Fin (m+1))
    (hi : MvPolynomial.eval p (a i) ≠ 0) (r : ℕ)
    (horder : OrderAtLeast (chartPullback i F)
      (fun j => MvPolynomial.eval p (a (i.succAbove j)) / MvPolynomial.eval p (a i)) r) :
    OrderAtLeast (MvPolynomial.aeval a F) p r := by
  by_cases hr : r = 0
  · subst r
    simp [OrderAtLeast]
  let K := pointIdealOver p
  let R := Poly n ⧸ K^r
  let q : Poly n →ₐ[ℂ] R := Ideal.Quotient.mkₐ ℂ (K^r)
  have hK : K = RingHom.ker (MvPolynomial.aeval p).toRingHom := by
    ext f
    change f ∈ MvPolynomial.vanishingIdeal ℂ {p} ↔ _
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff, RingHom.mem_ker]
    rfl
  have hle : K^r ≤ RingHom.ker (MvPolynomial.aeval p).toRingHom := by
    rw [← hK]
    exact Ideal.pow_le_self hr
  let ρ : R →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ (K^r) (MvPolynomial.aeval p) hle
  have hρ (f : Poly n) : ρ (q f) = MvPolynomial.eval p f := by
    change MvPolynomial.aeval p f = MvPolynomial.eval p f
    simp only [MvPolynomial.aeval_eq_eval]
  have hker : RingHom.ker ρ.toRingHom = K.map q.toRingHom := by
    change RingHom.ker (Ideal.Quotient.lift (K^r) (MvPolynomial.aeval p).toRingHom hle) = _
    rw [Ideal.ker_quotient_lift, ← hK]
    rfl
  have hnil : (RingHom.ker ρ.toRingHom)^r = ⊥ := by
    rw [hker, ← Ideal.map_pow q.toRingHom K r]
    exact Ideal.map_quotient_self (K^r)
  have hnot : a i ∉ K := by
    rw [hK, RingHom.mem_ker]
    change MvPolynomial.aeval p (a i) ≠ 0
    simpa only [MvPolynomial.aeval_eq_eval] using hi
  obtain ⟨u, hu⟩ := Ideal.Quotient.isUnit_mk_pow_of_notMem K (n := r) hnot
  change (u : R) = q (a i) at hu
  let b : Fin m → R := fun j => ↑(u⁻¹) * q (a (i.succAbove j))
  have huρ : ρ (↑(u⁻¹) : R) = (MvPolynomial.eval p (a i))⁻¹ := by
    have hh : ρ (↑(u⁻¹) : R) * MvPolynomial.eval p (a i) = 1 := by
      rw [← hρ, ← hu, ← map_mul]
      simp
    have hh' := congrArg (fun z : ℂ => z * (MvPolynomial.eval p (a i))⁻¹) hh
    simpa [mul_assoc, hi] using hh'
  let B : Poly m →ₐ[ℂ] R := MvPolynomial.aeval b
  have hcomp : ρ.comp B = MvPolynomial.aeval
      (fun j => MvPolynomial.eval p (a (i.succAbove j)) / MvPolynomial.eval p (a i)) := by
    ext j
    simp [B, b, huρ, hρ, div_eq_mul_inv, mul_comm]
  have hmap : (pointIdealOver
      (fun j => MvPolynomial.eval p (a (i.succAbove j)) / MvPolynomial.eval p (a i))).map
      B.toRingHom ≤ RingHom.ker ρ.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change (ρ.comp B) f = 0
    rw [hcomp]
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff _ f).mp hf
  have hBzero : B (chartPullback i F) = 0 := by
    have hh := Ideal.mem_map_of_mem B.toRingHom horder
    rw [Ideal.map_pow] at hh
    have hh' := (pow_le_pow_left' hmap r) hh
    rw [hnil] at hh'
    exact hh'
  have hcoords : Fin.insertNth i (1 : R) b =
      fun j => ↑(u⁻¹) * q (a j) := by
    funext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
    · simp [hu.symm]
    · simp [b]
  have hchart : B (chartPullback i F) =
      MvPolynomial.aeval (fun j => ↑(u⁻¹) * q (a j)) F := by
    change MvPolynomial.aeval b (MvPolynomial.aeval
      (Fin.insertNth i (MvPolynomial.C 1) MvPolynomial.X) F) = _
    rw [MvPolynomial.comp_aeval_apply]
    have harg : (fun j => MvPolynomial.aeval b
        (Fin.insertNth (α := fun _ => Poly m) i (MvPolynomial.C 1) MvPolynomial.X j)) =
        Fin.insertNth i (1 : R) b := by
      funext j
      rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩ <;> simp
    rw [harg, hcoords]
  have hscale : (↑(u⁻¹) : R)^D * q (MvPolynomial.aeval a F) = 0 := by
    rw [MvPolynomial.comp_aeval_apply]
    rw [← homogeneous_aeval_scale F hF]
    exact hchart.symm.trans hBzero
  have hqzero : q (MvPolynomial.aeval a F) = 0 := by
    exact (IsUnit.pow D (Units.isUnit u⁻¹)).mul_right_eq_zero.mp hscale
  exact Ideal.Quotient.eq_zero_iff_mem.mp hqzero

end
end DistinctDistances.TrackA
