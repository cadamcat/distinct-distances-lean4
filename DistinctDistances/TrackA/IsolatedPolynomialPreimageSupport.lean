import DistinctDistances.TrackA.PrincipalPointIsolationSupport

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- The actual point map given by the supplied original coordinate polynomials. -/
def polynomialPoint {n m : ℕ} (a : Fin m → Poly n) (x : Point n) : Point m :=
  fun i => MvPolynomial.eval x (a i)

/-- Pullback along those same original coordinates. -/
def polynomialPointPullback {n m : ℕ} (a : Fin m → Poly n) : Poly m →ₐ[ℂ] Poly n :=
  MvPolynomial.aeval a

theorem polynomialPointPullback_eval {n m : ℕ} (a : Fin m → Poly n) (x : Point n)
    (f : Poly m) :
    MvPolynomial.eval x (polynomialPointPullback a f) = MvPolynomial.eval (polynomialPoint a x) f := by
  change MvPolynomial.aeval x (MvPolynomial.aeval a f) =
    MvPolynomial.aeval (fun i => MvPolynomial.aeval x (a i)) f
  rw [MvPolynomial.comp_aeval_apply]

/-- The original pulled equation ideal contains exactly the stated
center equations; no radical replacement is made in this argument. -/
theorem polynomial_preimage_zeroLocus {n m : ℕ} (I : Ideal (Poly n))
    (K : Ideal (Poly m)) (a : Fin m → Poly n) (x : Point n) :
    x ∈ MvPolynomial.zeroLocus ℂ (I ⊔ K.map (polynomialPointPullback a).toRingHom) ↔
      x ∈ MvPolynomial.zeroLocus ℂ I ∧ polynomialPoint a x ∈ MvPolynomial.zeroLocus ℂ K := by
  constructor
  · intro hx
    refine ⟨fun f hf => hx f (Ideal.mem_sup_left hf), ?_⟩
    intro f hf
    have h := hx _ (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hf))
    change MvPolynomial.eval x (polynomialPointPullback a f) = 0 at h
    simpa only [polynomialPointPullback_eval, MvPolynomial.aeval_eq_eval] using h
  · rintro ⟨hx, hy⟩
    have hI : I ⊔ K.map (polynomialPointPullback a).toRingHom ≤ pointIdeal x := by
      apply sup_le
      · intro f hf
        rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff]
        exact hx f hf
      · rw [Ideal.map_le_iff_le_comap]
        intro f hf
        change polynomialPointPullback a f ∈ pointIdeal x
        rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff]
        change MvPolynomial.eval x (polynomialPointPullback a f) = 0
        rw [polynomialPointPullback_eval]
        exact hy f hf
    intro f hf
    have h := hI hf
    rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff] at h
    exact h

/-- An isolated original center and a finite local original source fiber
make its preimage a minimal point component of the ORIGINAL pulled ideal. -/
theorem point_minimal_polynomial_preimage {n m : ℕ} (I : Ideal (Poly n))
    (K : Ideal (Poly m)) (a : Fin m → Poly n) (x : Point n)
    (hx : x ∈ MvPolynomial.zeroLocus ℂ I)
    (hcenter : pointIdeal (polynomialPoint a x) ∈ K.minimalPrimes)
    (g : Poly n) (hgx : MvPolynomial.eval x g ≠ 0)
    (hfinite : {z : Point n | z ∈ MvPolynomial.zeroLocus ℂ I ∧ MvPolynomial.eval z g ≠ 0 ∧
      polynomialPoint a z = polynomialPoint a x}.Finite) :
    pointIdeal x ∈ (I ⊔ K.map (polynomialPointPullback a).toRingHom).minimalPrimes := by
  obtain ⟨h, hhx, hopen⟩ := minimal_point_principal_open K (polynomialPoint a x) hcenter
  let J := I ⊔ K.map (polynomialPointPullback a).toRingHom
  let k := polynomialPointPullback a h * g
  have hxK : polynomialPoint a x ∈ MvPolynomial.zeroLocus ℂ K := by
    intro f hf
    have h := hcenter.le hf
    rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff] at h
    exact h
  have hxJ : x ∈ MvPolynomial.zeroLocus ℂ J :=
    (polynomial_preimage_zeroLocus I K a x).mpr ⟨hx, hxK⟩
  have hkx : MvPolynomial.eval x k ≠ 0 := by
    simpa only [k, map_mul, polynomialPointPullback_eval, mul_ne_zero_iff] using And.intro hhx hgx
  apply point_minimal_of_principal_finite_locus J x hxJ k hkx
  apply hfinite.subset
  intro z hz
  obtain ⟨hzJ, hzk⟩ := hz
  obtain ⟨hzI, hzK⟩ := (polynomial_preimage_zeroLocus I K a z).mp hzJ
  have hzparts : MvPolynomial.eval (polynomialPoint a z) h ≠ 0 ∧ MvPolynomial.eval z g ≠ 0 := by
    simpa only [k, map_mul, polynomialPointPullback_eval, mul_ne_zero_iff] using hzk
  exact ⟨hzI, hzparts.2, hopen (polynomialPoint a z) hzK hzparts.1⟩

end
end DistinctDistances.TrackA
