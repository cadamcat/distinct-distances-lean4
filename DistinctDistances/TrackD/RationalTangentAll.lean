import DistinctDistances.TrackD.RationalContainment
import DistinctDistances.TrackD.PolynomialDifferentials

namespace DistinctDistances.TrackD

open scoped BigOperators Classical Topology
noncomputable section

theorem rationalPoint_hasFDerivAt {n m : ℕ} (f : Fin m → Poly n) (g : Poly n)
    (x : Point n) (hg : MvPolynomial.eval x g ≠ 0) :
    HasFDerivAt (rationalPoint f g)
      (LinearMap.toContinuousLinearMap (rationalDifferential f g x)) x := by
  apply hasFDerivAt_pi'.mpr
  intro i
  have hinv := (hasFDerivAt_inv hg).comp x (polynomial_eval_hasFDerivAt g x)
  have hi := (polynomial_eval_hasFDerivAt (f i) x).mul hinv
  convert hi using 1
  · ext z
    simp [rationalPoint, div_eq_mul_inv, Function.comp_def]
  · apply ContinuousLinearMap.ext
    intro v
    simp [rationalDifferential, div_eq_mul_inv]
    ring

/-- The cleared numerator's derivative at a zero of the image equation is
the equation's chain-rule derivative times the nonzero denominator power. -/
theorem rationalNumerator_differential_at_zero {n m : ℕ}
    (f : Fin m → Poly n) (g : Poly n) (q : Poly m) (x : Point n)
    (hg : MvPolynomial.eval x g ≠ 0)
    (hq : MvPolynomial.eval (rationalPoint f g x) q = 0) :
    differential (rationalNumerator f g q) x =
      (MvPolynomial.eval x g)^q.totalDegree •
        (differential q (rationalPoint f g x)).comp (rationalDifferential f g x) := by
  have hchain := (polynomial_eval_hasFDerivAt q (rationalPoint f g x)).comp x
    (rationalPoint_hasFDerivAt f g x hg)
  have hprod := ((polynomial_eval_hasFDerivAt g x).pow q.totalDegree).mul hchain
  simp only [Function.comp_apply, hq, smul_smul, zero_mul, zero_smul, add_zero] at hprod
  have heq : (fun y : Point n => MvPolynomial.eval y (rationalNumerator f g q)) =ᶠ[𝓝 x]
      (fun y => (MvPolynomial.eval y g)^q.totalDegree * MvPolynomial.eval (rationalPoint f g y) q) := by
    filter_upwards [(polynomial_eval_hasFDerivAt g x).continuousAt.eventually_ne hg] with y hy
    exact rationalNumerator_eval f g q y hy
  have hnum := hprod.congr_of_eventuallyEq heq
  have hderiv := (polynomial_eval_hasFDerivAt (rationalNumerator f g q) x).unique hnum
  apply LinearMap.ext
  intro v
  have h := congrArg (fun L : Point n →L[ℂ] ℂ => L v) hderiv
  simpa using h

/-- `secants.tex:69–81`: all-point tangent containment follows by clearing
the image equations and differentiating on the denominator chart. -/
theorem rational_image_tangent_all {n m : ℕ}
    (X : AffineVariety n) (f : Fin m → Poly n) (g : Poly n)
    (x : Point n) (hx : x ∈ X) (hg : MvPolynomial.eval x g ≠ 0) :
    (X.tangentSpace x).map (rationalDifferential f g x) ≤
      (rationalImage X f g).tangentSpace (rationalPoint f g x) := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
  simp only [AffineVariety.tangentSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  intro q
  have hq0 : MvPolynomial.eval (rationalPoint f g x) q.val = 0 :=
    rationalPoint_mem_image X f g x hx hg q.val q.property
  let a := rationalNumerator f g q.val
  have hI : g * a ∈ X.ideal := (mem_ideal_iff_eval_zero X _).mpr (by
    intro z hz
    rw [map_mul]
    by_cases hzg : MvPolynomial.eval z g = 0
    · rw [hzg, zero_mul]
    · have hqz : MvPolynomial.eval (rationalPoint f g z) q.val = 0 :=
        rationalPoint_mem_image X f g z hz hzg q.val q.property
      change MvPolynomial.eval z g * MvPolynomial.eval z (rationalNumerator f g q.val) = 0
      rw [rationalNumerator_eval f g q.val z hzg, hqz, mul_zero, mul_zero])
  have hda : differential (g * a) x v = 0 :=
    (Submodule.mem_iInf _).mp hv ⟨g * a, hI⟩
  have ha0 : MvPolynomial.eval x a = 0 := by
    dsimp only [a]
    rw [rationalNumerator_eval f g q.val x hg, hq0, mul_zero]
  rw [differential_mul, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, ha0, zero_smul, zero_add, smul_eq_mul] at hda
  have hda0 : differential a x v = 0 := (mul_eq_zero.mp hda).resolve_left hg
  have hformula := rationalNumerator_differential_at_zero f g q.val x hg hq0
  have h := congrArg (fun L : Point n →ₗ[ℂ] ℂ => L v) hformula
  change differential a x v = (MvPolynomial.eval x g)^q.val.totalDegree *
    differential q.val (rationalPoint f g x) (rationalDifferential f g x v) at h
  rw [hda0] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ hg)

end
end DistinctDistances.TrackD
