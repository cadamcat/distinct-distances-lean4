import DistinctDistances.TrackD.Genericity
import DistinctDistances.TrackD.DifferentialConstants

namespace DistinctDistances.TrackD

noncomputable section
variable {d : ℕ}

/-- Transfer a constant ratio from an embedding of the reduced coordinate ring back to
all complex points, including the zeros of the denominator. -/
theorem polynomial_ratio_constancy (X : AffineVariety d)
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra.EssFiniteType ℂ K]
    (φ : Poly d →ₐ[ℂ] K) (hker : RingHom.ker φ = X.ideal)
    (a b : Poly d) (hb : ∃ x ∈ X, MvPolynomial.eval x b ≠ 0)
    (hD : φ b • KaehlerDifferential.D ℂ K (φ a) -
      φ a • KaehlerDifferential.D ℂ K (φ b) = 0) :
    ∃ c : ℂ, ∀ x ∈ X, MvPolynomial.eval x a = c * MvPolynomial.eval x b := by
  have hφb : φ b ≠ 0 := by
    intro hz
    obtain ⟨x, hx, hb⟩ := hb
    have hi : b ∈ X.ideal := hker ▸ (RingHom.mem_ker.mpr hz)
    exact hb ((mem_ideal_iff_eval_zero X b).mp hi x hx)
  have hratio : KaehlerDifferential.D ℂ K (φ a / φ b) = 0 := by
    rw [Derivation.leibniz_div, hD, smul_zero]
  obtain ⟨c, hc⟩ := differential_zero_is_constant K (φ a / φ b) hratio
  have hrel : φ (a - MvPolynomial.C c * b) = 0 := by
    have hquot := (div_eq_iff hφb).mp hc
    have hC : φ (MvPolynomial.C c) = algebraMap ℂ K c := φ.commutes c
    rwa [map_sub, map_mul, hC, sub_eq_zero]
  have hI : a - MvPolynomial.C c * b ∈ X.ideal := hker ▸ (RingHom.mem_ker.mpr hrel)
  refine ⟨c, ?_⟩
  intro x hx
  have := (mem_ideal_iff_eval_zero X _).mp hI x hx
  simpa only [map_sub, map_mul, MvPolynomial.eval_C, sub_eq_zero] using this

end
end DistinctDistances.TrackD
