import DistinctDistances.TrackC.FlatPatch
import DistinctDistances.TrackC.VectorRestriction

open Filter
open scoped Topology

namespace DistinctDistances.TrackC

/-- An open tangent-plane zero patch extends to the whole affine tangent plane
by univariate polynomial identity, as needed at CI:200–204. -/
theorem plane_patch_extension (f : Poly 3) (x : E 3) (r : ℝ) (hr : 0 < r)
    (hpatch : ∀ u ∈ Metric.ball (0 : (polynomialDifferential f x).ker) r,
      evalR f (x + (u : E 3)) = 0) :
    ∀ v : (polynomialDifferential f x).ker, evalR f (x + (v : E 3)) = 0 := by
  intro v
  let ε := r / (‖v‖ + 1)
  have hden : 0 < ‖v‖ + 1 := by positivity
  have hε : 0 < ε := div_pos hr hden
  let p := polynomialVectorRestriction f x v
  have hroot (t : ℝ) (ht : t ∈ Set.Ioo (-ε) ε) : p.IsRoot t := by
    have ht_abs : |t| < ε := abs_lt.mpr ht
    have hnorm : ‖t • v‖ < r := by
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |t| * ‖v‖ ≤ |t| * (‖v‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
        _ < ε * (‖v‖ + 1) := mul_lt_mul_of_pos_right ht_abs hden
        _ = r := div_mul_cancel₀ r hden.ne'
    have hvball : t • v ∈ Metric.ball (0 : (polynomialDifferential f x).ker) r := by
      simpa only [Metric.mem_ball, dist_zero_right] using hnorm
    have hz := hpatch (t • v) hvball
    change (polynomialVectorRestriction f x (v : E 3)).eval t = 0
    rw [eval_polynomialVectorRestriction]
    simpa using hz
  have hp : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p
    ((Set.Ioo_infinite (by linarith : -ε < ε)).mono (fun t ht => hroot t ht))
  have h := congrArg (Polynomial.eval 1) hp
  simpa [p, eval_polynomialVectorRestriction] using h

/-- Local regular flatness therefore forces vanishing on the tangent plane. -/
theorem flat_surface_on_tangent_plane (f : Poly 3) (x : E 3) (hx : regularPoint f x)
    (hflat : ∀ᶠ y in 𝓝 x, regularPoint f y → flatPoint f y) :
    ∀ v : (polynomialDifferential f x).ker, evalR f (x + (v : E 3)) = 0 := by
  obtain ⟨r, hr, hpatch⟩ := flat_surface_tangent_patch f x hx hflat
  exact plane_patch_extension f x r hr hpatch

end DistinctDistances.TrackC
