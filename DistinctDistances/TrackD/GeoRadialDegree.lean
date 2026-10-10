import DistinctDistances.TrackD.GeoRadial
import DistinctDistances.TrackA.DepthAlgebra
import DistinctDistances.Bridges.ProjectiveEnvelope

/-! Radial projection is injective outside a containing flat and preserves curve degree. -/

namespace DistinctDistances.TrackD.GeoRadial

open scoped Classical
noncomputable section
variable {d : ℕ}

theorem radial_injective_flat (S : AffineSubspace ℂ (Point d)) (p : Point d)
    (hp : p ∉ S) (x y : Point d) (hx : x ∈ S) (hy : y ∈ S)
    (hxp : x ≠ p) (hyp : y ≠ p)
    (he : radialProjection p x hxp = radialProjection p y hyp) : x = y := by
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ (x-p) (y-p)
    (sub_ne_zero.mpr hxp) (sub_ne_zero.mpr hyp)).mp he
  by_cases hc1 : c = 1
  · have hs : y-p = x-p := by simpa [hc1] using hc
    have h := congrArg (fun v : Point d => v+p) hs
    simpa only [sub_add_cancel] using h.symm
  · have hc0 : c-1 ≠ 0 := sub_ne_zero.mpr hc1
    have hxy : x-y = (c-1) • (y-p) := by
      calc
        x-y = (x-p)-(y-p) := by abel
        _ = c • (y-p)-(y-p) := by rw [← hc]
        _ = _ := by rw [sub_smul, one_smul]
    have hd : x-y ∈ S.direction := by
      simpa only [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hx hy
    have hdy : y-p ∈ S.direction := by
      have h := S.direction.smul_mem (c-1)⁻¹ hd
      rwa [hxy, smul_smul, inv_mul_cancel₀ hc0, one_smul] at h
    have hdp : p-y ∈ S.direction := by
      simpa only [neg_sub] using S.direction.neg_mem hdy
    have hmem := AffineSubspace.vadd_mem_of_mem_direction hdp hy
    have hpS : p ∈ S := by simpa only [vadd_eq_add, sub_add_cancel] using hmem
    exact (hp hpS).elim

theorem radial_fiber_subsingleton (S : AffineSubspace ℂ (Point d)) (p : Point d)
    (Y : AffineVariety d) (hYS : Y.points ⊆ S) (hp : p ∉ S) (z : ProjectivePoint d) :
    (radialFiber p Y z).Subsingleton := by
  intro x hx y hy
  obtain ⟨hxp, hxz⟩ := hx.2
  obtain ⟨hyp, hyz⟩ := hy.2
  exact radial_injective_flat S p hp x y (hYS hx.1) (hYS hy.1) hxp hyp
    (hxz.trans hyz.symm)

theorem homogeneous_witness (R : ProjectiveVariety d) (g : Poly d) (D : ℕ)
    (hg : g.IsHomogeneous D) (hnot : g ∉ R.ideal) :
    ∃ z ∈ R.points, MvPolynomial.aeval z.rep g ≠ 0 := by
  rw [← R.vanishingIdeal_points] at hnot
  change g ∉ MvPolynomial.vanishingIdeal ℂ
    (ProjectiveVariety.nonzeroRepresentatives R.points) at hnot
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hnot
  push Not at hnot
  obtain ⟨v, ⟨hv, hvR⟩, he⟩ := hnot
  refine ⟨Projectivization.mk ℂ v hv, hvR, ?_⟩
  intro hzero
  apply he
  exact (Bridges.homogeneous_eval_zero_mk_iff g hg v hv).mp hzero

theorem radial_degree_preserved (p : Point d) (Y : AffineVariety d) (hY : IsCurve Y)
    (S : AffineSubspace ℂ (Point d)) (hYS : Y.points ⊆ S) (hp : p ∉ S)
    (himage : (radialImage p Y).dimension = 1) :
    (radialImage p Y).degree = Y.degree := by
  have hr := TrackA.dep_radial_degree_exists Y hY.1 1 (by norm_num) hY.2 p himage
  have hf := TrackA.poly_projection_radial Y hY.1 1 (by norm_num) hY.2 p himage
    (TrackA.radialMapDegree p Y) hr
  obtain ⟨hrpos, g, D, hg, hnot, hfib⟩ := hr
  obtain ⟨z, hz, hgz⟩ := homogeneous_witness (radialImage p Y) g D hg hnot
  obtain ⟨hfin, hcard⟩ := hfib z hz hgz
  have hle : (radialFiber p Y z).ncard ≤ 1 :=
    (Set.ncard_le_one hfin).mpr (fun x hx y hy => radial_fiber_subsingleton S p Y hYS hp z hx hy)
  have hr1 : TrackA.radialMapDegree p Y = 1 := by omega
  have hpY : p ∉ Y.points := fun h => hp (hYS h)
  rw [hr1, Nat.cast_one, one_mul, Y.multiplicity_eq_zero_off p hpY, sub_zero] at hf
  exact hf

end
end DistinctDistances.TrackD.GeoRadial
