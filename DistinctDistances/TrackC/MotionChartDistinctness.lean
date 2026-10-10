import DistinctDistances.TrackC.MotionChartData
import DistinctDistances.TrackC.NormalPlaneUniqueness

open Classical

noncomputable section

namespace DistinctDistances.TrackC

theorem motionOrthogonalPart_neg (a : E 3) : motionOrthogonalPart (-a) = motionOrthogonalPart a := by
  ext x
  simp [inner_neg_left,neg_smul,smul_neg]

theorem cross3_neg_left (a x : E 3) : cross3 (-a) x = -cross3 a x := by
  ext i
  fin_cases i <;> simp [cross3] <;> ring

theorem MotionChartData.linear_intrinsic {g : Motion 3} (c : MotionChartData g) (x : E 3) :
    inner ℝ (motionChartAxis c.frame) (x+g.linearIsometryEquiv x) = 0 ∧
      motionOrthogonalPart (motionChartAxis c.frame) (x-g.linearIsometryEquiv x) =
        c.omega • cross3 (motionChartAxis c.frame) (x+g.linearIsometryEquiv x) := by
  let a := motionChartAxis c.frame
  let D := motionChartOffset c.frame c.d₀ c.d₁
  have hg : g x = g.linearIsometryEquiv x+g 0 := by
    have h := g.map_vadd (0 : E 3) x
    simpa only [vadd_eq_add,add_zero] using h
  obtain ⟨haxisx,hperpx⟩ := c.intrinsic_graph x
  obtain ⟨haxis0,hperp0⟩ := c.intrinsic_graph 0
  have hzero : motionOrthogonalPart a (-g 0) = c.omega • cross3 a (g 0)+2 • D := by
    simpa only [zero_sub,zero_add] using hperp0
  constructor
  · rw [hg] at haxisx
    simp only [inner_add_right] at haxisx
    simp only [zero_add] at haxis0
    rw [inner_add_right]
    linarith
  · calc
      motionOrthogonalPart a (x-g.linearIsometryEquiv x) =
          motionOrthogonalPart a (x-g x)-motionOrthogonalPart a (-g 0) := by
        rw [← map_sub,hg]
        congr 1
        abel
      _ = (c.omega • cross3 a (x+g x)+2 • D)-(c.omega • cross3 a (g 0)+2 • D) := by
        rw [hperpx,hzero]
      _ = c.omega • (cross3 a (x+g x)-cross3 a (g 0)) := by
        rw [smul_sub]
        abel
      _ = c.omega • cross3 a (x+g.linearIsometryEquiv x) := by
        rw [← cross3_sub_right,hg]
        congr 2
        abel

/-- The w-plane determines the complete linear part of a motion,
motions.tex:352–359. -/
theorem MotionChartData.same_linear_of_plane {g h : Motion 3}
    (c : MotionChartData g) (d : MotionChartData h)
    (hplane : {w : E 3 | inner ℝ (motionChartAxis c.frame) w = c.omega} =
      {w : E 3 | inner ℝ (motionChartAxis d.frame) w = d.omega}) :
    g.linearIsometryEquiv = h.linearIsometryEquiv := by
  have hplane' : {w : E 3 | inner ℝ w (motionChartAxis c.frame) = c.omega} =
      {w : E 3 | inner ℝ w (motionChartAxis d.frame) = d.omega} := by
    simpa only [real_inner_comm] using hplane
  obtain hnormal | hnormal := unit_normal_planes_eq (motionChartAxis c.frame)
    (motionChartAxis d.frame) c.omega d.omega (motionChartAxis_unit c.frame)
    (motionChartAxis_unit d.frame) hplane'
  · obtain ⟨ha,hω⟩ := hnormal
    apply LinearIsometryEquiv.ext
    intro x
    obtain ⟨hcaxis,hcperp⟩ := c.linear_intrinsic x
    obtain ⟨hdaxis,hdperp⟩ := d.linear_intrinsic x
    rw [ha] at hcaxis
    rw [ha,hω] at hcperp
    apply intrinsic_graph_point_unique (motionChartAxis d.frame) d.omega x
      (g.linearIsometryEquiv x) (h.linearIsometryEquiv x)
    · exact hcaxis.trans hdaxis.symm
    · rw [hcperp,hdperp]
      simp
  · obtain ⟨ha,hω⟩ := hnormal
    apply LinearIsometryEquiv.ext
    intro x
    obtain ⟨hcaxis,hcperp⟩ := c.linear_intrinsic x
    obtain ⟨hdaxis,hdperp⟩ := d.linear_intrinsic x
    have hcaxis' : inner ℝ (motionChartAxis d.frame) (x+g.linearIsometryEquiv x) = 0 := by
      simpa only [ha,inner_neg_left,neg_eq_zero] using hcaxis
    have hcperp' : motionOrthogonalPart (motionChartAxis d.frame) (x-g.linearIsometryEquiv x) =
        d.omega • cross3 (motionChartAxis d.frame) (x+g.linearIsometryEquiv x) := by
      simpa only [ha,hω,motionOrthogonalPart_neg,cross3_neg_left,neg_smul,smul_neg,neg_neg] using hcperp
    apply intrinsic_graph_point_unique (motionChartAxis d.frame) d.omega x
      (g.linearIsometryEquiv x) (h.linearIsometryEquiv x)
    · exact hcaxis'.trans hdaxis.symm
    · rw [hcperp',hdperp]
      simp

theorem motion_eq_of_same_linear_match (g h : Motion 3)
    (hlin : g.linearIsometryEquiv = h.linearIsometryEquiv) (x : E 3) (hx : g x = h x) : g = h := by
  ext z : 1
  have hpoint : (z-x)+ᵥ x = z := by change (z-x)+x = z;abel
  have hg := g.map_vadd x (z-x)
  have hh := h.map_vadd x (z-x)
  rw [hpoint] at hg hh
  calc
    g z = g.linearIsometryEquiv (z-x)+ᵥ g x := hg
    _ = h.linearIsometryEquiv (z-x)+ᵥ h x := by rw [hlin,hx]
    _ = h z := hh.symm

/-- Equality of two matched sections determines the incident motion,
motions.tex:350–359. -/
theorem MotionChartData.same_motion_of_pair_section {g h : Motion 3}
    (c : MotionChartData g) (d : MotionChartData h) (x y : E 3)
    (hg : g x = y) (hh : h x = y)
    (hsection : pairFlatSet x y ∩ c.parameterSet = pairFlatSet x y ∩ d.parameterSet) : g = h := by
  have hplane := congrArg (fun U : Set (E 6) => wCoord '' U) hsection
  rw [c.pair_w_projection x y hg,d.pair_w_projection x y hh] at hplane
  exact motion_eq_of_same_linear_match g h (c.same_linear_of_plane d hplane) x (hg.trans hh.symm)

end DistinctDistances.TrackC
