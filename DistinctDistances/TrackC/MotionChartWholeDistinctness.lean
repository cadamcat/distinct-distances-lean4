import DistinctDistances.TrackC.MotionChartDistinctness
import DistinctDistances.TrackC.RotationCross

open Classical

noncomputable section

namespace DistinctDistances.TrackC

theorem cross3_smul_self_right (a : E 3) (t : ℝ) : cross3 a (t • a) = 0 := by
  ext i
  fin_cases i <;> simp [cross3] <;> ring

/-- Two explicit parameter points recover the transverse offset and the
axis-height coefficient of a complete motion flat, motions.tex:361–372. -/
theorem MotionChartData.parameter_witnesses {g : Motion 3} (c : MotionChartData g) :
    let a := motionChartAxis c.frame
    let D := motionChartOffset c.frame c.d₀ c.d₁
    let v := c.frame.symm (EuclideanSpace.single (0 : Fin 3) 1)
    ∃ z₀ ∈ c.parameterSet, ∃ z₁ ∈ c.parameterSet,
      wCoord z₀ = c.omega • a ∧ cCoord z₀ = D ∧
      cCoord z₁ = D+c.s • v ∧ cross3 a (wCoord z₁) = v ∧ inner ℝ a v = 0 := by
  let e₀ : E 3 := EuclideanSpace.single (0 : Fin 3) 1
  let z₀ := sixRotate c.frame.symm (canonicalMotionParameter c.s c.omega c.d₀ c.d₁ 0)
  let z₁ := sixRotate c.frame.symm (canonicalMotionParameter c.s c.omega c.d₀ c.d₁ e₀)
  refine ⟨z₀,⟨canonicalMotionParameter c.s c.omega c.d₀ c.d₁ 0,Set.mem_range_self 0,rfl⟩,
    z₁,⟨canonicalMotionParameter c.s c.omega c.d₀ c.d₁ e₀,Set.mem_range_self e₀,rfl⟩,?_,?_,?_,?_,?_⟩
  · apply c.frame.injective
    rw [wCoord_sixRotate,c.frame.apply_symm_apply,map_smul,motionChartAxis_map]
    ext i
    fin_cases i <;> simp [canonicalMotionParameter,wCoord,PiLp.single_apply]
  · change cCoord (sixRotate c.frame.symm (canonicalMotionParameter c.s c.omega c.d₀ c.d₁ 0)) =
      motionChartOffset c.frame c.d₀ c.d₁
    rw [cCoord_sixRotate]
    change c.frame.symm (cCoord (canonicalMotionParameter c.s c.omega c.d₀ c.d₁ 0)) =
      c.frame.symm (WithLp.toLp 2 ![c.d₀,c.d₁,0])
    apply congrArg c.frame.symm
    ext i
    fin_cases i <;> simp [cCoord,canonicalMotionParameter]
  · apply c.frame.injective
    rw [cCoord_sixRotate,c.frame.apply_symm_apply,map_add,map_smul]
    simp only [motionChartOffset,c.frame.apply_symm_apply]
    ext i
    fin_cases i <;> simp [e₀,canonicalMotionParameter,cCoord,PiLp.single_apply] <;> ring
  · apply c.frame.injective
    rw [cross3_rotation c.frame c.proper,motionChartAxis_map,wCoord_sixRotate,c.frame.apply_symm_apply]
    ext i
    fin_cases i <;> simp [cross3,canonicalMotionParameter,wCoord,e₀,PiLp.single_apply]
  · rw [motionChartAxis_inner]
    simp [e₀]

/-- Recover the scalar coupling once the two axis directions are aligned. -/
theorem MotionChartData.recover_parameters {g h : Motion 3}
    (c : MotionChartData g) (d : MotionChartData h) (k : ℝ)
    (hsets : c.parameterSet = d.parameterSet)
    (hperp : motionOrthogonalPart (motionChartAxis d.frame) =
      motionOrthogonalPart (motionChartAxis c.frame))
    (hcross : ∀ w : E 3,d.s • cross3 (motionChartAxis d.frame) w =
      k • cross3 (motionChartAxis c.frame) w) :
    motionChartOffset c.frame c.d₀ c.d₁ = motionChartOffset d.frame d.d₀ d.d₁ ∧ c.s = k := by
  let a := motionChartAxis c.frame
  let D := motionChartOffset c.frame c.d₀ c.d₁
  let D' := motionChartOffset d.frame d.d₀ d.d₁
  let v := c.frame.symm (EuclideanSpace.single (0 : Fin 3) 1)
  obtain ⟨z₀,hz₀,z₁,hz₁,hw₀,hc₀,hc₁,hcross₁,hv⟩ := c.parameter_witnesses
  have hDperp : motionOrthogonalPart a D = D := by simp [a,D,motionChartOffset_perp]
  have hvperp : motionOrthogonalPart a v = v := by
    have hv' : inner ℝ a v = 0 := hv
    simp only [motionOrthogonalPart_apply,hv',zero_smul,sub_zero]
  have hz₀d : z₀ ∈ d.parameterSet := hsets ▸ hz₀
  have hz₁d : z₁ ∈ d.parameterSet := hsets ▸ hz₁
  rw [d.intrinsic_flat] at hz₀d hz₁d
  have hD : D = D' := by
    have h := hz₀d.2
    rw [hperp,hcross,hc₀,hw₀,cross3_smul_self_right,smul_zero,add_zero,hDperp] at h
    exact h
  have hscalar : c.s • v = k • v := by
    have h := hz₁d.2
    rw [hperp,hcross,hc₁,hcross₁,map_add,map_smul,hDperp,hvperp] at h
    change D+c.s • v = D'+k • v at h
    rw [← hD] at h
    exact add_left_cancel h
  have hk : c.s = k := by
    have h := congrArg (fun u : E 3 => (c.frame u) 0) hscalar
    simpa [v,map_smul,PiLp.single_apply] using h
  exact ⟨hD,hk⟩

/-- A whole motion flat determines the full physical motion, independently of
the orthonormal frame used to describe it, motions.tex:361–372. -/
theorem MotionChartData.same_motion_of_parameterSet {g h : Motion 3}
    (c : MotionChartData g) (d : MotionChartData h)
    (hsets : c.parameterSet = d.parameterSet) : g = h := by
  have hplanes := congrArg (fun U : Set (E 6) => wCoord '' U) hsets
  rw [c.w_projection,d.w_projection] at hplanes
  have hplanes' : {w : E 3 | inner ℝ w (motionChartAxis c.frame) = c.omega} =
      {w : E 3 | inner ℝ w (motionChartAxis d.frame) = d.omega} := by
    simpa only [real_inner_comm] using hplanes
  obtain hnormal | hnormal := unit_normal_planes_eq (motionChartAxis c.frame)
    (motionChartAxis d.frame) c.omega d.omega (motionChartAxis_unit c.frame)
    (motionChartAxis_unit d.frame) hplanes'
  · obtain ⟨ha,hω⟩ := hnormal
    have hperp : motionOrthogonalPart (motionChartAxis d.frame) =
        motionOrthogonalPart (motionChartAxis c.frame) := by rw [ha]
    have hcross : ∀ w : E 3,d.s • cross3 (motionChartAxis d.frame) w =
        d.s • cross3 (motionChartAxis c.frame) w := by intro w;rw [ha]
    obtain ⟨hD,hs⟩ := c.recover_parameters d d.s hsets hperp hcross
    ext x : 1
    obtain ⟨hcaxis,hcperp⟩ := c.intrinsic_graph x
    obtain ⟨hdaxis,hdperp⟩ := d.intrinsic_graph x
    rw [ha,hs] at hcaxis
    rw [ha,hω,hD] at hcperp
    apply intrinsic_graph_point_unique (motionChartAxis d.frame) d.omega x (g x) (h x)
    · exact hcaxis.trans hdaxis.symm
    · rw [hcperp,hdperp]
      abel
  · obtain ⟨ha,hω⟩ := hnormal
    have hperp : motionOrthogonalPart (motionChartAxis d.frame) =
        motionOrthogonalPart (motionChartAxis c.frame) := by rw [ha,motionOrthogonalPart_neg]
    have hb : motionChartAxis d.frame = -motionChartAxis c.frame := by rw [ha];simp
    have hcross : ∀ w : E 3,d.s • cross3 (motionChartAxis d.frame) w =
        (-d.s) • cross3 (motionChartAxis c.frame) w := by
      intro w
      rw [hb,cross3_neg_left,smul_neg,neg_smul]
    obtain ⟨hD,hs⟩ := c.recover_parameters d (-d.s) hsets hperp hcross
    ext x : 1
    obtain ⟨hcaxis,hcperp⟩ := c.intrinsic_graph x
    obtain ⟨hdaxis,hdperp⟩ := d.intrinsic_graph x
    have hcaxis' : inner ℝ (motionChartAxis d.frame) (x+g x) = 2*d.s := by
      rw [ha,hs,inner_neg_left] at hcaxis
      linarith
    have hcperp' : motionOrthogonalPart (motionChartAxis d.frame) (x-g x) =
        d.omega • cross3 (motionChartAxis d.frame) (x+g x)+
          2 • motionChartOffset d.frame d.d₀ d.d₁ := by
      simpa only [ha,hω,hD,motionOrthogonalPart_neg,cross3_neg_left,neg_smul,smul_neg,neg_neg] using hcperp
    apply intrinsic_graph_point_unique (motionChartAxis d.frame) d.omega x (g x) (h x)
    · exact hcaxis'.trans hdaxis.symm
    · rw [hcperp',hdperp]
      abel

end DistinctDistances.TrackC
