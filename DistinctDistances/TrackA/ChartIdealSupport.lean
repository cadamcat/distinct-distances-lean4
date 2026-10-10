import DistinctDistances.TrackA.ProjectiveChartSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

theorem chartPullback_rename {n : ℕ} (i : Fin (n+1)) (f : Poly n) :
    chartPullback i (MvPolynomial.rename i.succAbove f) = f := by
  have h : (chartPullback i).comp (MvPolynomial.rename i.succAbove) =
      AlgHom.id ℂ (Poly n) := by
    ext j
    simp [chartPullback]
  exact congrArg (fun F : Poly n →ₐ[ℂ] Poly n => F f) h

theorem chartPullback_eval {n : ℕ} (i : Fin (n+1)) (f : Poly (n+1)) (x : Point n) :
    MvPolynomial.eval x (chartPullback i f) =
      MvPolynomial.eval (Fin.insertNth i 1 x) f := by
  change MvPolynomial.aeval x (MvPolynomial.aeval
    (Fin.insertNth i (MvPolynomial.C 1) MvPolynomial.X) f) = _
  rw [MvPolynomial.comp_aeval_apply]
  have hcoords : (fun j : Fin (n+1) => MvPolynomial.aeval x
      (Fin.insertNth (α := fun _ => Poly n) i (MvPolynomial.C 1) MvPolynomial.X j)) =
      Fin.insertNth i 1 x := by
    funext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩ <;> simp
  rw [hcoords, MvPolynomial.aeval_eq_eval]

theorem chart_points_from_cone {n : ℕ} (C : ProjectiveVariety (n+1))
    (i : Fin (n+1)) (y : Point (n+1)) (hy : y ∈ C.affineCone.points)
    (hyi : y i = 1) : (fun j => y (i.succAbove j)) ∈ (C.affineChart i).points := by
  have hsurj : Function.Surjective (chartPullback i) := fun f =>
    ⟨MvPolynomial.rename i.succAbove f, chartPullback_rename i f⟩
  have hvec : Fin.insertNth i 1 (fun j => y (i.succAbove j)) = y := by
    funext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩ <;> simp [hyi]
  change (fun j => y (i.succAbove j)) ∈
    (AffineVariety.ofIdeal (C.ideal.map (chartPullback i).toRingHom)).points
  rw [AffineVariety.points_ofIdeal]
  intro f hf
  obtain ⟨g, hg, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective (chartPullback i).toRingHom hsurj).mp hf
  change MvPolynomial.eval (fun j => y (i.succAbove j)) (chartPullback i g) = 0
  rw [chartPullback_eval, hvec]
  simpa only [MvPolynomial.aeval_eq_eval] using hy g hg

/-- A homogeneous radical ideal remains radical in a coordinate chart.
An extra chart-coordinate power makes the lifted equation vanish at infinity. -/
theorem affineChart_ideal_exact {n : ℕ} (C : ProjectiveVariety (n+1)) (i : Fin (n+1)) :
    (C.affineChart i).ideal = C.ideal.map (chartPullback i).toRingHom := by
  apply le_antisymm
  · intro g hg
    let h : Poly (n+1) := MvPolynomial.rename i.succAbove g
    let D := g.totalDegree + 1
    let G := chartHomogenize (MvPolynomial.X i) D h
    have hhdegree : h.totalDegree < D :=
      (MvPolynomial.totalDegree_rename_le i.succAbove g).trans_lt (Nat.lt_succ_self _)
    have hhom : G.IsHomogeneous D :=
      chartHomogenize_homogeneous _ _ (MvPolynomial.isHomogeneous_X ℂ i)
    have hGmap : chartPullback i G = g := by
      have hXi : chartPullback i (MvPolynomial.X i) = 1 := by simp [chartPullback]
      simp only [G, chartHomogenize, map_sum, map_mul, map_pow, hXi, one_pow, one_mul]
      rw [← map_sum, chart_components_sum h hhdegree.le, chartPullback_rename]
    have hGideal : G ∈ C.ideal := by
      change G ∈ C.affineCone.ideal
      rw [← AffineVariety.vanishingIdeal_points]
      intro x hx
      change MvPolynomial.eval x G = 0
      by_cases hxi : x i = 0
      · simp only [G, chartHomogenize, map_sum, map_mul, map_pow, MvPolynomial.eval_X, hxi]
        apply Finset.sum_eq_zero
        intro j hj
        by_cases hjD : j < D
        · rw [zero_pow (by omega : D-j ≠ 0), zero_mul]
        · rw [MvPolynomial.homogeneousComponent_eq_zero j h (by omega)]
          simp
      · let c : ℂ := (x i)⁻¹
        let y := c • x
        have hycone : y ∈ C.affineCone.points := cone_smul_mem C x hx c
        have hyi : y i = 1 := by simp [y, c, hxi]
        have hychart := chart_points_from_cone C i y hycone hyi
        have hgzero : MvPolynomial.eval (fun j => y (i.succAbove j)) g = 0 := by
          simpa only [MvPolynomial.aeval_eq_eval] using hychart g hg
        have hGzero : MvPolynomial.eval y G = 0 := by
          rw [chartHomogenize_eval _ h hhdegree.le y (by simpa using hyi)]
          rw [MvPolynomial.eval_rename]
          exact hgzero
        have hscale : c^D * MvPolynomial.eval x G = 0 := by
          rw [← Bridges.homogeneous_eval_smul G hhom c x]
          exact hGzero
        exact (mul_eq_zero.mp hscale).resolve_left (pow_ne_zero _ (inv_ne_zero hxi))
    have hmap := Ideal.mem_map_of_mem (chartPullback i).toRingHom hGideal
    change chartPullback i G ∈ C.ideal.map (chartPullback i).toRingHom at hmap
    rwa [hGmap] at hmap
  · exact Ideal.le_radical

theorem chartPullback_nonzero {n : ℕ} (i : Fin (n+1)) (f : Poly (n+1))
    (hf : f ≠ 0) (d : ℕ) (hhom : f.IsHomogeneous d) : chartPullback i f ≠ 0 := by
  intro hzero
  have hprod : MvPolynomial.X i * f = 0 := by
    apply MvPolynomial.funext
    intro x
    simp only [map_mul, MvPolynomial.eval_X, map_zero]
    by_cases hxi : x i = 0
    · rw [hxi, zero_mul]
    · let c : ℂ := (x i)⁻¹
      let z : Point n := fun j => x (i.succAbove j) / x i
      have hvec : Fin.insertNth i 1 z = c • x := by
        funext j
        rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩
        · simp [c, hxi]
        · simp [z, c, div_eq_mul_inv, mul_comm]
      have hn : MvPolynomial.eval (c • x) f = 0 := by
        rw [← hvec, ← chartPullback_eval, hzero, map_zero]
      rw [Bridges.homogeneous_eval_smul f hhom] at hn
      have hxf := (mul_eq_zero.mp hn).resolve_left (pow_ne_zero _ (inv_ne_zero hxi))
      rw [hxf, mul_zero]
  exact (mul_ne_zero (MvPolynomial.X_ne_zero i) hf) hprod

theorem principal_chart_equation {n : ℕ} (C : ProjectiveVariety (n+1))
    (f : Poly (n+1)) (hf : f ≠ 0) (hhom : f.IsHomogeneous f.totalDegree)
    (hC : C.ideal = Ideal.span {f}) (i : Fin (n+1)) :
    chartPullback i f ≠ 0 ∧ (C.affineChart i).ideal = Ideal.span {chartPullback i f} := by
  refine ⟨chartPullback_nonzero i f hf _ hhom, ?_⟩
  rw [affineChart_ideal_exact, hC, Ideal.map_span, Set.image_singleton]
  rfl

end
end DistinctDistances.TrackA
