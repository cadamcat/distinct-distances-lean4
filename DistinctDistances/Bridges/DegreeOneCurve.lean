import DistinctDistances.Bridges.CurvePoints
import DistinctDistances.Bridges.CurveComponents
import DistinctDistances.Bridges.ComplexLineModel

/-! A degree-one irreducible affine curve is a parametrized complex line. -/

namespace DistinctDistances.Bridges
open scoped BigOperators Classical
noncomputable section

 theorem curve_hilbert_one_le_two {n : ℕ} (Y : AffineVariety n)
    (hY : Y.IsIrreducible) (hdim : Y.dimension = 1) (hdeg : Y.degree = 1) :
    Y.hilbert 1 ≤ 2 := by
  have hpure : AffineFamily.IsPure {Y} 1 := by
    intro V hV
    simpa only [Finset.mem_singleton.mp hV] using And.intro hY hdim
  have hlocus : AffineFamily.locus {Y} = Y := by
    apply AffineVariety.ext
    simp [AffineFamily.locus, AffineVariety.ofIdeal, Y.isRadical.radical]
  have h := TrackA.poly_hilbert_upper {Y} 1 hpure 1
  have hb : (Y.hilbert 1 : ℚ) ≤ 2 := by
    simpa [AffineFamily.hilbert, hlocus, AffineFamily.degree, hdeg] using h
  exact_mod_cast hb

 theorem degree_one_curve_line {n : ℕ} (Y : AffineVariety n)
    (hY : Y.IsIrreducible) (hdim : Y.dimension = 1) (hdeg : Y.degree = 1) :
    ∃ a v : Point n, v ≠ 0 ∧ Y.points = {z | ∃ t : ℂ, z = a + t • v} := by
  obtain ⟨a,ha⟩ := (curve_points_infinite Y hY hdim).nonempty
  obtain ⟨b,hb,hba⟩ := (curve_points_infinite Y hY hdim).exists_notMem_finset {a}
  have hne : b ≠ a := by simpa using hba
  let v := b-a
  have hv : v ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨j,hj⟩ : ∃ j : Fin n, v j ≠ 0 := by
    by_contra h
    apply hv
    funext i
    exact not_not.mp (fun hi => h ⟨i,hi⟩)
  let H := MvPolynomial.restrictTotalDegree (Fin n) ℂ 1
  let R := restrictionMap Y.points 1
  let E : H →ₗ[ℂ] (Fin 2 → ℂ) := LinearMap.pi fun i =>
    (MvPolynomial.aeval (if i = 0 then a else b)).toLinearMap.comp H.subtype
  have hsurj : Function.Surjective E := by
    intro y
    let c := (y 1 - y 0) / v j
    let f : Poly n := MvPolynomial.C (y 0) +
      MvPolynomial.C c * (MvPolynomial.X j - MvPolynomial.C (a j))
    have hf : f.totalDegree ≤ 1 := by
      dsimp only [f]
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le (by simp)
      apply (MvPolynomial.totalDegree_mul _ _).trans
      rw [MvPolynomial.totalDegree_C, zero_add]
      exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
    refine ⟨⟨f,(MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hf⟩, ?_⟩
    funext i
    fin_cases i
    · simp [E,f]
    · have hj' : b j - a j ≠ 0 := hj
      simp [E,f,c,v, div_mul_cancel₀ _ hj']
  have hkerle : LinearMap.ker R ≤ LinearMap.ker E := by
    intro f hf
    change R f = 0 at hf
    change E f = 0
    funext i
    fin_cases i
    · exact congrFun hf ⟨a,ha⟩
    · exact congrFun hf ⟨b,hb⟩
  have hErank : Module.finrank ℂ (LinearMap.range E) = 2 := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp
  have hRrank : Module.finrank ℂ (LinearMap.range R) ≤ 2 := by
    change restrictionRank Y.points 1 ≤ 2
    rw [restrictionRank_points_eq_hilbert]
    exact curve_hilbert_one_le_two Y hY hdim hdeg
  have hker : LinearMap.ker R = LinearMap.ker E := by
    apply Submodule.eq_of_le_of_finrank_le hkerle
    have he := E.finrank_range_add_finrank_ker
    have hr := R.finrank_range_add_finrank_ker
    change Module.finrank ℂ (LinearMap.range E) + Module.finrank ℂ (LinearMap.ker E) =
      Module.finrank ℂ H at he
    change Module.finrank ℂ (LinearMap.range R) + Module.finrank ℂ (LinearMap.ker R) =
      Module.finrank ℂ H at hr
    rw [hErank] at he
    exact Nat.le_of_add_le_add_left (he.trans_le
      (hr.symm.trans_le (Nat.add_le_add_right hRrank _)))
  have hsubset : Y.points ⊆ (complexLine a v).points := by
    intro z hz
    rw [complexLine_points a v j hj]
    refine ⟨(z j-a j)/v j, ?_⟩
    funext i
    let f : Poly n := MvPolynomial.X i - MvPolynomial.C (a i) -
      MvPolynomial.C (v i / v j) * (MvPolynomial.X j - MvPolynomial.C (a j))
    have hf : f.totalDegree ≤ 1 := by
      dsimp only [f]
      apply (MvPolynomial.totalDegree_sub _ _).trans
      apply max_le
      · exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
      · apply (MvPolynomial.totalDegree_mul _ _).trans
        rw [MvPolynomial.totalDegree_C, zero_add]
        exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
    let F : H := ⟨f,(MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hf⟩
    have hF : F ∈ LinearMap.ker E := by
      change E F = 0
      funext k
      fin_cases k
      · simp [E,F,f]
      · have hj' : b j-a j ≠ 0 := hj
        simp [E,F,f,v, div_mul_cancel₀ _ hj']
    rw [← hker] at hF
    have he := congrFun (show R F = 0 from hF) ⟨z,hz⟩
    change MvPolynomial.aeval z f = 0 at he
    have hi : z i-a i-(v i/v j)*(z j-a j) = 0 := by simpa [f] using he
    change z i = a i + ((z j-a j)/v j)*v i
    field_simp at hi ⊢
    linear_combination hi
  have heq : complexLine a v = Y := curve_eq_of_infinite_subvariety
    (complexLine a v) Y (complexLine_irreducible a v) (complexLine_dimension a v j hj)
    hY ((Y.subvariety_iff_points_subset (complexLine a v)).mpr hsubset)
    (curve_points_infinite Y hY hdim)
  exact ⟨a,v,hv,heq ▸ complexLine_points a v j hj⟩

end
end DistinctDistances.Bridges
