import DistinctDistances.TrackC.MotionGeometry

namespace DistinctDistances.TrackC

/-- Three nonvertical graph-dual sections have no common direction inside
their motion flat, motions.tex:423–431. The gradient proof supplies the
translated pair-flat memberships through its null-flat direction lemma. -/
theorem motion_model_direction_transverse (g : Motion 3) (S : Finset (E 3))
    (G : Flat 6 3) (hmodel : MotionFlatModel g S G) (z v : E 6)
    (hz : z ∈ G.1) (hv : v ∈ G.1.direction)
    (x₀ x₁ x₂ : E 3) (hx₀ : x₀ ∈ S) (hx₁ : x₁ ∈ S) (hx₂ : x₂ ∈ S)
    (htri : ¬ Collinear ℝ ({x₀,x₁,x₂} : Set (E 3)))
    (hz₀ : z ∈ pairFlatSet x₀ (g x₀)) (hz₁ : z ∈ pairFlatSet x₁ (g x₁))
    (hz₂ : z ∈ pairFlatSet x₂ (g x₂))
    (hv₀ : v+z ∈ pairFlatSet x₀ (g x₀)) (hv₁ : v+z ∈ pairFlatSet x₁ (g x₁))
    (hv₂ : v+z ∈ pairFlatSet x₂ (g x₂)) : v = 0 := by
  classical
  rcases hmodel with ⟨_, T, φ, hφ, hrange, hsection, hprojected⟩
  have hflat : G.1 = (⊤ : AffineSubspace ℝ (E 3)).map φ := by
    apply SetLike.coe_injective
    change (G.1 : Set (E 6)) = φ '' (Set.univ : Set (E 3))
    rw [Set.image_univ, hrange]
  have hdir : G.1.direction = LinearMap.range φ.linear := by
    rw [hflat, AffineSubspace.map_direction, AffineSubspace.direction_top,
      Submodule.map_top]
  have hvRange : v ∈ LinearMap.range φ.linear := by
    rw [← hdir]
    exact hv
  obtain ⟨q, hq⟩ := LinearMap.mem_range.mp hvRange
  have hzRange : z ∈ Set.range φ := by
    rw [hrange]
    exact hz
  obtain ⟨u, hu⟩ := hzRange
  have hzG' : v + z ∈ G.1 := by
    exact G.1.vadd_mem_of_mem_direction hv hz
  have hplanes (x : E 3) (hx : x ∈ S) (hpair : z ∈ pairFlatSet x (g x))
      (hpair' : v + z ∈ pairFlatSet x (g x)) :
      u ∈ graphDualPlane (T x) ∧ q +ᵥ u ∈ graphDualPlane (T x) := by
    have himage : z ∈ φ '' graphDualPlane (T x) := by
      rw [← hsection x hx]
      exact ⟨hpair, hz⟩
    obtain ⟨u₀, hu₀, hφu₀⟩ := himage
    have huu₀ : u₀ = u := hφ (hφu₀.trans hu.symm)
    subst u₀
    have himage' : v + z ∈ φ '' graphDualPlane (T x) := by
      rw [← hsection x hx]
      exact ⟨hpair', hzG'⟩
    obtain ⟨u₁, hu₁, hφu₁⟩ := himage'
    have hφqu : φ (q +ᵥ u) = v + z := by
      rw [φ.map_vadd, hq, hu]
      simp
    have huu₁ : u₁ = q +ᵥ u := hφ (hφu₁.trans hφqu.symm)
    have hqu₁ : q +ᵥ u ∈ graphDualPlane (T x) := by
      rw [← huu₁]
      exact hu₁
    exact ⟨hu₀, hqu₁⟩
  have hp0 := hplanes x₀ hx₀ hz₀ hv₀
  have hp1 := hplanes x₁ hx₁ hz₁ hv₁
  have hp2 := hplanes x₂ hx₂ hz₂ hv₂
  have hq0 : q 2 + q 0 * (T x₀) 0 + q 1 * (T x₀) 1 = 0 := by
    have h₀ := hp0.1
    have h₁ := hp0.2
    change u 2 + u 0 * (T x₀) 0 + u 1 * (T x₀) 1 = (T x₀) 2 at h₀
    change (q +ᵥ u) 2 + (q +ᵥ u) 0 * (T x₀) 0 +
      (q +ᵥ u) 1 * (T x₀) 1 = (T x₀) 2 at h₁
    simp only [vadd_eq_add, PiLp.add_apply] at h₁
    linarith
  have hq1 : q 2 + q 0 * (T x₁) 0 + q 1 * (T x₁) 1 = 0 := by
    have h₀ := hp1.1
    have h₁ := hp1.2
    change u 2 + u 0 * (T x₁) 0 + u 1 * (T x₁) 1 = (T x₁) 2 at h₀
    change (q +ᵥ u) 2 + (q +ᵥ u) 0 * (T x₁) 0 +
      (q +ᵥ u) 1 * (T x₁) 1 = (T x₁) 2 at h₁
    simp only [vadd_eq_add, PiLp.add_apply] at h₁
    linarith
  have hq2 : q 2 + q 0 * (T x₂) 0 + q 1 * (T x₂) 1 = 0 := by
    have h₀ := hp2.1
    have h₁ := hp2.2
    change u 2 + u 0 * (T x₂) 0 + u 1 * (T x₂) 1 = (T x₂) 2 at h₀
    change (q +ᵥ u) 2 + (q +ᵥ u) 0 * (T x₂) 0 +
      (q +ᵥ u) 1 * (T x₂) 1 = (T x₂) 2 at h₁
    simp only [vadd_eq_add, PiLp.add_apply] at h₁
    linarith
  let P (x : E 3) : E 2 := WithLp.toLp 2 ![(T x) 0, (T x) 1]
  let p : Fin 3 → E 2 := ![P x₀, P x₁, P x₂]
  have hnoncol : ¬ Collinear ℝ ({p 0, p 1, p 2} : Set (E 2)) := by
    simpa [p, P] using hprojected x₀ hx₀ x₁ hx₁ x₂ hx₂ htri
  have hAI : AffineIndependent ℝ p := by
    simpa [p] using (affineIndependent_iff_not_collinear_set (k := ℝ)
      (p₁ := p 0) (p₂ := p 1) (p₃ := p 2)).2 hnoncol
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    !![p 0 0, p 0 1, 1; p 1 0, p 1 1, 1; p 2 0, p 2 1, 1]
  have hrows : LinearIndependent ℝ M.row := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have h0 := congrArg (fun r : Fin 3 → ℝ => r 0) ha
    have h1 := congrArg (fun r : Fin 3 → ℝ => r 1) ha
    have h2 := congrArg (fun r : Fin 3 → ℝ => r 2) ha
    simp [M, Fin.sum_univ_three] at h0 h1 h2
    have hsum : ∑ j : Fin 3, a j = 0 := by
      simpa [Fin.sum_univ_three] using h2
    have hpoints : ∑ j : Fin 3, a j • p j = 0 := by
      ext k
      fin_cases k
      · simpa [Fin.sum_univ_three] using h0
      · simpa [Fin.sum_univ_three] using h1
    have hweighted : Finset.univ.weightedVSub p a = 0 := by
      calc
        Finset.univ.weightedVSub p a =
            ∑ j : Fin 3, a j • (p j -ᵥ p 0) := by
          rw [Finset.univ.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero
            a p hsum (p 0), Finset.weightedVSubOfPoint_apply]
        _ = (∑ j : Fin 3, a j • p j) - (∑ j : Fin 3, a j) • p 0 := by
          simp only [vsub_eq_sub, smul_sub]
          rw [Finset.sum_sub_distrib, Finset.sum_smul]
        _ = 0 := by rw [hpoints, hsum]; simp
    have haAll : ∀ j : Fin 3, a j = 0 :=
      (affineIndependent_iff_of_fintype ℝ p).mp hAI a hsum hweighted
    exact haAll i
  have hMunit : IsUnit M := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  have hq0' : q 2 + q 0 * p 0 0 + q 1 * p 0 1 = 0 := by simpa [p, P] using hq0
  have hq1' : q 2 + q 0 * p 1 0 + q 1 * p 1 1 = 0 := by simpa [p, P] using hq1
  have hq2' : q 2 + q 0 * p 2 0 + q 1 * p 2 1 = 0 := by simpa [p, P] using hq2
  have hMmul : M.mulVec ![q 0, q 1, q 2] = 0 := by
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, M, Fin.sum_univ_three]
      nlinarith [hq0']
    · simp [Matrix.mulVec, dotProduct, M, Fin.sum_univ_three]
      nlinarith [hq1']
    · simp [Matrix.mulVec, dotProduct, M, Fin.sum_univ_three]
      nlinarith [hq2']
  have hqvec : ![q 0, q 1, q 2] = 0 := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hMunit)
    simpa using hMmul
  have hqzero : q = 0 := by
    ext i
    fin_cases i
    · have h := congrArg (fun w : Fin 3 → ℝ => w 0) hqvec
      simpa using h
    · have h := congrArg (fun w : Fin 3 → ℝ => w 1) hqvec
      simpa using h
    · have h := congrArg (fun w : Fin 3 → ℝ => w 2) hqvec
      simpa using h
  rw [← hq]
  simp [hqzero]

end DistinctDistances.TrackC
