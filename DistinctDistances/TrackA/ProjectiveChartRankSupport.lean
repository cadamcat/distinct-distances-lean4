import DistinctDistances.TrackA.ProjectiveChartSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A chart with homogeneous kernel recovery has exactly the same restriction ranks. -/
theorem linearChart_hilbert {n : ℕ} (V : ProjectiveVariety n) (A : AffineVariety n)
    (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1) (hIA : V.ideal ≤ A.ideal)
    (hℓA : ℓ - 1 ∈ A.ideal)
    (hmem : ∀ (d : ℕ) (f : Poly n), f.IsHomogeneous d →
      (f ∈ A.ideal ↔ f ∈ V.ideal)) (D : ℕ) : A.hilbert D = V.hilbert D := by
  classical
  let Q := Ideal.Quotient.factorₐ ℂ hIA
  let S := V.restrictionSpace D
  let T := A.restrictionSpace D
  let e : S →ₗ[ℂ] T :=
    { toFun := fun x => ⟨Q x.val, by
        obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.property
        apply Submodule.mem_map.mpr
        refine ⟨f, OAI.QuarticPowerFree.mem_totalSpace.mpr hf.totalDegree_le, ?_⟩
        change Ideal.Quotient.mk A.ideal f = Q x.val
        change Ideal.Quotient.mk V.ideal f = x.val at hfx
        rw [← hfx]
        simp [Q]⟩
      map_add' x y := by
        apply Subtype.ext
        exact Q.map_add _ _
      map_smul' c x := by
        apply Subtype.ext
        exact Q.toLinearMap.map_smul c _ }
  have hzero (x : S) (hx : e x = 0) : x = 0 := by
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.property
    change Ideal.Quotient.mk V.ideal f = x.val at hfx
    have hq : Q x.val = 0 := congrArg Subtype.val hx
    rw [← hfx] at hq
    have hfA : f ∈ A.ideal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa [Q] using hq
    have hfV := (hmem D f hf).1 hfA
    apply Subtype.ext
    rw [← hfx]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hfV
  have hinj : Function.Injective e := by
    intro x y hxy
    have hz : e (x-y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hzero (x-y) hz)
  have hsurj : Function.Surjective e := by
    intro y
    obtain ⟨f, hf, hfy⟩ := Submodule.mem_map.mp y.property
    let g := chartHomogenize ℓ D f
    have hg : g.IsHomogeneous D := chartHomogenize_homogeneous ℓ f hℓ
    let x : S := ⟨Ideal.Quotient.mk V.ideal g, Submodule.mem_map.mpr ⟨g, hg, rfl⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change Q (Ideal.Quotient.mk V.ideal g) = y.val
    calc
      _ = Ideal.Quotient.mk A.ideal g := by simp [Q]
      _ = Ideal.Quotient.mk A.ideal f := chartHomogenize_mod ℓ f
        (OAI.QuarticPowerFree.mem_totalSpace.mp hf) A.ideal hℓA
      _ = y.val := hfy
  exact (LinearEquiv.ofBijective e ⟨hinj, hsurj⟩).finrank_eq.symm

theorem linearSlice_hilbert {n : ℕ} (V : ProjectiveVariety n)
    (hV : V.IsIrreducible) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hℓV : ℓ ∉ V.ideal) (D : ℕ) :
    (projectiveLinearSlice V ℓ).hilbert D = V.hilbert D := by
  apply linearChart_hilbert V (projectiveLinearSlice V ℓ) ℓ hℓ
  · exact le_sup_left.trans Ideal.le_radical
  · exact Ideal.le_radical (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
  · intro d f hf
    exact homogeneous_mem_linearSlice_iff V hV ℓ f hℓ hℓV hf

theorem linearChart_polynomial {n : ℕ} (V : ProjectiveVariety n) (A : AffineVariety n)
    (hH : ∀ D, A.hilbert D = V.hilbert D) : A.hilbertPolynomial = V.hilbertPolynomial := by
  apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
  obtain ⟨NP, hP⟩ := V.hilbert_eventually
  obtain ⟨NA, hA⟩ := Filter.eventually_atTop.mp A.hilbert_eventually
  filter_upwards [Filter.eventually_atTop.mpr ⟨max (NP+1) NA, by
    intro D hD
    have hDP : NP < D := Nat.lt_of_succ_le ((le_max_left _ _).trans hD)
    have hDA : NA ≤ D := (le_max_right _ _).trans hD
    calc
      A.hilbertPolynomial.eval (D : ℚ) = (A.hilbert D : ℚ) := (hA D hDA).symm
      _ = (V.hilbert D : ℚ) := by rw [hH D]
      _ = V.hilbertPolynomial.eval (D : ℚ) := hP D hDP⟩] with D hD
  exact hD

theorem linearSlice_dimension {n : ℕ} (V : ProjectiveVariety n)
    (hV : V.IsIrreducible) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hℓV : ℓ ∉ V.ideal) : (projectiveLinearSlice V ℓ).dimension = V.dimension := by
  have hP := linearChart_polynomial V (projectiveLinearSlice V ℓ)
    (linearSlice_hilbert V hV ℓ hℓ hℓV)
  change (projectiveLinearSlice V ℓ).hilbertPolynomial.natDegree = V.hilbertPolynomial.natDegree
  rw [hP]

theorem linearSlice_degree {n : ℕ} (V : ProjectiveVariety n)
    (hV : V.IsIrreducible) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hℓV : ℓ ∉ V.ideal) : (projectiveLinearSlice V ℓ).degree = V.degree := by
  have hP := linearChart_polynomial V (projectiveLinearSlice V ℓ)
    (linearSlice_hilbert V hV ℓ hℓ hℓV)
  have hdim := linearSlice_dimension V hV ℓ hℓ hℓV
  change ((projectiveLinearSlice V ℓ).dimension.factorial : ℚ) *
      (projectiveLinearSlice V ℓ).hilbertPolynomial.coeff (projectiveLinearSlice V ℓ).dimension =
    V.hilbertPolynomial.coeff V.dimension * (V.dimension.factorial : ℚ)
  rw [hdim, hP]
  ring

end
end DistinctDistances.TrackA
