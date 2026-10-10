import DistinctDistances.TrackA.ProjectiveChartRankSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_common_linear_chart {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ∀ V ∈ F, V.IsIrreducible) :
    ∃ ℓ : Poly n, ℓ.IsHomogeneous 1 ∧ ∀ V ∈ F, ℓ ∉ V.ideal := by
  let H := MvPolynomial.homogeneousSubmodule (Fin n) ℂ 1
  let bad (V : F) : Submodule ℂ H :=
    (V.val.ideal.restrictScalars ℂ).comap H.subtype
  have hbad (V : F) : bad V ≠ ⊤ := by
    intro ht
    have hx (i : Fin n) : (MvPolynomial.X i : Poly n) ∈ V.val.ideal := by
      let x : H := ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i⟩
      have hxb : x ∈ bad V := by rw [ht]; trivial
      exact hxb
    have hone : (1 : Poly n) ∈ V.val.ideal :=
      V.val.isSaturated 1 (fun i => ⟨1, by simpa only [pow_one, mul_one] using hx i⟩)
    exact (hF V.val V.property).one_notMem hone
  obtain ⟨ℓ, hℓ⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  refine ⟨ℓ.val, ℓ.property, ?_⟩
  intro V hV hmem
  exact hℓ ⟨V, hV⟩ hmem

/-- Projectivization of an affine carrier whose points lie in the linear slice. -/
def sliceProjectivization {n : ℕ} (A : AffineVariety n) : ProjectiveVariety n :=
  ProjectiveVariety.closure {p | ∃ x ∈ A.points, ∃ hx : x ≠ 0,
    Projectivization.mk ℂ x hx = p}

theorem slice_point_ne_zero {n : ℕ} (A : AffineVariety n) (ℓ : Poly n)
    (hℓ : ℓ.IsHomogeneous 1) (hℓA : ℓ - 1 ∈ A.ideal)
    (x : Point n) (hx : x ∈ A.points) : x ≠ 0 := by
  have hxℓ : MvPolynomial.eval x ℓ = 1 := by
    have hz := hx (ℓ-1) hℓA
    simpa only [MvPolynomial.aeval_eq_eval, map_sub, map_one, sub_eq_zero] using hz
  intro hx0
  have hzero : MvPolynomial.eval x ℓ = 0 := by
    rw [hx0]
    have h := Bridges.homogeneous_eval_smul ℓ hℓ (0 : ℂ) x
    simpa only [zero_smul, pow_one, zero_mul] using h
  exact zero_ne_one (hzero.symm.trans hxℓ)

theorem sliceProjectivization_mem_iff {n d : ℕ} (A : AffineVariety n) (ℓ f : Poly n)
    (hℓ : ℓ.IsHomogeneous 1) (hℓA : ℓ - 1 ∈ A.ideal) (hf : f.IsHomogeneous d) :
    f ∈ (sliceProjectivization A).ideal ↔ f ∈ A.ideal := by
  constructor
  · intro h
    rw [← A.vanishingIdeal_points]
    intro x hx
    have hx0 := slice_point_ne_zero A ℓ hℓ hℓA x hx
    exact h x ⟨hx0, ⟨x, hx, hx0, rfl⟩⟩
  · intro h
    intro v hv
    obtain ⟨hv0, x, hx, hx0, hpx⟩ := hv
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ v x hv0 hx0).1 hpx.symm
    have hxz : MvPolynomial.eval x f = 0 := by
      simpa only [MvPolynomial.aeval_eq_eval] using hx f h
    change MvPolynomial.eval v f = 0
    rw [← hc, Bridges.homogeneous_eval_smul f hf, hxz, mul_zero]

theorem sliceProjectivization_irreducible {n : ℕ} (A : AffineVariety n)
    (hA : A.IsIrreducible) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hℓA : ℓ - 1 ∈ A.ideal) : (sliceProjectivization A).IsIrreducible := by
  apply (sliceProjectivization A).isHomogeneous.isPrime_of_homogeneous_mem_or_mem
  · intro ht
    have hone : (1 : Poly n) ∈ (sliceProjectivization A).ideal := by rw [ht]; trivial
    exact hA.one_notMem ((sliceProjectivization_mem_iff A ℓ 1 hℓ hℓA
      (MvPolynomial.isHomogeneous_one _ _)).1 hone)
  · intro f g hf hg hfg
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    have hfgA := (sliceProjectivization_mem_iff A ℓ _ hℓ hℓA (ha.mul hb)).1 hfg
    rcases hA.mem_or_mem hfgA with h | h
    · exact Or.inl ((sliceProjectivization_mem_iff A ℓ f hℓ hℓA ha).2 h)
    · exact Or.inr ((sliceProjectivization_mem_iff A ℓ g hℓ hℓA hb).2 h)

/-- A selected projective minimal component remains minimal in its affine slice;
all original equations and their other components remain in the system. -/
theorem linearSlice_component {n : ℕ} (V : ProjectiveVariety n) (E : Set (Poly n))
    (hE : ∀ f ∈ E, ∃ d, f.IsHomogeneous d)
    (hV : V.ideal ∈ (Ideal.span E).minimalPrimes)
    (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1) (hℓV : ℓ ∉ V.ideal) :
    (projectiveLinearSlice V ℓ).IsComponentOf (Ideal.span (E ∪ {ℓ-1})) := by
  let A := projectiveLinearSlice V ℓ
  have hprime := linearSlice_irreducible V hV.isPrime ℓ hℓ hℓV
  have hEℓ : Ideal.span (E ∪ {ℓ-1}) ≤ A.ideal := by
    apply Ideal.span_le.mpr
    intro f hf
    rcases hf with hf | hf
    · exact Ideal.le_radical (Ideal.mem_sup_left (hV.le (Ideal.subset_span hf)))
    · exact Ideal.le_radical (Ideal.mem_sup_right (Ideal.subset_span hf))
  refine ⟨⟨hprime, hEℓ⟩, ?_⟩
  intro Q hQ hQA
  let B : AffineVariety n := ⟨Q, hQ.1.isRadical⟩
  have hℓQ : ℓ - 1 ∈ B.ideal := hQ.2 (Ideal.subset_span (Or.inr rfl))
  let W := sliceProjectivization B
  have hWP : W.IsIrreducible := sliceProjectivization_irreducible B hQ.1 ℓ hℓ hℓQ
  have hEW : Ideal.span E ≤ W.ideal := by
    apply Ideal.span_le.mpr
    intro f hf
    obtain ⟨d, hd⟩ := hE f hf
    apply (sliceProjectivization_mem_iff B ℓ f hℓ hℓQ hd).2
    exact hQ.2 (Ideal.subset_span (Or.inl hf))
  have hWV : W.ideal ≤ V.ideal := by
    intro f hf
    rw [MvPolynomial.mem_iff_homogeneousComponent_mem V.isHomogeneous]
    intro d
    have hdfW := MvPolynomial.homogeneousComponent_mem_of_mem W.isHomogeneous hf d
    have hdfQ := (sliceProjectivization_mem_iff B ℓ _ hℓ hℓQ
      (MvPolynomial.homogeneousComponent_isHomogeneous d f)).1 hdfW
    exact (homogeneous_mem_linearSlice_iff V hV.isPrime ℓ _ hℓ hℓV
      (MvPolynomial.homogeneousComponent_isHomogeneous d f)).1 (hQA hdfQ)
  have hVW : V.ideal ≤ W.ideal := hV.2 ⟨hWP, hEW⟩ hWV
  intro f hf
  have hpadV := (chartHomogenize_mem_iff V hV.isPrime ℓ f hℓ hℓV le_rfl).1 hf
  have hpadQ := (sliceProjectivization_mem_iff B ℓ _ hℓ hℓQ
    (chartHomogenize_homogeneous ℓ f hℓ)).1 (hVW hpadV)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [← chartHomogenize_mod ℓ f le_rfl Q hℓQ]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hpadQ

end
end DistinctDistances.TrackA
