import DistinctDistances.TrackA.InfinityParameterSelectionSupport

set_option backward.isDefEq.respectTransparency false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original homogenizing coordinate is nonzero on every nonempty
affine variety's projective closure: dehomogenizing it gives one. -/
theorem projectiveClosure_homogenizing_coordinate_not_mem {n : ℕ}
    (V : AffineVariety n) (hne : V.ideal ≠ ⊤) :
    MvPolynomial.X (0 : Fin (n+1)) ∉ (projectiveClosure V).ideal := by
  intro hx
  have h := projectiveClosure_aeval_mem V (MvPolynomial.X 0) hx
  have hone : (1 : Poly n) ∈ V.ideal := by
    simpa only [MvPolynomial.aeval_X, Fin.cons_zero] using h
  exact hne (V.ideal.eq_top_of_isUnit_mem hone isUnit_one)

/-- Simultaneous finite linear normalization for a nonempty pure family.
Normalize its whole literal infinity quotient, so the same original
linear parameters are finite on every member. -/
theorem nonempty_family_infinity_normalized_linear_projection {n k : ℕ}
    (F : AffineFamily.Family n) (hne : F.Nonempty) (hF : AffineFamily.IsPure F k) :
    ∃ ψ : LinearProjection n k, Function.Surjective ψ ∧
      ∀ V ∈ F, (MvPolynomial.aeval (R := ℂ) (fun i =>
        Ideal.Quotient.mk ((projectiveClosure V).ideal ⊔ Ideal.span {MvPolynomial.X 0})
          (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))).Finite := by
  let H : ProjectiveFamily.Family (n+1) := F.image projectiveClosure
  have hHne : H.Nonempty := Finset.image_nonempty.mpr hne
  have hHpure : ProjectiveFamily.IsPure H k := by
    intro W hW
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hW
    exact ⟨projectiveClosure_isIrreducible V (hF V hV).1,
      (projectiveClosure_dimension V (V.points_nonempty_of_isIrreducible (hF V hV).1)).trans
        (hF V hV).2⟩
  have havoid : ∀ W ∈ H, MvPolynomial.X 0 ∉ W.ideal := by
    intro W hW
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hW
    exact projectiveClosure_homogenizing_coordinate_not_mem V (hF V hV).1.ne_top
  let J := (ProjectiveFamily.locus H).ideal ⊔ Ideal.span {MvPolynomial.X 0}
  have hJhom : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ) :=
    (ProjectiveFamily.locus H).isHomogeneous.sup (Ideal.homogeneous_span _ _
      (by rintro f rfl; exact ⟨1, MvPolynomial.isHomogeneous_X ℂ 0⟩))
  have hJne : J ≠ ⊤ := projective_family_linear_cut_ne_top H hHne
    (fun W hW => (hHpure W hW).1) _ (MvPolynomial.isHomogeneous_X ℂ 0)
  have hJdim : ringKrullDim (Poly (n+1) ⧸ J) = (k : WithBot ℕ∞) :=
    projective_family_linear_cut_krull_dimension H k hHne hHpure _
      (MvPolynomial.isHomogeneous_X ℂ 0) havoid
  obtain ⟨ψ, hψ, _, hfinite⟩ := infinity_quotient_linear_normalization J hJhom hJne
    (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))) hJdim
  refine ⟨ψ, hψ, ?_⟩
  intro V hV
  have hJV : J ≤ (projectiveClosure V).ideal ⊔ Ideal.span {MvPolynomial.X 0} :=
    sup_le_sup (projective_family_member_subvariety H (projectiveClosure V)
      (Finset.mem_image.mpr ⟨V, hV, rfl⟩)) le_rfl
  let q := Ideal.Quotient.factorₐ ℂ hJV
  have hq : Function.Surjective q := Ideal.Quotient.factor_surjective hJV
  have he : q.comp (MvPolynomial.aeval (R := ℂ) (fun i => Ideal.Quotient.mk J
        (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))) =
      MvPolynomial.aeval (R := ℂ) (fun i =>
        Ideal.Quotient.mk ((projectiveClosure V).ideal ⊔ Ideal.span {MvPolynomial.X 0})
          (MvPolynomial.rename Fin.succ (linearCoordinate ψ i))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    rfl
  have h := (AlgHom.Finite.of_surjective q hq).comp hfinite
  rw [he] at h
  exact h

/-- The selected common infinity parameters give finite affine maps
on all members through the previously checked fixed-coordinate bridge. -/
theorem nonempty_family_finite_affine_linear_projection {n k : ℕ}
    (F : AffineFamily.Family n) (hne : F.Nonempty) (hF : AffineFamily.IsPure F k) :
    ∃ ψ : LinearProjection n k, Function.Surjective ψ ∧
      ∀ V ∈ F, FiniteAffineProjection (⟨ψ, 0⟩ : AffineProjection n k) V := by
  obtain ⟨ψ, hψ, hfinite⟩ := nonempty_family_infinity_normalized_linear_projection F hne hF
  exact ⟨ψ, hψ, fun V hV => finite_affine_projection_of_infinity_parameters V ψ (hfinite V hV)⟩

/-- The empty-family case uses an explicit surjective coordinate map. -/
theorem coordinate_projection_surjective {n k : ℕ} (hk : k ≤ n) :
    ∃ ψ : LinearProjection n k, Function.Surjective ψ := by
  let ψ : LinearProjection n k := LinearMap.pi fun i : Fin k => LinearMap.proj (Fin.castLE hk i)
  refine ⟨ψ, ?_⟩
  intro y
  let x : Point n := fun i => if hi : i.val < k then y ⟨i.val, hi⟩ else 0
  refine ⟨x, ?_⟩
  ext i
  simp [ψ, x]

/-- Preserve the actual infinity finiteness certificate for the later
generic-degree comparison; ordinary affine finiteness alone is insufficient. -/
theorem family_infinity_normalized_linear_projection {n k : ℕ}
    (F : AffineFamily.Family n) (hk : k ≤ n) (hF : AffineFamily.IsPure F k) :
    ∃ ψ : LinearProjection n k, Function.Surjective ψ ∧
      ∀ V ∈ F, (MvPolynomial.aeval (R := ℂ) (fun i =>
        Ideal.Quotient.mk ((projectiveClosure V).ideal ⊔ Ideal.span {MvPolynomial.X 0})
          (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))).Finite := by
  by_cases hne : F.Nonempty
  · exact nonempty_family_infinity_normalized_linear_projection F hne hF
  · obtain ⟨ψ, hψ⟩ := coordinate_projection_surjective hk
    exact ⟨ψ, hψ, fun V hV => False.elim (hne ⟨V, hV⟩)⟩

/-- The finite-projection part of `poly:hilbert.normalization`,
polynomial.tex:349–369. Generic-degree preservation is proved separately. -/
theorem family_finite_affine_linear_projection {n k : ℕ}
    (F : AffineFamily.Family n) (hk : k ≤ n) (hF : AffineFamily.IsPure F k) :
    ∃ ψ : LinearProjection n k, Function.Surjective ψ ∧
      ∀ V ∈ F, FiniteAffineProjection (⟨ψ, 0⟩ : AffineProjection n k) V := by
  obtain ⟨ψ, hψ, hfinite⟩ := family_infinity_normalized_linear_projection F hk hF
  exact ⟨ψ, hψ, fun V hV => finite_affine_projection_of_infinity_parameters V ψ (hfinite V hV)⟩

end
end DistinctDistances.TrackA
