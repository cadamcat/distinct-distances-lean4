import DistinctDistances.TrackA.ProjectiveChartFamily
import DistinctDistances.TrackA.ADepthAux

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- Actual point evaluation detects every coordinate class of a reduced point. -/
theorem affine_point_hilbert_le_one {n : ℕ} (V : AffineVariety n)
    (z : Point n) (hpoints : V.points = {z}) (D : ℕ) : V.hilbert D ≤ 1 := by
  have hle : V.ideal ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom := by
    intro f hf
    have hz : z ∈ V.points := by rw [hpoints]; exact Set.mem_singleton z
    exact hz f hf
  let ev : (Poly n ⧸ V.ideal) →ₐ[ℂ] ℂ :=
    Ideal.Quotient.liftₐ V.ideal (MvPolynomial.aeval z) hle
  have hcomp : ev.comp (Ideal.Quotient.mkₐ ℂ V.ideal) = MvPolynomial.aeval z :=
    Ideal.Quotient.liftₐ_comp V.ideal (MvPolynomial.aeval z) hle
  have hinj : Function.Injective ev := by
    intro x y hxy
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    have heval : MvPolynomial.aeval z f = MvPolynomial.aeval z g := by
      change (ev.comp (Ideal.Quotient.mkₐ ℂ V.ideal)) f =
        (ev.comp (Ideal.Quotient.mkₐ ℂ V.ideal)) g at hxy
      rwa [hcomp] at hxy
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem f g).mpr
    rw [← V.vanishingIdeal_points, hpoints, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simpa only [map_sub] using sub_eq_zero.mpr heval
  let e := ev.toLinearMap.comp (V.restrictionSpace D).subtype
  have he : Function.Injective e := hinj.comp Subtype.val_injective
  simpa only [AffineVariety.hilbert, Module.finrank_self] using
    (LinearMap.finrank_le_finrank_of_injective he)

/-- The exact upper bound for a distinct family of reduced points, at every degree. -/
theorem affine_zeroDim_family_hilbert_upper {n : ℕ} (F : AffineFamily.Family n)
    (hF : AffineFamily.IsPure F 0) (D : ℕ) :
    (AffineFamily.hilbert F D : ℚ) ≤ AffineFamily.degree F := by
  calc
    (AffineFamily.hilbert F D : ℚ) ≤ ((∑ V ∈ F, V.hilbert D : ℕ) : ℚ) := by
      exact_mod_cast AffineFamily.hilbert_le_sum F D
    _ = ∑ V ∈ F, (V.hilbert D : ℚ) := by simp
    _ ≤ ∑ V ∈ F, V.degree := by
      apply Finset.sum_le_sum
      intro V hV
      obtain ⟨z, hpoints, hdegree⟩ := zeroDim_irreducible_data V (hF V hV).1 (hF V hV).2
      rw [hdegree]
      exact_mod_cast affine_point_hilbert_le_one V z hpoints D
    _ = AffineFamily.degree F := rfl

/-- The homogeneous upper bound's zero-dimensional base uses the same
common chart for all components and preserves the exact family degree. -/
theorem projective_zeroDim_family_hilbert_upper {n : ℕ}
    (F : ProjectiveFamily.Family n) (hF : ProjectiveFamily.IsPure F 0) (D : ℕ) :
    (ProjectiveFamily.hilbert F D : ℚ) ≤ ProjectiveFamily.degree F := by
  have hirr : ∀ V ∈ F, V.IsIrreducible := fun V hV => (hF V hV).1
  obtain ⟨ℓ, hℓ, havoid⟩ := exists_common_linear_chart F hirr
  have hbound := affine_zeroDim_family_hilbert_upper (linearSliceFamily F ℓ)
    (linearSliceFamily_pure F 0 hF ℓ hℓ havoid) D
  rwa [linearSliceFamily_hilbert F hirr ℓ hℓ havoid D,
    linearSliceFamily_degree F hirr ℓ hℓ havoid] at hbound

/-- Restrictions to the separate components detect homogeneous restrictions
on the union, with no degree shift. -/
theorem projective_family_hilbert_le_sum {n : ℕ} (F : ProjectiveFamily.Family n)
    (hirr : ∀ V ∈ F, V.IsIrreducible) (D : ℕ) :
    ProjectiveFamily.hilbert F D ≤ ∑ V ∈ F, V.hilbert D := by
  obtain ⟨ℓ, hℓ, havoid⟩ := exists_common_linear_chart F hirr
  rw [← linearSliceFamily_hilbert F hirr ℓ hℓ havoid D]
  calc
    AffineFamily.hilbert (linearSliceFamily F ℓ) D ≤
        ∑ A ∈ linearSliceFamily F ℓ, A.hilbert D := AffineFamily.hilbert_le_sum _ _
    _ = ∑ V ∈ F, (projectiveLinearSlice V ℓ).hilbert D := by
      unfold linearSliceFamily
      exact Finset.sum_image (fun V hV W hW h =>
        linearSlice_injective V W (hirr V hV) (hirr W hW) ℓ hℓ (havoid V hV) (havoid W hW) h)
    _ = ∑ V ∈ F, V.hilbert D := by
      apply Finset.sum_congr rfl
      intro V hV
      exact linearSlice_hilbert V (hirr V hV) ℓ hℓ (havoid V hV) D

/-- Constant polynomial restrictions have dimension at most one, including
the empty locus. -/
theorem affine_hilbert_zero_le_one {n : ℕ} (V : AffineVariety n) :
    V.hilbert 0 ≤ 1 := by
  letI := OAI.QuarticPowerFree.totalSpace_finite (n := n) (K := ℂ) 0
  have h := Submodule.finrank_map_le (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap
    (OAI.QuarticPowerFree.totalSpace 0)
  simpa only [AffineVariety.hilbert, OAI.QuarticPowerFree.totalSpace_finrank,
    Nat.zero_add, Nat.choose_self] using h

/-- The degree-zero upper bound needs only constants and positive
irreducible component degrees, rather than global-section finiteness. -/
theorem projective_family_hilbert_zero_upper {n : ℕ}
    (F : ProjectiveFamily.Family n) (hirr : ∀ V ∈ F, V.IsIrreducible) :
    (ProjectiveFamily.hilbert F 0 : ℚ) ≤ ProjectiveFamily.degree F := by
  obtain ⟨ℓ, hℓ, havoid⟩ := exists_common_linear_chart F hirr
  let A := linearSliceFamily F ℓ
  have hApure : ∀ V ∈ A, V.IsIrreducible := by
    intro V hV
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hV
    exact linearSlice_irreducible W (hirr W hW) ℓ hℓ (havoid W hW)
  have hbound : (AffineFamily.hilbert A 0 : ℚ) ≤ AffineFamily.degree A := by
    calc
      (AffineFamily.hilbert A 0 : ℚ) ≤ ((∑ V ∈ A, V.hilbert 0 : ℕ) : ℚ) := by
        exact_mod_cast AffineFamily.hilbert_le_sum A 0
      _ = ∑ V ∈ A, (V.hilbert 0 : ℚ) := by simp
      _ ≤ ∑ V ∈ A, V.degree := by
        apply Finset.sum_le_sum
        intro V hV
        have hzero : (V.hilbert 0 : ℚ) ≤ 1 := by
          exact_mod_cast affine_hilbert_zero_le_one V
        exact hzero.trans (V.one_le_degree (hApure V hV).ne_top)
      _ = AffineFamily.degree A := rfl
  rwa [linearSliceFamily_hilbert F hirr ℓ hℓ havoid 0,
    linearSliceFamily_degree F hirr ℓ hℓ havoid] at hbound

set_option maxHeartbeats 800000 in
/-- The numerical dimension induction used after the genuine section
restriction sequence. It does not assume a coordinate-quotient recurrence. -/
theorem hilbert_binomial_upper_of_recursion (H : ℕ → ℚ) (a : ℚ) (k : ℕ)
    (hzero : H 0 ≤ a)
    (hsucc : ∀ D, H (D+1) ≤ H D + a * ((D+k+1).choose k : ℚ)) (D : ℕ) :
    H D ≤ a * ((D+k+1).choose (k+1) : ℚ) := by
  induction D with
  | zero => simpa only [Nat.zero_add, Nat.choose_self, Nat.cast_one, mul_one] using hzero
  | succ D ih =>
    calc
      H (D+1) ≤ H D + a * ((D+k+1).choose k : ℚ) := hsucc D
      _ ≤ a * ((D+k+1).choose (k+1) : ℚ) + a * ((D+k+1).choose k : ℚ) :=
        add_le_add ih le_rfl
      _ = a * ((D+1+k+1).choose (k+1) : ℚ) := by
        have hc : (D+1+k+1).choose (k+1) =
            (D+k+1).choose k + (D+k+1).choose (k+1) := by
          rw [show D+1+k+1 = (D+k+1)+1 by omega]
          exact Nat.choose_succ_succ (D+k+1) k
        rw [hc, Nat.cast_add]
        ring

/-- Once the positive-dimension, positive-degree irreducible bound is
proved, the zero-dimensional and degree-zero cases and finite unions
require no further geometric input. -/
theorem projective_family_hilbert_upper_from_positive {n : ℕ}
    (F : ProjectiveFamily.Family n) (k : ℕ) (hF : ProjectiveFamily.IsPure F k) (D : ℕ)
    (hpositive : 1 ≤ k → 1 ≤ D → ∀ V ∈ F,
      (V.hilbert D : ℚ) ≤ V.degree * ((D+k).choose k : ℚ)) :
    (ProjectiveFamily.hilbert F D : ℚ) ≤ ProjectiveFamily.degree F * ((D+k).choose k : ℚ) := by
  by_cases hk : k = 0
  · subst k
    simpa only [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] using
      projective_zeroDim_family_hilbert_upper F hF D
  by_cases hD : D = 0
  · subst D
    simpa only [Nat.zero_add, Nat.choose_self, Nat.cast_one, mul_one] using
      projective_family_hilbert_zero_upper F (fun V hV => (hF V hV).1)
  calc
    (ProjectiveFamily.hilbert F D : ℚ) ≤ ((∑ V ∈ F, V.hilbert D : ℕ) : ℚ) := by
      exact_mod_cast projective_family_hilbert_le_sum F (fun V hV => (hF V hV).1) D
    _ = ∑ V ∈ F, (V.hilbert D : ℚ) := by simp
    _ ≤ ∑ V ∈ F, V.degree * ((D+k).choose k : ℚ) :=
      Finset.sum_le_sum (hpositive (by omega) (by omega))
    _ = ProjectiveFamily.degree F * ((D+k).choose k : ℚ) := by
      simp only [ProjectiveFamily.degree, Finset.sum_mul]

end
end DistinctDistances.TrackA
