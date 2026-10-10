import DistinctDistances.TrackA.Requests

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- Exactness transfers finiteness from the two outer section spaces to
the middle one. This avoids using an infinite-dimensional finrank as zero. -/
theorem regularSection_finite_of_exact {n : ℕ} (V W : ProjectiveVariety n)
    (hWV : W.Subvariety V) (D : ℕ) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    [Module.Finite ℂ (regularSectionSpace V D)]
    [Module.Finite ℂ (regularSectionSpace W (D+1))]
    (hexact : LinearMap.ker (sectionRestriction V W hWV (D+1)) =
      LinearMap.range (sectionMultiplyLinear V D ℓ hℓ)) :
    Module.Finite ℂ (regularSectionSpace V (D+1)) := by
  let r := sectionRestriction V W hWV (D+1)
  haveI : Module.Finite ℂ (LinearMap.ker r) := by
    rw [show LinearMap.ker r = LinearMap.range (sectionMultiplyLinear V D ℓ hℓ) from hexact]
    infer_instance
  have hfin : Module.Finite ℂ (Submodule.comap r (⊤ : Submodule ℂ (regularSectionSpace W (D+1)))) :=
    inferInstance
  haveI : Module.Finite ℂ (⊤ : Submodule ℂ (regularSectionSpace V (D+1))) := by
    rw [← Submodule.comap_top r]
    exact hfin
  exact Module.Finite.of_surjective (⊤ : Submodule ℂ (regularSectionSpace V (D+1))).subtype
    (fun s => ⟨⟨s, Submodule.mem_top⟩, rfl⟩)

/-- Rank-nullity for the actual restriction and multiplication maps. All
three section spaces are finite before their finranks are compared. -/
theorem regularSection_finrank_recurrence {n : ℕ} (V W : ProjectiveVariety n)
    (hWV : W.Subvariety V) (D : ℕ) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    [Module.Finite ℂ (regularSectionSpace V D)]
    [Module.Finite ℂ (regularSectionSpace W (D+1))]
    (hexact : LinearMap.ker (sectionRestriction V W hWV (D+1)) =
      LinearMap.range (sectionMultiplyLinear V D ℓ hℓ)) :
    Module.finrank ℂ (regularSectionSpace V (D+1)) ≤
      Module.finrank ℂ (regularSectionSpace V D) +
      Module.finrank ℂ (regularSectionSpace W (D+1)) := by
  haveI := regularSection_finite_of_exact V W hWV D ℓ hℓ hexact
  let r := sectionRestriction V W hWV (D+1)
  let m := sectionMultiplyLinear V D ℓ hℓ
  have hker : Module.finrank ℂ (LinearMap.ker r) ≤
      Module.finrank ℂ (regularSectionSpace V D) := by
    rw [show LinearMap.ker r = LinearMap.range m from hexact]
    exact LinearMap.finrank_range_le m
  have hrange : Module.finrank ℂ (LinearMap.range r) ≤
      Module.finrank ℂ (regularSectionSpace W (D+1)) := Submodule.finrank_le _
  have hdim := LinearMap.finrank_range_add_finrank_ker r
  omega

/-- Section finiteness for the pure families consumed by the paper follows
from the actual finite D=0 base, finite zero-fold sections and exact maps. -/
theorem regularSection_pure_family_finite_of_hyperplane {n : ℕ}
    (hpoints : ∀ (F : ProjectiveFamily.Family n), ProjectiveFamily.IsPure F 0 → ∀ D,
      Module.Finite ℂ (regularSectionSpace (ProjectiveFamily.locus F) D))
    (hcut : ∀ (F : ProjectiveFamily.Family n) k, ProjectiveFamily.IsPure F (k+1) →
      ∃ (W : ProjectiveFamily.Family n) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
        (hWV : (ProjectiveFamily.locus W).Subvariety (ProjectiveFamily.locus F)),
        ProjectiveFamily.IsPure W k ∧
        ∀ D, LinearMap.ker (sectionRestriction (ProjectiveFamily.locus F)
            (ProjectiveFamily.locus W) hWV (D+1)) =
          LinearMap.range (sectionMultiplyLinear (ProjectiveFamily.locus F) D ℓ hℓ))
    (F : ProjectiveFamily.Family n) (k : ℕ) (hF : ProjectiveFamily.IsPure F k) (D : ℕ) :
    Module.Finite ℂ (regularSectionSpace (ProjectiveFamily.locus F) D) := by
  induction k generalizing F D with
  | zero => exact hpoints F hF D
  | succ k ih =>
    obtain ⟨W, ℓ, hℓ, hWV, hW, hexact⟩ := hcut F k hF
    induction D with
    | zero => exact regularSection_family_zero_finite F (fun V hV => (hF V hV).1)
    | succ d ihD =>
      haveI := ihD
      haveI := ih W hW (d+1)
      exact regularSection_finite_of_exact (ProjectiveFamily.locus F)
        (ProjectiveFamily.locus W) hWV d ℓ hℓ (hexact d)

set_option maxHeartbeats 800000 in
/-- Dimension and degree induction requires finiteness only on pure
families. The geometric inputs remain explicit hypotheses. -/
theorem regularSection_pure_family_upper_of_hyperplane {n : ℕ}
    (hfinite : ∀ (F : ProjectiveFamily.Family n) k, ProjectiveFamily.IsPure F k → ∀ D,
      Module.Finite ℂ (regularSectionSpace (ProjectiveFamily.locus F) D))
    (hzero : ∀ (F : ProjectiveFamily.Family n) k, ProjectiveFamily.IsPure F k →
      (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) 0) : ℚ) ≤
        ProjectiveFamily.degree F)
    (hpoints : ∀ (F : ProjectiveFamily.Family n), ProjectiveFamily.IsPure F 0 → ∀ D,
      (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) D) : ℚ) ≤
        ProjectiveFamily.degree F)
    (hcut : ∀ (F : ProjectiveFamily.Family n) k, ProjectiveFamily.IsPure F (k+1) →
      ∃ (W : ProjectiveFamily.Family n) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
        (hWV : (ProjectiveFamily.locus W).Subvariety (ProjectiveFamily.locus F)),
        ProjectiveFamily.IsPure W k ∧ ProjectiveFamily.degree W = ProjectiveFamily.degree F ∧
        ∀ D, LinearMap.ker (sectionRestriction (ProjectiveFamily.locus F)
            (ProjectiveFamily.locus W) hWV (D+1)) =
          LinearMap.range (sectionMultiplyLinear (ProjectiveFamily.locus F) D ℓ hℓ))
    (F : ProjectiveFamily.Family n) (k : ℕ) (hF : ProjectiveFamily.IsPure F k) (D : ℕ) :
    (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) D) : ℚ) ≤
      ProjectiveFamily.degree F * ((D+k).choose k : ℚ) := by
  induction k generalizing F D with
  | zero =>
    simpa only [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] using
      hpoints F hF D
  | succ k ih =>
    obtain ⟨W, ℓ, hℓ, hWV, hW, hdeg, hexact⟩ := hcut F k hF
    apply hilbert_binomial_upper_of_recursion
      (fun d => (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) d) : ℚ))
      (ProjectiveFamily.degree F) k (hzero F (k+1) hF)
    intro d
    haveI := hfinite F (k+1) hF d
    haveI := hfinite W k hW (d+1)
    have hrec := regularSection_finrank_recurrence (ProjectiveFamily.locus F)
      (ProjectiveFamily.locus W) hWV d ℓ hℓ (hexact d)
    have hrecQ :
        (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) (d+1)) : ℚ) ≤
          (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) d) : ℚ) +
          (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus W) (d+1)) : ℚ) := by
      exact_mod_cast hrec
    have hWbound := ih W hW (d+1)
    rw [hdeg, show d+1+k = d+k+1 by omega] at hWbound
    exact hrecQ.trans (add_le_add le_rfl hWbound)

/-- The earlier general-finiteness API follows from the consumer-specific
pure-family induction, preserving its original statement. -/
theorem regularSection_family_upper_of_hyperplane {n : ℕ}
    (hfinite : ∀ (V : ProjectiveVariety n) D,
      Module.Finite ℂ (regularSectionSpace V D))
    (hzero : ∀ (F : ProjectiveFamily.Family n) k, ProjectiveFamily.IsPure F k →
      (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) 0) : ℚ) ≤
        ProjectiveFamily.degree F)
    (hpoints : ∀ (F : ProjectiveFamily.Family n), ProjectiveFamily.IsPure F 0 → ∀ D,
      (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) D) : ℚ) ≤
        ProjectiveFamily.degree F)
    (hcut : ∀ (F : ProjectiveFamily.Family n) k, ProjectiveFamily.IsPure F (k+1) →
      ∃ (W : ProjectiveFamily.Family n) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
        (hWV : (ProjectiveFamily.locus W).Subvariety (ProjectiveFamily.locus F)),
        ProjectiveFamily.IsPure W k ∧ ProjectiveFamily.degree W = ProjectiveFamily.degree F ∧
        ∀ D, LinearMap.ker (sectionRestriction (ProjectiveFamily.locus F)
            (ProjectiveFamily.locus W) hWV (D+1)) =
          LinearMap.range (sectionMultiplyLinear (ProjectiveFamily.locus F) D ℓ hℓ))
    (F : ProjectiveFamily.Family n) (k : ℕ) (hF : ProjectiveFamily.IsPure F k) (D : ℕ) :
    (Module.finrank ℂ (regularSectionSpace (ProjectiveFamily.locus F) D) : ℚ) ≤
      ProjectiveFamily.degree F * ((D+k).choose k : ℚ) :=
  regularSection_pure_family_upper_of_hyperplane
    (fun G _ _ d => hfinite (ProjectiveFamily.locus G) d) hzero hpoints hcut F k hF D

/-- The specialized actual finiteness interface used by the public bound.
It uses only zero-fold finiteness and reduced hyperplane geometry. -/
theorem regularSection_pure_family_finite {n : ℕ} (F : ProjectiveFamily.Family n)
    (k : ℕ) (hF : ProjectiveFamily.IsPure F k) (D : ℕ) :
    Module.Finite ℂ (regularSectionSpace (ProjectiveFamily.locus F) D) := by
  apply regularSection_pure_family_finite_of_hyperplane
    (fun G hG d => request_regularSection_zeroDim_finite G hG d) _ F k hF D
  intro G j hG
  obtain ⟨W, ℓ, hℓ, hWV, hW, _, _, _, hexact⟩ := request_regularSection_hyperplane G j hG
  exact ⟨W, ℓ, hℓ, hWV, hW, hexact⟩

end
end DistinctDistances.TrackA
