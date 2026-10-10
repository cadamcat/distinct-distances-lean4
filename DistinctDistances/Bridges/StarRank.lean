import DistinctDistances.Foundations.Projective
import DistinctDistances.TrackE.Basic

/-! Homogeneous star rank is the Hilbert rank of any variety with the same degree kernel. -/

namespace DistinctDistances.Bridges

noncomputable section

theorem starRank_eq_hilbert {d D : ℕ} (p : RPoint d) (T : Finset (RPoint d))
    (_hp : p ∉ T) (V : ProjectiveVariety d)
    (hkernel : ∀ f : Poly d, f.IsHomogeneous D →
      (f ∈ V.ideal ↔ ∀ q ∈ T, MvPolynomial.eval (cplx (q - p)) f = 0)) :
    starRank D p T = V.hilbert D := by
  let H := MvPolynomial.homogeneousSubmodule (Fin d) ℂ D
  let L : T → Module.Dual ℂ H := fun q => homEval d D (cplx (q.val - p))
  let ev : H →ₗ[ℂ] (T → ℂ) := LinearMap.pi L
  let q : H →ₗ[ℂ] (Poly d ⧸ V.ideal) :=
    (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap.comp H.subtype
  have hrange : LinearMap.range q = V.restrictionSpace D := by
    ext z
    change (∃ f : H, q f = z) ↔ ∃ f,
      f ∈ H ∧ (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap f = z
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f.val, f.property, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, rfl⟩
  have hker : LinearMap.ker ev = LinearMap.ker q := by
    ext f
    change (ev f = 0) ↔ Ideal.Quotient.mk V.ideal f.val = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hkernel f.val f.property]
    constructor
    · intro hf x hx
      exact congrFun hf ⟨x, hx⟩
    · intro hf
      funext x
      exact hf x.val x.property
  have hspan : Submodule.span ℂ (Set.range L) = (LinearMap.ker ev).dualAnnihilator := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      apply (Submodule.mem_dualAnnihilator _).mpr
      intro f hf
      exact congrFun (LinearMap.mem_ker.mp hf) x
    · intro φ hφ
      apply FiniteDimensional.mem_span_of_iInf_ker_le_ker (L := L)
      rw [← LinearMap.ker_pi]
      intro f hf
      exact LinearMap.mem_ker.mpr ((Submodule.mem_dualAnnihilator φ).mp hφ f hf)
  have hrank : Module.finrank ℂ (LinearMap.range ev) =
      Module.finrank ℂ (LinearMap.range q) := by
    have he := ev.finrank_range_add_finrank_ker
    have hq := q.finrank_range_add_finrank_ker
    rw [← hker] at hq
    exact Nat.add_right_cancel (he.trans hq.symm)
  change Module.finrank ℂ (Submodule.span ℂ (Set.range L)) =
    Module.finrank ℂ (V.restrictionSpace D)
  rw [hspan, ← ev.range_dualMap_eq_dualAnnihilator_ker,
    ev.finrank_range_dualMap_eq_finrank_range, hrank, hrange]

end
end DistinctDistances.Bridges
