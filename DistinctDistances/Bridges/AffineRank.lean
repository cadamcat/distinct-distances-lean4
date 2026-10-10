import DistinctDistances.Foundations.Affine
import DistinctDistances.TrackE.Basic

/-! Evaluation rank and coordinate-ring Hilbert rank agree after finite coordinate reindexing. -/

namespace DistinctDistances.Bridges

noncomputable section

/-- The affine rank bridge, including arbitrary finite coordinate types. -/
theorem restrictionRank_eq_hilbertOfSet {σ : Type*} [Fintype σ]
    (e : σ ≃ Fin (Fintype.card σ)) (T : Set (σ → ℂ)) (D : ℕ) :
    restrictionRank T D =
      hilbertOfSet ((fun x : σ → ℂ => fun i => x (e.symm i)) '' T) D := by
  let T' : Set (Point (Fintype.card σ)) :=
    (fun x : σ → ℂ => fun i => x (e.symm i)) '' T
  let V := AffineVariety.closure T'
  let rename := MvPolynomial.renameEquiv ℂ e
  let q : MvPolynomial.restrictTotalDegree σ ℂ D →ₗ[ℂ] (Poly (Fintype.card σ) ⧸ V.ideal) :=
    (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap.comp
      (rename.toLinearMap.comp (MvPolynomial.restrictTotalDegree σ ℂ D).subtype)
  have hrange : LinearMap.range q = V.restrictionSpace D := by
    ext y
    change (∃ f, q f = y) ↔ ∃ f,
      f ∈ OAI.QuarticPowerFree.totalSpace D ∧
        (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap f = y
    constructor
    · rintro ⟨f, rfl⟩
      refine ⟨rename f.val, OAI.QuarticPowerFree.mem_totalSpace.mpr ?_, rfl⟩
      rw [MvPolynomial.totalDegree_renameEquiv]
      exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mp f.property
    · rintro ⟨f, hf, rfl⟩
      have hdegree : (rename.symm f).totalDegree ≤ D := by
        rw [MvPolynomial.renameEquiv_symm, MvPolynomial.totalDegree_renameEquiv]
        exact OAI.QuarticPowerFree.mem_totalSpace.mp hf
      let p : MvPolynomial.restrictTotalDegree σ ℂ D :=
        ⟨rename.symm f, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hdegree⟩
      refine ⟨p, ?_⟩
      change Ideal.Quotient.mk V.ideal (rename (rename.symm f)) =
        Ideal.Quotient.mk V.ideal f
      rw [rename.apply_symm_apply]
  have hker : LinearMap.ker (restrictionMap T D) = LinearMap.ker q := by
    ext f
    change (restrictionMap T D f = 0) ↔
      Ideal.Quotient.mk V.ideal (rename f.val) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change (restrictionMap T D f = 0) ↔
      ∀ x ∈ T', MvPolynomial.aeval x (rename f.val) = 0
    constructor
    · intro hf x hx
      obtain ⟨z, hz, rfl⟩ := hx
      have hzero := congrFun hf ⟨z, hz⟩
      change MvPolynomial.aeval z f.val = 0 at hzero
      simpa only [rename, MvPolynomial.renameEquiv_apply, MvPolynomial.aeval_rename,
        Function.comp_def, Equiv.symm_apply_apply] using hzero
    · intro hf
      funext z
      have hzero := hf (fun i => z.val (e.symm i)) ⟨z.val, z.property, rfl⟩
      change MvPolynomial.aeval z.val f.val = 0
      simpa only [rename, MvPolynomial.renameEquiv_apply, MvPolynomial.aeval_rename,
        Function.comp_def, Equiv.symm_apply_apply] using hzero
  have he := (restrictionMap T D).finrank_range_add_finrank_ker
  have hq := q.finrank_range_add_finrank_ker
  rw [← hker] at hq
  change Module.finrank ℂ (LinearMap.range (restrictionMap T D)) =
    Module.finrank ℂ (V.restrictionSpace D)
  rw [← hrange]
  exact Nat.add_right_cancel (he.trans hq.symm)

end
end DistinctDistances.Bridges
