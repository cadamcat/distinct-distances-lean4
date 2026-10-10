import DistinctDistances.TrackD.Profiles.Regularity

namespace DistinctDistances.TrackD
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

theorem regularity_zero_carrier (π : CutPath d) (Z : AffineVariety d)
    (hZ : π.IsCarrier 0 Z) : Z.ideal = ⊥ := by
  have hs : π.system 0 = ⊥ := by simp [CutPath.system]
  change Z.ideal ∈ (π.system 0).minimalPrimes at hZ
  rw [hs, Ideal.minimalPrimes_eq_subsingleton_self] at hZ
  simpa using hZ

theorem regularity_zero_minor : (1 : Poly d) ∈
    Submodule.span ℂ (TrackA.jacobianMinors ([] : List (Poly d)) 0) := by
  apply Submodule.subset_span
  refine ⟨Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, ?_⟩
  simp

theorem regularity_pool_tolerance_mono (P : Finset (Pt d)) (pl : Finset (Piece d))
    (θ θ' η K ρ s : ℝ) (t : Fin d → ℝ) (hθ : θ ≤ θ') (hs : 0 ≤ s)
    (hpl : PoolGood P θ η K ρ pl s t) : PoolGood P θ' η K ρ pl s t := by
  refine { hpl with pieces := ?_, count := ?_ }
  · intro X hX
    exact dprofiles2_pieceGood_mono P X hθ (by simpa [hpl.width X hX] using hs)
      (hpl.pieces X hX)
  · exact hpl.count.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hθ hs))

theorem regularity_test_mono (B s a b : ℝ) (hB : 0 ≤ B) (hs : 0 ≤ s) (hab : a ≤ b) :
    testDeg B s a ≤ testDeg B s b := by
  unfold testDeg
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab hs)) hB

theorem regularity_empty_kernel (y : Point d) : jacKer (∅ : Finset (Poly d)) y = ⊤ := by
  ext v
  simp only [jacKer, Submodule.mem_iInf, Submodule.mem_top, iff_true]
  intro f hf
  exact False.elim (Finset.notMem_empty f hf)

theorem regularity_jacobian_zero (P : Finset (Pt d)) (pl : Finset (Piece d))
    (θ η K T : ℝ) (hpl : ∀ X ∈ pl, PieceGood P θ η K X) (hT : 1 ≤ T) :
    (∀ y : Point d, MvPolynomial.eval y (1 : Poly d) ≠ 0 →
      Module.finrank ℂ (jacKer (∅ : Finset (Poly d)) y) + 0 ≤ d) ∧
    ∀ X ∈ pl, ∀ x ∈ X.pts, JacRegularAt pl 0 ∅ 1 (toC x) := by
  refine ⟨?_, ?_⟩
  · intro y hy
    rw [regularity_empty_kernel]
    simp [Module.finrank_fintype_fun_eq_card]
  · intro X hX x hx
    obtain ⟨Z, hZ⟩ := local_carrier_exists X x hx ((hpl X hX).vanish x hx) 0
    obtain ⟨hZirr, hdim⟩ := prof_partition_pure X x hx ((hpl X hX).vanish x hx)
      ((hpl X hX).proper x hx) 0 (Nat.zero_le _) Z hZ
    have hZbot := regularity_zero_carrier X.path Z hZ.1
    have htangent : Z.tangentSpace (toC x) = ⊤ := by
      ext v
      simp only [AffineVariety.tangentSpace, Submodule.mem_iInf,
        Submodule.mem_top, iff_true]
      intro f
      have hfzero : f.val = 0 := Ideal.mem_bot.mp (hZbot ▸ f.property)
      rw [hfzero]
      simp [differential]
    have hpoolZ : PoolCarrier pl 0 Z := ⟨X, hX, hZ.1, x, hx, hZ.2⟩
    refine ⟨by simp, Z, ⟨hpoolZ, hZ.2⟩, ?_, ?_, ?_⟩
    · intro Z' hZ'
      obtain ⟨X', _, hcarrier, _⟩ := hZ'.1
      exact AffineVariety.ext ((regularity_zero_carrier X'.path Z' hcarrier).trans hZbot.symm)
    · refine ⟨hZ.2, ?_⟩
      rw [Z.localDimension_eq_dimension (toC x) hZirr hZ.2, hdim, htangent]
      simp [Module.finrank_fintype_fun_eq_card]
    · rw [htangent, regularity_empty_kernel]

end
end DistinctDistances.TrackD
