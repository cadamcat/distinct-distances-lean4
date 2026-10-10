import DistinctDistances.TrackA.HomogeneousRegularitySupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

theorem homogeneous_generic_rank_detected_by_minor {n : ℕ}
    (F : ProjectiveFamily.Family n) (V : ProjectiveVariety n) (hV : V ∈ F)
    (hprime : V.IsIrreducible) (k D : ℕ) (hk : k ≤ n) (E : List (Poly n))
    (hE : ∀ f ∈ E, f ∈ (ProjectiveFamily.locus F).ideal ∧ f.IsHomogeneous D)
    (hspan : ∀ f : Poly n, f ∈ (ProjectiveFamily.locus F).ideal → f.IsHomogeneous D →
      f ∈ Submodule.span ℂ {f | f ∈ E})
    (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1) (hℓV : ℓ ∉ V.ideal)
    (hrank : GenericJacobianRank (coneFamily F) V.affineCone D k) :
    ∃ m ∈ jacobianMinors E (n-k), m ∉ V.ideal := by
  obtain ⟨g, hg, hgeneric⟩ := hrank
  have hprod : g*ℓ ∉ V.ideal := by
    intro h
    exact (hprime.mem_or_mem h).elim hg hℓV
  have hex : ∃ x ∈ V.affineCone.points, MvPolynomial.eval x (g*ℓ) ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hprod
    change g*ℓ ∈ V.affineCone.ideal
    rw [← V.affineCone.vanishingIdeal_points]
    intro x hx
    simpa [MvPolynomial.aeval_eq_eval] using hn x hx
  obtain ⟨x, hx, hxprod⟩ := hex
  have hxg : MvPolynomial.eval x g ≠ 0 := by
    exact (mul_ne_zero_iff.mp (by simpa only [map_mul] using hxprod)).1
  have hxℓ : MvPolynomial.eval x ℓ ≠ 0 := by
    exact (mul_ne_zero_iff.mp (by simpa only [map_mul] using hxprod)).2
  have hxF : x ∈ (ProjectiveFamily.locus F).affineCone.points := by
    intro f hf
    exact hx f ((chart_projective_family_mem F f).1 hf V hV)
  have hdim := hgeneric x hx hxg
  let A := evaluatedJacobian E x
  have hA : A.rank = n-k := by
    have he := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    change A.rank + Module.finrank ℂ (LinearMap.ker A.mulVecLin) =
      Module.finrank ℂ (Point n) at he
    rw [homogeneous_evaluatedJacobian_kernel F E D hE hspan x hxF ℓ hℓ hxℓ, hdim] at he
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at he
    omega
  obtain ⟨rows, cols, hdet⟩ := matrix_rank_minor A hA
  let m := Matrix.det ((jacobian E).submatrix rows cols)
  have hmeval : MvPolynomial.eval x m ≠ 0 := by
    have he : (MvPolynomial.eval x).mapMatrix ((jacobian E).submatrix rows cols) =
        A.submatrix rows cols := by ext i j; rfl
    change MvPolynomial.eval x ((jacobian E).submatrix rows cols).det ≠ 0
    rw [(MvPolynomial.eval x).map_det, he]
    exact hdet
  refine ⟨m, ⟨rows, cols, rfl⟩, ?_⟩
  intro hm
  apply hmeval
  simpa [MvPolynomial.aeval_eq_eval] using hx m hm

end
end DistinctDistances.TrackA
