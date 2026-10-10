import DistinctDistances.TrackB.PairProjectionSupport
import DistinctDistances.TrackB.Requests

namespace DistinctDistances.TrackB
noncomputable section

section Ruling
variable {e j N : ℕ} (C : SkewCoordinates e)
  (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e)) (a : Fin e) (R : IsRulingIncidence C V Γ H a j N)
include R

theorem parameter_base_resolution : liftedParameterBase C Γ H ⊆ resolutionPairs e := by
  apply closedPairs_resolution
  rintro ⟨d, p⟩ ⟨z, v, hw, hv, hd, hp⟩
  change d = Projectivization.mk ℂ v hv at hd
  change p = graphParameter C z v hv at hp
  have hinc : incidenceCondition C d p (affineEmbedding z) := by
    rw [hd, hp]
    exact graph_incidenceCondition C z v hv
  obtain ⟨t, ht, hy, _⟩ := hinc
  exact ⟨t, ht, hy⟩

/-- The actual lifted base has the whole parameter closure as its second image.
Properness supplies closedness; the original ruling parameters supply density. -/
theorem parameter_base_projection :
    {p | ∃ d : ProjectivePoint e, (d, p) ∈ liftedParameterBase C Γ H} =
      (parameterClosure C Γ H).points := by
  let T := liftedParameterPairs C Γ H
  let S : Set (ProjectivePoint (e + e)) :=
    {p | ∃ d : ProjectivePoint e, (d, p) ∈ liftedParameterBase C Γ H}
  have hfactor : ∀ b ∈ (pairClosure T).points,
      ∃ d : ProjectivePoint e, ∃ p : ProjectivePoint (e + e), segrePoint d p = b :=
    fun b hb => pairClosure_factorization T b hb
  have hclosed : S = (ProjectiveVariety.closure S).points :=
    Request.projective_segre_projection_closed (pairClosure T) hfactor
  have hT : ∀ d p, (d, p) ∈ T → p ∈ (parameterClosure C Γ H).points := by
    rintro d p ⟨z, v, hw, hv, hd, hp⟩
    exact ProjectiveVariety.subset_closure _ ⟨z, v, hw, hv, hp.symm⟩
  have hforward : S ⊆ (parameterClosure C Γ H).points := by
    rintro p ⟨d, hdp⟩
    exact pairClosure_projection_contained T (parameterClosure C Γ H) hT d p hdp
  have hImage : parameterImage C Γ H ⊆ S := by
    rintro p ⟨z, v, hw, hv, hp⟩
    refine ⟨Projectivization.mk ℂ v hv, ?_⟩
    apply ProjectiveVariety.subset_closure
    exact ⟨Projectivization.mk ℂ v hv, p, ⟨z, v, hw, hv, rfl, hp.symm⟩, rfl⟩
  have hback : (parameterClosure C Γ H).points ⊆ S := by
    have h := projective_closure_subset (parameterImage C Γ H) (ProjectiveVariety.closure S)
      (hImage.trans (ProjectiveVariety.subset_closure S))
    rwa [← hclosed] at h
  exact Set.Subset.antisymm hforward hback

theorem parameter_base_unique_lift (p : ProjectivePoint (e + e))
    (hpY : p ∈ (parameterClosure C Γ H).points) (hp : p ∈ affineParameters e) :
    ∃! d : ProjectivePoint e, (d, p) ∈ liftedParameterBase C Γ H := by
  have hpS : p ∈ {p | ∃ d : ProjectivePoint e, (d, p) ∈ liftedParameterBase C Γ H} := by
    rw [parameter_base_projection C V Γ H a R]
    exact hpY
  obtain ⟨d, hd⟩ := hpS
  obtain ⟨d0, hd0, huniq⟩ := parameterResolution_open e p hp
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  exact (huniq d' (parameter_base_resolution C V Γ H a R hd')).trans
    (huniq d (parameter_base_resolution C V Γ H a R hd)).symm

theorem parameter_first_coordinate_not_mem :
    MvPolynomial.X (Fin.castAdd e a) ∉ (parameterClosure C Γ H).ideal := by
  have hg := rulingOpenPolynomial_not_mem C V Γ H a R
  have hex : ∃ w ∈ Γ.points, MvPolynomial.aeval w (rulingOpenPolynomial H) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hg
    rw [← Γ.vanishingIdeal_points]
    exact h
  obtain ⟨w, hw, hgw⟩ := hex
  let z := firstPoint w
  let v := secondPoint w
  have hnorm : v a = 1 := R.normalized w hw
  have hv : v ≠ 0 := by intro h; rw [h] at hnorm; exact zero_ne_one hnorm
  have hwjoin : joinPoints z v ∈ rulingPoints Γ H := by
    rw [show joinPoints z v = w from joinPoints_eta w]
    exact ⟨hw, by simpa only [eval_rulingOpenPolynomial] using hgw⟩
  let p := graphParameter C z v hv
  have hpY : p ∈ (parameterClosure C Γ H).points :=
    ProjectiveVariety.subset_closure _ ⟨z, v, hwjoin, hv, rfl⟩
  intro hf
  have hzero : p.rep (Fin.castAdd e a) = 0 := by
    have h := hpY p.rep p.rep_nonzero (Projectivization.mk_rep p) _ hf
    simpa using h
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (graphVector C z v)
    (graphVector_ne_zero C z v hv)
  have hfirst : p.rep (Fin.castAdd e a) = (u : ℂ) * v a := by
    change (graphParameter C z v hv).rep (Fin.castAdd e a) = _
    rw [graphParameter, ← hu, Units.smul_def]
    simp [graphVector, joinPoints, Pi.smul_apply, smul_eq_mul]
  rw [hfirst, hnorm, mul_one] at hzero
  exact u.ne_zero hzero

/-- A fixed actual first coordinate defines a birational open of the second
projection. The inverse is the unique lift in the quadric resolution. -/
theorem parameter_base_birational_open :
    ∃ (g : Poly (e + e)) (D : ℕ), g.IsHomogeneous D ∧ g ∉ (parameterClosure C Γ H).ideal ∧
      ∀ p ∈ (parameterClosure C Γ H).points, MvPolynomial.aeval p.rep g ≠ 0 →
        ∃! d : ProjectivePoint e, (d, p) ∈ liftedParameterBase C Γ H := by
  refine ⟨MvPolynomial.X (Fin.castAdd e a), 1, MvPolynomial.isHomogeneous_X ℂ _,
    parameter_first_coordinate_not_mem C V Γ H a R, ?_⟩
  intro p hpY hpG
  have hfirst : firstPoint p.rep ≠ 0 := by
    intro hz
    have hcoord : p.rep (Fin.castAdd e a) = 0 := congrFun hz a
    exact hpG (by simpa using hcoord)
  exact parameter_base_unique_lift C V Γ H a R p hpY
    ⟨parameterClosure_subset_quadric C Γ H hpY, hfirst⟩

end Ruling
#print axioms parameter_base_projection
#print axioms parameter_base_birational_open
end
end DistinctDistances.TrackB
