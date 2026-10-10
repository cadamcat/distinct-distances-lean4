import DistinctDistances.TrackB.IncidenceLinearSupport
import DistinctDistances.TrackB.ParameterImageSupport
import DistinctDistances.TrackB.AffineFlatGeometry

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators

theorem graphParameter_mem_affine {e : ℕ} (C : SkewCoordinates e)
    (z : Point (skewDim e)) (v : Point e) (hv : v ≠ 0) :
    graphParameter C z v hv ∈ affineParameters e := by
  refine ⟨graphParameter_mem_quadric C z v hv, ?_⟩
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (graphVector C z v)
    (graphVector_ne_zero C z v hv)
  have hfirst : firstPoint (graphParameter C z v hv).rep = (a : ℂ) • v := by
    rw [graphParameter, ← ha, Units.smul_def]
    funext i
    simp [firstPoint, graphVector, joinPoints, Pi.smul_apply]
  rw [hfirst]
  exact smul_ne_zero a.ne_zero hv

def tailEmbeddingLinear (n : ℕ) : Point n →ₗ[ℂ] Point (n + 1) :=
  LinearMap.pi (Fin.cons 0 (fun k => LinearMap.proj k))

theorem consOne_ne_zero {n : ℕ} (z : Point n) : (Fin.cons 1 z : Point (n + 1)) ≠ 0 := by
  intro hz
  have h := congrFun hz 0
  exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using h)

theorem projective_closure_subset {n : ℕ} (T : Set (ProjectivePoint n))
    (W : ProjectiveVariety n) (hT : T ⊆ W.points) :
    (ProjectiveVariety.closure T).points ⊆ W.points := by
  intro p hp v hv he f hf
  apply hp v hv he f
  rintro w ⟨hw, hpoint⟩
  exact hT hpoint w hw rfl f hf

theorem zero_mem_nonempty_projective_cone {n : ℕ} (W : ProjectiveVariety n)
    (hW : W.points.Nonempty) : (0 : Point n) ∈ W.affineCone.points := by
  intro f hf
  have h := zero_mem_projective_cone W.points hW
  have hf' : f ∈ (ProjectiveVariety.closure W.points).ideal := by
    change f ∈ W.ideal at hf
    rwa [← W.vanishingIdeal_points] at hf
  exact h f hf'

section Ruling
variable {e j N : ℕ} (C : SkewCoordinates e)
  (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e)) (a : Fin e) (R : IsRulingIncidence C V Γ H a j N)
  (W : ProjectiveVariety ((e * (e + e)) * (skewDim e + 1)))
  (hGraph : ∀ z v, joinPoints z v ∈ rulingPoints Γ H → ∀ hv : v ≠ 0,
    segrePoint (segrePoint (Projectivization.mk ℂ v hv) (graphParameter C z v hv))
      (affineEmbedding z) ∈ W.points)

include R hGraph

/-- The ruling's full affine fiber is dense in the whole projective incidence fiber.
The proof uses prime vanishing ideals and the actual flat closure, not dimensions. -/
theorem ruling_projective_fiber_mem (d : ProjectivePoint e)
    (p : ProjectivePoint (e + e)) (hp : p ∈ parameterImage C Γ H)
    (hdp : (d, p) ∈ resolutionPairs e) (x : ProjectivePoint (skewDim e + 1))
    (hx : incidenceCondition C d p x) : segrePoint (segrePoint d p) x ∈ W.points := by
  obtain ⟨z0, v0, hw0, hv0, hp0⟩ := hp
  have hpimage : p ∈ parameterImage C Γ H := ⟨z0, v0, hw0, hv0, hp0⟩
  have hpaff : p ∈ affineParameters e := hp0 ▸ graphParameter_mem_affine C z0 v0 hv0
  have hfirst0 : firstPoint (joinPoints z0 v0) = z0 := by
    funext i
    exact Fin.addCases_left (m := skewDim e) (n := e) (motive := fun _ => ℂ)
      (left := z0) (right := v0) i
  have hwork0 : z0 ∈ workingPoints V H := by
    refine ⟨?_, ?_⟩
    · have h := R.point_containment (joinPoints z0 v0) hw0.1
      rwa [hfirst0] at h
    · exact hfirst0 ▸ hw0.2
  have hz0flat : z0 ∈ evaluationFlat C p :=
    (R.full_parameter_fibers p hpimage z0 hwork0).mpr ⟨v0, hw0, hv0, hp0⟩
  have hflatV : evaluationFlat C p ⊆ V.points := by
    rw [← hp0]
    exact R.actual_flats z0 v0 hw0 hv0
  have hH : H ∉ MvPolynomial.vanishingIdeal ℂ (evaluationFlat C p) := by
    intro h
    exact hwork0.2 (h z0 hz0flat)
  have hGraphAt (z : Point (skewDim e)) (hz : z ∈ evaluationFlat C p)
      (hzH : MvPolynomial.aeval z H ≠ 0) :
      segrePoint (segrePoint d p) (affineEmbedding z) ∈ W.points := by
    have hzwork : z ∈ workingPoints V H := ⟨hflatV hz, hzH⟩
    obtain ⟨v, hw, hv, hparam⟩ := (R.full_parameter_fibers p hpimage z hzwork).mp hz
    have hdgraph : (Projectivization.mk ℂ v hv, p) ∈ resolutionPairs e := by
      have hinc := graph_incidenceCondition C z v hv
      rw [hparam] at hinc
      obtain ⟨t, ht, hy, _⟩ := hinc
      exact ⟨t, ht, hy⟩
    obtain ⟨d0, hd0, huniq⟩ := parameterResolution_open e p hpaff
    have hd : d = Projectivization.mk ℂ v hv :=
      (huniq d hdp).trans (huniq _ hdgraph).symm
    simpa only [← hd, hparam] using hGraph z v hw hv
  let φ := fixedSegreLinear (o := skewDim e + 1) d p
  let b0 : Point (skewDim e + 1) := Fin.cons 1 0
  let ψ : Point (skewDim e) →ₗ[ℂ] Point ((e * (e + e)) * (skewDim e + 1)) :=
    φ.comp (tailEmbeddingLinear (skewDim e))
  have hpull (f : Poly ((e * (e + e)) * (skewDim e + 1))) (z : Point (skewDim e)) :
      MvPolynomial.aeval z (affineLinearPullback (φ b0) ψ f) =
        MvPolynomial.aeval (φ (Fin.cons 1 z)) f := by
    rw [eval_affineLinearPullback]
    change MvPolynomial.aeval (φ b0 + φ (tailEmbeddingLinear (skewDim e) z)) f = _
    rw [← map_add]
    have hsplit : b0 + tailEmbeddingLinear (skewDim e) z = Fin.cons 1 z := by
      funext k
      cases k using Fin.cases <;> simp [b0, tailEmbeddingLinear]
    rw [hsplit]
  have hAff (z : Point (skewDim e)) (hz : z ∈ evaluationFlat C p) :
      segrePoint (segrePoint d p) (affineEmbedding z) ∈ W.points := by
    apply (fixedSegreLinear_mk_mem d p (Fin.cons 1 z) (consOne_ne_zero z) W).mpr
    intro f hf
    let q := affineLinearPullback (φ b0) ψ f
    have hprod : H * q ∈ MvPolynomial.vanishingIdeal ℂ (evaluationFlat C p) := by
      intro z hz
      rw [map_mul]
      by_cases hzH : MvPolynomial.aeval z H = 0
      · rw [hzH, zero_mul]
      · have hvan := (fixedSegreLinear_mk_mem d p (Fin.cons 1 z) (consOne_ne_zero z) W).mp
          (hGraphAt z hz hzH)
        have hq : MvPolynomial.aeval z q = 0 := by
          rw [hpull]
          exact hvan f hf
        rw [hq, mul_zero]
    have hq : q ∈ MvPolynomial.vanishingIdeal ℂ (evaluationFlat C p) :=
      ((evaluationFlat_vanishingIdeal_prime C p hpaff).mem_or_mem hprod).resolve_left hH
    exact (hpull f z).symm.trans (hq z hz)
  have hφ : Function.Injective φ := fixedSegreLinear_injective d p
  have hφx : φ x.rep ≠ 0 := by
    intro hzero
    exact x.rep_nonzero (hφ (hzero.trans φ.map_zero.symm))
  have hImage : ∀ q ∈ affineEmbedding '' evaluationFlat C p, ∀ hq : φ q.rep ≠ 0,
      TrackA.projectiveMap φ q hq ∈ W.points := by
    rintro q ⟨z, hz, rfl⟩ hq
    rw [fixedSegreLinear_projective]
    exact hAff z hz
  have hxflat := incidenceCondition_flatClosure C d p hpaff hdp x hx
  have hw := projective_linear_closure φ hφ _ W hImage x hxflat hφx
  rwa [fixedSegreLinear_projective] at hw

/-- Extend fiberwise polynomial vanishing from the actual parameter image to its
closed base. Explicit spanning vectors include the boundary fibers. -/
theorem ruling_incidence_generator_mem (d : ProjectivePoint e)
    (p : ProjectivePoint (e + e)) (hbase : (d, p) ∈ liftedParameterBase C Γ H)
    (x : ProjectivePoint (skewDim e + 1)) (hx : incidenceCondition C d p x) :
    segrePoint (segrePoint d p) x ∈ W.points := by
  classical
  let T := liftedParameterPairs C Γ H
  let b := segrePoint d p
  have hb : b ∈ pairClosure T := hbase
  obtain ⟨k, hk⟩ := exists_nonzero_coordinate b
  let ci := (finProdFinEquiv.symm k).1
  let cj := (finProdFinEquiv.symm k).2
  have hpivot : b.rep (finProdFinEquiv (ci, cj)) ≠ 0 := by
    simpa only [ci, cj, Prod.mk.eta, Equiv.apply_symm_apply] using hk
  obtain ⟨hc, hr, hfactor⟩ := pairClosure_pivot_reconstruction T b.rep b.rep_nonzero
    (by simpa only [Projectivization.mk_rep] using hb) ci cj hpivot
  have hpair :
      (Projectivization.mk ℂ (segreColumn cj b.rep) hc,
        Projectivization.mk ℂ (segreRow ci b.rep) hr) = (d, p) := by
    apply segrePoint_injective
    simpa only [Projectivization.mk_rep, b] using hfactor
  have hd : Projectivization.mk ℂ (segreColumn cj b.rep) hc = d := congrArg Prod.fst hpair
  have hp : Projectivization.mk ℂ (segreRow ci b.rep) hr = p := congrArg Prod.snd hpair
  have hraw := (incidenceCondition_mk_iff C (segreColumn cj b.rep) (segreRow ci b.rep)
    x.rep hc hr x.rep_nonzero).mp
      (by simpa only [hd, hp, Projectivization.mk_rep] using hx)
  obtain ⟨t, ht, hy, hxf⟩ := hraw
  have hci : segreColumn cj b.rep ci ≠ 0 := hpivot
  obtain ⟨u, hu⟩ := incidenceChartVector_surjective C ci (segreColumn cj b.rep)
    (segreRow ci b.rep) t ht hy hci x.rep hxf
  have hWnonempty : W.points.Nonempty := by
    have hopen : (rulingPoints Γ H).Nonempty := by
      by_contra hnone
      apply rulingOpenPolynomial_not_mem C V Γ H a R
      rw [← Γ.vanishingIdeal_points]
      intro w hw
      by_contra hH
      apply hnone
      refine ⟨w, hw, ?_⟩
      exact (eval_rulingOpenPolynomial H w) ▸ hH
    obtain ⟨w, hw⟩ := hopen
    let z := firstPoint w
    let v := secondPoint w
    have hv : v ≠ 0 := by
      intro hzero
      have hnorm := R.normalized w hw.1
      change v a = 1 at hnorm
      rw [hzero] at hnorm
      exact zero_ne_one hnorm
    have hjoin : joinPoints z v = w := joinPoints_eta w
    exact ⟨_, hGraph z v (hjoin.symm ▸ hw) hv⟩
  have hzero : (0 : Point ((e * (e + e)) * (skewDim e + 1))) ∈ W.affineCone.points :=
    zero_mem_nonempty_projective_cone W hWnonempty
  have hvan (f : Poly ((e * (e + e)) * (skewDim e + 1))) (hf : f ∈ W.ideal) :
      MvPolynomial.aeval
        (segreVector (segreVector (segreColumn cj b.rep) (segreRow ci b.rep)) x.rep) f = 0 := by
    let g := threeLinearSegrePullback (segreColumn cj) (segreRow ci)
      (incidenceChartLinear C ci cj u) f
    have hg : g ∈ (pairClosure T).ideal := by
      rintro s ⟨hs, hsource⟩
      obtain ⟨ds, ps, hT, hpoint⟩ := hsource
      have hsbase : Projectivization.mk ℂ s hs ∈ pairClosure T :=
        ProjectiveVariety.subset_closure _ ⟨ds, ps, hT, hpoint⟩
      rw [eval_threeLinearSegrePullback, incidenceChartLinear_apply]
      by_cases hsij : s (finProdFinEquiv (ci, cj)) = 0
      · rcases pairClosure_zero_pivot T s hs hsbase ci cj hsij with hcol | hrow
        · have hz : segreVector (segreVector (segreColumn cj s) (segreRow ci s))
              (incidenceChartVector C ci (segreColumn cj s) (segreRow ci s) u) = 0 := by
            rw [hcol]
            funext k
            simp only [segreVector, Pi.zero_apply, zero_mul]
          rw [hz]
          exact hzero f hf
        · have hz : segreVector (segreVector (segreColumn cj s) (segreRow ci s))
              (incidenceChartVector C ci (segreColumn cj s) (segreRow ci s) u) = 0 := by
            rw [hrow]
            funext k
            simp only [segreVector, Pi.zero_apply, mul_zero, zero_mul]
          rw [hz]
          exact hzero f hf
      · obtain ⟨hc', hr', hfactor'⟩ := pairClosure_pivot_reconstruction T s hs hsbase ci cj hsij
        have hpairs :
            (Projectivization.mk ℂ (segreColumn cj s) hc',
              Projectivization.mk ℂ (segreRow ci s) hr') = (ds, ps) := by
          apply segrePoint_injective
          exact hfactor'.trans hpoint.symm
        have hT' : (Projectivization.mk ℂ (segreColumn cj s) hc',
            Projectivization.mk ℂ (segreRow ci s) hr') ∈ T := hpairs.symm ▸ hT
        obtain ⟨zs, vs, hw, hvs, hds, hps⟩ := hT'
        change Projectivization.mk ℂ (segreColumn cj s) hc' = Projectivization.mk ℂ vs hvs at hds
        change Projectivization.mk ℂ (segreRow ci s) hr' = graphParameter C zs vs hvs at hps
        have hpimage : Projectivization.mk ℂ (segreRow ci s) hr' ∈ parameterImage C Γ H :=
          ⟨zs, vs, hw, hvs, hps.symm⟩
        have hinc0 : incidenceCondition C (Projectivization.mk ℂ (segreColumn cj s) hc')
            (Projectivization.mk ℂ (segreRow ci s) hr') (affineEmbedding zs) := by
          simpa only [hds, hps] using graph_incidenceCondition C zs vs hvs
        obtain ⟨ts, hts, hys, _⟩ :=
          (incidenceCondition_mk_iff C (segreColumn cj s) (segreRow ci s)
            (affineEmbedding zs).rep hc' hr' (affineEmbedding zs).rep_nonzero).mp
            (by simpa only [Projectivization.mk_rep] using hinc0)
        have hres : (Projectivization.mk ℂ (segreColumn cj s) hc',
            Projectivization.mk ℂ (segreRow ci s) hr') ∈ resolutionPairs e := by
          obtain ⟨ts', hts', hys', _⟩ := hinc0
          exact ⟨ts', hts', hys'⟩
        let y := incidenceChartVector C ci (segreColumn cj s) (segreRow ci s) u
        by_cases hyn : y = 0
        · rw [show incidenceChartVector C ci (segreColumn cj s) (segreRow ci s) u = 0 from hyn]
          have hz : segreVector (segreVector (segreColumn cj s) (segreRow ci s))
              (0 : Point (skewDim e + 1)) = 0 := by
            funext k
            simp only [segreVector, Pi.zero_apply, mul_zero]
          rw [hz]
          exact hzero f hf
        · have hincy : incidenceCondition C (Projectivization.mk ℂ (segreColumn cj s) hc')
              (Projectivization.mk ℂ (segreRow ci s) hr') (Projectivization.mk ℂ y hyn) := by
            apply (incidenceCondition_mk_iff C (segreColumn cj s) (segreRow ci s) y hc' hr' hyn).mpr
            exact ⟨ts, hts, hys, incidenceChartVector_mem C ci _ _ ts hts hys u⟩
          have hwy := ruling_projective_fiber_mem C V Γ H a R W hGraph
            _ _ hpimage hres (Projectivization.mk ℂ y hyn) hincy
          have hpointW : Projectivization.mk ℂ
              (segreVector (segreVector (segreColumn cj s) (segreRow ci s)) y)
              (segreVector_ne_zero _ _ (segreVector_ne_zero _ _ hc' hr') hyn) ∈ W.points := by
            simpa only [segrePoint_mk] using hwy
          exact ((ProjectiveVariety.mem_points_mk_iff W _ _).mp hpointW) f hf
    have hgb : MvPolynomial.aeval b.rep g = 0 :=
      hb b.rep b.rep_nonzero (Projectivization.mk_rep b) g hg
    simpa only [g, eval_threeLinearSegrePullback, incidenceChartLinear_apply, hu] using hgb
  have hrawW : segreVector (segreVector (segreColumn cj b.rep) (segreRow ci b.rep)) x.rep ∈
      W.affineCone.points := hvan
  have hpointW : Projectivization.mk ℂ
      (segreVector (segreVector (segreColumn cj b.rep) (segreRow ci b.rep)) x.rep)
      (segreVector_ne_zero _ _ (segreVector_ne_zero _ _ hc hr) x.rep_nonzero) ∈ W.points :=
    (ProjectiveVariety.mem_points_mk_iff W _ _).mpr hrawW
  have htripleW : segrePoint
      (segrePoint (Projectivization.mk ℂ (segreColumn cj b.rep) hc)
        (Projectivization.mk ℂ (segreRow ci b.rep) hr))
      (Projectivization.mk ℂ x.rep x.rep_nonzero) ∈ W.points := by
    simpa only [segrePoint_mk] using hpointW
  simpa only [hd, hp, Projectivization.mk_rep] using htripleW

theorem compact_incidence_subset_of_ruling_graph : (compactIncidence C Γ H).points ⊆ W.points := by
  apply projective_closure_subset
  rintro q ⟨d, p, x, hinc, rfl⟩
  exact ruling_incidence_generator_mem C V Γ H a R W hGraph d p hinc.1 x hinc.2

end Ruling
#print axioms ruling_projective_fiber_mem
#print axioms compact_incidence_subset_of_ruling_graph
end
end DistinctDistances.TrackB
