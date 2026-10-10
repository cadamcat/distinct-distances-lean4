import DistinctDistances.TrackE.OuterRegularity
import DistinctDistances.TrackE.MOLiftAux

/-! Discarding non-contained direction components (sparse-cones.tex:564–578).

`outer_discard_uncontained` (sc:564–578): Bézout against one equation nonzero
on each non-contained component, times the light-line sample cap. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The direction component `γ` lies in the specialized common label
equations at the source `p`, in chart `i₀`: every equation vanishes at the
label `(p, z/z_{i₀})` of every direction `z ∈ γ` off the chart hyperplane. -/
def outerGammaInEqs (i₀ : Fin d) (Eqs : Finset (TrackD.PairPoly d)) (p : Point d)
    (γ : ProjectiveVariety d) : Prop :=
  ∀ G ∈ Eqs, ∀ z ∈ γ.points, z.rep i₀ ≠ 0 →
    MvPolynomial.eval (TrackD.pairPt p ((z.rep i₀)⁻¹ • z.rep)) G = 0

/-- The light-line cap of the selected graph at index `i`: `B^ρ` with the
selection tolerance (`TrackD.SelectedIncidence`, `occ` clause). -/
def outerLineCap {F : ConeCoverageSequence regime} (T : SelectedProfileSequence F)
    (i : ℕ) : ℝ :=
  TrackD.cfgB (regime.P i) ^ selectionTolerance (T.precision i)

/-- A non-contained component yields a witnessing equation and chart direction. -/
theorem exists_witness_of_not_outerGammaInEqs (i₀ : Fin d)
    (Eqs : Finset (TrackD.PairPoly d)) (p : Point d) (γ : ProjectiveVariety d)
    (h : ¬ outerGammaInEqs i₀ Eqs p γ) :
    ∃ G ∈ Eqs, ∃ z ∈ γ.points, z.rep i₀ ≠ 0 ∧
      MvPolynomial.eval (TrackD.pairPt p (((z.rep i₀)⁻¹) • z.rep)) G ≠ 0 := by
  classical
  unfold outerGammaInEqs at h
  push_neg at h
  obtain ⟨G, hGmem, z, hzmem, hw, hne⟩ := h
  exact ⟨G, hGmem, z, hzmem, hw, hne⟩

/-- A good pair's label satisfies every common equation. -/
theorem good_pair_label_vanishing {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (k i j : ℕ) (i₀ : Fin d) (ρ ε ρ' Bdeg : ℝ) {τ : ℝ}
    (cert : OuterRegularityCert T M k i j i₀ ρ ε ρ' Bdeg τ)
    (pq : RPoint d × RPoint d) (hpq : pq ∈ cert.chart.G)
    (hgood : cert.good pq) (G : TrackD.PairPoly d) (hG : G ∈ cert.Eqs) :
    MvPolynomial.eval
      (fun kk => TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)
        (finSumFinEquiv.symm kk))
      (commonPairEquation G) = 0 := by
  have hmem := cert.hvanish pq hpq hgood G hG
  have hpt := cert.chart.hlabel pq hpq
  have hzero := MvPolynomial.mem_zeroLocus_iff.mp hpt _ hmem
  simpa [MvPolynomial.aeval_eq_eval] using hzero

/-- A good pair's displacement is a homogenized zero for every equation. -/
theorem good_pair_homogenized_vanishing_at_displacement
    {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (k i j : ℕ) (i₀ : Fin d) (ρ ε ρ' Bdeg : ℝ) {τ : ℝ}
    (cert : OuterRegularityCert T M k i j i₀ ρ ε ρ' Bdeg τ)
    (pq : RPoint d × RPoint d) (hpq : pq ∈ cert.chart.G)
    (hgood : cert.good pq) (G : TrackD.PairPoly d) (hG : G ∈ cert.Eqs) :
    MvPolynomial.eval (TrackD.toC pq.2 - TrackD.toC pq.1)
      (MOLiftAux.chartHomogenize
        (TrackD.pairFixLeft G (TrackD.toC pq.1)) i₀) = 0 := by
  classical
  set p := TrackD.toC pq.1 with hpdef
  set q := TrackD.toC pq.2 with hqdef
  set v := q - p with hvdef
  have hchart : v i₀ ≠ 0 := cert.chart.hchart pq hpq
  set H := TrackD.pairFixLeft G p with hHdef
  have heval := MOLiftAux.chartHomogenize_eval H i₀ v hchart
  rw [heval]
  have hspec : MvPolynomial.eval (((v i₀)⁻¹) • v) H =
      MvPolynomial.eval (TrackD.pairPt p (((v i₀)⁻¹) • v)) G := by
    rw [hHdef]
    exact TrackD.eval_pairFixLeft G p _
  rw [hspec]
  have hlabel_eq : TrackD.pairPt p (((v i₀)⁻¹) • v) =
      TrackD.labelPt i₀ p q := by
    simp [TrackD.labelPt, hvdef]
  rw [hlabel_eq]
  have hlab := good_pair_label_vanishing T M k i j i₀ ρ ε ρ' Bdeg cert pq hpq hgood G hG
  have hrename : MvPolynomial.eval
      (fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk))
      (commonPairEquation G) =
      MvPolynomial.eval (TrackD.labelPt i₀ p q) G := by
    simp only [commonPairEquation, MvPolynomial.eval_rename]
    have hcomp : ((fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk)) ∘
        ⇑finSumFinEquiv) = TrackD.labelPt i₀ p q := by
      funext x
      simp [Function.comp]
    rw [hcomp]
  have hlab' : MvPolynomial.eval (TrackD.labelPt i₀ p q) G = 0 := hrename ▸ hlab
  rw [hlab']
  exact mul_zero _

/-- One witnessing equation bounds all common-equation zeros on a
non-contained projective curve. -/
theorem noncontained_curve_zero_finset (i₀ : Fin d)
    (Eqs : Finset (TrackD.PairPoly d)) (Bdeg : ℝ)
    (hdeg : ∀ G ∈ Eqs, (G.totalDegree : ℝ) ≤ Bdeg)
    (p : Point d) (γ : ProjectiveVariety d) (hγ : γ.IsIrreducible)
    (hdim : γ.dimension = 1) (hnot : ¬ outerGammaInEqs i₀ Eqs p γ) :
    ∃ Z : Finset (ProjectivePoint d),
      (Z.card : ℝ) ≤ (γ.degree : ℝ) * Bdeg ∧
      ∀ z ∈ γ.points,
        (∀ G ∈ Eqs, MvPolynomial.eval z.rep
          (MOLiftAux.chartHomogenize (TrackD.pairFixLeft G p) i₀) = 0) → z ∈ Z := by
  obtain ⟨G, hG, z, hz, hw, hne⟩ :=
    exists_witness_of_not_outerGammaInEqs i₀ Eqs p γ hnot
  let H := TrackD.pairFixLeft G p
  have hH : MvPolynomial.eval (((z.rep i₀)⁻¹) • z.rep) H ≠ 0 := by
    rw [TrackD.eval_pairFixLeft]
    exact hne
  have hnon := MOLiftAux.chartHomogenize_not_mem_of_witness H i₀ γ z hz hw hH
  obtain ⟨Z, hZ, hcard⟩ := MOLiftAux.projective_curve_zero_finset γ hγ hdim
    (MOLiftAux.chartHomogenize H i₀) H.totalDegree
    (MOLiftAux.chartHomogenize_homogeneous H i₀) hnon
  have hHdeg : (H.totalDegree : ℝ) ≤ Bdeg := by
    have hle : H.totalDegree ≤ G.totalDegree := MOLiftAux.pairFixLeft_totalDegree_le G p
    exact (by exact_mod_cast hle : (H.totalDegree : ℝ) ≤ (G.totalDegree : ℝ)).trans (hdeg G hG)
  refine ⟨Z, ?_, ?_⟩
  · calc
      (Z.card : ℝ) ≤ (H.totalDegree : ℝ) * (γ.degree : ℝ) := hcard
      _ ≤ Bdeg * (γ.degree : ℝ) :=
        mul_le_mul_of_nonneg_right hHdeg (MOLiftAux.projective_degree_nonneg γ)
      _ = (γ.degree : ℝ) * Bdeg := mul_comm _ _
  · intro u hu hzero
    exact (hZ u).2 ⟨hu, hzero G hG⟩

/-- sc:outer-discard.uncontained (sparse-cones.tex:564–578).
Fix `p ∈ S`. At a good pair the label `(p, (q-p)/(q-p)_{i₀})` satisfies every
equation of `Eqs` (`hvanish` + `chart.hlabel`). If a component `γ` of `C_p` is
not in the specialized equations (`¬ outerGammaInEqs`), one equation `G` is
nonzero at some chart point of `γ`; the homogenization in `w_{i₀}` of
`G(p, w)` has degree `≤ Bdeg` and does not vanish on `γ`, so it meets `γ` in
at most `deg γ · Bdeg` directions (Bézout for an irreducible projective curve
against a hypersurface; cf. `TrackA.fa_bezout_curve_length`,
`TrackD.prof_budget_bezout`). Summing over `γ ∈ Cf p` gives `≤ E·Bdeg`
directions; the targets of the selected graph in one real direction from `p`
lie on one real line and number at most `outerLineCap T i` (`occ` clause of
`TrackD.SelectedIncidence`, valid since `G ⊆ outerSelectedGraph`). Hence the
deleted pairs number at most `|S|·E·Bdeg·cap ≤ ρ'|S|²` by `hsmall`. -/
theorem outer_discard_uncontained {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (k i j : ℕ) (i₀ : Fin d) (ρ ε ρ' Bdeg : ℝ) {τ : ℝ}
    (cert : OuterRegularityCert T M k i j i₀ ρ ε ρ' Bdeg τ)
    (Cf : TrackD.Pt d → ProjectiveFamily.Family d)
    (hDir : ∀ pq ∈ cert.chart.G, cert.good pq →
      TrackD.DirIn (Cf pq.1) pq.1 pq.2)
    (E : ℝ) (hE : ∀ p ∈ cert.chart.pool.S,
      ((ProjectiveFamily.degree (Cf p) : ℚ) : ℝ) ≤ E)
    (hsmall : E * Bdeg * outerLineCap T i ≤ ρ' * (cert.chart.pool.S.card : ℝ)) :
    ∃ D : Finset (RPoint d × RPoint d), D ⊆ cert.chart.G ∧
      ((D.card : ℝ)) ≤ ρ' * (cert.chart.pool.S.card : ℝ) ^ 2 ∧
      ∀ pq ∈ cert.chart.G \ D, cert.good pq → ∀ γ ∈ Cf pq.1,
        γ.IsIrreducible → γ.dimension = 1 →
        (∃ h : TrackD.toC pq.2 ≠ TrackD.toC pq.1,
          radialProjection (TrackD.toC pq.1) (TrackD.toC pq.2) h ∈ γ.points) →
        outerGammaInEqs i₀ cert.Eqs (TrackD.toC pq.1) γ := by
  classical
  have hbudget : 0 ≤ ρ' * (cert.chart.pool.S.card : ℝ) ^ 2 :=
    (Nat.cast_nonneg _).trans cert.hbad
  by_cases hB : 0 ≤ Bdeg
  · have hex (p : RPoint d) (γ : ProjectiveVariety d) :
        ∃ Z : Finset (ProjectivePoint d),
          (Z.card : ℝ) ≤ (γ.degree : ℝ) * Bdeg ∧
          ((γ.IsIrreducible ∧ γ.dimension = 1 ∧
            ¬ outerGammaInEqs i₀ cert.Eqs (TrackD.toC p) γ) →
          ∀ z ∈ γ.points,
            (∀ G ∈ cert.Eqs, MvPolynomial.eval z.rep
              (MOLiftAux.chartHomogenize (TrackD.pairFixLeft G (TrackD.toC p)) i₀) = 0) →
            z ∈ Z) := by
      by_cases ha : γ.IsIrreducible ∧ γ.dimension = 1 ∧
          ¬ outerGammaInEqs i₀ cert.Eqs (TrackD.toC p) γ
      · obtain ⟨Z, hcard, hcover⟩ := noncontained_curve_zero_finset i₀ cert.Eqs
          Bdeg cert.hEqdeg (TrackD.toC p) γ ha.1 ha.2.1 ha.2.2
        exact ⟨Z, hcard, fun _ => hcover⟩
      · refine ⟨∅, ?_, fun h => (ha h).elim⟩
        simpa using mul_nonneg (MOLiftAux.projective_degree_nonneg γ) hB
    choose bad hbadcard hbadcover using hex
    let dirs (p : RPoint d) := (Cf p).biUnion (bad p)
    let D := cert.chart.G.filter (fun pq => cert.good pq ∧
      ∃ h : TrackD.toC pq.2 ≠ TrackD.toC pq.1,
        radialProjection (TrackD.toC pq.1) (TrackD.toC pq.2) h ∈ dirs pq.1)
    let row (p : RPoint d) := (D.filter (fun pq => pq.1 = p)).image Prod.snd
    have hDsub : D ⊆ cert.chart.G := Finset.filter_subset _ _
    have hrowmem (p q : RPoint d) : q ∈ row p ↔ (p, q) ∈ D := by
      constructor
      · intro hq
        obtain ⟨⟨a, b⟩, hab, hb⟩ := Finset.mem_image.mp hq
        obtain ⟨habD, ha⟩ := Finset.mem_filter.mp hab
        dsimp at ha hb
        subst a
        subst b
        exact habD
      · intro hpq
        exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_filter.mpr ⟨hpq, rfl⟩, rfl⟩
    have hrowcard (p : RPoint d) : (D.filter (fun pq => pq.1 = p)).card = (row p).card := by
      symm
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      apply Prod.ext
      · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
      · exact hab
    have hcap : 0 ≤ outerLineCap T i := by
      unfold outerLineCap
      exact Real.rpow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _
    have hSsub : cert.chart.pool.S ⊆ regime.P i := by
      intro q hq
      have hpool := cert.chart.pool.hSsub hq
      obtain ⟨X, hX, hqX⟩ := Finset.mem_biUnion.mp hpool
      exact ((T.certificate i).good.pieces_good X
        ((T.certificate i).sources_subset hX)).1.subset hqX
    have hrowbound : ∀ p ∈ cert.chart.pool.S,
        ((row p).card : ℝ) ≤ outerLineCap T i * (E * Bdeg) := by
      intro p hp
      apply MOLiftAux.discard_row_bound_of_gamma_bounds (regime.P i) (row p) p
        (Cf p) E Bdeg (outerLineCap T i) hcap hB (hE p hp) (bad p)
        (fun γ _ => hbadcard p γ)
      · intro q hq
        exact hSsub (cert.chart.hGmem (p, q) (hDsub ((hrowmem p q).1 hq))).2
      · intro q hq
        have hG := hDsub ((hrowmem p q).1 hq)
        have hsel := (Finset.mem_filter.mp (cert.chart.hGsub hG)).2
        exact hsel.2.2.2
      · intro q hq
        have hD := (hrowmem p q).1 hq
        exact (Finset.mem_filter.mp hD).2.2
    have hcardD : D.card = ∑ p ∈ cert.chart.pool.S, (row p).card := by
      rw [MOLiftAux.discard_pair_card_eq_fiber_sum cert.chart.pool.S D
        (fun pq hpq => (cert.chart.hGmem pq (hDsub hpq)).1)]
      exact Finset.sum_congr rfl (fun p _ => hrowcard p)
    refine ⟨D, hDsub, ?_, ?_⟩
    · rw [hcardD]
      exact MOLiftAux.discard_global_bound_of_row_sums cert.chart.pool.S
        (fun p => (row p).card) (outerLineCap T i) E Bdeg ρ' hsmall hrowbound
    · intro pq hpq hgood γ hγmem hγ hdim hdir
      by_contra hnot
      obtain ⟨hneq, hzγ⟩ := hdir
      let z := radialProjection (TrackD.toC pq.1) (TrackD.toC pq.2) hneq
      have hzbad : z ∈ bad pq.1 γ := by
        apply hbadcover pq.1 γ ⟨hγ, hdim, hnot⟩ z hzγ
        intro G hG
        apply MOLiftAux.homogenized_zero_of_rep_eq_of_vector_zero
          (TrackD.pairFixLeft G (TrackD.toC pq.1)) i₀
          (TrackD.toC pq.2 - TrackD.toC pq.1) (sub_ne_zero.mpr hneq) z rfl
        exact good_pair_homogenized_vanishing_at_displacement T M k i j i₀ ρ ε ρ'
          Bdeg cert pq (Finset.mem_sdiff.mp hpq).1 hgood G hG
      have hzdirs : z ∈ dirs pq.1 := Finset.mem_biUnion.mpr ⟨γ, hγmem, hzbad⟩
      have hpqD : pq ∈ D := Finset.mem_filter.mpr
        ⟨(Finset.mem_sdiff.mp hpq).1, hgood, hneq, hzdirs⟩
      exact (Finset.mem_sdiff.mp hpq).2 hpqD
  · refine ⟨∅, Finset.empty_subset _, by simpa using hbudget, ?_⟩
    intro pq hpq hgood γ hγmem hγ hdim hdir
    intro G hG z hz hw
    have hnonneg : (0 : ℝ) ≤ (G.totalDegree : ℝ) := Nat.cast_nonneg _
    exact (hB (hnonneg.trans (cert.hEqdeg G hG))).elim

end
end DistinctDistances.SparseCones
