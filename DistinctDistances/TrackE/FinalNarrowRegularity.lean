import DistinctDistances.TrackE.FinalRegularityInputs

/-! Whole-family homogeneous regularity on the selected narrow final batch,
sparse-cones.tex:870–906. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section

/-- sc:u-final-curve.homogeneous-batch: the complete covering-envelope curve
family satisfies regularity at the reserved later degree, with the original
narrow depth deletions and a strictly smaller exceptional assigned mass. -/
theorem selected_final_narrow_regularity {n : ℕ} {regime : Regime (n + 1)}
    {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    {S : LimitingSeparatedProfile regime} [Fintype (ProfilePlateau S)]
    (K : FinalNarrowBatchData T S)
    (G : ∀ i p, CoveringEnvelopeComponents (F.family i (realCenter p))
      (finalNarrowTestDegree K K.b₀ i)) :
    let D := K.H.data K.finalPlateau
    ∃ C : ℕ, 0 < C ∧
      ∃ (badFamily : ℕ → Point (n + 1) → ProjectiveFamily.Family (n + 1))
        (E : ℕ → Point (n + 1) → List (Poly (n + 1)))
        (g : ℕ → Point (n + 1) → Poly (n + 1)),
        (∀ᶠ i in atTop, ∀ p ∈ D.centers i, p ∉ K.H.batch.badCenters i →
          HomogeneousCurveRegularityCertificate (envelopeDimensionPart (G i p).components 1)
            (badFamily i p) (E i p) (g i p) C (finalNarrowTestDegree K K.b_eq i)) ∧
        Framework.UniformLittleO
          (fun i => {p : Point (n + 1) // p ∈ D.centers i ∧ p ∉ K.H.batch.badCenters i})
          (fun i p => (((D.targets i).filter (fun q => D.owner i q ∈
            exceptional_carriers D i (K.H.batch.bad K.finalPlateau i) p.val
              (badFamily i p.val))).card : ℝ))
          (fun i _ => (D.targets i).card) := by
  classical
  dsimp only
  let D := K.H.data K.finalPlateau
  have hfrom : DepthFromProfile S D := K.H.from_profile K.finalPlateau
  have hn : 1 ≤ n := by have := regime.dimension_ge_three; omega
  obtain ⟨C, hC, hregular⟩ := homogeneous_final_curve_regularity n hn
  obtain ⟨Cf, hCf, hcover⟩ := covering_envelope_curve_family (n + 1)
  let L := finalNarrowTestDegree K K.b₀
  let R := finalNarrowTestDegree K K.b_eq
  let curves := fun i p => envelopeDimensionPart (G i p).components 1
  have hδ : ∀ᶠ i in atTop, 0 ≤ F.delta i ∧ F.delta i ≤ 1 := by
    filter_upwards [F.delta_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with i hi
    exact ⟨(F.delta_pos i).le, hi.le⟩
  have hinputs : ∀ᶠ i in atTop, ∀ p ∈ D.centers i, p ∉ K.H.batch.badCenters i →
      ProjectiveFamily.IsPure (curves i p) 1 ∧ 1 ≤ L i ∧
      TrackA.FromProjectiveLists (curves i p) (L i) ∧ C * L i ≤ R i ∧
      (ProjectiveFamily.degree (curves i p) : ℝ) ≤
        Cf * F.delta i * (regime.N i / regime.A i) ∧
      (L i : ℝ) / (R i : ℝ) ≤
        4 * Real.exp (-(K.b_eq - K.b₀) * D.s i) := by
    filter_upwards [final_narrow_regularization_degrees K C] with i hi
    intro p hp _hgood
    have hpImage : p ∈ (S.sequence.source i).pts.image TrackD.toC := by
      rw [← (hfrom.2.2.2 i).1]
      exact hp
    obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hpImage
    have hreal : realCenter p = r := by
      rw [← heq]
      ext k
      change ((r k : ℂ).re) = r k
      exact Complex.ofReal_re (r k)
    have hpP : realCenter p ∈ regime.P i := by
      rw [hreal]
      exact (S.sequence.base_good i).1.subset hr
    obtain ⟨hpure, hlists, hdegree⟩ := hcover
      (F.family i (realCenter p)) (F.directional i _ hpP) (L i) hi.1 (G i p)
    refine ⟨hpure, hi.1, hlists, hi.2.1, ?_, ?_⟩
    · calc
        _ ≤ Cf * (ProjectiveFamily.degree (F.family i (realCenter p)) : ℝ) := hdegree
        _ ≤ Cf * (F.delta i * regime.N i / regime.A i) :=
          mul_le_mul_of_nonneg_left (F.degree i _ hpP) hCf.le
        _ = _ := by ring
    · simpa only [hfrom.1] using hi.2.2
  obtain ⟨badFamily, E, g, hcert, hmass⟩ := hregular D K.final_index
    Cf 4 K.ε (K.b_eq - K.b₀) hCf (by norm_num) K.epsilon_gap
    (K.H.batch.bad K.finalPlateau) K.H.batch.badCenters
    (final_narrow_depth_lower K) F.delta hδ L R curves hinputs
  refine ⟨C, hC, badFamily, E, g, ?_, hmass⟩
  filter_upwards [hcert] with i hi
  exact fun p hp hgood => (hi p hp hgood).1

end
end DistinctDistances.SparseCones
