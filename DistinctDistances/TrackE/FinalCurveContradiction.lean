import DistinctDistances.TrackE.FinalCurveSurvivor

/-! The separated narrow final-curve contradiction, sparse-cones.tex:795–928. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section

/-- sc:u-final-curve: choose one complete whole-family envelope sequence and
common homogeneous certificates, then contradict the original global terminal
exclusion at a surviving regular covered label. -/
theorem final_narrow_profile_contradiction {n : ℕ} {regime : Regime (n + 1)}
    {F : ConeCoverageSequence regime} (T : SelectedProfileSequence F)
    (S : LimitingSeparatedProfile regime) [Fintype (ProfilePlateau S)]
    (hsource : ∀ i, T.sources i = {S.sequence.source i})
    (htarget : ∀ i, T.targets i = {S.sequence.target i}) : False := by
  classical
  obtain ⟨K⟩ := selected_final_narrow_batch T S hsource htarget
  let G : ∀ i (p : RPoint (n + 1)), CoveringEnvelopeComponents (F.family i p)
      (finalNarrowTestDegree K K.b₀ i) :=
    fun i p => Classical.choice (exists_covering_envelope_components
      regime.dimension_ge_three (F.family i p) (finalNarrowTestDegree K K.b₀ i))
  let Gcx : ∀ i p, CoveringEnvelopeComponents (F.family i (realCenter p))
      (finalNarrowTestDegree K K.b₀ i) := fun i p => G i (realCenter p)
  obtain ⟨Creg, _hCreg, badFamily, E, g, hcert, hmass⟩ :=
    selected_final_narrow_regularity K Gcx
  let D := K.H.data K.finalPlateau
  have hfrom := K.H.from_profile K.finalPlateau
  have hphysical : ∀ᶠ i in atTop, ∀ p ∈ (S.sequence.source i).pts,
      TrackD.toC p ∉ K.H.batch.badCenters i →
      HomogeneousCurveRegularityCertificate (envelopeDimensionPart (G i p).components 1)
        (badFamily i (TrackD.toC p)) (E i (TrackD.toC p)) (g i (TrackD.toC p))
        Creg (finalNarrowTestDegree K K.b_eq i) := by
    filter_upwards [hcert] with i hi
    intro p hp hgood
    have hpD : TrackD.toC p ∈ D.centers i := by
      rw [(hfrom.2.2.2 i).1]
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hreal : realCenter (TrackD.toC p) = p := by
      ext k
      change ((p k : ℂ).re) = p k
      exact Complex.ofReal_re (p k)
    have hcomponents : (Gcx i (TrackD.toC p)).components = (G i p).components := by
      change (G i (realCenter (TrackD.toC p))).components = (G i p).components
      exact congrArg (fun r : RPoint (n + 1) => (G i r).components) hreal
    have hc := hi (TrackD.toC p) hpD hgood
    rw [hcomponents] at hc
    exact hc
  obtain ⟨i, p, _hpP, q, hedge, hproject⟩ :=
    (final_narrow_regular_row_survives T S hsource htarget K G badFamily E g
      Creg hphysical hmass).exists
  have hlast : K.finalPlateau.val.val = n + 1 - 1 := by
    have := K.final_index
    omega
  exact K.H.terminal_excluded K.finalPlateau hlast i p q
    (Finset.mem_filter.mp hedge).1 hproject

/-- Restore the arbitrary ambient-dimension interface consumed by the final
selected-profile alternatives; the regime already supplies d≥3. -/
theorem separated_profile_contradiction {d : ℕ} {regime : Regime d}
    {F : ConeCoverageSequence regime} (T : SelectedProfileSequence F)
    (S : LimitingSeparatedProfile regime) [Fintype (ProfilePlateau S)]
    (hsource : ∀ i, T.sources i = {S.sequence.source i})
    (htarget : ∀ i, T.targets i = {S.sequence.target i}) : False := by
  cases d with
  | zero =>
      have hd := regime.dimension_ge_three
      omega
  | succ n =>
      exact final_narrow_profile_contradiction T S hsource htarget

end
end DistinctDistances.SparseCones
