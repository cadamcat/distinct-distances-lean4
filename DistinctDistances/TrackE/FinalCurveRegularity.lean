import DistinctDistances.TrackE.RegularityBudget
import DistinctDistances.TrackE.FinalCurveMass
import DistinctDistances.TrackE.AssignedMass

/-!
The regularity and depth comparison on the final curve plateau
(`sc:u-final-curve.regularity`, sparse-cones.tex:870–906).
The incidence and center deletions are inputs fixed before the envelope families.
One regularity constant works for every index and center; the chosen certificates
retain that uniform constant.
-/

namespace DistinctDistances.SparseCones

open Filter
open scoped Topology

noncomputable section

open Classical in
/-- Apply whole-family projective regularity to every typical-center envelope,
then discard its exceptional components using the earlier adaptive depth bound.
The equations and minor tests are retained for the final component identification.
The testing-degree ratio and family degree bound are hypotheses to be supplied
by the envelope and the two reserved interior times. -/
theorem final_curve_regularity (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℕ, 0 < C ∧
      ∀ {j : ℕ} {regime : Regime (n + 1)}
        (D : TrackA.SeparatedDepthData regime j) (hlast : j + 1 = n + 1)
        (Cf Cr ε η : ℝ), 0 < Cf → 0 < Cr → ε < η →
      ∀ (bad : ℕ → Finset (Point (n + 1) × AffineVariety (n + 1)))
        (badCenters : ℕ → Finset (Point (n + 1))),
        (∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
          ∀ p ∈ D.centers i, p ∉ badCenters i →
          ∀ J : AffineFamily.Family (n + 1), J ⊆ D.retained i (bad i) p →
            ρ * ((D.targets i).card : ℝ) ≤ D.submass i J →
            D.degreeBudget i / D.narrowRate i * Real.exp (-ε * D.s i) ≤
              (ProjectiveFamily.degree (TrackA.projectedFamily p J) : ℝ)) →
      ∀ (δ : ℕ → ℝ), (∀ᶠ i in atTop, 0 ≤ δ i ∧ δ i ≤ 1) →
      ∀ (L T : ℕ → ℕ) (F : ℕ → Point (n + 1) → ProjectiveFamily.Family (n + 1)),
        (∀ᶠ i in atTop, ∀ p ∈ D.centers i, p ∉ badCenters i →
          ProjectiveFamily.IsPure (F i p) 1 ∧ 1 ≤ L i ∧
          TrackA.FromProjectiveLists (F i p) (L i) ∧ C * L i ≤ T i ∧
          (ProjectiveFamily.degree (F i p) : ℝ) ≤ Cf * δ i * (regime.N i / regime.A i) ∧
          (L i : ℝ) / (T i : ℝ) ≤ Cr * Real.exp (-η * D.s i)) →
      ∃ (badFamily : ℕ → Point (n + 1) → ProjectiveFamily.Family (n + 1))
        (E : ℕ → Point (n + 1) → List (Poly (n + 1)))
        (g : ℕ → Point (n + 1) → Poly (n + 1)),
        (∀ᶠ i in atTop, ∀ p ∈ D.centers i, p ∉ badCenters i →
          CurveRegularityCertificate (F i p) (badFamily i p) (E i p) (g i p) C (T i) ∧
          (ProjectiveFamily.degree (badFamily i p) : ℝ) ≤
            ((C : ℝ) * Cf * Cr) * δ i * (regime.N i / regime.A i) *
              Real.exp (-η * D.s i)) ∧
        Framework.UniformLittleO
          (fun i => {p : Point (n + 1) // p ∈ D.centers i ∧ p ∉ badCenters i})
          (fun i p => (((D.targets i).filter (fun q => D.owner i q ∈
            exceptional_carriers D i (bad i) p.val (badFamily i p.val))).card : ℝ))
          (fun i _ => (D.targets i).card) := by
  classical
  obtain ⟨C, hC, hregular⟩ := curve_regularity_budget n hn
  refine ⟨C, hC, ?_⟩
  intro j regime D hlast Cf Cr ε η hCf hCr hgap bad badCenters hlower δ hδ L T F hF
  let Q := fun i p =>
    ProjectiveFamily.IsPure (F i p) 1 ∧ 1 ≤ L i ∧
    TrackA.FromProjectiveLists (F i p) (L i) ∧ C * L i ≤ T i ∧
    (ProjectiveFamily.degree (F i p) : ℝ) ≤ Cf * δ i * (regime.N i / regime.A i) ∧
    (L i : ℝ) / (T i : ℝ) ≤ Cr * Real.exp (-η * D.s i) ∧ 0 ≤ δ i
  have hchoices : ∀ i p,
      ∃ (badF : ProjectiveFamily.Family (n + 1)) (E : List (Poly (n + 1))) (g : Poly (n + 1)),
        Q i p → CurveRegularityCertificate (F i p) badF E g C (T i) ∧
          (ProjectiveFamily.degree badF : ℝ) ≤
            ((C : ℝ) * Cf * Cr) * δ i * (regime.N i / regime.A i) *
              Real.exp (-η * D.s i) := by
    intro i p
    by_cases hQ : Q i p
    · obtain ⟨hpure, hL, hlists, hT, hdegree, hratio, hδ₀⟩ := hQ
      obtain ⟨badF, E, g, hcert, hbound⟩ :=
        hregular (F i p) (L i) (T i) hpure hL hlists hT
          Cf Cr (δ i) (regime.N i / regime.A i) η (D.s i)
          hCf hCr hδ₀ (div_pos (regime.N_pos i) (regime.A_pos i)).le hdegree hratio
      exact ⟨badF, E, g, fun _ => ⟨hcert, hbound⟩⟩
    · exact ⟨∅, [], 0, fun h => (hQ h).elim⟩
  choose badFamily E g hchoice using hchoices
  have hcert : ∀ᶠ i in atTop, ∀ p ∈ D.centers i, p ∉ badCenters i →
      CurveRegularityCertificate (F i p) (badFamily i p) (E i p) (g i p) C (T i) ∧
      (ProjectiveFamily.degree (badFamily i p) : ℝ) ≤
        ((C : ℝ) * Cf * Cr) * δ i * (regime.N i / regime.A i) * Real.exp (-η * D.s i) := by
    filter_upwards [hF, hδ] with i hi hδi
    intro p hp hgood
    obtain ⟨hpure, hL, hlists, hT, hdegree, hratio⟩ := hi p hp hgood
    exact hchoice i p ⟨hpure, hL, hlists, hT, hdegree, hratio, hδi.1⟩
  refine ⟨badFamily, E, g, hcert, ?_⟩
  have hupper : ∀ᶠ i in atTop, ∀ p ∈ D.centers i, p ∉ badCenters i →
      (ProjectiveFamily.degree (badFamily i p) : ℝ) ≤
        ((C : ℝ) * Cf * Cr) * δ i * (regime.N i / regime.A i) * Real.exp (-η * D.s i) := by
    filter_upwards [hcert] with i hi
    exact fun p hp hgood => (hi p hp hgood).2
  have hmass := final_narrow_exceptional_mass D hlast ((C : ℝ) * Cf * Cr) ε η
    (by positivity) hgap bad badCenters hlower δ hδ badFamily hupper
  simpa only [submass_eq_assigned_card] using hmass

end

end DistinctDistances.SparseCones
