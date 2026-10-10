import DistinctDistances.TrackE.ProjectedMass
import DistinctDistances.TrackE.NarrowScale
import DistinctDistances.TrackA.Depth

/-!
# Adaptive exceptional families after actual-center deletions

`sc:u-final-curve.regularity.mass`, sparse-cones.tex:870–906.
The bad incidence set and bad centers are fixed before the exceptional projective
family. The lower bound is exactly the last clause of A's `ProjectedDegreeConclusion`.
Later family choices and every later positive density remain inside its uniform quantifiers.
-/

namespace DistinctDistances.SparseCones

open Filter
open scoped Topology BigOperators

noncomputable section

open Classical in
def exceptional_carriers {d j : ℕ} {regime : Regime d}
    (D : TrackA.SeparatedDepthData regime j) (i : ℕ)
    (bad : Finset (Point d × AffineVariety d)) (p : Point d)
    (F : ProjectiveFamily.Family d) : AffineFamily.Family d :=
  (D.retained i bad p).filter fun Y => radialImage p Y ∈ F

open Classical in
/-- The actual-center projected-degree bound controls every adaptive exceptional family
with a strictly faster degree decay. In applications `R = D.narrowRate`, and the final
plateau identity converts the common scale `D.degreeBudget / R` to `N/A`. -/
theorem final_curve_exceptional_mass {d j : ℕ} {regime : Regime d}
    (D : TrackA.SeparatedDepthData regime j) (R : ℕ → ℝ) (C ε η : ℝ)
    (hC : 0 < C) (hgap : ε < η)
    (hscale : ∀ᶠ i in atTop, 0 < D.degreeBudget i / R i)
    (bad : ℕ → Finset (Point d × AffineVariety d))
    (badCenters : ℕ → Finset (Point d))
    (hlower : ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ p ∈ D.centers i, p ∉ badCenters i →
      ∀ J : AffineFamily.Family d, J ⊆ D.retained i (bad i) p →
        ρ * ((D.targets i).card : ℝ) ≤ D.submass i J →
        D.degreeBudget i / R i * Real.exp (-ε * D.s i) ≤
          (ProjectiveFamily.degree (TrackA.projectedFamily p J) : ℝ)) :
    ∀ F : ℕ → Point d → ProjectiveFamily.Family d,
      (∀ᶠ i in atTop, ∀ p ∈ D.centers i, p ∉ badCenters i →
        (ProjectiveFamily.degree (F i p) : ℝ) ≤
          C * (D.degreeBudget i / R i) * Real.exp (-η * D.s i)) →
      Framework.UniformLittleO
        (fun i => {p : Point d // p ∈ D.centers i ∧ p ∉ badCenters i})
        (fun i p => D.submass i (exceptional_carriers D i (bad i) p.val (F i p.val)))
        (fun i _ => (D.targets i).card) := by
  classical
  intro F hupper
  let I := fun i => {p : Point d // p ∈ D.centers i ∧ p ∉ badCenters i}
  let J := fun i (p : I i) => exceptional_carriers D i (bad i) p.val (F i p.val)
  apply uniform_small_mass_of_degree_gap I
    (fun i p => D.submass i (J i p)) (fun i _ => (D.targets i).card)
    (fun i p => (ProjectiveFamily.degree (TrackA.projectedFamily p.val (J i p)) : ℝ))
    (fun i => D.degreeBudget i / R i) D.s C ε η D.s_grows hC hgap hscale
  · intro i p
    unfold TrackA.SeparatedDepthData.submass
    exact Finset.sum_nonneg fun Y _ => Nat.cast_nonneg _
  · intro i p
    exact Nat.cast_nonneg _
  · intro ρ hρ
    filter_upwards [hlower ρ hρ] with i hi
    intro p hmass
    exact hi p.val p.property.1 p.property.2 (J i p) (Finset.filter_subset _ _) hmass
  · filter_upwards [hupper] with i hi
    intro p
    have hsubset : TrackA.projectedFamily p.val (J i p) ⊆ F i p.val := by
      intro γ hγ
      change γ ∈ (J i p).image (radialImage p.val) at hγ
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hγ
      exact (Finset.mem_filter.mp hY).2
    have hdegree : (ProjectiveFamily.degree (TrackA.projectedFamily p.val (J i p)) : ℝ) ≤
        (ProjectiveFamily.degree (F i p.val) : ℝ) := by
      exact_mod_cast projective_family_degree_mono _ _ hsubset
    exact hdegree.trans (hi p.val p.property.1 p.property.2)

open Classical in
/-- The final-plateau form consumed at `sparse-cones.tex:880–906`. Only boundedness
`δ ≤ 1` is used: the fixed gap `η-ε` makes the conclusion independent of how slowly δ tends to
zero. The actual-center deletions and their lower bound precede the adaptive family `F`. -/
theorem final_narrow_exceptional_mass {d j : ℕ} {regime : Regime d}
    (D : TrackA.SeparatedDepthData regime j) (hlast : j + 1 = d) (C ε η : ℝ)
    (hC : 0 < C) (hgap : ε < η)
    (bad : ℕ → Finset (Point d × AffineVariety d))
    (badCenters : ℕ → Finset (Point d))
    (hlower : ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ p ∈ D.centers i, p ∉ badCenters i →
      ∀ J : AffineFamily.Family d, J ⊆ D.retained i (bad i) p →
        ρ * ((D.targets i).card : ℝ) ≤ D.submass i J →
        D.degreeBudget i / D.narrowRate i * Real.exp (-ε * D.s i) ≤
          (ProjectiveFamily.degree (TrackA.projectedFamily p J) : ℝ))
    (δ : ℕ → ℝ) (hδ : ∀ᶠ i in atTop, 0 ≤ δ i ∧ δ i ≤ 1)
    (F : ℕ → Point d → ProjectiveFamily.Family d)
    (hupper : ∀ᶠ i in atTop, ∀ p ∈ D.centers i, p ∉ badCenters i →
      (ProjectiveFamily.degree (F i p) : ℝ) ≤
        C * δ i * (regime.N i / regime.A i) * Real.exp (-η * D.s i)) :
    Framework.UniformLittleO
      (fun i => {p : Point d // p ∈ D.centers i ∧ p ∉ badCenters i})
      (fun i p => D.submass i (exceptional_carriers D i (bad i) p.val (F i p.val)))
      (fun i _ => (D.targets i).card) := by
  have hscale : ∀ᶠ i in atTop, 0 < D.degreeBudget i / D.narrowRate i :=
    Eventually.of_forall fun i => by
      rw [final_narrow_scale D hlast i]
      exact div_pos (regime.N_pos i) (regime.A_pos i)
  apply final_curve_exceptional_mass D D.narrowRate C ε η hC hgap hscale bad badCenters hlower F
  filter_upwards [hupper, hδ] with i hi hδi
  intro p hp hpGood
  rw [final_narrow_scale D hlast i]
  calc
    _ ≤ C * δ i * (regime.N i / regime.A i) * Real.exp (-η * D.s i) := hi p hp hpGood
    _ ≤ C * (regime.N i / regime.A i) * Real.exp (-η * D.s i) := by
      have ha : 0 ≤ regime.N i / regime.A i :=
        (div_pos (regime.N_pos i) (regime.A_pos i)).le
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_right _ ha
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hδi.2 hC.le

end

end DistinctDistances.SparseCones
