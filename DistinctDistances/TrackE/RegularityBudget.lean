import DistinctDistances.TrackA.Regularity
import DistinctDistances.TrackE.ProjectedMass

/-! The exceptional-degree estimate on the final curve plateau (`sparse-cones.tex:870–887`). -/

namespace DistinctDistances.SparseCones

noncomputable section

open scoped Classical

/-- The part of A's projective regularity certificate consumed by the final endpoint.
Equations describe the whole family; the minor test is nonzero on every retained component. -/
def CurveRegularityCertificate {n : ℕ} (F bad : ProjectiveFamily.Family (n + 1))
    (E : List (Poly (n + 1))) (g : Poly (n + 1)) (C D : ℕ) : Prop :=
  bad ⊆ F ∧
  (∀ f ∈ E, f ∈ (ProjectiveFamily.locus F).ideal ∧ f.IsHomogeneous D) ∧
  g.totalDegree ≤ C * D ∧
  (∀ V ∈ F, V ∉ bad → g ∉ V.ideal) ∧
  ∀ p ∈ (ProjectiveFamily.locus F).points, MvPolynomial.eval p.rep g ≠ 0 →
    TrackA.SameGermAt (TrackA.equationLocus E) (ProjectiveFamily.locus F).affineCone p.rep ∧
    (TrackA.equationLocus E).IsSmoothAt p.rep ∧
    (TrackA.equationLocus E).localDimension p.rep = 2 ∧
    ∀ V ∈ F, ∀ W ∈ F, p ∈ V → p ∈ W → V = W

/-- The regularity constant is chosen before any center or envelope. A testing-degree
ratio `L/D ≤ Cr exp(-ηs)` converts A's exact exceptional-degree bound into the strict
exponent estimate used by `final_narrow_exceptional_mass`. -/
theorem curve_regularity_budget (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℕ, 0 < C ∧ ∀ (F : ProjectiveFamily.Family (n + 1)) (L D : ℕ),
      ProjectiveFamily.IsPure F 1 → 1 ≤ L → TrackA.FromProjectiveLists F L → C * L ≤ D →
      ∀ (Cf Cr δ a η s : ℝ), 0 < Cf → 0 < Cr → 0 ≤ δ → 0 ≤ a →
      (ProjectiveFamily.degree F : ℝ) ≤ Cf * δ * a →
      (L : ℝ) / (D : ℝ) ≤ Cr * Real.exp (-η * s) →
      ∃ (bad : ProjectiveFamily.Family (n + 1)) (E : List (Poly (n + 1))) (g : Poly (n + 1)),
        CurveRegularityCertificate F bad E g C D ∧
        (ProjectiveFamily.degree bad : ℝ) ≤
          ((C : ℝ) * Cf * Cr) * δ * a * Real.exp (-η * s) := by
  obtain ⟨C, hC, hregular⟩ := TrackA.poly_regularity_projective n
  refine ⟨C, hC, ?_⟩
  intro F L D hF hL hLists hD Cf Cr δ a η s hCf hCr hδ ha hdegree hratio
  obtain ⟨bad, E, g, hbad, hdegBad, hE, hgDeg, hgHom, hgSpan, hgGood, hGerm⟩ :=
    hregular F 1 L D hn hF hL hLists hD
  refine ⟨bad, E, g, ⟨hbad, hE, hgDeg, hgGood, ?_⟩, ?_⟩
  · intro p hp hgp
    simpa only [Nat.cast_ofNat, Nat.reduceAdd] using hGerm p hp hgp
  · have hdeg : (ProjectiveFamily.degree bad : ℝ) ≤
        (C : ℝ) * (ProjectiveFamily.degree F : ℝ) * (L : ℝ) / (D : ℝ) := by
      exact_mod_cast hdegBad
    have hC₀ : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    have hratio₀ : 0 ≤ (L : ℝ) / (D : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    calc
      _ ≤ (C : ℝ) * (ProjectiveFamily.degree F : ℝ) * ((L : ℝ) / (D : ℝ)) := by
        simpa only [mul_div_assoc] using hdeg
      _ ≤ (C : ℝ) * (Cf * δ * a) * ((L : ℝ) / (D : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdegree hC₀) hratio₀
      _ ≤ (C : ℝ) * (Cf * δ * a) * (Cr * Real.exp (-η * s)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring

end

end DistinctDistances.SparseCones
