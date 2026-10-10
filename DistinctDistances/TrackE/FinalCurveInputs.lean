import DistinctDistances.TrackE.FinalNarrowRegularity
import DistinctDistances.TrackE.FinalMinorCuts

/-! Surviving final regular labels, sparse-cones.tex:908–928. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Every complete original covering curve lies in the whole covering envelope. -/
theorem covering_member_sub_envelope (C : ProjectiveFamily.Family d) (L : ℕ)
    (V : ProjectiveVariety d) (hV : V ∈ C) :
    V.Subvariety (coveringDirectionEnvelope C L) := by
  have hspec := (Bridges.projective_envelope d (ProjectiveFamily.locus C).points L).choose_spec
  have hpoints : V.points ⊆ (coveringDirectionEnvelope C L).points := by
    intro p hp
    rw [coveringDirectionEnvelope, hspec.1]
    change ∀ f ∈ Bridges.homogeneousEquations (ProjectiveFamily.locus C).points L,
      MvPolynomial.eval p.rep f = 0
    intro f hf
    change f.IsHomogeneous L ∧ _ at hf
    apply hf.2
    have hpC : p ∈ (ProjectiveFamily.locus C).points := by
      rw [ProjectiveFamily.points_locus]
      exact Set.mem_iUnion.mpr ⟨V, Set.mem_iUnion.mpr ⟨hV, hp⟩⟩
    exact ⟨p.rep_nonzero,
      by simpa only [Projectivization.mk_rep] using hpC⟩
  change (coveringDirectionEnvelope C L).ideal ≤ V.ideal
  rw [← V.vanishingIdeal_points,
    ← ProjectiveVariety.vanishingIdeal_points (coveringDirectionEnvelope C L)]
  apply MvPolynomial.vanishingIdeal_anti_mono
  rintro x ⟨hx, hxV⟩
  exact ⟨hx, hpoints hxV⟩

/-- Physical labels whose unchanged owner belongs to the later exceptional family. -/
def realExceptionalTargets {j : ℕ} (D : TrackA.SeparatedDepthData regime j)
    (i : ℕ) (bad : Finset (Point d × AffineVariety d)) (p : Point d)
    (Q : Finset (RPoint d)) (badFamily : ProjectiveFamily.Family d) : Finset (RPoint d) :=
  Q.filter fun q => D.owner i (TrackD.toC q) ∈ exceptional_carriers D i bad p badFamily

/-- Injective complexification bounds the physical exceptional count by the
original assigned target count. No projection injectivity is assumed. -/
theorem real_exceptional_targets_card_le {j : ℕ} (D : TrackA.SeparatedDepthData regime j)
    (i : ℕ) (bad : Finset (Point d × AffineVariety d)) (p : Point d)
    (Q : Finset (RPoint d)) (badFamily : ProjectiveFamily.Family d)
    (hQ : Q.image TrackD.toC ⊆ D.targets i) :
    ((realExceptionalTargets D i bad p Q badFamily).card : ℝ) ≤
      (((D.targets i).filter (fun q => D.owner i q ∈
        exceptional_carriers D i bad p badFamily)).card : ℝ) := by
  classical
  let A := realExceptionalTargets D i bad p Q badFamily
  let B := (D.targets i).filter (fun q => D.owner i q ∈
    exceptional_carriers D i bad p badFamily)
  have himage : A.image TrackD.toC ⊆ B := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    have hqA : q ∈ Q ∧ D.owner i (TrackD.toC q) ∈
        exceptional_carriers D i bad p badFamily := by
      simpa only [A, realExceptionalTargets, Finset.mem_filter] using hq
    change TrackD.toC q ∈ (D.targets i).filter _
    exact Finset.mem_filter.mpr
      ⟨hQ (Finset.mem_image.mpr ⟨q, hqA.1, rfl⟩), hqA.2⟩
  have hcard : A.card ≤ B.card := by
    calc
      A.card = (A.image TrackD.toC).card := by
        symm
        exact Finset.card_image_of_injective _ profile_toC_injective
      _ ≤ B.card := Finset.card_le_card himage
  exact_mod_cast hcard

/-- Four later removals with a strict total count gap leave an actual physical label. -/
theorem four_removals_leave_label (Q B₁ B₂ B₃ B₄ : Finset (RPoint d))
    (hgap : (B₁.card : ℝ) + B₂.card + B₃.card + B₄.card < Q.card) :
    ∃ q ∈ Q, q ∉ B₁ ∧ q ∉ B₂ ∧ q ∉ B₃ ∧ q ∉ B₄ := by
  classical
  by_contra h
  have hsub : Q ⊆ B₁ ∪ B₂ ∪ B₃ ∪ B₄ := by
    intro q hq
    by_contra hu
    apply h
    exact ⟨q, hq, by simpa only [Finset.mem_union, not_or, and_assoc] using hu⟩
  have hcard : Q.card ≤ B₁.card + B₂.card + B₃.card + B₄.card := by
    calc
      Q.card ≤ (B₁ ∪ B₂ ∪ B₃ ∪ B₄).card := Finset.card_le_card hsub
      _ ≤ (B₁ ∪ B₂ ∪ B₃).card + B₄.card := Finset.card_union_le _ _
      _ ≤ ((B₁ ∪ B₂).card + B₃.card) + B₄.card := by
        exact Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (B₁.card + B₂.card + B₃.card) + B₄.card := by
        exact Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
  have hcardR : (Q.card : ℝ) ≤ (B₁.card : ℝ) + B₂.card + B₃.card + B₄.card := by
    exact_mod_cast hcard
  linarith

end
end DistinctDistances.SparseCones
