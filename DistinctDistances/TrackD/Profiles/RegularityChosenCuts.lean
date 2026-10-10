import DistinctDistances.TrackD.Profiles.RegularityDegreePackages
import DistinctDistances.TrackD.Profiles.RegularityMass

namespace DistinctDistances.TrackD
open scoped BigOperators Classical
noncomputable section

/-- A sufficient capture-margin interface. The margin is chosen before the
sample and before the individual polynomial tests. The original frozen
`prof_regularity_cuts` is unchanged. -/
theorem prof_regularity_cuts_with_margin (d : ℕ) (hd : 3 ≤ d) :
    ∀ θ > 0, ∀ ξ > 0, ∀ K ≥ 1, ∃ θ₁ > 0, ∃ η > 0,
      η ≤ ξ / 2 ∧ ∃ s₁ : ℝ,
      ∀ (P : Finset (Pt d)) (X : Piece d), PieceGood P θ₁ η 1 X → s₁ ≤ X.width →
        ∀ j : ℕ, j < d → ∀ b : ℝ, OnPlateau X.path.time j ξ b →
          1 ≤ testDeg (cfgB P) X.width b →
          ∀ f : AffineVariety d → Poly d,
            (∀ Z, ((f Z).totalDegree : ℝ) ≤ K * testDeg (cfgB P) X.width b) →
            ((X.pts.filter (fun x => ∃ Z ∈ X.path.localCarriers j (toC x),
                f Z ∉ Z.ideal ∧ MvPolynomial.eval (toC x) (f Z) = 0)).card : ℝ) ≤
              θ * X.pts.card := by
  intro θ hθ ξ hξ K hK
  obtain ⟨θD, hθD, sD, hpool⟩ := regularity_cut_pooling d hd ξ hξ K hK
  let γ : ℝ := ξ / 128
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨θB, hθB, hbez⟩ := prof_budget_bezout d hd γ hγ
  obtain ⟨θS, hθS, ξS, hξS, sS, hsum⟩ := prof_budget_sum d hd γ hγ
  obtain ⟨sE, hE⟩ := regularity_exp_threshold (ξ / 16) (θ / 2)
    (by positivity) (by positivity)
  let θ₁ : ℝ := min θD (min θB (min θS (min γ (θ / 2))))
  let η : ℝ := min ξS (ξ / 2)
  let s₁ : ℝ := max sD (max sS (max sE 1))
  have hθ₁ : 0 < θ₁ := by dsimp [θ₁]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hηS : η ≤ ξS := min_le_left _ _
  have hηξ : η ≤ ξ / 2 := min_le_right _ _
  have hθ₁D : θ₁ ≤ θD := min_le_left _ _
  have hθ₁B : θ₁ ≤ θB := (min_le_right _ _).trans (min_le_left _ _)
  have hθ₁S : θ₁ ≤ θS :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hθ₁γ : θ₁ ≤ γ :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_left _ _)
  have hθ₁θ : θ₁ ≤ θ / 2 :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)
  refine ⟨θ₁, hθ₁, η, hη, hηξ, s₁, ?_⟩
  intro P X hX hs j hj b hb hT f hf
  have hsD : sD ≤ X.width := (le_max_left _ _).trans hs
  have hsS : sS ≤ X.width := ((le_max_left _ _).trans (le_max_right _ _)).trans hs
  have hsE : sE ≤ X.width :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hs
  have hs1 : 1 ≤ X.width :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hs
  have hs0 : 0 ≤ X.width := by linarith
  have hXD := dprofiles2_pieceGood_mono P X hθ₁D hs0 hX
  obtain ⟨bad, g, hbad, hdeg, hgdeg, hzero, hproper⟩ :=
    hpool P X η hXD hsD j hj b hb hT f hf
  have hXB := dprofiles2_pieceGood_mono P X hθ₁B hs0 hX
  have hXS := dprofiles2_pieceGood_mono P X hθ₁S hs0 hX
  have hXγ := dprofiles2_pieceGood_mono P X hθ₁γ hs0 hX
  have htimes := hsum P X η 1 hη hηS le_rfl hXS hsS
  have hpure : ∀ Z ∈ bad, Z.IsIrreducible := by
    intro Z hZ
    exact ((mem_pieceCarrierFamily X j Z).mp (hbad hZ)).1.isPrime
  have hB0 : 0 ≤ cfgB P := by unfold cfgB; positivity
  have hm := regularity_bad_mass P X j bad η (ξ / 8) γ γ (by omega) hs0 hB0
    hXγ (by simpa only [neg_div] using hdeg) hpure (abs_le.mp htimes).2 (fun A hA =>
      (hbez P X η 1 hXB hs0 j (by omega) A hA).2)
  have hexp : Real.exp ((γ + 2 * γ - ξ / 8) * X.width) ≤ θ / 2 := by
    apply (Real.exp_le_exp.mpr ?_).trans (hE X.width hsE)
    apply mul_le_mul_of_nonneg_right _ hs0
    dsimp [γ]
    linarith
  have hbadMass : ((X.pts.filter (fun x =>
      ∃ Z ∈ X.path.localCarriers j (toC x), Z ∈ bad)).card : ℝ) ≤
        (θ / 2) * X.pts.card := by
    calc
      _ ≤ X.pts.card * Real.exp ((γ + 2 * γ - ξ / 8) * X.width) := hm
      _ ≤ X.pts.card * (θ / 2) := mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _)
      _ = _ := mul_comm _ _
  have hb' : OnPlateau X.path.time j η (b + ξ / 4) := by
    intro i
    obtain ⟨hpre, hpost⟩ := hb i
    constructor
    · intro hi
      have h := hpre hi
      linarith
    · intro hi
      have h := hpost hi
      linarith
  have hT' : 1 ≤ testDeg (cfgB P) X.width (b + ξ / 4) := by
    apply hT.trans
    unfold testDeg
    gcongr
    linarith
  have hcap := hX.noCapture j hj (b + ξ / 4) hb' hT' g (by simpa using hgdeg)
  have hcap' : ((X.path.captured j X.pts g).card : ℝ) ≤ (θ / 2) * X.pts.card :=
    hcap.trans (mul_le_mul_of_nonneg_right hθ₁θ (Nat.cast_nonneg _))
  have hcount := regularity_cut_count X j f g bad (θ / 2) (θ / 2)
    hzero hproper hbadMass hcap'
  simpa only [show θ / 2 + θ / 2 = θ by ring] using hcount

end
end DistinctDistances.TrackD
