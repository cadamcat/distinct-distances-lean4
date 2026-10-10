import DistinctDistances.TrackD.Profiles.RegularityChosenCuts
import DistinctDistances.TrackD.Profiles.RegularityZero

namespace DistinctDistances.TrackD
open scoped BigOperators Classical
noncomputable section

/-- Sufficient chosen-input-margin form of pooled Jacobian regularity.
All thresholds precede the pool and any later testing point. -/
theorem prof_regularity_jacobian_with_margin (d : ℕ) (hd : 3 ≤ d) :
    ∀ θ > 0, ∀ ξ > 0, ∃ θ₁ > 0, ∃ η > 0, ∃ ρ₀ > 0,
      η ≤ ξ / 4 ∧ ∃ s₁ : ℝ,
      ∀ (P : Finset (Pt d)) (pl : Finset (Piece d)) (s ρ : ℝ) (t : Fin d → ℝ),
        ρ ≤ ρ₀ → PoolGood P θ₁ η 1 ρ pl s t → s₁ ≤ s →
        ∀ j : ℕ, j < d → ∀ b : ℝ, OnPlateau t j ξ b → 1 ≤ testDeg (cfgB P) s b →
          ∃ (F : Finset (Poly d)) (gph : Poly d),
            (∀ f ∈ F, (f.totalDegree : ℝ) ≤ testDeg (cfgB P) s b) ∧
            (gph.totalDegree : ℝ) ≤ testDeg (cfgB P) s b ∧
            (∀ Z, PoolCarrier pl j Z → ∀ f ∈ F, f ∈ Z.ideal) ∧
            (∀ y : Point d, MvPolynomial.eval y gph ≠ 0 →
              Module.finrank ℂ (jacKer F y) + j ≤ d) ∧
            ∀ X ∈ pl, ((X.pts.filter (fun x => ¬ JacRegularAt pl j F gph (toC x))).card : ℝ) ≤
              θ * X.pts.card := by
  intro θ hθ ξ hξ
  obtain ⟨θD, hθD, ρD, hρD, sD, hdegree⟩ := regularity_pool_degree_certificate d hd ξ hξ
  obtain ⟨θC, hθC, ηC, hηC, hηCxi, sC, hcuts⟩ :=
    prof_regularity_cuts_with_margin d hd (θ / 2) (by positivity) (ξ / 2)
      (by positivity) 1 le_rfl
  let γ : ℝ := ξ / 128
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨θB, hθB, hbez⟩ := prof_budget_bezout d hd γ hγ
  obtain ⟨θS, hθS, ξS, hξS, sS, hsum⟩ := prof_budget_sum d hd γ hγ
  obtain ⟨sE, hE⟩ := regularity_exp_threshold (ξ / 16) (θ / 2)
    (by positivity) (by positivity)
  let θ₁ : ℝ := min θD (min θC (min θB (min θS γ)))
  let η : ℝ := min ηC ξS
  let ρ₀ : ℝ := min ρD (ξ / 8)
  let s₁ : ℝ := max sD (max sC (max sS (max sE 1)))
  have hθ₁ : 0 < θ₁ := by dsimp [θ₁]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hρ₀ : 0 < ρ₀ := by dsimp [ρ₀]; positivity
  have hηC' : η ≤ ηC := min_le_left _ _
  have hηS : η ≤ ξS := min_le_right _ _
  have hηxi : η ≤ ξ / 4 := hηC'.trans (by linarith)
  have hθ₁D : θ₁ ≤ θD := min_le_left _ _
  have hθ₁C : θ₁ ≤ θC := (min_le_right _ _).trans (min_le_left _ _)
  have hθ₁B : θ₁ ≤ θB :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hθ₁S : θ₁ ≤ θS :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_left _ _)
  have hθ₁γ : θ₁ ≤ γ :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)
  refine ⟨θ₁, hθ₁, η, hη, ρ₀, hρ₀, hηxi, s₁, ?_⟩
  intro P pl s ρ t hρ hpl hs j hj b hb hT
  have hsD : sD ≤ s := (le_max_left _ _).trans hs
  have hsC : sC ≤ s := ((le_max_left _ _).trans (le_max_right _ _)).trans hs
  have hsS : sS ≤ s :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hs
  have hsE : sE ≤ s :=
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans hs
  have hs1 : 1 ≤ s :=
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans hs
  have hs0 : 0 ≤ s := by linarith
  have hB0 : 0 ≤ cfgB P := by unfold cfgB; positivity
  by_cases hnonempty : pl.Nonempty
  · by_cases hj0 : j = 0
    · subst j
      have hzero := regularity_jacobian_zero P pl θ₁ η 1 (testDeg (cfgB P) s b)
        hpl.pieces hT
      refine ⟨∅, 1, by simp, ?_, by simp, hzero.1, ?_⟩
      · simpa using (by linarith : (0 : ℝ) ≤ testDeg (cfgB P) s b)
      · intro X hX
        have hempty : X.pts.filter (fun x => ¬ JacRegularAt pl 0 ∅ 1 (toC x)) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          obtain ⟨hxX, hbad⟩ := Finset.mem_filter.mp hx
          exact hbad (hzero.2 X hX x hxX)
        rw [hempty]
        simp only [Finset.card_empty, Nat.cast_zero]
        positivity
    · have hplD := regularity_pool_tolerance_mono P pl θ₁ θD η 1 ρ s t hθ₁D hs0 hpl
      obtain ⟨bad, E, g, hbad, hdeg, hEdeg, hgdeg, hgspan, hproper, hunique, hInterior⟩ :=
        hdegree P pl s ρ η t (hρ.trans (min_le_left _ _)) hplD hsD hnonempty j
          (by omega) hj b hb hT
      have hpure := poolCarrierFamily_pure P pl θ₁ η 1 hpl.pieces j (by omega)
      have hbadPure : ∀ Z ∈ bad, Z.IsIrreducible := fun Z hZ => (hpure Z (hbad hZ)).1
      have hbadMass : ∀ X ∈ pl, ((X.pts.filter (fun x =>
          ∃ Z ∈ X.path.localCarriers j (toC x), Z ∈ bad)).card : ℝ) ≤
            (θ / 2) * X.pts.card := by
        intro X hX
        have hwidth := hpl.width X hX
        have hX0 : 0 ≤ X.width := by simpa [hwidth] using hs0
        have hXB := dprofiles2_pieceGood_mono P X hθ₁B hX0 (hpl.pieces X hX)
        have hXS := dprofiles2_pieceGood_mono P X hθ₁S hX0 (hpl.pieces X hX)
        have hXγ := dprofiles2_pieceGood_mono P X hθ₁γ hX0 (hpl.pieces X hX)
        have htimes := hsum P X η 1 hη hηS le_rfl hXS (by simpa [hwidth] using hsS)
        have hm := regularity_bad_mass P X j bad η (ξ / 8) γ γ (by omega) hX0 hB0
          hXγ (by simpa only [hwidth, neg_div] using hdeg X hX) hbadPure
          (abs_le.mp htimes).2 (fun A hA =>
            (hbez P X η 1 hXB hX0 j (by omega) A hA).2)
        have hexp : Real.exp ((γ + 2 * γ - ξ / 8) * X.width) ≤ θ / 2 := by
          apply (Real.exp_le_exp.mpr ?_).trans (hE X.width (by simpa [hwidth] using hsE))
          apply mul_le_mul_of_nonneg_right _ hX0
          dsimp [γ]
          linarith
        exact hm.trans (by
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left hexp
            (Nat.cast_nonneg X.pts.card))
      have htest : testDeg (cfgB P) s (b - ξ / 2) ≤ testDeg (cfgB P) s (b - ξ / 4) :=
        regularity_test_mono _ _ _ _ hB0 hs0 (by linarith)
      have htestOut : testDeg (cfgB P) s (b - ξ / 2) ≤ testDeg (cfgB P) s b :=
        regularity_test_mono _ _ _ _ hB0 hs0 (by linarith)
      have hcutMass : ∀ X ∈ pl, ((X.pts.filter (fun x =>
          ∃ Z ∈ X.path.localCarriers j (toC x),
            g ∉ Z.ideal ∧ MvPolynomial.eval (toC x) g = 0)).card : ℝ) ≤
            (θ / 2) * X.pts.card := by
        intro X hX
        have hwidth := hpl.width X hX
        have hXC := pieceGood_margin_mono P X θC η ηC 1 hηC'
          (dprofiles2_pieceGood_mono P X hθ₁C (by simpa [hwidth] using hs0) (hpl.pieces X hX))
        have hbX : OnPlateau X.path.time j (ξ / 2) (b - ξ / 4) := by
          intro i
          obtain ⟨hpre, hpost⟩ := hb i
          obtain ⟨hlo, hhi⟩ := abs_le.mp (hpl.close X hX i)
          have hρsmall : ρ ≤ ξ / 8 := hρ.trans (min_le_right _ _)
          constructor
          · intro hi
            have h := hpre hi
            linarith
          · intro hi
            have h := hpost hi
            linarith
        have hc := hcuts P X hXC (by simpa [hwidth] using hsC) j hj (b - ξ / 4) hbX
          (by simpa [hwidth] using hInterior.trans htest) (fun _ => g)
          (by intro Z; simpa [hwidth] using hgdeg.trans htest)
        simpa using hc
      have hcert := jacobian_pool_certificate P pl θ₁ η 1 hpl.pieces j (by omega)
        (testDeg (cfgB P) s b) E g bad
        (fun f hf => ⟨(hEdeg f hf).1, (hEdeg f hf).2.trans htestOut⟩)
        (hgdeg.trans htestOut) hgspan hproper hunique (θ / 2) (θ / 2) hbadMass hcutMass
      refine ⟨E.toFinset, g, hcert.1, hcert.2.1, hcert.2.2.1, hcert.2.2.2.1, ?_⟩
      simpa only [show θ / 2 + θ / 2 = θ by ring] using hcert.2.2.2.2
  · have hempty : pl = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    refine ⟨∅, 0, by simp, ?_, by simp, by simp, ?_⟩
    · simpa using (by linarith : (0 : ℝ) ≤ testDeg (cfgB P) s b)
    · simp [hempty]

end
end DistinctDistances.TrackD
