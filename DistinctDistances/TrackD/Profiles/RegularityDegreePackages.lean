import DistinctDistances.TrackD.Profiles.Budget
import DistinctDistances.TrackD.Profiles.PoolFamilies
import DistinctDistances.TrackD.Profiles.MDMarginAux

namespace DistinctDistances.TrackD
open scoped BigOperators Classical
noncomputable section

set_option maxHeartbeats 1000000 in
/-- `profiles.tex:370–379`: the degree part of individual-cut pooling.
No bound on the full recorded product is asserted here. -/
theorem regularity_cut_pooling (d : ℕ) (hd : 3 ≤ d) :
    ∀ ξ > 0, ∀ K ≥ 1, ∃ θ₁ > 0, ∃ s₁ : ℝ,
      ∀ (P : Finset (Pt d)) (X : Piece d) (η : ℝ),
        PieceGood P θ₁ η 1 X → s₁ ≤ X.width →
        ∀ j : ℕ, j < d → ∀ b : ℝ, OnPlateau X.path.time j ξ b →
          1 ≤ testDeg (cfgB P) X.width b →
          ∀ f : AffineVariety d → Poly d,
            (∀ Z, ((f Z).totalDegree : ℝ) ≤ K * testDeg (cfgB P) X.width b) →
            ∃ (bad : AffineFamily.Family d) (g : Poly d),
              bad ⊆ pieceCarrierFamily X j ∧
              (AffineFamily.degree bad : ℝ) ≤
                eScale (cfgB P) X.width X.path.time j * Real.exp (-ξ / 8 * X.width) ∧
              (g.totalDegree : ℝ) ≤ testDeg (cfgB P) X.width (b + ξ / 4) ∧
              (∀ x ∈ X.pts,
                (∃ Z ∈ X.path.localCarriers j (toC x),
                  f Z ∉ Z.ideal ∧ MvPolynomial.eval (toC x) (f Z) = 0) →
                MvPolynomial.eval (toC x) g = 0) ∧
              ∀ Z ∈ pieceCarrierFamily X j, Z ∉ bad → g ∉ Z.ideal := by
  intro ξ hξ K hK
  obtain ⟨C, hCpos, hpool⟩ := TrackA.poly_pooling d
  have hxi16 : 0 < ξ / 16 := by positivity
  obtain ⟨θB, hθB, hbez⟩ := prof_budget_bezout d hd (ξ / 16) hxi16
  let θ₁ : ℝ := min θB (ξ / 2)
  have hθ₁ : 0 < θ₁ := by dsimp [θ₁]; positivity
  have hθ₁B : θ₁ ≤ θB := min_le_left _ _
  have hθ₁ξ : θ₁ ≤ ξ / 2 := min_le_right _ _
  have hCposR : 0 < (C : ℝ) := by exact_mod_cast hCpos
  have hK2pos : 0 < (K + 2 : ℝ) := by linarith
  have hCp : 0 < (2 * (C : ℝ) * (K + 2) : ℝ) := by positivity
  obtain ⟨sE, hsE⟩ := md_exp_ge (ξ / 16) (2 * (C : ℝ) * (K + 2))
    (by positivity) hCp
  let s₁ : ℝ := max sE 0
  refine ⟨θ₁, hθ₁, s₁, ?_⟩
  intro P X η hX hs j hj b hb hT f hf
  have hs0 : 0 ≤ X.width := le_trans (le_max_right _ _) hs
  have hsE' : sE ≤ X.width := le_trans (le_max_left _ _) hs
  have hB0 : 0 ≤ cfgB P := md_cfgB_nonneg P
  have hXB : PieceGood P θB η 1 X :=
    dprofiles2_pieceGood_mono P X hθ₁B hs0 hX
  -- Reduce to positive base; zero base contradicts the testing-degree hypothesis.
  by_cases hBpos : 0 < cfgB P
  · -- Setup for the positive-base case.
    have hjLe : j ≤ d := by omega
    have hFpure : AffineFamily.IsPure (pieceCarrierFamily X j) (d - j) :=
      md_piece_pure P X θ₁ η 1 hX j hjLe
    -- Testing degrees.
    have hTb_nonneg : 0 ≤ testDeg (cfgB P) X.width b :=
      md_testDeg_nonneg _ _ _ hB0
    have hTplus_nonneg : 0 ≤ testDeg (cfgB P) X.width (b + ξ / 4) :=
      md_testDeg_nonneg _ _ _ hB0
    have hTpre_nonneg : 0 ≤ testDeg (cfgB P) X.width (b - ξ + θ₁) :=
      md_testDeg_nonneg _ _ _ hB0
    have hKT_nonneg : 0 ≤ K * testDeg (cfgB P) X.width b := by
      apply mul_nonneg _ hTb_nonneg
      linarith
    -- Integer bounds.
    let L' : ℕ := ⌈K * testDeg (cfgB P) X.width b⌉₊ + 1
    let D : ℕ := ⌊testDeg (cfgB P) X.width (b + ξ / 4)⌋₊
    have hL'pos : 1 ≤ L' := by dsimp [L']; omega
    have hTplus_ge_one : 1 ≤ testDeg (cfgB P) X.width (b + ξ / 4) := by
      have hexp : 1 ≤ Real.exp ((ξ / 4) * X.width) := by
        apply Real.one_le_exp_iff.mpr
        apply mul_nonneg _ hs0
        positivity
      have hshift := md_testDeg_shift (cfgB P) X.width b (b + ξ / 4)
      rw [show (b + ξ / 4 - b) = ξ / 4 by ring] at hshift
      rw [hshift]
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ testDeg (cfgB P) X.width b * Real.exp ((ξ / 4) * X.width) :=
          mul_le_mul hT hexp zero_le_one (le_trans zero_le_one hT)
    have hDpos : 1 ≤ D := by
      dsimp [D]
      apply Nat.le_floor
      simpa using hTplus_ge_one
    have hD_nonneg_real : 0 ≤ (D : ℝ) := Nat.cast_nonneg _
    have hL'ge : (⌈K * testDeg (cfgB P) X.width b⌉₊ : ℝ) ≤ (L' : ℝ) := by
      dsimp [L']
      exact_mod_cast Nat.le_succ _
    -- Prefix cuts are bounded by L'.
    have hcut_le : ∀ i : Fin d, i.val < j →
        (X.path.cut i).totalDegree ≤ L' := by
      intro i hi
      have hdeg := hX.degree i
      have hti : X.path.time i + θ₁ ≤ b - ξ + θ₁ := by
        have hplate := (hb i).1 hi
        linarith
      have hTmono : testDeg (cfgB P) X.width (X.path.time i + θ₁) ≤
          testDeg (cfgB P) X.width (b - ξ + θ₁) :=
        md_testDeg_mono_of_nonneg _ _ _ _ hB0 hs0 hti
      have hTpre_le_Tb : testDeg (cfgB P) X.width (b - ξ + θ₁) ≤
          testDeg (cfgB P) X.width b := by
        apply md_testDeg_mono_of_nonneg _ _ _ _ hB0 hs0
        linarith
      have hreal : ((X.path.cut i).totalDegree : ℝ) ≤ K * testDeg (cfgB P) X.width b := by
        calc ((X.path.cut i).totalDegree : ℝ) ≤
              testDeg (cfgB P) X.width (X.path.time i + θ₁) := hdeg
          _ ≤ testDeg (cfgB P) X.width (b - ξ + θ₁) := hTmono
          _ ≤ testDeg (cfgB P) X.width b := hTpre_le_Tb
          _ ≤ K * testDeg (cfgB P) X.width b := by
              have hK1 : 1 ≤ K := hK
              exact le_mul_of_one_le_left hTb_nonneg hK1
      have hceil : ((X.path.cut i).totalDegree : ℝ) ≤ (⌈K * testDeg (cfgB P) X.width b⌉₊ : ℝ) :=
        le_trans hreal (Nat.le_ceil _)
      have hle_real : ((X.path.cut i).totalDegree : ℝ) ≤ (L' : ℝ) :=
        le_trans hceil hL'ge
      exact_mod_cast hle_real
    have hFlists : TrackA.FromAffineLists (pieceCarrierFamily X j) L' :=
      md_piece_from_lists X j L' hL'pos hcut_le
    -- Carrier family for the Bézout bound.
    have hFmem : ∀ Z ∈ pieceCarrierFamily X j,
        X.path.IsCarrier j Z ∧ ∃ x ∈ X.pts, toC x ∈ Z := by
      intro Z hZ
      exact (mem_pieceCarrierFamily X j Z).mp hZ
    have hdegF_Q : (∑ Z ∈ pieceCarrierFamily X j, (Z.degree : ℝ)) ≤
        eScale (cfgB P) X.width X.path.time j * Real.exp ((ξ / 16) * X.width) :=
      (hbez P X η 1 hXB hs0 j hjLe (pieceCarrierFamily X j) hFmem).1
    -- Pooling input: replace by 1 where the test already contains the carrier.
    let h : AffineVariety d → Poly d := fun Z =>
      if f Z ∈ Z.ideal then 1 else f Z
    have hh : ∀ V ∈ pieceCarrierFamily X j,
        (h V).totalDegree ≤ L' ∧ h V ∉ V.ideal := by
      intro V hV
      have hpureV := hFpure V hV
      have hirr : V.IsIrreducible := hpureV.1
      have hne : V.ideal ≠ ⊤ := hirr.ne_top
      dsimp only [h]
      by_cases hmem : f V ∈ V.ideal
      · rw [if_pos hmem]
        refine ⟨?_, ?_⟩
        · simpa using Nat.zero_le L'
        · intro h1mem
          have htop : V.ideal = ⊤ := Ideal.eq_top_iff_one V.ideal |>.mpr h1mem
          exact hne htop
      · rw [if_neg hmem]
        refine ⟨?_, hmem⟩
        have hreal : ((f V).totalDegree : ℝ) ≤ K * testDeg (cfgB P) X.width b :=
          hf V
        have hceil : ((f V).totalDegree : ℝ) ≤
            (⌈K * testDeg (cfgB P) X.width b⌉₊ : ℝ) :=
          le_trans hreal (Nat.le_ceil _)
        have hle_real : ((f V).totalDegree : ℝ) ≤ (L' : ℝ) :=
          le_trans hceil hL'ge
        exact_mod_cast hle_real
    -- Width thresholds give the pooling numerics and the exceptional-degree estimate.
    have hExp16 : 2 * (C : ℝ) * (K + 2) ≤ Real.exp ((ξ / 16) * X.width) :=
      hsE X.width hsE'
    have hExpMono : Real.exp ((ξ / 16) * X.width) ≤ Real.exp ((ξ / 4) * X.width) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ hs0
      linarith
    have hExp4 : 2 * (C : ℝ) * (K + 2) ≤ Real.exp ((ξ / 4) * X.width) :=
      le_trans hExp16 hExpMono
    have hCge1 : 1 ≤ (C : ℝ) := by exact_mod_cast hCpos
    have hK2ge1 : 1 ≤ (K + 2 : ℝ) := by linarith
    have hXge1 : 1 ≤ (C : ℝ) * (K + 2) :=
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (C : ℝ) * (K + 2) :=
          mul_le_mul hCge1 hK2ge1 zero_le_one (le_trans zero_le_one hCge1)
    have hExp4' : (C : ℝ) * (K + 2) + 1 ≤ Real.exp ((ξ / 4) * X.width) := by
      linarith
    have hTpos : 0 < testDeg (cfgB P) X.width b := lt_of_lt_of_le zero_lt_one hT
    have hL'le : (L' : ℝ) ≤ K * testDeg (cfgB P) X.width b + 2 := by
      have hceil_le : (⌈K * testDeg (cfgB P) X.width b⌉₊ : ℝ) ≤
          K * testDeg (cfgB P) X.width b + 1 :=
        md_ceil_le_add_one _ hKT_nonneg
      dsimp [L']
      push_cast
      linarith
    have hL'le2 : (L' : ℝ) ≤ (K + 2) * testDeg (cfgB P) X.width b := by
      have h2le : (2 : ℝ) ≤ 2 * testDeg (cfgB P) X.width b :=
        calc (2 : ℝ) = 2 * 1 := by ring
          _ ≤ 2 * testDeg (cfgB P) X.width b :=
            mul_le_mul_of_nonneg_left hT (by norm_num)
      calc (L' : ℝ) ≤ K * testDeg (cfgB P) X.width b + 2 := hL'le
        _ ≤ K * testDeg (cfgB P) X.width b + 2 * testDeg (cfgB P) X.width b := by
            gcongr
        _ = (K + 2) * testDeg (cfgB P) X.width b := by ring
    have hTplus_eq : testDeg (cfgB P) X.width (b + ξ / 4) =
        testDeg (cfgB P) X.width b * Real.exp ((ξ / 4) * X.width) := by
      have hshift := md_testDeg_shift (cfgB P) X.width b (b + ξ / 4)
      rw [show (b + ξ / 4 - b) = ξ / 4 by ring] at hshift
      exact hshift
    have hDge : testDeg (cfgB P) X.width (b + ξ / 4) - 1 ≤ (D : ℝ) :=
      md_floor_sub_one_le _ hTplus_nonneg
    have hCLD_real : (C : ℝ) * (L' : ℝ) ≤ (D : ℝ) := by
      calc (C : ℝ) * (L' : ℝ) ≤ (C : ℝ) * ((K + 2) * testDeg (cfgB P) X.width b) :=
            mul_le_mul_of_nonneg_left hL'le2 (le_of_lt hCposR)
        _ = ((C : ℝ) * (K + 2) + 1 - 1) * testDeg (cfgB P) X.width b := by ring
        _ ≤ ((Real.exp ((ξ / 4) * X.width)) - 1) * testDeg (cfgB P) X.width b := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hTpos)
            linarith
        _ = testDeg (cfgB P) X.width b * Real.exp ((ξ / 4) * X.width) -
            testDeg (cfgB P) X.width b := by ring
        _ ≤ testDeg (cfgB P) X.width b * Real.exp ((ξ / 4) * X.width) - 1 := by
            linarith [hT]
        _ = testDeg (cfgB P) X.width (b + ξ / 4) - 1 := by rw [hTplus_eq]
        _ ≤ (D : ℝ) := hDge
    have hCLD : C * max L' L' ≤ D := by
      rw [max_self]
      have hcast : ((C * L' : ℕ) : ℝ) ≤ ((D : ℕ) : ℝ) := by
        push_cast
        exact hCLD_real
      exact_mod_cast hcast
    obtain ⟨bad, g, hbad_sub, hbad_degQ, hgdeg_nat, hgne, hgzero, hgproper⟩ :=
      hpool (pieceCarrierFamily X j) (d - j) L' L' D hFpure hL'pos hFlists hL'pos hCLD h hh
    have hgdeg : (g.totalDegree : ℝ) ≤ testDeg (cfgB P) X.width (b + ξ / 4) := by
      have h1 : (g.totalDegree : ℝ) ≤ (D : ℝ) := by exact_mod_cast hgdeg_nat
      have h2 : (D : ℝ) ≤ testDeg (cfgB P) X.width (b + ξ / 4) :=
        Nat.floor_le hTplus_nonneg
      exact le_trans h1 h2
    have hzero : ∀ x ∈ X.pts,
        (∃ Z ∈ X.path.localCarriers j (toC x),
          f Z ∉ Z.ideal ∧ MvPolynomial.eval (toC x) (f Z) = 0) →
        MvPolynomial.eval (toC x) g = 0 := by
      intro x hx hcut
      obtain ⟨Z, hZmem, hZnot, hZzero⟩ := hcut
      have hZcar : X.path.IsCarrier j Z := hZmem.1
      have hZpt : toC x ∈ Z := hZmem.2
      have hZinF : Z ∈ pieceCarrierFamily X j :=
        (mem_pieceCarrierFamily X j Z).mpr ⟨hZcar, x, hx, hZpt⟩
      have hhZ : h Z = f Z := by
        dsimp only [h]
        rw [if_neg hZnot]
      have heval_h : MvPolynomial.eval (toC x) (h Z) = 0 := by
        rw [hhZ]
        exact hZzero
      exact hgzero Z hZinF (toC x) hZpt heval_h
    have hbad_deg : (AffineFamily.degree bad : ℝ) ≤
        eScale (cfgB P) X.width X.path.time j * Real.exp (-ξ / 8 * X.width) := by
      have hDposR : 0 < (D : ℝ) := by exact_mod_cast hDpos
      have hDneR : (D : ℝ) ≠ 0 := ne_of_gt hDposR
      have hej_nonneg : 0 ≤ eScale (cfgB P) X.width X.path.time j :=
        md_eScale_nonneg _ _ _ _ hB0
      -- Cast the pooling ℚ-bound to ℝ.
      have hbad_degR : (AffineFamily.degree bad : ℝ) ≤
          (C : ℝ) * ((AffineFamily.degree (pieceCarrierFamily X j) : ℚ) : ℝ) *
            (L' : ℝ) / (D : ℝ) := by
        have hQ := hbad_degQ
        -- hQ : deg bad ≤ C * degF * L' / D  in ℚ
        have hcast : ((AffineFamily.degree bad : ℚ) : ℝ) ≤
            (((C : ℚ) * AffineFamily.degree (pieceCarrierFamily X j) *
              (L' : ℚ) / (D : ℚ) : ℚ) : ℝ) := by
          exact_mod_cast hQ
        simpa [push_cast] using hcast
      -- Identify the ℚ-degree sum with the ℝ-sum bounded by Bézout.
      have hdegF_eq : ((AffineFamily.degree (pieceCarrierFamily X j) : ℚ) : ℝ) =
          ∑ Z ∈ pieceCarrierFamily X j, (Z.degree : ℝ) := by
        simp [AffineFamily.degree]
      rw [hdegF_eq] at hbad_degR
      have hdegF_le : ∑ Z ∈ pieceCarrierFamily X j, (Z.degree : ℝ) ≤
          eScale (cfgB P) X.width X.path.time j * Real.exp ((ξ / 16) * X.width) :=
        hdegF_Q
      have hCL'D_nonneg : 0 ≤ (C : ℝ) * (L' : ℝ) / (D : ℝ) := by
        positivity
      have hbad_le : (AffineFamily.degree bad : ℝ) ≤
          (C : ℝ) * (eScale (cfgB P) X.width X.path.time j *
            Real.exp ((ξ / 16) * X.width)) * (L' : ℝ) / (D : ℝ) := by
        calc (AffineFamily.degree bad : ℝ) ≤
                (C : ℝ) * (∑ Z ∈ pieceCarrierFamily X j, (Z.degree : ℝ)) *
                  (L' : ℝ) / (D : ℝ) := hbad_degR
          _ ≤ (C : ℝ) * (eScale (cfgB P) X.width X.path.time j *
                Real.exp ((ξ / 16) * X.width)) * (L' : ℝ) / (D : ℝ) := by
              gcongr
      -- Reduce to a scalar ratio bound independent of the family.
      have hfactor_nonneg : 0 ≤ eScale (cfgB P) X.width X.path.time j := hej_nonneg
      have hinner : (C : ℝ) * Real.exp ((ξ / 16) * X.width) * (L' : ℝ) / (D : ℝ) ≤
          Real.exp (-ξ / 8 * X.width) := by
        have hTb : 1 ≤ testDeg (cfgB P) X.width b := hT
        have hexp4_pos : 0 < Real.exp ((ξ / 4) * X.width) := Real.exp_pos _
        have hexp16_pos : 0 < Real.exp ((ξ / 16) * X.width) := Real.exp_pos _
        have hexp_neg_pos : 0 < Real.exp (-ξ / 8 * X.width) := Real.exp_pos _
        -- D bounds via T_plus.
        have hDge2 : testDeg (cfgB P) X.width b * Real.exp ((ξ / 4) * X.width) / 2 ≤
            (D : ℝ) := by
          have hge : testDeg (cfgB P) X.width b * Real.exp ((ξ / 4) * X.width) - 1 ≤
              (D : ℝ) := by
            calc testDeg (cfgB P) X.width b * Real.exp ((ξ / 4) * X.width) - 1 =
                    testDeg (cfgB P) X.width (b + ξ / 4) - 1 := by rw [← hTplus_eq]
              _ ≤ (D : ℝ) := hDge
          have h2le : (2 : ℝ) ≤ 2 * (C : ℝ) * (K + 2) := by linarith [hXge1]
          have h2exp : (2 : ℝ) ≤ Real.exp ((ξ / 4) * X.width) :=
            le_trans h2le hExp4
          have hprod_ge2 : 2 ≤ testDeg (cfgB P) X.width b *
              Real.exp ((ξ / 4) * X.width) := by
            calc (2 : ℝ) = 1 * 2 := by ring
              _ ≤ testDeg (cfgB P) X.width b * Real.exp ((ξ / 4) * X.width) := by
                apply mul_le_mul hTb h2exp (by norm_num) (le_trans zero_le_one hTb)
          linarith
        -- L'/D ratio via a single division lemma.
        have hK2_nonneg : 0 ≤ (K + 2 : ℝ) := by linarith
        have hTb_exp_le : testDeg (cfgB P) X.width b *
            Real.exp ((ξ / 4) * X.width) ≤ 2 * (D : ℝ) := by
          linarith [hDge2]
        have hdiv : (L' : ℝ) / (D : ℝ) ≤
            2 * (K + 2) / Real.exp ((ξ / 4) * X.width) := by
          rw [div_le_iff₀ hDposR]
          have h1 : (L' : ℝ) ≤ (K + 2) * testDeg (cfgB P) X.width b := hL'le2
          have h2 : testDeg (cfgB P) X.width b ≤
              2 * (D : ℝ) / Real.exp ((ξ / 4) * X.width) := by
            rw [le_div_iff₀ hexp4_pos]
            linarith [hTb_exp_le]
          calc (L' : ℝ) ≤ (K + 2) * testDeg (cfgB P) X.width b := h1
            _ ≤ (K + 2) * (2 * (D : ℝ) / Real.exp ((ξ / 4) * X.width)) := by
                apply mul_le_mul_of_nonneg_left h2 hK2_nonneg
            _ = 2 * (K + 2) / Real.exp ((ξ / 4) * X.width) * (D : ℝ) := by
                ring
        have hCexp_nonneg : 0 ≤ (C : ℝ) * Real.exp ((ξ / 16) * X.width) := by
          positivity
        calc (C : ℝ) * Real.exp ((ξ / 16) * X.width) * (L' : ℝ) / (D : ℝ) =
                ((C : ℝ) * Real.exp ((ξ / 16) * X.width)) * ((L' : ℝ) / (D : ℝ)) := by
              ring
          _ ≤ ((C : ℝ) * Real.exp ((ξ / 16) * X.width)) *
                (2 * (K + 2) / Real.exp ((ξ / 4) * X.width)) := by
              apply mul_le_mul_of_nonneg_left hdiv hCexp_nonneg
          _ = 2 * (C : ℝ) * (K + 2) * Real.exp ((ξ / 16) * X.width) /
                Real.exp ((ξ / 4) * X.width) := by
              ring
          _ ≤ Real.exp (-ξ / 8 * X.width) := by
            have hexp_split : Real.exp ((ξ / 4) * X.width) =
                Real.exp ((ξ / 16) * X.width) * Real.exp ((3 * ξ / 16) * X.width) := by
              rw [← Real.exp_add]
              congr 1
              ring
            have hexp3_neg : Real.exp ((3 * ξ / 16) * X.width) *
                Real.exp (-ξ / 8 * X.width) =
                Real.exp ((ξ / 16) * X.width) := by
              rw [← Real.exp_add]
              congr 1
              ring
            have hexp4_pos' : 0 < Real.exp ((ξ / 4) * X.width) := hexp4_pos
            rw [div_le_iff₀ hexp4_pos']
            -- 2*C*(K+2)*exp16 ≤ expNeg8 * exp4 = exp16*exp16
            have hexp16_nonneg : 0 ≤ Real.exp ((ξ / 16) * X.width) :=
              le_of_lt hexp16_pos
            have hmul_le : 2 * (C : ℝ) * (K + 2) * Real.exp ((ξ / 16) * X.width) ≤
                Real.exp ((ξ / 16) * X.width) * Real.exp ((ξ / 16) * X.width) :=
              mul_le_mul_of_nonneg_right hExp16 hexp16_nonneg
            have hexp_eq : Real.exp (-ξ / 8 * X.width) * Real.exp ((ξ / 4) * X.width) =
                Real.exp ((ξ / 16) * X.width) * Real.exp ((ξ / 16) * X.width) := by
              have h1 : Real.exp (-ξ / 8 * X.width) * Real.exp ((ξ / 4) * X.width) =
                  Real.exp ((-ξ / 8 + ξ / 4) * X.width) := by
                rw [← Real.exp_add]
                congr 1
                ring
              have h2 : Real.exp ((ξ / 16) * X.width) * Real.exp ((ξ / 16) * X.width) =
                  Real.exp ((ξ / 8) * X.width) := by
                rw [← Real.exp_add]
                congr 1
                ring
              -- (-ξ/8 + ξ/4) = ξ/8
              have harg : (-ξ / 8 + ξ / 4) * X.width = (ξ / 8) * X.width := by ring
              rw [h1, harg, ← h2]
            calc 2 * (C : ℝ) * (K + 2) * Real.exp ((ξ / 16) * X.width) ≤
                    Real.exp ((ξ / 16) * X.width) * Real.exp ((ξ / 16) * X.width) :=
                  hmul_le
              _ = Real.exp (-ξ / 8 * X.width) * Real.exp ((ξ / 4) * X.width) := by
                  rw [hexp_eq]
      calc (AffineFamily.degree bad : ℝ) ≤
              (C : ℝ) * (eScale (cfgB P) X.width X.path.time j *
                Real.exp ((ξ / 16) * X.width)) * (L' : ℝ) / (D : ℝ) := hbad_le
        _ = eScale (cfgB P) X.width X.path.time j *
                ((C : ℝ) * Real.exp ((ξ / 16) * X.width) * (L' : ℝ) / (D : ℝ)) := by
            ring
        _ ≤ eScale (cfgB P) X.width X.path.time j * Real.exp (-ξ / 8 * X.width) :=
            mul_le_mul_of_nonneg_left hinner hfactor_nonneg
    exact ⟨bad, g, hbad_sub, hbad_deg, hgdeg, hzero, hgproper⟩
  · have hBzero : cfgB P = 0 := le_antisymm (le_of_not_gt hBpos) hB0
    have hTzero : testDeg (cfgB P) X.width b = 0 := by
      unfold testDeg
      rw [hBzero]
      ring
    rw [hTzero] at hT
    norm_num at hT

set_option maxHeartbeats 1000000 in
/-- `profiles.tex:385–425`: common equations and minors with an exceptional
degree estimate, before the separate per-piece mass calculation. -/
theorem regularity_pool_degree_certificate (d : ℕ) (hd : 3 ≤ d) :
    ∀ ξ > 0, ∃ θ₁ > 0, ∃ ρ₀ > 0, ∃ s₁ : ℝ,
      ∀ (P : Finset (Pt d)) (pl : Finset (Piece d)) (s ρ η : ℝ) (t : Fin d → ℝ),
        ρ ≤ ρ₀ → PoolGood P θ₁ η 1 ρ pl s t → s₁ ≤ s → pl.Nonempty →
        ∀ j : ℕ, 0 < j → j < d → ∀ b : ℝ, OnPlateau t j ξ b →
          1 ≤ testDeg (cfgB P) s b →
          ∃ (bad : AffineFamily.Family d) (E : List (Poly d)) (g : Poly d),
            bad ⊆ poolCarrierFamily pl j ∧
            (∀ X ∈ pl, (AffineFamily.degree bad : ℝ) ≤
              eScale (cfgB P) s X.path.time j * Real.exp (-ξ / 8 * s)) ∧
            (∀ f ∈ E, f ∈ (AffineFamily.locus (poolCarrierFamily pl j)).ideal ∧
              (f.totalDegree : ℝ) ≤ testDeg (cfgB P) s (b - ξ / 2)) ∧
            (g.totalDegree : ℝ) ≤ testDeg (cfgB P) s (b - ξ / 2) ∧
            g ∈ Submodule.span ℂ (TrackA.jacobianMinors E j) ∧
            (∀ Z ∈ poolCarrierFamily pl j, Z ∉ bad → g ∉ Z.ideal) ∧
            (∀ y : Point d, MvPolynomial.eval y g ≠ 0 →
              ∀ Z ∈ poolCarrierFamily pl j, ∀ Z' ∈ poolCarrierFamily pl j,
                y ∈ Z → y ∈ Z' → Z = Z') ∧
            1 ≤ testDeg (cfgB P) s (b - ξ / 2) := by
  intro ξ hξ
  obtain ⟨C, hCpos, hreg⟩ := TrackA.poly_regularity d
  have hxi16 : 0 < ξ / 32 := by positivity
  obtain ⟨θB, hθB, hbez⟩ := prof_budget_bezout d hd (ξ / 32) hxi16
  have hdposR : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  let θ₁ : ℝ := min θB (ξ / 32)
  have hθ₁ : 0 < θ₁ := by dsimp [θ₁]; positivity
  have hθ₁B : θ₁ ≤ θB := min_le_left _ _
  have hθ₁ξ : θ₁ ≤ ξ / 32 := min_le_right _ _
  let ρ₀ : ℝ := min (ξ / 8) (ξ / (32 * (d : ℝ)))
  have hρ₀ : 0 < ρ₀ := by dsimp [ρ₀]; positivity
  have hρ₀ξ : ρ₀ ≤ ξ / 8 := min_le_left _ _
  have hCposR : 0 < (C : ℝ) := by exact_mod_cast hCpos
  have hC1posR : 0 < ((C : ℝ) + 1) := by positivity
  -- Large exponential threshold dominates all fixed constants.
  have hCp : 0 < (100 * ((C : ℝ) + 2) ^ 2 + 100 : ℝ) := by positivity
  obtain ⟨sE, hsE⟩ := md_exp_ge (ξ / 32)
    (100 * ((C : ℝ) + 2) ^ 2 + 100) (by positivity) hCp
  let s₁ : ℝ := max sE 0
  refine ⟨θ₁, hθ₁, ρ₀, hρ₀, s₁, ?_⟩
  intro P pl s ρ η t hρ hpl hs hne j hj0 hj b hb hT
  have hs0 : 0 ≤ s := le_trans (le_max_right _ _) hs
  have hsE' : sE ≤ s := le_trans (le_max_left _ _) hs
  have hB0 : 0 ≤ cfgB P := md_cfgB_nonneg P
  by_cases hBpos : 0 < cfgB P
  · have hjLe : j ≤ d := by omega
    have hFpure : AffineFamily.IsPure (poolCarrierFamily pl j) (d - j) :=
      poolCarrierFamily_pure P pl θ₁ η 1 hpl.pieces j hjLe
    -- ρ is nonnegative on a nonempty pool.
    have hρ_nonneg : 0 ≤ ρ := by
      obtain ⟨X0, hX0⟩ := hne
      have hclose := hpl.close X0 hX0 ⟨0, by omega⟩
      have habs : 0 ≤ |(X0.path.time ⟨0, by omega⟩ - t ⟨0, by omega⟩)| :=
        abs_nonneg _
      exact le_trans habs hclose
    have hρ0_le : ρ ≤ ξ / 8 := le_trans hρ hρ₀ξ
    have hwidth_eq : ∀ X ∈ pl, X.width = s := hpl.width
    -- Testing degrees.
    have hTb_nonneg : 0 ≤ testDeg (cfgB P) s b := md_testDeg_nonneg _ _ _ hB0
    have hTmid_nonneg : 0 ≤ testDeg (cfgB P) s (b - ξ / 2) :=
      md_testDeg_nonneg _ _ _ hB0
    have hTpre_nonneg : 0 ≤ testDeg (cfgB P) s (b - ξ + ρ + θ₁) :=
      md_testDeg_nonneg _ _ _ hB0
    -- Prefix bound uses the reference plateau plus closeness and tolerance.
    let Tpre : ℝ := testDeg (cfgB P) s (b - ξ + ρ + θ₁)
    let Tmid : ℝ := testDeg (cfgB P) s (b - ξ / 2)
    let L0 : ℕ := ⌈Tpre⌉₊ + 1
    let D : ℕ := ⌊Tmid / ((C : ℝ) + 1)⌋₊
    have hL0pos : 1 ≤ L0 := by dsimp [L0]; omega
    have hTpre_ge_one : 1 ≤ Tpre := by
      obtain ⟨X0, hX0⟩ := hne
      have hX0good := hpl.pieces X0 hX0
      have hX0width : X0.width = s := hwidth_eq X0 hX0
      -- N > 0 from B > 0, so X0 has points.
      have hNpos : 0 < cfgN P := by
        by_contra hnot
        have hNzero : cfgN P = 0 := le_antisymm (le_of_not_gt hnot)
          (by unfold cfgN; positivity)
        have hBzero' : cfgB P = 0 := by
          have hcard0 : (P.card : ℝ) = 0 := by simpa [cfgN] using hNzero
          unfold cfgB
          rw [hcard0]
          apply Real.zero_rpow
          have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
          exact div_ne_zero one_ne_zero hdne
        linarith
      have hX0size := hX0good.size
      rw [hX0width] at hX0size
      have hcard_posR : 0 < (X0.pts.card : ℝ) := lt_of_lt_of_le
        (mul_pos hNpos (Real.exp_pos _)) hX0size
      have hcard_pos : 0 < X0.pts.card := by exact_mod_cast hcard_posR
      obtain ⟨x0, hx0⟩ := Finset.card_pos.mp hcard_pos
      have hcut_ge : 1 ≤ (X0.path.cut ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj⟩).totalDegree :=
        dprofiles2_cut_degree_pos P X0 θ₁ η 1 hX0good ⟨x0, hx0⟩ ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj⟩
      have hcut_real : (1 : ℝ) ≤ ((X0.path.cut ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj⟩).totalDegree : ℝ) := by
        exact_mod_cast hcut_ge
      have hdeg_up : ((X0.path.cut ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj⟩).totalDegree : ℝ) ≤
          testDeg (cfgB P) s (X0.path.time ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj⟩ + θ₁) := by
        have hdeg := hX0good.degree ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj⟩
        rw [hX0width] at hdeg
        exact hdeg
      have ht_le : X0.path.time ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj⟩ + θ₁ ≤ b - ξ + ρ + θ₁ := by
        have ht_ref : t ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj⟩ + ξ ≤ b := (hb ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj⟩).1 (Nat.sub_one_lt_of_le hj0 le_rfl)
        have hclose := hpl.close X0 hX0 ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj⟩
        have hle : X0.path.time ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj⟩ - t ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj⟩ ≤ ρ :=
          le_trans (le_abs_self _) hclose
        linarith
      have hTmono : testDeg (cfgB P) s (X0.path.time ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj⟩ + θ₁) ≤ Tpre := by
        dsimp [Tpre]
        apply md_testDeg_mono_of_nonneg _ _ _ _ hB0 hs0 ht_le
      calc (1 : ℝ) ≤ ((X0.path.cut ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj⟩).totalDegree : ℝ) := hcut_real
        _ ≤ testDeg (cfgB P) s (X0.path.time ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj⟩ + θ₁) := hdeg_up
        _ ≤ Tpre := hTmono
    have hTmid_ge_one : 1 ≤ Tmid := by
      have hle : b - ξ + ρ + θ₁ ≤ b - ξ / 2 := by
        have hρle : ρ ≤ ξ / 8 := hρ0_le
        have hθle : θ₁ ≤ ξ / 32 := hθ₁ξ
        linarith
      have hmono : Tpre ≤ Tmid := by
        dsimp [Tpre, Tmid]
        apply md_testDeg_mono_of_nonneg _ _ _ _ hB0 hs0 hle
      exact le_trans hTpre_ge_one hmono
    have hDpos : 1 ≤ D := by
      have hC1pos : 0 < (C : ℝ) + 1 := by positivity
      have hCoeff_ge : ξ / 32 ≤ ξ / 2 - ρ - θ₁ := by
        have hρle : ρ ≤ ξ / 8 := hρ0_le
        have hθle : θ₁ ≤ ξ / 32 := hθ₁ξ
        linarith
      have hCoeff_nonneg : 0 ≤ ξ / 2 - ρ - θ₁ := le_trans (by positivity) hCoeff_ge
      have hTmid_eq : Tmid = Tpre * Real.exp ((ξ / 2 - ρ - θ₁) * s) := by
        dsimp [Tmid, Tpre]
        have hshift := md_testDeg_shift (cfgB P) s (b - ξ + ρ + θ₁) (b - ξ / 2)
        rw [show (b - ξ / 2 - (b - ξ + ρ + θ₁)) = ξ / 2 - ρ - θ₁ by ring] at hshift
        exact hshift
      have hExp_ge : Real.exp ((ξ / 32) * s) ≤ Real.exp ((ξ / 2 - ρ - θ₁) * s) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right hCoeff_ge hs0
      have hC'_le : (100 * ((C : ℝ) + 2) ^ 2 + 100 : ℝ) ≤
          Real.exp ((ξ / 32) * s) := hsE s hsE'
      have hC1_le_exp : (C : ℝ) + 1 ≤ Real.exp ((ξ / 2 - ρ - θ₁) * s) := by
        calc (C : ℝ) + 1 ≤ 100 * ((C : ℝ) + 2) ^ 2 + 100 := by
              nlinarith [hCposR]
          _ ≤ Real.exp ((ξ / 32) * s) := hC'_le
          _ ≤ Real.exp ((ξ / 2 - ρ - θ₁) * s) := hExp_ge
      have hTmid_ge_exp : Real.exp ((ξ / 2 - ρ - θ₁) * s) ≤ Tmid := by
        rw [hTmid_eq]
        exact le_mul_of_one_le_left (Real.exp_nonneg _) hTpre_ge_one
      have hC1_le_Tmid : (C : ℝ) + 1 ≤ Tmid := le_trans hC1_le_exp hTmid_ge_exp
      dsimp [D]
      apply Nat.le_floor
      rw [le_div_iff₀ hC1pos]
      simpa using hC1_le_Tmid
    have hLfun : ∀ X ∈ pl, 1 ≤ L0 := fun X _ => hL0pos
    have hcut_le : ∀ X ∈ pl, ∀ i : Fin d, i.val < j → (X.path.cut i).totalDegree ≤ L0 := by
      intro X hX i hi
      have hXgood := hpl.pieces X hX
      have hXwidth : X.width = s := hwidth_eq X hX
      have hdeg := hXgood.degree i
      rw [hXwidth] at hdeg
      have ht_ref : t i + ξ ≤ b := (hb i).1 hi
      have hclose := hpl.close X hX i
      have hXle : X.path.time i ≤ t i + ρ := by
        have habs := abs_le.mp hclose
        linarith
      have ht_le : X.path.time i + θ₁ ≤ b - ξ + ρ + θ₁ := by linarith
      have hTmono : testDeg (cfgB P) s (X.path.time i + θ₁) ≤ Tpre := by
        dsimp [Tpre]
        apply md_testDeg_mono_of_nonneg _ _ _ _ hB0 hs0 ht_le
      have hreal : ((X.path.cut i).totalDegree : ℝ) ≤ Tpre :=
        le_trans hdeg hTmono
      have hceil : ((X.path.cut i).totalDegree : ℝ) ≤ (⌈Tpre⌉₊ : ℝ) :=
        le_trans hreal (Nat.le_ceil _)
      have hL0ge : (⌈Tpre⌉₊ : ℝ) ≤ (L0 : ℝ) := by
        dsimp [L0]
        exact_mod_cast Nat.le_succ _
      have hle_real : ((X.path.cut i).totalDegree : ℝ) ≤ (L0 : ℝ) :=
        le_trans hceil hL0ge
      exact_mod_cast hle_real
    have hFlists : TrackA.FromAffineLists (poolCarrierFamily pl j) (∑ X ∈ pl, L0) := by
      apply poolCarrierFamily_from_lists pl j (fun _ => L0) _ _
      · intro X hX
        exact hLfun X hX
      · intro X hX i hi
        exact hcut_le X hX i hi
    have hCLD : C * (∑ X ∈ pl, L0) ≤ D := by
      have hC1pos : 0 < (C : ℝ) + 1 := by positivity
      have hC1posNat : 0 < C + 1 := by omega
      have hcard_le : (pl.card : ℝ) ≤ Real.exp (θ₁ * s) := hpl.count
      have hL0_le : (L0 : ℝ) ≤ Tpre + 2 := by
        have hceil_le : (⌈Tpre⌉₊ : ℝ) ≤ Tpre + 1 :=
          md_ceil_le_add_one _ hTpre_nonneg
        dsimp [L0]
        push_cast
        linarith
      have hL0_le3 : (L0 : ℝ) ≤ 3 * Tpre := by
        linarith [hTpre_ge_one]
      have hsum_eq : ((∑ X ∈ pl, L0 : ℕ) : ℝ) = (pl.card : ℝ) * (L0 : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      -- Tpre/Tmid relation via the interior gap.
      have hTpre_eq : Tpre = Tmid * Real.exp ((ρ + θ₁ - ξ / 2) * s) := by
        dsimp [Tpre, Tmid]
        have hshift := md_testDeg_shift (cfgB P) s (b - ξ / 2) (b - ξ + ρ + θ₁)
        rw [show (b - ξ + ρ + θ₁ - (b - ξ / 2)) = ρ + θ₁ - ξ / 2 by ring] at hshift
        exact hshift
      have hGap1 : ξ / 32 ≤ ξ / 2 - ρ - θ₁ := by
        have hρle : ρ ≤ ξ / 8 := hρ0_le
        have hθle : θ₁ ≤ ξ / 32 := hθ₁ξ
        linarith
      have hGap2 : ξ / 32 ≤ ξ / 2 - ρ - 2 * θ₁ := by
        have hρle : ρ ≤ ξ / 8 := hρ0_le
        have hθle : θ₁ ≤ ξ / 32 := hθ₁ξ
        linarith
      have hExp32 : (100 * ((C : ℝ) + 2) ^ 2 + 100 : ℝ) ≤
          Real.exp ((ξ / 32) * s) := hsE s hsE'
      have hExp_gap1 : Real.exp ((ξ / 32) * s) ≤
          Real.exp ((ξ / 2 - ρ - θ₁) * s) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right hGap1 hs0
      have hExp_gap2 : Real.exp ((ξ / 32) * s) ≤
          Real.exp ((ξ / 2 - ρ - 2 * θ₁) * s) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right hGap2 hs0
      have hC_nonneg : 0 ≤ (C : ℝ) := Nat.cast_nonneg _
      have h2C1_le : 2 * ((C : ℝ) + 1) ≤
          100 * ((C : ℝ) + 2) ^ 2 + 100 :=
        md_const_2C1_le _ hC_nonneg
      have h6CC1_le : 6 * (C : ℝ) * ((C : ℝ) + 1) ≤
          100 * ((C : ℝ) + 2) ^ 2 + 100 :=
        md_const_le_large3 _ hC_nonneg
      have hTmid_pos : 0 < Tmid := lt_of_lt_of_le zero_lt_one hTmid_ge_one
      have hTmid_nonneg' : 0 ≤ Tmid := le_of_lt hTmid_pos
      -- 2*(C+1) ≤ Tmid for the +1 part.
      have h2C1_le_Tmid : 2 * ((C : ℝ) + 1) ≤ Tmid := by
        calc 2 * ((C : ℝ) + 1) ≤ 100 * ((C : ℝ) + 2) ^ 2 + 100 := h2C1_le
          _ ≤ Real.exp ((ξ / 32) * s) := hExp32
          _ ≤ Real.exp ((ξ / 2 - ρ - θ₁) * s) := hExp_gap1
          _ ≤ Tmid := by
            calc Real.exp ((ξ / 2 - ρ - θ₁) * s) =
                    1 * Real.exp ((ξ / 2 - ρ - θ₁) * s) := by ring
              _ ≤ Tpre * Real.exp ((ξ / 2 - ρ - θ₁) * s) := by
                  apply mul_le_mul_of_nonneg_right hTpre_ge_one (Real.exp_nonneg _)
              _ = Tmid := by
                have hexp_inv : Tpre * Real.exp ((ξ / 2 - ρ - θ₁) * s) = Tmid := by
                  rw [hTpre_eq]
                  have hadd : (ρ + θ₁ - ξ / 2) * s + (ξ / 2 - ρ - θ₁) * s = 0 := by
                    ring
                  calc Tmid * Real.exp ((ρ + θ₁ - ξ / 2) * s) *
                          Real.exp ((ξ / 2 - ρ - θ₁) * s) =
                          Tmid * (Real.exp ((ρ + θ₁ - ξ / 2) * s) *
                            Real.exp ((ξ / 2 - ρ - θ₁) * s)) := by ring
                    _ = Tmid * Real.exp ((ρ + θ₁ - ξ / 2) * s +
                            (ξ / 2 - ρ - θ₁) * s) := by rw [← Real.exp_add]
                    _ = Tmid * Real.exp (0 : ℝ) := by rw [hadd]
                    _ = Tmid := by rw [Real.exp_zero, mul_one]
                exact hexp_inv
      -- Main product bound for the card*L0 part.
      have hprod_le : (C : ℝ) * ((pl.card : ℝ) * (L0 : ℝ)) ≤
          Tmid / (2 * ((C : ℝ) + 1)) := by
        have hexp_a_pos : 0 < Real.exp ((ξ / 2 - ρ - 2 * θ₁) * s) := Real.exp_pos _
        have h6CC1_le_exp : 6 * (C : ℝ) * ((C : ℝ) + 1) ≤
            Real.exp ((ξ / 2 - ρ - 2 * θ₁) * s) :=
          le_trans (le_trans h6CC1_le hExp32) hExp_gap2
        -- Rewrite card*L0 via Tpre/Tmid to isolate the decaying exponential.
        have hcardL0_le : (pl.card : ℝ) * (L0 : ℝ) ≤
            3 * Tmid * Real.exp (-(ξ / 2 - ρ - 2 * θ₁) * s) := by
          calc (pl.card : ℝ) * (L0 : ℝ) ≤
                  Real.exp (θ₁ * s) * (3 * Tpre) := by
                apply mul_le_mul hcard_le hL0_le3 (by positivity) (by positivity)
            _ = 3 * (Tmid * Real.exp ((ρ + θ₁ - ξ / 2) * s)) *
                  Real.exp (θ₁ * s) := by
                rw [← hTpre_eq]
                ring
            _ = 3 * Tmid * Real.exp ((ρ + 2 * θ₁ - ξ / 2) * s) := by
              have hexp_add : Real.exp ((ρ + θ₁ - ξ / 2) * s) * Real.exp (θ₁ * s) =
                  Real.exp ((ρ + 2 * θ₁ - ξ / 2) * s) := by
                rw [← Real.exp_add]
                congr 1
                ring
              calc 3 * (Tmid * Real.exp ((ρ + θ₁ - ξ / 2) * s)) * Real.exp (θ₁ * s) =
                      3 * Tmid * (Real.exp ((ρ + θ₁ - ξ / 2) * s) * Real.exp (θ₁ * s)) := by
                    ring
                _ = 3 * Tmid * Real.exp ((ρ + 2 * θ₁ - ξ / 2) * s) := by
                    rw [hexp_add]
            _ = 3 * Tmid * Real.exp (-(ξ / 2 - ρ - 2 * θ₁) * s) := by
              have harg : (ρ + 2 * θ₁ - ξ / 2) * s = -(ξ / 2 - ρ - 2 * θ₁) * s := by
                ring
              rw [harg]
        -- Reduce to 6*C*(C+1) ≤ exp(a) via Tmid > 0.
        have hTmid_ne : Tmid ≠ 0 := ne_of_gt hTmid_pos
        have hC1_ne : (2 : ℝ) * ((C : ℝ) + 1) ≠ 0 := by positivity
        rw [div_eq_mul_inv]
        have h1 : (C : ℝ) * ((pl.card : ℝ) * (L0 : ℝ)) ≤
            (C : ℝ) * (3 * Tmid * Real.exp (-(ξ / 2 - ρ - 2 * θ₁) * s)) :=
          mul_le_mul_of_nonneg_left hcardL0_le (le_of_lt hCposR)
        have hexp_neg : Real.exp (-(ξ / 2 - ρ - 2 * θ₁) * s) =
            (Real.exp ((ξ / 2 - ρ - 2 * θ₁) * s))⁻¹ := by
          have harg : (-(ξ / 2 - ρ - 2 * θ₁)) * s = -(((ξ / 2 - ρ - 2 * θ₁) * s)) := by
            ring
          rw [harg, Real.exp_neg]
        rw [hexp_neg] at h1
        -- Need C*3*Tmid*(exp(a))⁻¹ ≤ Tmid*(2*(C+1))⁻¹ ↔ 3*C/(exp(a)) ≤ 1/(2*(C+1))
        -- Divide by Tmid>0 to reduce to 3*C*exp(-a) ≤ (2*(C+1))⁻¹.
        have h2 : (C : ℝ) * (3 * Tmid * (Real.exp ((ξ / 2 - ρ - 2 * θ₁) * s))⁻¹) =
            Tmid * ((3 * (C : ℝ)) / Real.exp ((ξ / 2 - ρ - 2 * θ₁) * s)) := by
          rw [div_eq_mul_inv]
          ring
        have h3 : Tmid * ((2 : ℝ) * ((C : ℝ) + 1))⁻¹ =
            Tmid / (2 * ((C : ℝ) + 1)) := by
          rw [div_eq_mul_inv]
        -- It suffices to show 3*C/exp(a) ≤ 1/(2*(C+1)), i.e. 6*C*(C+1) ≤ exp(a).
        have hdiv_le : (3 * (C : ℝ)) / Real.exp ((ξ / 2 - ρ - 2 * θ₁) * s) ≤
            1 / (2 * ((C : ℝ) + 1)) := by
          rw [div_le_iff₀ hexp_a_pos]
          have hC1pos2 : 0 < (2 : ℝ) * ((C : ℝ) + 1) := by positivity
          have heq : (1 / (2 * ((C : ℝ) + 1))) * Real.exp ((ξ / 2 - ρ - 2 * θ₁) * s) =
              Real.exp ((ξ / 2 - ρ - 2 * θ₁) * s) / (2 * ((C : ℝ) + 1)) := by
            ring
          rw [heq]
          rw [le_div_iff₀ hC1pos2]
          calc (3 : ℝ) * (C : ℝ) * (2 * ((C : ℝ) + 1)) = 6 * (C : ℝ) * ((C : ℝ) + 1) := by
                ring
            _ ≤ Real.exp ((ξ / 2 - ρ - 2 * θ₁) * s) := h6CC1_le_exp
        have hexp_neg_eq : Real.exp (-(ξ / 2 - ρ - 2 * θ₁) * s) =
            (Real.exp ((ξ / 2 - ρ - 2 * θ₁) * s))⁻¹ := by
          have harg2 : (-(ξ / 2 - ρ - 2 * θ₁)) * s = -(((ξ / 2 - ρ - 2 * θ₁) * s)) := by
            ring
          rw [harg2, Real.exp_neg]
        have h1 : (C : ℝ) * ((pl.card : ℝ) * (L0 : ℝ)) ≤
            (C : ℝ) * (3 * Tmid * Real.exp (-(ξ / 2 - ρ - 2 * θ₁) * s)) :=
          mul_le_mul_of_nonneg_left hcardL0_le (Nat.cast_nonneg _)
        have h2 : (C : ℝ) * (3 * Tmid * Real.exp (-(ξ / 2 - ρ - 2 * θ₁) * s)) =
            Tmid * ((3 * (C : ℝ)) / Real.exp ((ξ / 2 - ρ - 2 * θ₁) * s)) := by
          rw [hexp_neg_eq, div_eq_mul_inv]
          ring
        have h3 : Tmid / (2 * ((C : ℝ) + 1)) =
            Tmid * (1 / (2 * ((C : ℝ) + 1))) := by
          rw [div_eq_mul_inv]
          ring
        calc (C : ℝ) * ((pl.card : ℝ) * (L0 : ℝ)) ≤
                (C : ℝ) * (3 * Tmid * Real.exp (-(ξ / 2 - ρ - 2 * θ₁) * s)) := h1
          _ = Tmid * ((3 * (C : ℝ)) / Real.exp ((ξ / 2 - ρ - 2 * θ₁) * s)) := h2
          _ ≤ Tmid * (1 / (2 * ((C : ℝ) + 1))) :=
              mul_le_mul_of_nonneg_left hdiv_le (le_of_lt hTmid_pos)
          _ = Tmid / (2 * ((C : ℝ) + 1)) := by rw [← h3]
      have hCLD_real : (C : ℝ) * (((∑ X ∈ pl, L0 : ℕ) : ℝ)) ≤ (D : ℝ) := by
        have hC1pos2 : 0 < (2 : ℝ) * ((C : ℝ) + 1) := by positivity
        have hDge' : Tmid / ((C : ℝ) + 1) - 1 ≤ (D : ℝ) := by
          have hnonneg : 0 ≤ Tmid / ((C : ℝ) + 1) := by positivity
          have hfloor := md_floor_sub_one_le (Tmid / ((C : ℝ) + 1)) hnonneg
          simpa [D] using hfloor
        have hmid_le : Tmid / (2 * ((C : ℝ) + 1)) ≤ Tmid / ((C : ℝ) + 1) - 1 := by
          have h1le : 1 ≤ Tmid / (2 * ((C : ℝ) + 1)) := by
            rw [le_div_iff₀ hC1pos2]
            simpa using h2C1_le_Tmid
          have hC1ne : ((C : ℝ) + 1) ≠ 0 := ne_of_gt hC1pos
          have hC1pos2ne : (2 : ℝ) * ((C : ℝ) + 1) ≠ 0 := ne_of_gt hC1pos2
          have heq : Tmid / ((C : ℝ) + 1) - 1 =
              Tmid / (2 * ((C : ℝ) + 1)) + (Tmid / (2 * ((C : ℝ) + 1)) - 1) := by
            field_simp
            ring
          -- Actually Tmid/(C+1) -1 = Tmid/(2*(C+1)) + (Tmid/(2*(C+1)) -1) since Tmid/(C+1)=2*(Tmid/(2*(C+1)))
          -- Since 1 ≤ Tmid/(2*(C+1)), second term ≥0, so first ≤ whole.
          have hsplit : Tmid / ((C : ℝ) + 1) =
              Tmid / (2 * ((C : ℝ) + 1)) + Tmid / (2 * ((C : ℝ) + 1)) := by
            field_simp
            ring
          linarith [h1le]
        calc (C : ℝ) * (((∑ X ∈ pl, L0 : ℕ) : ℝ)) =
                (C : ℝ) * ((pl.card : ℝ) * (L0 : ℝ)) := by rw [hsum_eq]
          _ ≤ Tmid / (2 * ((C : ℝ) + 1)) := hprod_le
          _ ≤ Tmid / ((C : ℝ) + 1) - 1 := hmid_le
          _ ≤ (D : ℝ) := hDge'
      have hcast : ((C * (∑ X ∈ pl, L0) : ℕ) : ℝ) ≤ ((D : ℕ) : ℝ) := by
        push_cast
        simpa [hsum_eq] using hCLD_real
      exact_mod_cast hcast
    obtain ⟨bad, E, g, hbad_sub, hbad_degQ, hEdeg, hgdeg_nat, hgspan, hgproper, hgunique⟩ :=
      hreg (poolCarrierFamily pl j) (d - j) (∑ X ∈ pl, L0) D
        (by omega) hFpure (by
          obtain ⟨X0, hX0⟩ := hne
          have hsub : {X0} ⊆ pl := Finset.singleton_subset_iff.mpr hX0
          have hle : ∑ X ∈ ({X0} : Finset (Piece d)), L0 ≤ ∑ X ∈ pl, L0 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
          have heq : ∑ X ∈ ({X0} : Finset (Piece d)), L0 = L0 := by simp
          linarith [hL0pos]) hFlists hCLD
    have hbad_perX : ∀ X ∈ pl, (AffineFamily.degree bad : ℝ) ≤
        eScale (cfgB P) s X.path.time j * Real.exp (-ξ / 8 * s) := by
      intro X0 hX0
      -- Degree of pool ≤ sum of piece degrees via biUnion.
      have hpure_each : ∀ X ∈ pl, AffineFamily.IsPure (pieceCarrierFamily X j) (d - j) := by
        intro X hX
        exact md_piece_pure P X θ₁ η 1 (hpl.pieces X hX) j hjLe
      have hdeg_pool_le : (AffineFamily.degree (poolCarrierFamily pl j) : ℝ) ≤
          ∑ X ∈ pl, ((AffineFamily.degree (pieceCarrierFamily X j) : ℚ) : ℝ) := by
        have hbi : poolCarrierFamily pl j = pl.biUnion (fun X => pieceCarrierFamily X j) := by
          simp [poolCarrierFamily]
        have hQ : AffineFamily.degree (poolCarrierFamily pl j) ≤
            ∑ X ∈ pl, AffineFamily.degree (pieceCarrierFamily X j) := by
          rw [hbi]
          exact TrackA.pooling_degree_biUnion pl _ (d - j) (fun X hX => hpure_each X hX)
        have hcast : ((AffineFamily.degree (poolCarrierFamily pl j) : ℚ) : ℝ) ≤
            ((∑ X ∈ pl, AffineFamily.degree (pieceCarrierFamily X j) : ℚ) : ℝ) := by
          exact_mod_cast hQ
        simpa using hcast
      -- Each piece degree via Bézout.
      have hdeg_piece_le : ∀ X ∈ pl, ((AffineFamily.degree (pieceCarrierFamily X j) : ℚ) : ℝ) ≤
          eScale (cfgB P) s X.path.time j * Real.exp ((ξ / 32) * s) := by
        intro X hX
        have hXwidth0 : 0 ≤ X.width := by
          rw [hwidth_eq X hX]
          exact hs0
        have hXgoodB : PieceGood P θB η 1 X :=
          dprofiles2_pieceGood_mono P X hθ₁B hXwidth0 (hpl.pieces X hX)
        have hFmemX : ∀ Z ∈ pieceCarrierFamily X j,
            X.path.IsCarrier j Z ∧ ∃ x ∈ X.pts, toC x ∈ Z := by
          intro Z hZ
          exact (mem_pieceCarrierFamily X j Z).mp hZ
        have hbezX := (hbez P X η 1 hXgoodB hXwidth0 j hjLe _ hFmemX).1
        rw [hwidth_eq X hX] at hbezX
        have heq : ((AffineFamily.degree (pieceCarrierFamily X j) : ℚ) : ℝ) =
            ∑ Z ∈ pieceCarrierFamily X j, (Z.degree : ℝ) := by
          simp [AffineFamily.degree]
        rw [heq]
        exact hbezX
      -- eScale closeness via 2ρ per cut.
      have hescale_close : ∀ X ∈ pl,
          eScale (cfgB P) s X.path.time j ≤
            eScale (cfgB P) s X0.path.time j * Real.exp (2 * (d : ℝ) * ρ * s) := by
        intro X hX
        -- Index set S has card j.
        have hcardS : (Finset.univ.filter (fun i : Fin d => i.val < j)).card = j := by
          have hcard_ge : (Finset.univ.filter (fun i : Fin d => j ≤ i.val)).card =
              d - j := RankCore.card_after j hjLe
          have hcard_univ : (Finset.univ : Finset (Fin d)).card = d := by
            simp [Finset.card_univ, Fintype.card_fin]
          have hdisj : Disjoint (Finset.univ.filter (fun i : Fin d => i.val < j))
              (Finset.univ.filter (fun i : Fin d => j ≤ i.val)) := by
            apply Finset.disjoint_filter.mpr
            intro i _ hlt hle
            omega
          have hunion : Finset.univ.filter (fun i : Fin d => i.val < j) ∪
              Finset.univ.filter (fun i : Fin d => j ≤ i.val) = Finset.univ := by
            ext i
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro _; trivial
            · intro _; exact lt_or_ge _ _
          have hcard_add := Finset.card_union_of_disjoint hdisj
          rw [hunion, hcard_univ, hcard_ge] at hcard_add
          omega
        -- Each time differs by at most 2ρ.
        have hXX0_le : ∀ i : Fin d, i.val < j →
            X.path.time i ≤ X0.path.time i + 2 * ρ := by
          intro i hi
          have htX : X.path.time i ≤ t i + ρ := by
            have hclose := hpl.close X hX i
            have habs := abs_le.mp hclose
            linarith
          have htX0 : t i - ρ ≤ X0.path.time i := by
            have hclose0 := hpl.close X0 hX0 i
            have habs0 := abs_le.mp hclose0
            linarith
          linarith
        -- Sum over S: ∑ X ≤ ∑ X0 + 2ρ*j ≤ ∑ X0 + 2dρ.
        have hsum_le : ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j),
            X.path.time i ≤
            (∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), X0.path.time i) +
              2 * ρ * (j : ℝ) := by
          calc ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), X.path.time i ≤
                  ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j),
                    (X0.path.time i + 2 * ρ) := by
                apply Finset.sum_le_sum
                intro i hi
                have hi' : i.val < j := Finset.mem_filter.mp hi |>.2
                exact hXX0_le i hi'
            _ = (∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), X0.path.time i) +
                  2 * ρ * (j : ℝ) := by
                rw [Finset.sum_add_distrib]
                congr 1
                rw [Finset.sum_const, hcardS]
                ring
        have hj_le_d : (j : ℝ) ≤ (d : ℝ) := by exact_mod_cast hjLe
        have hρ_nonneg' : 0 ≤ ρ := hρ_nonneg
        have h2ρj_le : 2 * ρ * (j : ℝ) ≤ 2 * (d : ℝ) * ρ := by
          have h2ρ_nonneg : 0 ≤ 2 * ρ := by positivity
          calc 2 * ρ * (j : ℝ) = (2 * ρ) * (j : ℝ) := by ring
            _ ≤ (2 * ρ) * (d : ℝ) :=
              mul_le_mul_of_nonneg_left hj_le_d h2ρ_nonneg
            _ = 2 * (d : ℝ) * ρ := by ring
        have hsum_le2 : ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j),
            X.path.time i ≤
            (∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), X0.path.time i) +
              2 * (d : ℝ) * ρ := by
          linarith [hsum_le, h2ρj_le]
        -- eScale as B^j * exp(sum*s).
        have heScale_eq_X : eScale (cfgB P) s X.path.time j =
            (cfgB P ^ j) * Real.exp ((∑ i ∈ Finset.univ.filter
              (fun i : Fin d => i.val < j), X.path.time i) * s) := by
          dsimp [eScale, cutScale, testDeg]
          rw [Finset.prod_mul_distrib]
          congr 1
          · rw [Finset.prod_const, hcardS]
          · rw [← Real.exp_sum]
            congr 1
            rw [Finset.sum_mul]
        have heScale_eq_X0 : eScale (cfgB P) s X0.path.time j =
            (cfgB P ^ j) * Real.exp ((∑ i ∈ Finset.univ.filter
              (fun i : Fin d => i.val < j), X0.path.time i) * s) := by
          dsimp [eScale, cutScale, testDeg]
          rw [Finset.prod_mul_distrib]
          congr 1
          · rw [Finset.prod_const, hcardS]
          · rw [← Real.exp_sum]
            congr 1
            rw [Finset.sum_mul]
        have hBpow_nonneg : 0 ≤ (cfgB P ^ j : ℝ) := pow_nonneg hB0 _
        have hexp_sum_le : Real.exp ((∑ i ∈ Finset.univ.filter
              (fun i : Fin d => i.val < j), X.path.time i) * s) ≤
            Real.exp (((∑ i ∈ Finset.univ.filter
              (fun i : Fin d => i.val < j), X0.path.time i) + 2 * (d : ℝ) * ρ) * s) := by
          apply Real.exp_le_exp.mpr
          have hsum_le_X0 : ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j),
              X.path.time i ≤
              (∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), X0.path.time i) +
                2 * (d : ℝ) * ρ := by
            have hXX0_le : ∀ i : Fin d, i.val < j →
                X.path.time i ≤ X0.path.time i + 2 * ρ := by
              intro i hi
              have htX : X.path.time i ≤ t i + ρ := by
                have hclose := hpl.close X hX i
                have habs := abs_le.mp hclose
                linarith
              have htX0 : t i - ρ ≤ X0.path.time i := by
                have hclose0 := hpl.close X0 hX0 i
                have habs0 := abs_le.mp hclose0
                linarith
              linarith
            have hsum_le_2ρj : ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j),
                X.path.time i ≤
                (∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), X0.path.time i) +
                  2 * ρ * (j : ℝ) := by
              calc ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), X.path.time i ≤
                      ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j),
                        (X0.path.time i + 2 * ρ) := by
                    apply Finset.sum_le_sum
                    intro i hi
                    have hi' : i.val < j := Finset.mem_filter.mp hi |>.2
                    exact hXX0_le i hi'
                _ = (∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), X0.path.time i) +
                      2 * ρ * (j : ℝ) := by
                    rw [Finset.sum_add_distrib]
                    congr 1
                    rw [Finset.sum_const, hcardS]
                    ring
            have hj_le_d : (j : ℝ) ≤ (d : ℝ) := by exact_mod_cast hjLe
            have h2ρj_le : 2 * ρ * (j : ℝ) ≤ 2 * (d : ℝ) * ρ := by
              have h2ρ_nonneg : 0 ≤ 2 * ρ := by positivity
              calc 2 * ρ * (j : ℝ) = (2 * ρ) * (j : ℝ) := by ring
                _ ≤ (2 * ρ) * (d : ℝ) :=
                  mul_le_mul_of_nonneg_left hj_le_d h2ρ_nonneg
                _ = 2 * (d : ℝ) * ρ := by ring
            linarith [hsum_le_2ρj, h2ρj_le]
          calc (∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), X.path.time i) * s ≤
                  ((∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), X0.path.time i) +
                    2 * (d : ℝ) * ρ) * s := by
                apply mul_le_mul_of_nonneg_right hsum_le_X0 hs0
            _ = ((∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < j), X0.path.time i) +
                  2 * (d : ℝ) * ρ) * s := by ring
        have hexp_add2 : Real.exp (((∑ i ∈ Finset.univ.filter
              (fun i : Fin d => i.val < j), X0.path.time i) + 2 * (d : ℝ) * ρ) * s) =
            Real.exp ((∑ i ∈ Finset.univ.filter
              (fun i : Fin d => i.val < j), X0.path.time i) * s) *
              Real.exp (2 * (d : ℝ) * ρ * s) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hBpow_nonneg2 : 0 ≤ (cfgB P ^ j : ℝ) := pow_nonneg hB0 _
        calc eScale (cfgB P) s X.path.time j
              = (cfgB P ^ j) * Real.exp ((∑ i ∈ Finset.univ.filter
                (fun i : Fin d => i.val < j), X.path.time i) * s) := heScale_eq_X
            _ ≤ (cfgB P ^ j) * Real.exp (((∑ i ∈ Finset.univ.filter
                (fun i : Fin d => i.val < j), X0.path.time i) + 2 * (d : ℝ) * ρ) * s) := by
              apply mul_le_mul_of_nonneg_left hexp_sum_le hBpow_nonneg2
            _ = (cfgB P ^ j) * (Real.exp ((∑ i ∈ Finset.univ.filter
                (fun i : Fin d => i.val < j), X0.path.time i) * s) *
                Real.exp (2 * (d : ℝ) * ρ * s)) := by
              rw [hexp_add2]
            _ = ((cfgB P ^ j) * Real.exp ((∑ i ∈ Finset.univ.filter
                (fun i : Fin d => i.val < j), X0.path.time i) * s)) *
                Real.exp (2 * (d : ℝ) * ρ * s) := by
              ring
            _ = eScale (cfgB P) s X0.path.time j * Real.exp (2 * (d : ℝ) * ρ * s) := by
              rw [← heScale_eq_X0]
      -- Cast the pooling ℚ-bound and combine with the uniform piece estimate.
      have hDposR : 0 < (D : ℝ) := by exact_mod_cast hDpos
      have hCnonneg : 0 ≤ (C : ℝ) := Nat.cast_nonneg _
      have hTmid_pos : 0 < Tmid := lt_of_lt_of_le zero_lt_one hTmid_ge_one
      have hTpre_pos : 0 < Tpre := lt_of_lt_of_le zero_lt_one hTpre_ge_one
      have heX0_nonneg : 0 ≤ eScale (cfgB P) s X0.path.time j :=
        md_eScale_nonneg _ _ _ _ hB0
      have hbad_degR : (AffineFamily.degree bad : ℝ) ≤
          (C : ℝ) * (((AffineFamily.degree (poolCarrierFamily pl j) : ℚ)) : ℝ) *
            ((((∑ X ∈ pl, L0 : ℕ)) : ℝ)) / (D : ℝ) := by
        have hQ := hbad_degQ
        have hcast : ((AffineFamily.degree bad : ℚ) : ℝ) ≤
            (((((C : ℚ) * AffineFamily.degree (poolCarrierFamily pl j) *
              ((∑ X ∈ pl, L0 : ℕ) : ℚ) / (D : ℚ) : ℚ))) : ℝ) := by
          exact_mod_cast hQ
        simpa [push_cast] using hcast
      have hE32_pos : 0 < Real.exp ((ξ / 32) * s) := Real.exp_pos _
      have hE2d_pos : 0 < Real.exp (2 * (d : ℝ) * ρ * s) := Real.exp_pos _
      have hpiece_unif : ∀ X ∈ pl, ((((AffineFamily.degree (pieceCarrierFamily X j) : ℚ))) : ℝ) ≤
          eScale (cfgB P) s X0.path.time j * Real.exp (2 * (d : ℝ) * ρ * s) *
            Real.exp ((ξ / 32) * s) := by
        intro X hX
        calc ((((AffineFamily.degree (pieceCarrierFamily X j) : ℚ))) : ℝ)
              ≤ eScale (cfgB P) s X.path.time j * Real.exp ((ξ / 32) * s) :=
              hdeg_piece_le X hX
          _ ≤ (eScale (cfgB P) s X0.path.time j * Real.exp (2 * (d : ℝ) * ρ * s)) *
              Real.exp ((ξ / 32) * s) := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hE32_pos)
              exact hescale_close X hX
          _ = eScale (cfgB P) s X0.path.time j * Real.exp (2 * (d : ℝ) * ρ * s) *
              Real.exp ((ξ / 32) * s) := by ring
      have hpool_le : ((((AffineFamily.degree (poolCarrierFamily pl j) : ℚ))) : ℝ) ≤
          (pl.card : ℝ) * (eScale (cfgB P) s X0.path.time j *
            Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s)) := by
        calc ((((AffineFamily.degree (poolCarrierFamily pl j) : ℚ))) : ℝ)
              ≤ ∑ X ∈ pl, ((((AffineFamily.degree (pieceCarrierFamily X j) : ℚ))) : ℝ) :=
              hdeg_pool_le
          _ ≤ ∑ X ∈ pl, (eScale (cfgB P) s X0.path.time j *
              Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s)) := by
              apply Finset.sum_le_sum
              intro X hX
              exact hpiece_unif X hX
          _ = (pl.card : ℝ) * (eScale (cfgB P) s X0.path.time j *
              Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      -- Scalar facts re-derived inside this block.
      have hcard_le : (pl.card : ℝ) ≤ Real.exp (θ₁ * s) := hpl.count
      have hcard_nonneg : 0 ≤ (pl.card : ℝ) := Nat.cast_nonneg _
      have hL0_le3 : (L0 : ℝ) ≤ 3 * Tpre := by
        have hceil_le : (⌈Tpre⌉₊ : ℝ) ≤ Tpre + 1 :=
          md_ceil_le_add_one _ (le_of_lt hTpre_pos)
        have hL0_eq : (L0 : ℝ) = (⌈Tpre⌉₊ : ℝ) + 1 := by
          dsimp [L0]
          push_cast
          ring
        linarith [hTpre_ge_one]
      have hsum_eq : ((((∑ X ∈ pl, L0 : ℕ))) : ℝ) = (pl.card : ℝ) * (L0 : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      have hTpre_eq : Tpre = Tmid * Real.exp ((ρ + θ₁ - ξ / 2) * s) := by
        dsimp [Tpre, Tmid]
        have hshift := md_testDeg_shift (cfgB P) s (b - ξ / 2) (b - ξ + ρ + θ₁)
        rw [show (b - ξ + ρ + θ₁ - (b - ξ / 2)) = ρ + θ₁ - ξ / 2 by ring] at hshift
        exact hshift
      have hTmid_eq : Tmid = Tpre * Real.exp ((ξ / 2 - ρ - θ₁) * s) := by
        dsimp [Tmid, Tpre]
        have hshift := md_testDeg_shift (cfgB P) s (b - ξ + ρ + θ₁) (b - ξ / 2)
        rw [show (b - ξ / 2 - (b - ξ + ρ + θ₁)) = ξ / 2 - ρ - θ₁ by ring] at hshift
        exact hshift
      have hExp32 : (100 * ((C : ℝ) + 2) ^ 2 + 100 : ℝ) ≤ Real.exp ((ξ / 32) * s) :=
        hsE s hsE'
      have h6CC1_le : 6 * (C : ℝ) * ((C : ℝ) + 1) ≤
          100 * ((C : ℝ) + 2) ^ 2 + 100 :=
        md_const_le_large3 _ hCnonneg
      have h2C1_le : 2 * ((C : ℝ) + 1) ≤ 100 * ((C : ℝ) + 2) ^ 2 + 100 :=
        md_const_2C1_le _ hCnonneg
      have hρ8 : ρ ≤ ξ / 8 := hρ0_le
      have hθ32 : θ₁ ≤ ξ / 32 := hθ₁ξ
      have hρd : ρ ≤ ξ / (32 * (d : ℝ)) := le_trans hρ (min_le_right _ _)
      have h2dρ_le : 2 * (d : ℝ) * ρ ≤ ξ / 16 := by
        have hdpos : 0 < (d : ℝ) := hdposR
        have h1 : (d : ℝ) * ρ ≤ ξ / 32 := by
          calc (d : ℝ) * ρ = ρ * (d : ℝ) := by ring
            _ ≤ (ξ / (32 * (d : ℝ))) * (d : ℝ) :=
              mul_le_mul_of_nonneg_right hρd (le_of_lt hdpos)
            _ = ξ / 32 := by
              field_simp
        linarith
      have hGap1 : ξ / 32 ≤ ξ / 2 - ρ - θ₁ := by linarith
      have hExp_gap1 : Real.exp ((ξ / 32) * s) ≤ Real.exp ((ξ / 2 - ρ - θ₁) * s) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right hGap1 hs0
      have h2C1_le_Tmid : 2 * ((C : ℝ) + 1) ≤ Tmid := by
        calc 2 * ((C : ℝ) + 1) ≤ 100 * ((C : ℝ) + 2) ^ 2 + 100 := h2C1_le
          _ ≤ Real.exp ((ξ / 32) * s) := hExp32
          _ ≤ Real.exp ((ξ / 2 - ρ - θ₁) * s) := hExp_gap1
          _ ≤ Tmid := by
            rw [hTmid_eq]
            exact le_mul_of_one_le_left (Real.exp_nonneg _) hTpre_ge_one
      have hDge_half : Tmid / (2 * ((C : ℝ) + 1)) ≤ (D : ℝ) := by
        have hC1pos2 : 0 < 2 * ((C : ℝ) + 1) := by positivity
        have hC1ne : ((C : ℝ) + 1) ≠ 0 := ne_of_gt hC1posR
        have hDge' : Tmid / ((C : ℝ) + 1) - 1 ≤ (D : ℝ) := by
          have hnonneg : 0 ≤ Tmid / ((C : ℝ) + 1) := by positivity
          have hfloor := md_floor_sub_one_le (Tmid / ((C : ℝ) + 1)) hnonneg
          simpa [D] using hfloor
        have hge2 : (2 : ℝ) ≤ Tmid / ((C : ℝ) + 1) := by
          rw [le_div_iff₀ hC1posR]
          linarith [h2C1_le_Tmid]
        have hsplit : Tmid / ((C : ℝ) + 1) =
            Tmid / (2 * ((C : ℝ) + 1)) + Tmid / (2 * ((C : ℝ) + 1)) := by
          field_simp
          ring
        linarith
      -- Reduce the bad-degree bound to a scalar bracket.
      have hS_le : ((((∑ X ∈ pl, L0 : ℕ))) : ℝ) ≤ (pl.card : ℝ) * (3 * Tpre) := by
        rw [hsum_eq]
        apply mul_le_mul_of_nonneg_left hL0_le3 hcard_nonneg
      have hCoeff_nonneg : 0 ≤ (C : ℝ) * (pl.card : ℝ) / (D : ℝ) *
          Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s) := by
        apply mul_nonneg
        · apply mul_nonneg
          · apply div_nonneg
            · apply mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
            · apply Nat.cast_nonneg _
          · exact Real.exp_nonneg _
        · exact Real.exp_nonneg _
      have hbad_le_mid : (AffineFamily.degree bad : ℝ) ≤
          eScale (cfgB P) s X0.path.time j *
            ((C : ℝ) * (pl.card : ℝ) * ((((∑ X ∈ pl, L0 : ℕ))) : ℝ) / (D : ℝ) *
              Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s)) := by
        have hpool_nonneg : 0 ≤ ((((AffineFamily.degree (poolCarrierFamily pl j) : ℚ))) : ℝ) := by
          have hQnonneg : 0 ≤ AffineFamily.degree (poolCarrierFamily pl j) := by
            dsimp [AffineFamily.degree]
            apply Finset.sum_nonneg
            intro V hV
            have hprime : V.ideal.IsPrime := (hFpure V hV).1
            have htop : V.ideal ≠ ⊤ := hprime.ne_top
            exact le_trans (by decide : (0 : ℚ) ≤ 1) (AffineVariety.one_le_degree V htop)
          exact_mod_cast hQnonneg
        have hKS_nonneg : 0 ≤ (C : ℝ) * ((((∑ X ∈ pl, L0 : ℕ))) : ℝ) / (D : ℝ) := by
          apply div_nonneg
          · apply mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          · apply Nat.cast_nonneg _
        calc (AffineFamily.degree bad : ℝ)
              ≤ (C : ℝ) * ((((AffineFamily.degree (poolCarrierFamily pl j) : ℚ))) : ℝ) *
                ((((∑ X ∈ pl, L0 : ℕ))) : ℝ) / (D : ℝ) := hbad_degR
          _ = ((C : ℝ) * ((((∑ X ∈ pl, L0 : ℕ))) : ℝ) / (D : ℝ)) *
              ((((AffineFamily.degree (poolCarrierFamily pl j) : ℚ))) : ℝ) := by ring
          _ ≤ ((C : ℝ) * ((((∑ X ∈ pl, L0 : ℕ))) : ℝ) / (D : ℝ)) *
              ((pl.card : ℝ) * (eScale (cfgB P) s X0.path.time j *
                Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s))) :=
              mul_le_mul_of_nonneg_left hpool_le hKS_nonneg
          _ = eScale (cfgB P) s X0.path.time j *
              ((C : ℝ) * (pl.card : ℝ) * ((((∑ X ∈ pl, L0 : ℕ))) : ℝ) / (D : ℝ) *
                Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s)) := by ring
      -- The scalar bracket decays to exp(-ξ/8·s).
      have hbracket : (C : ℝ) * (pl.card : ℝ) * ((((∑ X ∈ pl, L0 : ℕ))) : ℝ) / (D : ℝ) *
          Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s) ≤
          Real.exp (-ξ / 8 * s) := by
        have hEneg_nonneg : 0 ≤ Real.exp (-ξ / 8 * s) := Real.exp_nonneg _
        have h6_le_exp32 : 6 * (C : ℝ) * ((C : ℝ) + 1) ≤ Real.exp ((ξ / 32) * s) :=
          le_trans h6CC1_le hExp32
        -- card² via the pool-count bound.
        have hcard2_le : (pl.card : ℝ) * (pl.card : ℝ) ≤
            Real.exp (θ₁ * s) * Real.exp (θ₁ * s) :=
          mul_le_mul hcard_le hcard_le hcard_nonneg (le_of_lt (Real.exp_pos _))
        have hcard_exp2 : Real.exp (θ₁ * s) * Real.exp (θ₁ * s) =
            Real.exp (2 * θ₁ * s) := by
          rw [← Real.exp_add]
          congr 1
          ring
        -- Combine card·S into card²·3·Tpre.
        have hCS_le : (C : ℝ) * (pl.card : ℝ) * ((((∑ X ∈ pl, L0 : ℕ))) : ℝ) ≤
            (C : ℝ) * ((pl.card : ℝ) * (pl.card : ℝ)) * (3 * Tpre) := by
          calc (C : ℝ) * (pl.card : ℝ) * ((((∑ X ∈ pl, L0 : ℕ))) : ℝ)
                ≤ (C : ℝ) * (pl.card : ℝ) * ((pl.card : ℝ) * (3 * Tpre)) := by
                apply mul_le_mul_of_nonneg_left hS_le
                apply mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
            _ = (C : ℝ) * ((pl.card : ℝ) * (pl.card : ℝ)) * (3 * Tpre) := by ring
        -- Clear the D denominator: suffices to show numerator ≤ Eneg·D.
        have hDposR' : 0 < (D : ℝ) := hDposR
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
          div_le_iff₀ hDposR']
        -- Now goal: C·card·S·E2d·E32 ≤ Eneg·D; bound D below by Tmid/(2(C+1)).
        have hEneg_pos : 0 < Real.exp (-ξ / 8 * s) := Real.exp_pos _
        have hEhalf_nonneg : 0 ≤ Tmid / (2 * ((C : ℝ) + 1)) := by
          apply div_nonneg (le_of_lt hTmid_pos)
          apply mul_nonneg (by norm_num) (le_trans (Nat.cast_nonneg _) (le_add_of_nonneg_right zero_le_one))
        suffices hmain : (C : ℝ) * (pl.card : ℝ) * ((((∑ X ∈ pl, L0 : ℕ))) : ℝ) *
            Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s) ≤
            Real.exp (-ξ / 8 * s) * (Tmid / (2 * ((C : ℝ) + 1))) by
          calc (C : ℝ) * (pl.card : ℝ) * ((((∑ X ∈ pl, L0 : ℕ))) : ℝ) *
                Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s)
                ≤ Real.exp (-ξ / 8 * s) * (Tmid / (2 * ((C : ℝ) + 1))) := hmain
            _ ≤ Real.exp (-ξ / 8 * s) * (D : ℝ) :=
                mul_le_mul_of_nonneg_left hDge_half (le_of_lt hEneg_pos)
            _ = Real.exp (-ξ / 8 * s) * (D : ℝ) := by ring
        -- Prove hmain via Tpre/Tmid gap.
        have hTmid_ne : Tmid ≠ 0 := ne_of_gt hTmid_pos
        have hC1pos2 : 0 < 2 * ((C : ℝ) + 1) := by positivity
        -- Rewrite S and Tpre in terms of Tmid.
        have hnum_le : (C : ℝ) * (pl.card : ℝ) * ((((∑ X ∈ pl, L0 : ℕ))) : ℝ) *
            Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s) ≤
            (C : ℝ) * ((pl.card : ℝ) * (pl.card : ℝ)) * (3 * Tmid *
              Real.exp ((ρ + θ₁ - ξ / 2) * s)) *
              Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s) := by
          have h1 : (C : ℝ) * (pl.card : ℝ) * ((((∑ X ∈ pl, L0 : ℕ))) : ℝ) ≤
              (C : ℝ) * ((pl.card : ℝ) * (pl.card : ℝ)) * (3 * Tpre) := hCS_le
          have hpos2 : 0 ≤ Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s) := by
            apply mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
          calc (C : ℝ) * (pl.card : ℝ) * ((((∑ X ∈ pl, L0 : ℕ))) : ℝ) *
                Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s)
                = ((C : ℝ) * (pl.card : ℝ) * ((((∑ X ∈ pl, L0 : ℕ))) : ℝ)) *
                  (Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s)) := by ring
            _ ≤ ((C : ℝ) * ((pl.card : ℝ) * (pl.card : ℝ)) * (3 * Tpre)) *
                  (Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s)) :=
                mul_le_mul_of_nonneg_right h1 hpos2
            _ = (C : ℝ) * ((pl.card : ℝ) * (pl.card : ℝ)) * (3 * Tmid *
                  Real.exp ((ρ + θ₁ - ξ / 2) * s)) *
                  Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s) := by
                rw [hTpre_eq]
                ring
        -- It remains to bound the right-hand side by Eneg·Tmid/(2(C+1)).
        have ha_ge : ξ / 32 ≤ 11 * ξ / 32 - ρ - 3 * θ₁ - 2 * (d : ℝ) * ρ := by
          linarith [hρ8, hθ32, h2dρ_le]
        have hexp_a_ge : Real.exp ((ξ / 32) * s) ≤
            Real.exp ((11 * ξ / 32 - ρ - 3 * θ₁ - 2 * (d : ℝ) * ρ) * s) := by
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_right ha_ge hs0
        have h6_le_expa : 6 * (C : ℝ) * ((C : ℝ) + 1) ≤
            Real.exp ((11 * ξ / 32 - ρ - 3 * θ₁ - 2 * (d : ℝ) * ρ) * s) :=
          le_trans h6_le_exp32 hexp_a_ge
        have hcard2_exp_le : (pl.card : ℝ) * (pl.card : ℝ) ≤ Real.exp (2 * θ₁ * s) :=
          le_trans hcard2_le (le_of_eq hcard_exp2)
        have hexp_all_eq : Real.exp (2 * θ₁ * s) *
            (Real.exp ((ρ + θ₁ - ξ / 2) * s) *
              (Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s))) =
            Real.exp ((3 * θ₁ + ρ + 2 * (d : ℝ) * ρ - 15 * ξ / 32) * s) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        have hexp_final_eq : Real.exp ((11 * ξ / 32 - ρ - 3 * θ₁ - 2 * (d : ℝ) * ρ) * s) *
            Real.exp ((3 * θ₁ + ρ + 2 * (d : ℝ) * ρ - 15 * ξ / 32) * s) =
            Real.exp (-ξ / 8 * s) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hRHS1_le : (C : ℝ) * ((pl.card : ℝ) * (pl.card : ℝ)) *
            (3 * Tmid * Real.exp ((ρ + θ₁ - ξ / 2) * s)) *
            Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s) ≤
            Real.exp (-ξ / 8 * s) * (Tmid / (2 * ((C : ℝ) + 1))) := by
          have hEq1 : (C : ℝ) * ((pl.card : ℝ) * (pl.card : ℝ)) *
              (3 * Tmid * Real.exp ((ρ + θ₁ - ξ / 2) * s)) *
              Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s) =
              Tmid * (3 * (C : ℝ) * ((pl.card : ℝ) * (pl.card : ℝ)) *
                (Real.exp ((ρ + θ₁ - ξ / 2) * s) *
                  (Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s)))) := by
            ring
          have hEq2 : Real.exp (-ξ / 8 * s) * (Tmid / (2 * ((C : ℝ) + 1))) =
              Tmid * (Real.exp (-ξ / 8 * s) / (2 * ((C : ℝ) + 1))) := by
            ring
          rw [hEq1, hEq2]
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hTmid_pos)
          have hEq3 : 3 * (C : ℝ) * ((pl.card : ℝ) * (pl.card : ℝ)) *
              (Real.exp ((ρ + θ₁ - ξ / 2) * s) *
                (Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s))) ≤
              Real.exp (-ξ / 8 * s) / (2 * ((C : ℝ) + 1)) := by
            rw [le_div_iff₀ hC1pos2]
            have hEq4 : 3 * (C : ℝ) * ((pl.card : ℝ) * (pl.card : ℝ)) *
                (Real.exp ((ρ + θ₁ - ξ / 2) * s) *
                  (Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s))) *
                (2 * ((C : ℝ) + 1)) =
                6 * (C : ℝ) * ((C : ℝ) + 1) * ((pl.card : ℝ) * (pl.card : ℝ)) *
                  (Real.exp ((ρ + θ₁ - ξ / 2) * s) *
                    (Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s))) := by
              ring
            rw [hEq4]
            have h6C_nonneg : 0 ≤ 6 * (C : ℝ) * ((C : ℝ) + 1) := by positivity
            have hexp_mid_nonneg : 0 ≤ Real.exp ((ρ + θ₁ - ξ / 2) * s) *
                (Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s)) := by
              positivity
            calc 6 * (C : ℝ) * ((C : ℝ) + 1) * ((pl.card : ℝ) * (pl.card : ℝ)) *
                  (Real.exp ((ρ + θ₁ - ξ / 2) * s) *
                    (Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s)))
                ≤ 6 * (C : ℝ) * ((C : ℝ) + 1) * Real.exp (2 * θ₁ * s) *
                  (Real.exp ((ρ + θ₁ - ξ / 2) * s) *
                    (Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s))) := by
                  apply mul_le_mul_of_nonneg_right _ hexp_mid_nonneg
                  apply mul_le_mul_of_nonneg_left hcard2_exp_le h6C_nonneg
              _ = 6 * (C : ℝ) * ((C : ℝ) + 1) *
                  (Real.exp (2 * θ₁ * s) *
                    (Real.exp ((ρ + θ₁ - ξ / 2) * s) *
                      (Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s)))) := by
                ring
              _ = 6 * (C : ℝ) * ((C : ℝ) + 1) *
                  Real.exp ((3 * θ₁ + ρ + 2 * (d : ℝ) * ρ - 15 * ξ / 32) * s) := by
                rw [hexp_all_eq]
              _ ≤ Real.exp ((11 * ξ / 32 - ρ - 3 * θ₁ - 2 * (d : ℝ) * ρ) * s) *
                  Real.exp ((3 * θ₁ + ρ + 2 * (d : ℝ) * ρ - 15 * ξ / 32) * s) :=
                mul_le_mul_of_nonneg_right h6_le_expa (Real.exp_nonneg _)
              _ = Real.exp (-ξ / 8 * s) := hexp_final_eq
          exact hEq3
        exact le_trans hnum_le hRHS1_le
      calc (AffineFamily.degree bad : ℝ)
            ≤ eScale (cfgB P) s X0.path.time j *
              ((C : ℝ) * (pl.card : ℝ) * ((((∑ X ∈ pl, L0 : ℕ))) : ℝ) / (D : ℝ) *
                Real.exp (2 * (d : ℝ) * ρ * s) * Real.exp ((ξ / 32) * s)) := hbad_le_mid
        _ ≤ eScale (cfgB P) s X0.path.time j * Real.exp (-ξ / 8 * s) :=
            mul_le_mul_of_nonneg_left hbracket heX0_nonneg
    have hEdegR : ∀ f ∈ E, f ∈ (AffineFamily.locus (poolCarrierFamily pl j)).ideal ∧
        (f.totalDegree : ℝ) ≤ Tmid := by
      intro f hf
      obtain ⟨hfmem, hfdeg⟩ := hEdeg f hf
      refine ⟨hfmem, ?_⟩
      have h1 : (f.totalDegree : ℝ) ≤ (D : ℝ) := by exact_mod_cast hfdeg
      have h2 : (D : ℝ) ≤ Tmid / ((C : ℝ) + 1) := by
        have hle : (D : ℝ) ≤ Tmid / ((C : ℝ) + 1) := Nat.floor_le
          (by positivity)
        exact hle
      have h3 : Tmid / ((C : ℝ) + 1) ≤ Tmid := by
        have hC1ge1 : 1 ≤ (C : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
        exact div_le_self hTmid_nonneg hC1ge1
      exact le_trans h1 (le_trans h2 h3)
    have hgdegR : (g.totalDegree : ℝ) ≤ Tmid := by
      have h1 : (g.totalDegree : ℝ) ≤ ((C * D : ℕ) : ℝ) := by exact_mod_cast hgdeg_nat
      have h2 : ((C * D : ℕ) : ℝ) = (C : ℝ) * (D : ℝ) := by push_cast; ring
      rw [h2] at h1
      have hDle : (D : ℝ) ≤ Tmid / ((C : ℝ) + 1) := Nat.floor_le (by positivity)
      have hCle : (C : ℝ) * (Tmid / ((C : ℝ) + 1)) ≤ Tmid := by
        have hC1ge : (C : ℝ) ≤ (C : ℝ) + 1 := le_add_of_nonneg_right zero_le_one
        calc (C : ℝ) * (Tmid / ((C : ℝ) + 1)) = Tmid * ((C : ℝ) / ((C : ℝ) + 1)) := by
                ring
          _ ≤ Tmid * 1 := by
              apply mul_le_mul_of_nonneg_left _ hTmid_nonneg
              rw [div_le_one hC1posR]
              exact hC1ge
          _ = Tmid := by ring
      calc (g.totalDegree : ℝ) ≤ (C : ℝ) * (D : ℝ) := h1
        _ ≤ (C : ℝ) * (Tmid / ((C : ℝ) + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            exact hDle
        _ ≤ Tmid := hCle
    have hgspanR : g ∈ Submodule.span ℂ (TrackA.jacobianMinors E j) := by
      have hj_eq : d - (d - j) = j := Nat.sub_sub_self hjLe
      have hspan := hgspan
      simpa [hj_eq] using hspan
    have huniqR : ∀ y : Point d, MvPolynomial.eval y g ≠ 0 →
        ∀ Z ∈ poolCarrierFamily pl j, ∀ Z' ∈ poolCarrierFamily pl j,
          y ∈ Z → y ∈ Z' → Z = Z' := by
      intro y hy Z hZ Z' hZ' hyZ hyZ'
      have hy_locus : y ∈ (AffineFamily.locus (poolCarrierFamily pl j)).points := by
        rw [AffineFamily.points_locus]
        exact Set.mem_iUnion₂.mpr ⟨Z, hZ, hyZ⟩
      obtain ⟨_, _, _, hunique⟩ := hgunique y hy_locus hy
      exact hunique Z hZ Z' hZ' hyZ hyZ'
    exact ⟨bad, E, g, hbad_sub, hbad_perX, hEdegR, hgdegR, hgspanR, hgproper, huniqR,
      hTmid_ge_one⟩
  · have hBzero : cfgB P = 0 := le_antisymm (le_of_not_gt hBpos) hB0
    have hTzero : testDeg (cfgB P) s b = 0 := by
      unfold testDeg
      rw [hBzero]
      ring
    rw [hTzero] at hT
    norm_num at hT

end
end DistinctDistances.TrackD
