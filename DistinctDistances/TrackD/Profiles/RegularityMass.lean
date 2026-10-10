import DistinctDistances.TrackD.Profiles.Budget
import DistinctDistances.TrackD.Profiles.PoolFamilies
import DistinctDistances.TrackD.Profiles.ProfileMargins

namespace DistinctDistances.TrackD
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

theorem regularity_exp_threshold (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ s₀ : ℝ, ∀ s ≥ s₀, Real.exp (-a * s) ≤ ε := by
  refine ⟨-Real.log ε / a, ?_⟩
  intro s hs
  have hm := (div_le_iff₀ ha).mp hs
  have he : -a * s ≤ Real.log ε := by linarith
  exact (Real.exp_le_exp.mpr he).trans_eq (Real.exp_log hε)

theorem regularity_scale_product (B s : ℝ) (t : Fin d → ℝ) (j : ℕ) :
    eScale B s t j * tailScale B s t j = B ^ d * Real.exp ((∑ i, t i) * s) := by
  unfold eScale tailScale
  simp only [Finset.prod_filter]
  rw [← Finset.prod_mul_distrib]
  have hprod :
      (∏ i : Fin d, (if i.val < j then cutScale B s t i else 1) *
        (if j ≤ i.val then cutScale B s t i else 1)) = ∏ i : Fin d, cutScale B s t i := by
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : i.val < j
    · simp [h, Nat.not_le.mpr h]
    · simp [h, Nat.le_of_not_gt h]
  rw [hprod]
  simp only [cutScale, testDeg, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Real.exp_sum, ← Finset.sum_mul]

theorem regularity_B_pow (hd : 0 < d) (P : Finset (Pt d)) : cfgB P ^ d = cfgN P := by
  unfold cfgB cfgN
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : (1 : ℝ) / (d : ℝ) * (d : ℝ) = 1 := by field_simp
  rw [he, Real.rpow_one]

theorem regularity_family_degree_mono (F G : AffineFamily.Family d) (hsub : F ⊆ G)
    (hpure : ∀ Z ∈ G, Z.IsIrreducible) : (AffineFamily.degree F : ℝ) ≤ AffineFamily.degree G := by
  have hQ : AffineFamily.degree F ≤ AffineFamily.degree G := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro Z hZ hnot
    exact (by norm_num : (0 : ℚ) ≤ 1).trans
      (AffineVariety.one_le_degree Z (hpure Z hZ).ne_top)
  exact_mod_cast hQ

/-- A degree exceptional set is charged only against X's own later cuts. -/
theorem regularity_bad_mass (P : Finset (Pt d)) (X : Piece d) (j : ℕ)
    (bad : AffineFamily.Family d) (q a γ θ : ℝ) (hd : 0 < d) (hs : 0 ≤ X.width)
    (hB : 0 ≤ cfgB P) (hX : PieceGood P θ q 1 X)
    (hdeg : (AffineFamily.degree bad : ℝ) ≤
      eScale (cfgB P) X.width X.path.time j * Real.exp (-a * X.width))
    (hbad : ∀ Z ∈ bad, Z.IsIrreducible)
    (hsum : ∑ i, X.path.time i ≤ γ)
    (hmass : ∀ A : AffineFamily.Family d,
      (∀ Z ∈ A, X.path.IsCarrier j Z ∧ ∃ x ∈ X.pts, toC x ∈ Z) →
      ((X.pts.filter (fun x => ∃ Z ∈ A, toC x ∈ Z)).card : ℝ) ≤
        (∑ Z ∈ A, (Z.degree : ℝ)) * tailScale (cfgB P) X.width X.path.time j *
          Real.exp (θ * X.width)) :
    ((X.pts.filter (fun x => ∃ Z ∈ X.path.localCarriers j (toC x), Z ∈ bad)).card : ℝ) ≤
      X.pts.card * Real.exp ((γ + 2 * θ - a) * X.width) := by
  let A := bad ∩ pieceCarrierFamily X j
  have hA : ∀ Z ∈ A, X.path.IsCarrier j Z ∧ ∃ x ∈ X.pts, toC x ∈ Z := by
    intro Z hZ
    exact (mem_pieceCarrierFamily X j Z).mp (Finset.mem_inter.mp hZ).2
  have hEq : X.pts.filter (fun x => ∃ Z ∈ X.path.localCarriers j (toC x), Z ∈ bad) =
      X.pts.filter (fun x => ∃ Z ∈ A, toC x ∈ Z) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, Z, ⟨hcarrier, hxZ⟩, hbadZ⟩
      exact ⟨hx, Z, Finset.mem_inter.mpr ⟨hbadZ,
        (mem_pieceCarrierFamily X j Z).mpr ⟨hcarrier, x, hx, hxZ⟩⟩, hxZ⟩
    · rintro ⟨hx, Z, hZA, hxZ⟩
      exact ⟨hx, Z, ⟨(hA Z hZA).1, hxZ⟩, (Finset.mem_inter.mp hZA).1⟩
  have hdegA := regularity_family_degree_mono A bad (Finset.inter_subset_left) hbad
  have hsumA : (∑ Z ∈ A, (Z.degree : ℝ)) = (AffineFamily.degree A : ℝ) := by
    simp [AffineFamily.degree]
  have htail : 0 ≤ tailScale (cfgB P) X.width X.path.time j := by
    unfold tailScale cutScale testDeg
    apply Finset.prod_nonneg
    intro i hi
    exact mul_nonneg hB (Real.exp_nonneg _)
  have hN : 0 ≤ cfgN P := by unfold cfgN; positivity
  rw [hEq]
  calc
    _ ≤ (∑ Z ∈ A, (Z.degree : ℝ)) * tailScale (cfgB P) X.width X.path.time j *
        Real.exp (θ * X.width) := hmass A hA
    _ ≤ (eScale (cfgB P) X.width X.path.time j * Real.exp (-a * X.width)) *
        tailScale (cfgB P) X.width X.path.time j * Real.exp (θ * X.width) := by
      rw [hsumA]
      gcongr
      exact hdegA.trans hdeg
    _ = cfgN P * Real.exp (((∑ i, X.path.time i) + θ - a) * X.width) := by
      rw [show (eScale (cfgB P) X.width X.path.time j * Real.exp (-a * X.width)) *
          tailScale (cfgB P) X.width X.path.time j * Real.exp (θ * X.width) =
          (eScale (cfgB P) X.width X.path.time j * tailScale (cfgB P) X.width X.path.time j) *
            (Real.exp (-a * X.width) * Real.exp (θ * X.width)) by ring]
      rw [regularity_scale_product, regularity_B_pow hd P, ← Real.exp_add, mul_assoc,
        ← Real.exp_add]
      congr 2
      ring
    _ ≤ cfgN P * Real.exp ((γ + θ - a) * X.width) := by
      gcongr
    _ = (cfgN P * Real.exp (-θ * X.width)) *
        Real.exp ((γ + 2 * θ - a) * X.width) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hX.size (Real.exp_nonneg _)

theorem regularity_cut_count (X : Piece d) (j : ℕ)
    (f : AffineVariety d → Poly d) (g : Poly d) (bad : AffineFamily.Family d)
    (ε δ : ℝ)
    (hzero : ∀ x ∈ X.pts,
      (∃ Z ∈ X.path.localCarriers j (toC x),
        f Z ∉ Z.ideal ∧ MvPolynomial.eval (toC x) (f Z) = 0) →
      MvPolynomial.eval (toC x) g = 0)
    (hproper : ∀ Z ∈ pieceCarrierFamily X j, Z ∉ bad → g ∉ Z.ideal)
    (hbad : ((X.pts.filter (fun x =>
      ∃ Z ∈ X.path.localCarriers j (toC x), Z ∈ bad)).card : ℝ) ≤ ε * X.pts.card)
    (hcap : ((X.path.captured j X.pts g).card : ℝ) ≤ δ * X.pts.card) :
    ((X.pts.filter (fun x => ∃ Z ∈ X.path.localCarriers j (toC x),
      f Z ∉ Z.ideal ∧ MvPolynomial.eval (toC x) (f Z) = 0)).card : ℝ) ≤
        (ε + δ) * X.pts.card := by
  let B := X.pts.filter (fun x => ∃ Z ∈ X.path.localCarriers j (toC x), Z ∈ bad)
  let C := X.pts.filter (fun x => ∃ Z ∈ X.path.localCarriers j (toC x),
    f Z ∉ Z.ideal ∧ MvPolynomial.eval (toC x) (f Z) = 0)
  have hsub : C ⊆ B ∪ X.path.captured j X.pts g := by
    intro x hx
    obtain ⟨hxX, hcut⟩ := Finset.mem_filter.mp hx
    by_cases hb : ∃ Z ∈ X.path.localCarriers j (toC x), Z ∈ bad
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxX, hb⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hxX, hzero x hxX hcut, ?_⟩
      intro Z hZ
      exact hproper Z ((mem_pieceCarrierFamily X j Z).mpr
        ⟨hZ.1, x, hxX, hZ.2⟩) (fun h => hb ⟨Z, hZ, h⟩)
  have hcard : (C.card : ℝ) ≤ B.card + (X.path.captured j X.pts g).card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hb : (B.card : ℝ) ≤ ε * X.pts.card := hbad
  change (C.card : ℝ) ≤ _
  linarith

end
end DistinctDistances.TrackD
