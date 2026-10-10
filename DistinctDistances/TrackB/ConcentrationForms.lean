import DistinctDistances.TrackB.UniformCompletion
import DistinctDistances.Bridges.AmbientHilbert
import DistinctDistances.TrackB.PolynomialFlatSupport

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators

/-- conc:theorem.endpoints, concentration.tex:72–74 and 1036–1039. The complete
case (a) range required by TrackE/GlobalConcentration.lean:30–37 includes both endpoints. -/
theorem uniform_concentration_all_dimensions (e : ℕ) (he : 3 ≤ e)
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ B : ℝ, 0 < B ∧ ∀ (C : SkewCoordinates e) (A : ℝ), 1 ≤ A →
      ∀ P : Finset (ProjectivePoint (e + e)),
        (∀ p ∈ P, p ∈ affineParameters e) → HasSeparators P (C0 * A) →
        HasIsotropicCap P (C0 * A ^ (e - 2)) → (P.card : ℝ) ≤ C0 * A ^ (e - 1) →
        ∀ (V : AffineVariety (skewDim e)) (h : ℕ), V.IsIrreducible → h ≤ e - 1 →
          V.dimension = flatDim e + h →
          (containedFlatCount C P V : ℝ) ≤ B * (V.degree : ℝ) * A ^ h := by
  classical
  obtain ⟨Bmain, hBmain, hmain⟩ := uniform_concentration e he C0 hC0
  let B : ℝ := max (max Bmain C0) 1
  have hBone : 1 ≤ B := le_max_right _ _
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hBone
  have hmainB : Bmain ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hC0B : C0 ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨B, hBpos, ?_⟩
  intro C A hA P hP hsep hcap hcard V h hV hh hdim
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hdegone := HighCarrier.irreducible_degree_one_le V hV
  have hdeg : 0 < (V.degree : ℝ) := lt_of_lt_of_le (by norm_num) hdegone
  have hpow : 0 ≤ A ^ h := (pow_pos hApos h).le
  by_cases htop : h = e - 1
  · have hc : (containedFlatCount C P V : ℝ) ≤ (P.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hBd : B ≤ B * (V.degree : ℝ) := by nlinarith
    calc
      (containedFlatCount C P V : ℝ) ≤ (P.card : ℝ) := hc
      _ ≤ C0 * A ^ h := by simpa [htop] using hcard
      _ ≤ B * A ^ h := mul_le_mul_of_nonneg_right hC0B hpow
      _ ≤ B * (V.degree : ℝ) * A ^ h := mul_le_mul_of_nonneg_right hBd hpow
  · have hlt : h < e - 1 := by omega
    have hchoose : skewDim e = flatDim e + (e - 1) := by
      simp only [skewDim, flatDim]
      rw [show e = (e - 1) + 1 by omega, Nat.choose_succ_succ']
      simp [Nat.choose_one_right, Nat.add_comm]
    have hproper : V ≠ AffineVariety.whole := by
      intro hwhole
      rw [hwhole, Bridges.affine_whole_dimension, hchoose] at hdim
      omega
    have hallowed : AllowedCarrier true A C0 V := ⟨hV, hproper, Or.inl rfl⟩
    by_cases hz : h = 0
    · have hprof := concentrationProfile_endpoints C he P hP true A C0 hA hC0
        (by intro _; exact hcard)
      have hnorm := HighCarrier.profile_contains_carrier C P true A C0 hA V h hlt
        hallowed hdim
      have hprofh : concentrationProfile C P true A C0 h ≤ 1 := by
        simpa [hz] using hprof.2.1
      have hratio : (containedFlatCount C P V : ℝ) / (V.degree : ℝ) ≤ 1 := by
        simpa [hz, normalizedFlatCount] using hnorm.trans hprofh
      have hc : (containedFlatCount C P V : ℝ) ≤ (V.degree : ℝ) := by
        simpa using (div_le_iff₀ hdeg).mp hratio
      calc
        (containedFlatCount C P V : ℝ) ≤ (V.degree : ℝ) := hc
        _ ≤ B * (V.degree : ℝ) := by nlinarith
        _ = B * (V.degree : ℝ) * A ^ h := by simp [hz]
    · have hbound := hmain C A hA P true hP hsep hcap (by intro _; exact hcard)
        V h hallowed (by omega) (by omega) hdim
      exact hbound.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmainB hdeg.le) hpow)


/-- conc:theorem.polynomial-sum, concentration.tex:75–78. The summed form of case (b)
needed by TrackE/Concentration.lean:112–124 has no cardinality hypothesis on P. -/
theorem uniform_concentration_polynomial (e : ℕ) (he : 3 ≤ e)
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ B : ℝ, 0 < B ∧ ∀ (C : SkewCoordinates e) (A : ℝ), 1 ≤ A →
      ∀ P : Finset (ProjectivePoint (e + e)),
        (∀ p ∈ P, p ∈ affineParameters e) → HasSeparators P (C0 * A) →
        HasIsotropicCap P (C0 * A ^ (e - 2)) →
        ∀ f : Poly (skewDim e), f ≠ 0 → (f.totalDegree : ℝ) ≤ C0 * A →
          (containedFlatCount C P (AffineVariety.ofIdeal (Ideal.span {f})) : ℝ) ≤
            B * (f.totalDegree : ℝ) * A ^ (e - 2) := by
  classical
  obtain ⟨B, hB, hmain⟩ := uniform_concentration e he C0 hC0
  refine ⟨B, hB, ?_⟩
  intro C A hA P hP hsep hcap f hf hfdegree
  let H := AffineVariety.ofIdeal (Ideal.span {f})
  have hchoose : skewDim e = flatDim e + (e - 1) := by
    simp only [skewDim, flatDim]
    rw [show e = (e - 1) + 1 by omega, Nat.choose_succ_succ']
    simp [Nat.choose_one_right, Nat.add_comm]
  have hbotdim : OAI.QuarticPowerFree.affineDimension (⊥ : Ideal (Poly (skewDim e))) =
      (flatDim e + (e - 2)) + 1 := by
    have h := Bridges.affine_whole_dimension (skewDim e)
    simp only [AffineVariety.whole, AffineVariety.ofIdeal,
      Ideal.radical_bot_of_isReduced] at h
    change OAI.QuarticPowerFree.affineDimension (⊥ : Ideal (Poly (skewDim e))) =
      skewDim e at h
    rw [h, hchoose]
    omega
  have hbotdegree : OAI.QuarticPowerFree.affineDegree (⊥ : Ideal (Poly (skewDim e))) = 1 := by
    simpa only [AffineVariety.whole, AffineVariety.ofIdeal,
      Ideal.radical_bot_of_isReduced] using whole_degree (skewDim e)
  have hQ (W : H.Component) : W.val ∈
      ((⊥ : Ideal (Poly (skewDim e))) ⊔ Ideal.span {f}).minimalPrimes := by
    simpa [H, AffineVariety.ofIdeal, Ideal.radical_minimalPrimes] using W.property
  have hsum : (∑ W : H.Component, W.variety.degree) ≤ (f.totalDegree : ℚ) := by
    change (∑ W : H.Component, OAI.QuarticPowerFree.affineDegree W.val) ≤
      (f.totalDegree : ℚ)
    have hs := OAI.QuarticPowerFree.proper_cut_sum_affineDegree_le
      (⊥ : Ideal (Poly (skewDim e))) f (by simpa using hf) hbotdim
      (fun W : H.Component => W.val) hQ Subtype.val_injective
    simpa only [hbotdegree, mul_one] using hs
  have hsumR : (∑ W : H.Component, (W.variety.degree : ℝ)) ≤ (f.totalDegree : ℝ) := by
    exact_mod_cast hsum
  have hcomponent (W : H.Component) : (containedFlatCount C P W.variety : ℝ) ≤
      B * (W.variety.degree : ℝ) * A ^ (e - 2) := by
    letI : W.val.IsPrime := W.property.isPrime
    have hdim : W.variety.dimension = flatDim e + (e - 2) :=
      OAI.QuarticPowerFree.proper_cut_component_dimension
        (⊥ : Ideal (Poly (skewDim e))) W.val f (by simpa using hf) (hQ W) hbotdim
    have hmem : f ∈ W.variety.ideal := by
      exact (hQ W).le (by simp)
    have hproper : W.variety ≠ AffineVariety.whole := by
      intro hwhole
      rw [hwhole] at hmem
      apply hf
      simpa [AffineVariety.whole, AffineVariety.ofIdeal,
        Ideal.radical_bot_of_isReduced] using hmem
    have hallowed : AllowedCarrier false A C0 W.variety :=
      ⟨W.irreducible, hproper, Or.inr ⟨f, hf, hmem, hfdegree⟩⟩
    exact hmain C A hA P false hP hsep hcap (by simp) W.variety (e - 2)
      hallowed (by omega) (by omega) hdim
  have hcover : (containedFlatCount C P H : ℝ) ≤
      ∑ W : H.Component, (containedFlatCount C P W.variety : ℝ) := by
    exact_mod_cast contained_count_components_le C P hP H
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  calc
    (containedFlatCount C P H : ℝ) ≤
        ∑ W : H.Component, (containedFlatCount C P W.variety : ℝ) := hcover
    _ ≤ ∑ W : H.Component, B * (W.variety.degree : ℝ) * A ^ (e - 2) :=
      Finset.sum_le_sum (fun W hW => hcomponent W)
    _ = B * (∑ W : H.Component, (W.variety.degree : ℝ)) * A ^ (e - 2) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ B * (f.totalDegree : ℝ) * A ^ (e - 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsumR hB.le)
        (pow_pos hApos _).le


#print axioms uniform_concentration_all_dimensions
#print axioms uniform_concentration_polynomial

end
end DistinctDistances.TrackB
